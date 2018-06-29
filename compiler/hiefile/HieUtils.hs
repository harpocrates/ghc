{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
module HieUtils where

import Prelude hiding (span)
import HieTypes
import SrcLoc
import Name hiding (varName)
import Type
import TyCoRep
import TyCon
import Var
import FastString (FastString)
import Data.Monoid
import Data.Maybe
import Data.Traversable
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import qualified Data.Array as A
import DynFlags (DynFlags)
import Outputable (renderWithStyle, ppr, defaultUserStyle)

import Control.Monad.Trans.State.Strict hiding (get)

import CoreMap
import IfaceType
import ToIface
import VarEnv

generateReferencesMap :: Foldable f => f (HieAST a) -> M.Map Identifier [(Span, IdentifierDetails a)]
generateReferencesMap asts = foldr (\ast m -> M.unionWith (++) (go ast) m) M.empty asts
  where
    go ast = M.unionsWith (++) (this : map go (nodeChildren ast))
      where this = fmap (pure . (nodeSpan ast,)) $ nodeIdentifiers $ nodeInfo ast

renderHieType :: DynFlags -> HieTypeFix -> String
renderHieType df ht = renderWithStyle df (ppr $ hieTypeToIface ht) (defaultUserStyle df)

resolveVisibility :: Type -> [Type] -> [(Bool,Type)]
resolveVisibility kind ty_args
  = go (mkEmptyTCvSubst in_scope) kind ty_args
  where
    in_scope = mkInScopeSet (tyCoVarsOfTypes ty_args)

    go _   _                   []     = []
    go env ty                  ts
      | Just ty' <- coreView ty
      = go env ty' ts
    go env (ForAllTy (TvBndr tv vis) res) (t:ts)
      | isVisibleArgFlag vis = (True , t) : ts'
      | otherwise            = (False, t) : ts'
      where
        ts' = go (extendTvSubst env tv t) res ts

    go env (FunTy _ res) (t:ts) -- No type-class args in tycon apps
      = (True,t) : (go env res ts)

    go env (TyVarTy tv) ts
      | Just ki <- lookupTyVar env tv = go env ki ts
    go env kind (t:ts) = (True, t) : (go env kind ts) -- Ill-kinded

foldType :: (HieType a -> a) -> HieTypeFix -> a
foldType f (Roll t) = f $ fmap (foldType f) t

hieTypeToIface :: HieTypeFix -> IfaceType
hieTypeToIface = foldType go
  where
    go (HTyVarTy n) = IfaceTyVar $ occNameFS $ getOccName n
    go (HAppTy a b) = IfaceAppTy a (hieToIfaceArgs b)
    go (HLitTy l) = IfaceLitTy l
    go (HForAllTy ((n,k),af) t) = IfaceForAllTy (TvBndr (occNameFS $ getOccName n, k) af) t
    go (HFunTy pred a b)
      | pred = IfaceDFunTy a b
      | otherwise = IfaceFunTy a b
    go (HCastTy a) = a
    go HCoercionTy = IfaceTyVar "<coercion type>"
    go (HTyConApp a xs) = IfaceTyConApp a (hieToIfaceArgs xs)

    hieToIfaceArgs :: HieArgs IfaceType -> IfaceAppArgs
    hieToIfaceArgs (HieArgs xs) = go' xs
      where
        go' [] = IA_Nil
        go' ((True ,x):xs) = IA_Vis x $ go' xs
        go' ((False,x):xs) = IA_Invis x $ go' xs

data HieTypeState
  = HTS
    { tyMap      :: !(TypeMap TypeIndex)
    , htyTable   :: !(IM.IntMap HieTypeFlat)
    , freshIndex :: !TypeIndex
    }

initialHTS :: HieTypeState
initialHTS = HTS emptyTypeMap IM.empty 0

freshTypeIndex :: State HieTypeState TypeIndex
freshTypeIndex = do
  index <- gets freshIndex
  modify' $ \hts -> hts { freshIndex = index+1 }
  return index

compressTypes :: HieASTs Type -> (HieASTs TypeIndex, A.Array TypeIndex HieTypeFlat)
compressTypes asts = (a, arr)
  where
    (a, (HTS _ m i)) = flip runState initialHTS $
      for asts $ \typ -> do
        i <- getTypeIndex typ
        return i
    arr = A.array (0,i-1) (IM.toList m)

recoverFullType :: TypeIndex -> A.Array TypeIndex HieTypeFlat -> HieTypeFix
recoverFullType i m = go i
  where
    go i = Roll $ fmap go (m A.! i)

getTypeIndex :: Type -> State HieTypeState TypeIndex
getTypeIndex t
  | otherwise = do
      tm <- gets tyMap
      case lookupTypeMap tm t of
        Just i -> return i
        Nothing -> do
          ht <- go t
          extendHTS t ht
  where
    extendHTS t ht = do
      i <- freshTypeIndex
      modify' $ \(HTS tm tt fi) ->
        HTS (extendTypeMap tm t i) (IM.insert i ht tt) fi
      return i

    go (TyVarTy v) = return $ HTyVarTy $ varName v
    go ty@(AppTy _ _) = do
      let (head,args) = splitAppTys ty
          visArgs = HieArgs $ resolveVisibility (typeKind head) args
      ai <- getTypeIndex head
      argsi <- mapM getTypeIndex visArgs
      return $ HAppTy ai argsi
    go (TyConApp f xs) = do
      let visArgs = HieArgs $ resolveVisibility (tyConKind f) xs
      is <- mapM getTypeIndex visArgs
      return $ HTyConApp (toIfaceTyCon f) is
    go (ForAllTy (TvBndr v a) t) = do
      k <- getTypeIndex (varType v)
      i <- getTypeIndex t
      return $ HForAllTy ((varName v,k),a) i
    go (FunTy a b) = do
      ai <- getTypeIndex a
      bi <- getTypeIndex b
      return $ HFunTy (isPredTy a) ai bi
    go (LitTy a) = return $ HLitTy $ toIfaceTyLit a
    go (CastTy t _) = do
      i <- getTypeIndex t
      return $ HCastTy i
    go (CoercionTy _) = return HCoercionTy

resolveTyVarScopes :: M.Map FastString (HieAST a) -> M.Map FastString (HieAST a)
resolveTyVarScopes asts = M.map go asts
  where
    go ast = resolveTyVarScopeLocal ast asts

resolveTyVarScopeLocal :: HieAST a -> M.Map FastString (HieAST a) -> HieAST a
resolveTyVarScopeLocal ast asts = go ast
  where
    resolveNameScope dets = dets{identInfo = S.map resolveScope (identInfo dets)}
    resolveScope (TyVarBind sc (UnresolvedScope names Nothing)) =
      TyVarBind sc $ ResolvedScopes
        $ concatMap (\name -> map LocalScope $ maybeToList $ getNameBinding name asts) names
    resolveScope (TyVarBind sc (UnresolvedScope names (Just sp))) =
      TyVarBind sc $ ResolvedScopes
        $ concatMap (\name ->
            map LocalScope $ maybeToList $ getNameBindingInClass name sp asts) names
    resolveScope scope = scope
    go (Node info span children) = Node info' span $ map go children
      where
        info' = info { nodeIdentifiers = idents }
        idents = M.map resolveNameScope $ nodeIdentifiers info

getNameBinding :: Name -> M.Map FastString (HieAST a) -> Maybe Span
getNameBinding n asts = do
  (_,msp) <- getNameScopeAndBinding n asts
  msp

getNameScope :: Name -> M.Map FastString (HieAST a) -> Maybe [Scope]
getNameScope n asts = do
  (scopes,_) <- getNameScopeAndBinding n asts
  return scopes

getNameBindingInClass :: Name -> Span -> M.Map FastString (HieAST a) -> Maybe Span
getNameBindingInClass n sp asts = do
  ast <- M.lookup (srcSpanFile sp) asts
  getFirst $ foldMap First $ do
    child <- flattenAst ast
    dets <- maybeToList
      $ M.lookup (Right n) $ nodeIdentifiers $ nodeInfo child
    let binding = getFirst $ foldMap (First . getBindSiteFromContext) (identInfo dets)
    return binding

getNameScopeAndBinding :: Name -> M.Map FastString (HieAST a) -> Maybe ([Scope], Maybe Span)
getNameScopeAndBinding n asts = case nameSrcSpan n of
  RealSrcSpan sp -> do -- @Maybe
    ast <- M.lookup (srcSpanFile sp) asts
    defNode <- selectLargestContainedBy sp ast
    getFirst $ foldMap First $ do -- @[]
      node <- flattenAst defNode
      dets <- maybeToList
        $ M.lookup (Right n) $ nodeIdentifiers $ nodeInfo node
      scopes <- maybeToList $ foldMap getScopeFromContext (identInfo dets)
      let binding = getFirst $ foldMap (First . getBindSiteFromContext) (identInfo dets)
      return $ Just (scopes, binding)
  _ -> Nothing

getScopeFromContext :: ContextInfo -> Maybe [Scope]
getScopeFromContext (ValBind _ sc _) = Just [sc]
getScopeFromContext (PatternBind a b _) = Just [a, b]
getScopeFromContext (ClassTyDecl _) = Just [ModuleScope]
getScopeFromContext (Decl _ _) = Just [ModuleScope]
getScopeFromContext (TyVarBind a (ResolvedScopes xs)) = Just $ a:xs
getScopeFromContext (TyVarBind a _) = Just [a]
getScopeFromContext _ = Nothing

getBindSiteFromContext :: ContextInfo -> Maybe Span
getBindSiteFromContext (ValBind _ _ sp) = sp
getBindSiteFromContext (PatternBind _ _ sp) = sp
getBindSiteFromContext _ = Nothing

flattenAst :: HieAST a -> [HieAST a]
flattenAst n =
  n : concatMap flattenAst (nodeChildren n)

smallestContainingSatisfying :: Span -> (HieAST a -> Bool) -> HieAST a -> Maybe (HieAST a)
smallestContainingSatisfying sp cond node
  | nodeSpan node `containsSpan` sp = getFirst $ mconcat
      [ foldMap (First . smallestContainingSatisfying sp cond) $ nodeChildren node
      , First $ if cond node then Just node else Nothing
      ]
  | sp `containsSpan` nodeSpan node = Nothing
  | otherwise = Nothing

selectLargestContainedBy :: Span -> HieAST a -> Maybe (HieAST a)
selectLargestContainedBy sp node
  | sp `containsSpan` nodeSpan node = Just node
  | nodeSpan node `containsSpan` sp =
      getFirst $ foldMap (First . selectLargestContainedBy sp) $ nodeChildren node
  | otherwise = Nothing

selectSmallestContaining :: Span -> HieAST a -> Maybe (HieAST a)
selectSmallestContaining sp node
  | nodeSpan node `containsSpan` sp = getFirst $ mconcat
      [ foldMap (First . selectSmallestContaining sp) $ nodeChildren node
      , First (Just node)
      ]
  | sp `containsSpan` nodeSpan node = Nothing
  | otherwise = Nothing

definedInAsts :: M.Map FastString (HieAST a) -> Name -> Bool
definedInAsts asts n = case nameSrcSpan n of
  RealSrcSpan sp -> srcSpanFile sp `elem` M.keys asts
  _ -> False

isOccurrence :: ContextInfo -> Bool
isOccurrence Use = True
isOccurrence _ = False

scopeContainsSpan :: Scope -> Span -> Bool
scopeContainsSpan NoScope _ = False
scopeContainsSpan ModuleScope _ = True
scopeContainsSpan (LocalScope a) b = a `containsSpan` b

-- | One must contain the other. Leaf nodes cannot contain anything
combineAst :: Ord a => HieAST a -> HieAST a -> HieAST a
combineAst a@(Node aInf aSpn xs) b@(Node bInf bSpn ys)
  | aSpn == bSpn = Node (aInf <> bInf) aSpn (mergeAsts xs ys)
  | aSpn `containsSpan` bSpn = combineAst b a
combineAst a (Node xs span children) = Node xs span (insertAst a children)

-- | Insert an AST in a sorted list of disjoint Asts
insertAst :: Ord a => HieAST a -> [HieAST a] -> [HieAST a]
insertAst x = mergeAsts [x]

-- Merge two sorted, disjoint lists of ASTs, combining when necessary
mergeAsts :: Ord a => [HieAST a] -> [HieAST a] -> [HieAST a]
mergeAsts xs [] = xs
mergeAsts [] ys = ys
mergeAsts xs@(a:as) ys@(b:bs)
  | nodeSpan a `containsSpan` nodeSpan b = mergeAsts (combineAst a b : as) bs
  | nodeSpan b `containsSpan` nodeSpan a = mergeAsts as (combineAst a b : bs)
  | nodeSpan a `rightOf` nodeSpan b = b : mergeAsts xs bs
  | nodeSpan a `leftOf`  nodeSpan b = a : mergeAsts as ys
  | otherwise = error $ "mergeAsts: Spans overlapping"

rightOf :: Span -> Span -> Bool
rightOf s1 s2
  = (srcSpanStartLine s1, srcSpanStartCol s1)
       >= (srcSpanEndLine s2, srcSpanEndCol s2)
    && (srcSpanFile s1 == srcSpanFile s2)

leftOf :: Span -> Span -> Bool
leftOf s1 s2
  = (srcSpanEndLine s1, srcSpanEndCol s1)
       <= (srcSpanStartLine s2, srcSpanStartCol s2)
    && (srcSpanFile s1 == srcSpanFile s2)

-- | combines and sorts ASTs using a merge sort
mergeSortAsts :: Ord a => [HieAST a] -> [HieAST a]
mergeSortAsts = go . map pure
  where
    go [] = []
    go [xs] = xs
    go xss = go (mergePairs xss)
    mergePairs [] = []
    mergePairs [xs] = [xs]
    mergePairs (xs:ys:xss) = mergeAsts xs ys : mergePairs xss

simpleNodeInfo :: FastString -> FastString -> NodeInfo a
simpleNodeInfo cons typ = NodeInfo (S.singleton (cons, typ)) [] M.empty

locOnly :: SrcSpan -> [HieAST a]
locOnly (RealSrcSpan span) =
  [Node e span []]
    where e = NodeInfo S.empty [] M.empty
locOnly _ = []

mkScope :: SrcSpan -> Scope
mkScope (RealSrcSpan sp) = LocalScope sp
mkScope _ = NoScope

mkLScope :: Located a -> Scope
mkLScope = mkScope . getLoc

combineScopes :: Scope -> Scope -> Scope
combineScopes ModuleScope _ = ModuleScope
combineScopes _ ModuleScope = ModuleScope
combineScopes NoScope x = x
combineScopes x NoScope = x
combineScopes (LocalScope a) (LocalScope b) =
  mkScope $ combineSrcSpans (RealSrcSpan a) (RealSrcSpan b)

makeNode :: Applicative m => FastString -> SrcSpan -> FastString -> m [HieAST a]
makeNode typ (RealSrcSpan span) cons = pure [Node (simpleNodeInfo cons typ) span []]
makeNode _ _ _ = pure []

makeTypeNode :: FastString -> FastString -> SrcSpan -> Type -> [HieAST Type]
makeTypeNode cons typ spn etyp = case spn of
  RealSrcSpan span ->
    [Node (NodeInfo (S.singleton (cons,typ)) [etyp] M.empty) span []]
  _ -> []
