{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module HieAst (mkHieFile) where

import Class (FunDep)
import BasicTypes
import FieldLabel
import BooleanFormula
import Bag (Bag, bagToList)
import Var
import FastString (FastString)
import ConLike (conLikeName)
import TcHsSyn (hsPatType)
import MonadUtils
import Desugar (deSugarExpr)
import CoreUtils (exprType)
import HsSyn
import HscTypes
import Avail
import Type
import SrcLoc
import Name hiding (varName)
import Module

import HieTypes
import HieUtils

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Array as A
import Data.List hiding (span)
import qualified Data.ByteString as BS
import Data.Coerce
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class

import GhcPrelude

type RenamedSource     = (HsGroup GhcRn, [LImportDecl GhcRn], Maybe [(LIE GhcRn, Avails)],
                          Maybe LHsDocString)
type TypecheckedSource = LHsBinds GhcTc


{- Note [Name Remapping]
The Typechecker introduces new names for mono names in AbsBinds.
We don't care about the distinction between mono and poly bindings,
so we replace all occurrences of the mono name with the poly name.
-}
newtype HieState = HieState
  { name_remapping :: M.Map Name Id
  }

initState :: HieState
initState = HieState M.empty

class ModifyState a where -- See Note [Name Remapping]
  addSubstitution :: a -> a -> HieState -> HieState

instance ModifyState Name where
  addSubstitution _ _ hs = hs

instance ModifyState Id where
  addSubstitution mono poly hs =
    hs{name_remapping = M.insert (varName mono) poly (name_remapping hs)}

modifyState :: ModifyState (IdP p) => [ABExport p] -> HieState -> HieState
modifyState = foldr go id
  where
    go ABE{abe_poly=poly,abe_mono=mono} f = addSubstitution mono poly . f
    go _ f = f

type HieM = ReaderT HieState Hsc

mkHieFile :: ModSummary -> TypecheckedSource -> RenamedSource
  -> Hsc HieFile
mkHieFile ms ts rs = do
  (asts', arr) <- getCompressedAsts ts rs
  let Just src_file = ml_hs_file $ ms_location ms
  src <- liftIO $ BS.readFile src_file
  return $ HieFile
      { hieVersion = curHieVersion
      , ghcVersion = "8.7"
      , hsFile = src_file
      , hieTypes = arr
      , hieAST = asts'
      , hsSrc = src
      }

getCompressedAsts :: TypecheckedSource -> RenamedSource
  -> Hsc (HieASTs TypeIndex, A.Array TypeIndex HieTypeFlat)
getCompressedAsts ts rs = do
  asts <- enrichHie ts rs
  return $ compressTypes $ coerce asts

enrichHie :: TypecheckedSource -> RenamedSource -> Hsc (HieASTs CmpType)
enrichHie ts (hsGrp, imports, exports, _) = flip runReaderT initState $ do
    tasts <- toHie $ fmap (BC RegularBind ModuleScope) ts
    rasts <- processGrp hsGrp
    imps <- toHie $ filter (not . ideclImplicit . unLoc) imports
    exps <- toHie $ fmap (map $ IEC Export . fst) exports
    let spanFile children = case children of
          [] -> mkRealSrcSpan (mkRealSrcLoc "" 1 1) (mkRealSrcLoc "" 1 1)
          _ -> mkRealSrcSpan (realSrcSpanStart $ nodeSpan $ head children)
                             (realSrcSpanEnd   $ nodeSpan $ last children)

        modulify xs =
          Node (simpleNodeInfo "Module" "Module") (spanFile xs) xs

        asts = HieASTs
          $ resolveTyVarScopes
          $ M.map (modulify . mergeSortAsts . coerce)
          $ M.fromListWith (++) $ map (\x -> (srcSpanFile (nodeSpan x),[x])) flat_asts

        flat_asts = concat
          [ tasts
          , rasts
          , imps
          , exps
          ]
    return asts
  where
    processGrp grp = concatM
      [ toHie $ fmap (RS ModuleScope ) hs_valds grp
      , toHie $ hs_splcds grp
      , toHie $ hs_tyclds grp
      , toHie $ hs_derivds grp
      , toHie $ hs_fixds grp
      , toHie $ hs_defds grp
      , toHie $ hs_fords grp
      , toHie $ hs_warnds grp
      , toHie $ hs_annds grp
      , toHie $ hs_ruleds grp
      ]

getRealSpan :: SrcSpan -> Maybe Span
getRealSpan (RealSrcSpan sp) = Just sp
getRealSpan _ = Nothing

grhss_span :: GRHSs p body -> SrcSpan
grhss_span (GRHSs _ xs binds) = foldr combineSrcSpans (getLoc binds) (getLoc <$> xs)
grhss_span (XGRHSs _) = error "XGRHS has no span"

bindingsOnly :: [Context Name] -> [HieAST a]
bindingsOnly [] = []
bindingsOnly (C c n : xs) = case nameSrcSpan n of
  RealSrcSpan span ->
      Node (NodeInfo S.empty [] (M.singleton (Right n) info)) span [] : bindingsOnly xs
    where info = mempty{identInfo = S.singleton c}
  _ -> bindingsOnly xs

concatM :: Monad m => [m [a]] -> m [a]
concatM xs = concat <$> sequence xs

{- Note [Capturing Scopes and other non local information]
toHie is a local tranformation, but scopes of bindings cannot be known locally,
hence we have to push the relevant info down into the binding nodes.
We use the following types (*Context and *Scoped) to wrap things and
carry the required info
(Maybe Span) always carries the span of the entire binding, including rhs
-}
data Context a = C ContextInfo a -- Used for names and bindings

data RContext a = RC RecFieldContext a
data RFContext a = RFC RecFieldContext (Maybe Span) a
-- ^ context for record fields

data IEContext a = IEC IEType a
-- ^ context for imports/exports

data BindContext a = BC BindType Scope a
-- ^ context for imports/exports

data PatSynFieldContext a = PSC (Maybe Span) a
-- ^ context for pattern synonym fields.

data SigContext a = SC SigInfo a
-- ^ context for type signatures

data SigInfo = SI SigType (Maybe Span)

data SigType = BindSig | ClassSig | InstSig

data RScoped a = RS Scope a
-- ^ Scope spans over everything to the right of a, (mostly) not
-- including a itself
-- (Includes a in a few special cases like recursive do bindings) or
-- let/where bindings

data PScoped a = PS (Maybe Span) Scope Scope a -- Pattern Scope
-- ^ First Scope spans over the use site of the pattern, second spans over the
-- patterns to the right of a, not including a

{- Note [TyVar Scopes]
Due to -XScopedTypeVariables, type variables can be in scope quite far from
their original binding. We resolve the scope of these type variables
in a seperate pass
-}
data TScoped a = TS TyVarScope a -- TyVarScope

data TVScoped a = TVS TyVarScope Scope a -- TyVarScope
-- ^ First scope remains constant
-- Second scope is used to build up the scope of a tyvar over
-- things to its right, ala RScoped

-- | Each element scopes over the elements to the right
listScopes :: Scope -> [Located a] -> [RScoped (Located a)]
listScopes _ [] = []
listScopes rhsScope [pat] = [RS rhsScope pat]
listScopes rhsScope (pat : pats) = RS sc pat : pats'
  where
    pats'@((RS scope p):_) = listScopes rhsScope pats
    sc = combineScopes scope $ mkScope $ getLoc p

-- | listScopes specialised to PScoped things
patScopes :: Maybe Span -> Scope -> Scope -> [LPat a] -> [PScoped (LPat a)]
patScopes rsp useScope patScope xs =
  map (\(RS sc a) -> PS rsp useScope sc a) $ listScopes patScope xs

-- | listScopes specialised to TVScoped things
tvScopes :: TyVarScope -> Scope -> [LHsTyVarBndr a] -> [TVScoped (LHsTyVarBndr a)]
tvScopes tvScope rhsScope xs =
  map (\(RS sc a)-> TVS tvScope sc a) $ listScopes rhsScope xs

{- Note [Scoping Rules for SigPat]
Explicitly quantified variables in pattern type signatures are not
brought into scope in the rhs, but implicitly quantified variables
are (HsWC and HsIB).
This is unlike other signatures, where explicitly quantified variables
are brought into the RHS Scope
For example
foo :: forall a. ...;
foo = ... -- a is in scope here

bar (x :: forall a. a -> a) = ... -- a is not in scope here
--   ^ a is in scope here (pattern body)

bax (x :: a) = ... -- a is in scope here
Because of HsWC and HsIB pass on their scope to their children
we must wrap the LHsType in pattern signatures in a
Shielded explictly, so that the HsWC/HsIB scope is not passed
on the the LHsType
-}

data Shielded a = SH Scope a -- Ignores its TScope, uses its own scope instead

type family ProtectedSig a where
  ProtectedSig GhcRn = HsWildCardBndrs GhcRn (HsImplicitBndrs GhcRn (Shielded (LHsType GhcRn)))
  ProtectedSig GhcTc = NoExt

class ProtectSig a where
  protectSig :: Scope -> XSigPat a -> ProtectedSig a

instance (HasLoc a) => HasLoc (Shielded a) where
  loc (SH _ a) = loc a

instance (ToHie (TScoped a)) => ToHie (TScoped (Shielded a)) where
  toHie (TS _ (SH sc a)) = toHie (TS (ResolvedScopes [sc]) a)

instance ProtectSig GhcTc where
  protectSig _ _ = NoExt

instance ProtectSig GhcRn where
  protectSig sc (HsWC a (HsIB b sig)) =
    HsWC a (HsIB b (SH sc sig))
  protectSig _ _ = error "protectSig not given HsWC (HsIB)"

class HasLoc a where
  -- ^ defined so that HsImplicitBndrs and HsWildCardBndrs can
  -- know what their implicit bindings are scoping over
  loc :: a -> SrcSpan

instance HasLoc thing => HasLoc (TScoped thing) where
  loc (TS _ a) = loc a

instance HasLoc thing => HasLoc (PScoped thing) where
  loc (PS _ _ _ a) = loc a

instance HasLoc (LHsQTyVars GhcRn) where
  loc (HsQTvs _ vs) = loc vs
  loc _ = noSrcSpan

instance HasLoc thing => HasLoc (HsImplicitBndrs a thing) where
  loc (HsIB _ a) = loc a
  loc _ = noSrcSpan

instance HasLoc thing => HasLoc (HsWildCardBndrs a thing) where
  loc (HsWC _ a) = loc a
  loc _ = noSrcSpan

instance HasLoc (Located a) where
  loc (L l _) = l

instance HasLoc a => HasLoc [a] where
  loc [] = noSrcSpan
  loc xs = foldl1' combineSrcSpans $ map loc xs

instance (HasLoc a, HasLoc b) => HasLoc (FamEqn s a b) where
  loc (FamEqn _ a b _ c) = foldl1' combineSrcSpans [loc a, loc b, loc c]
  loc _ = noSrcSpan

instance HasLoc (HsDataDefn GhcRn) where
  loc def@(HsDataDefn{}) = loc $ dd_cons def
    -- Only used for data family instances, so we only need rhs
    -- Most probably the rest will be unhelpful anyway
  loc _ = noSrcSpan

-- | The main worker class
class ToHie a where
  toHie :: a -> HieM [HieAST Type]

-- | Used to collect type info
class HasType a where
  getTypeNode :: a -> FastString -> HieM [HieAST Type]
  -- ^ string carries constructor name

instance (ToHie a) => ToHie [a] where
  toHie = concatMapM toHie

instance (ToHie a) => ToHie (Bag a) where
  toHie = toHie . bagToList

instance (ToHie a) => ToHie (Maybe a) where
  toHie = maybe (pure []) toHie

instance ToHie (Context (Located NoExt)) where
  toHie _ = pure []

instance ToHie (TScoped NoExt) where
  toHie _ = pure []

instance ToHie (IEContext (Located ModuleName)) where
  toHie (IEC c (L (RealSrcSpan span) mname)) =
      pure $ [Node (NodeInfo S.empty [] idents) span []]
    where idents = M.singleton (Left mname) mempty{identInfo = S.singleton (IEThing c)}
  toHie _ = pure []

instance ToHie (Context (Located Var)) where
  toHie c = case c of
      C context (L (RealSrcSpan span) name')
        -> do
        m <- asks name_remapping
        let name = (M.findWithDefault name' (varName name') m){varType = varType name'}
        pure
          [Node
            (NodeInfo S.empty [] $
              M.singleton (Right $ varName name)
                          (IdentifierDetails (Just $ varType name)
                                             (S.singleton context)))
            span
            []]
      _ -> pure []

instance ToHie (Context (Located Name)) where
  toHie c = case c of
      C context (L (RealSrcSpan span) name') -> do
        m <- asks name_remapping
        let name = case M.lookup name' m of
              Just var -> varName var
              Nothing -> name'
        pure
          [Node
            (NodeInfo S.empty [] $
              M.singleton (Right name)
                          (IdentifierDetails Nothing
                                             (S.singleton context)))
            span
            []]
      _ -> pure []

-- | Dummy instances - never called
instance ToHie (TScoped (LHsSigWcType GhcTc)) where
  toHie _ = pure []
instance ToHie (TScoped (LHsWcType GhcTc)) where
  toHie _ = pure []
instance ToHie (SigContext (LSig GhcTc)) where
  toHie _ = pure []
instance ToHie (TScoped Type) where
  toHie _ = pure []

instance HasType (LHsBind GhcRn) where
  getTypeNode (L spn _) cons = makeNode "HsBindLR" spn cons

instance HasType (LHsBind GhcTc) where
  getTypeNode (L spn bind) cons = case bind of
      FunBind{fun_id = name} -> pure $ makeTypeNode cons "HsBindLR" spn (varType $ unLoc name)
      _ -> makeNode "HsBindLR" spn cons

instance HasType (LPat GhcRn) where
  getTypeNode (L spn _) cons = makeNode "Pat" spn cons

instance HasType (LPat GhcTc) where
  getTypeNode (L spn opat) cons =
    pure $ makeTypeNode cons "Pat" spn (hsPatType opat)

instance HasType (LHsExpr GhcRn) where
  getTypeNode (L spn _) cons = makeNode "HsExpr" spn cons

instance HasType (LHsExpr GhcTc) where
  getTypeNode e@(L spn _) cons = lift $ do
    hs_env <- Hsc $ \e w -> return (e,w)
    (_,mbe) <- liftIO $ deSugarExpr hs_env e
    case mbe of
      Just te -> pure $ makeTypeNode cons "HsExpr" spn (exprType te)
      Nothing -> makeNode "HsExpr" spn cons

instance ( ToHie (Context (Located (IdP a)))
         , ToHie (MatchGroup a (LHsExpr a))
         , ToHie (PScoped (LPat a))
         , ToHie (GRHSs a (LHsExpr a))
         , ToHie (LHsExpr a)
         , ToHie (Located (PatSynBind a a))
         , HasType (LHsBind a)
         , ModifyState (IdP a)
         ) => ToHie (BindContext (LHsBind a)) where
  toHie (BC context scope b@(L span bind)) = concatM $ case bind of
      FunBind{fun_id = name, fun_matches = matches} ->
        [ mkTypeNode "FunBind"
        , toHie $ C (ValBind context scope $ getRealSpan span) name
        , toHie matches
        ]
      PatBind{pat_lhs = lhs, pat_rhs = rhs} ->
        [ mkNode "PatBind"
        , toHie $ PS (getRealSpan span) scope NoScope lhs
        , toHie rhs
        ]
      VarBind{var_rhs = expr} ->
        [ mkNode "VarBind"
        , toHie expr
        ]
      AbsBinds{abs_exports = xs, abs_binds = binds} ->
        [ mkNode "AbsBinds"
        , local (modifyState xs) $ -- Note [Name Remapping]
            toHie $ fmap (BC context scope) binds
        ]
      PatSynBind _ psb ->
        [ mkNode "PatSynBind"
        , toHie $ L span psb -- PatSynBinds only occur at the top level
        ]
      XHsBindsLR _ -> []
    where mkNode = makeNode "HsBindLR" span
          mkTypeNode cons = getTypeNode b cons

instance ( ToHie (LMatch a body)
         ) => ToHie (MatchGroup a body) where
  toHie mg = concatM $ case mg of
    MG{ mg_alts = (L span alts) , mg_origin = FromSource } ->
      [ pure $ locOnly span -- causes crash in compiler/prelude/PrimOp.hs
      , toHie alts
      ]
    MG{} -> []
    XMatchGroup _ -> []

instance ( ToHie (Context (Located (IdP a)))
         , ToHie (PScoped (LPat a))
         , ToHie (HsPatSynDir a)
         ) => ToHie (Located (PatSynBind a a)) where
    toHie (L sp psb) = concatM $ case psb of
      PSB{psb_id=var, psb_args=dets, psb_def=pat, psb_dir=dir} ->
        [ toHie $ C (Decl PatSynDec $ getRealSpan sp) var
        , toHie $ toBind dets
        , toHie $ PS Nothing lhsScope NoScope pat
        , toHie dir
        ]
        where
          lhsScope = combineScopes varScope detScope
          varScope = mkLScope var
          detScope = case dets of
            (PrefixCon args) -> foldr combineScopes NoScope $ map mkLScope args
            (InfixCon a b) -> combineScopes (mkLScope a) (mkLScope b)
            (RecCon r) -> foldr go NoScope r
          go (RecordPatSynField a b) c = combineScopes c
            $ combineScopes (mkLScope a) (mkLScope b)
          detSpan = case detScope of
            LocalScope a -> Just a
            _ -> Nothing
          toBind (PrefixCon args) = PrefixCon $ map (C Use) args
          toBind (InfixCon a b) = InfixCon (C Use a) (C Use b)
          toBind (RecCon r) = RecCon $ map (PSC detSpan) r
      XPatSynBind _ -> []

instance ( ToHie (MatchGroup a (LHsExpr a))
         ) => ToHie (HsPatSynDir a) where
  toHie dir = case dir of
    ExplicitBidirectional mg -> toHie mg
    _ -> pure []

instance ( ToHie body
         , ToHie (HsMatchContext (NameOrRdrName (IdP a)))
         , ToHie (PScoped (LPat a))
         , ToHie (GRHSs a body)
         ) => ToHie (LMatch a body) where
  toHie (L span m ) = concatM $ case m of
    Match{m_ctxt=mctx, m_pats = pats, m_grhss =  grhss } ->
      [ makeNode "Match" span "Match"
      , toHie mctx
      , let rhsScope = mkScope $ grhss_span grhss
          in toHie $ patScopes Nothing rhsScope NoScope pats
      , toHie grhss
      ]
    XMatch _ -> []

instance ( ToHie (Context (Located a))
         ) => ToHie (HsMatchContext a) where
  toHie (FunRhs{mc_fun=name}) = toHie $ C MatchBind name
  toHie (StmtCtxt a) = toHie a
  toHie _ = pure []

instance ( ToHie (HsMatchContext a)
         ) => ToHie (HsStmtContext a) where
  toHie (PatGuard a) = toHie a
  toHie (ParStmtCtxt a) = toHie a
  toHie (TransStmtCtxt a) = toHie a
  toHie _ = pure []

instance ( ToHie (Context (Located (IdP a)))
         , ToHie (RContext (HsRecFields a (PScoped (LPat a))))
         , ToHie (LHsExpr a)
         , ToHie (TScoped (LHsSigWcType a))
         , ProtectSig a
         , ToHie (TScoped (ProtectedSig a))
         , HasType (LPat a)
         ) => ToHie (PScoped (LPat a)) where
  toHie (PS rsp scope pscope lpat@(L ospan opat)) = concatM $ case opat of
      WildPat _ ->
        [ mkNode "WildPat"
        ]
      VarPat _ lname ->
        [ mkNode "VarPat"
        , toHie $ C (PatternBind scope pscope rsp) lname
        ]
      LazyPat _ p ->
        [ mkNode "LazyPat"
        , toHie $ PS rsp scope pscope p
        ]
      AsPat _ lname pat ->
        [ mkNode "AsPat"
        , toHie $ C (PatternBind scope (combineScopes (mkLScope pat) pscope) rsp) lname
        , toHie $ PS rsp scope pscope pat
        ]
      ParPat _ pat ->
        [ mkNode "ParPat"
        , toHie $ PS rsp scope pscope pat
        ]
      BangPat _ pat ->
        [ mkNode "BangPat"
        , toHie $ PS rsp scope pscope pat
        ]
      ListPat _ pats ->
        [ mkNode "ListPat"
        , toHie $ patScopes rsp scope pscope pats
        ]
      TuplePat _ pats _ ->
        [ mkNode "TuplePat"
        , toHie $ patScopes rsp scope pscope pats
        ]
      SumPat _ pat _ _ ->
        [ mkNode "SumPat"
        , toHie $ PS rsp scope pscope pat
        ]
      ConPatIn c dets ->
        [ mkNode "ConPatIn"
        , toHie $ C Use c
        , toHie $ contextify dets
        ]
      ConPatOut {pat_con = con, pat_args = dets}->
        [ mkNode "ConPatIn"
        , toHie $ C Use $ fmap conLikeName con
        , toHie $ contextify dets
        ]
      ViewPat _ expr pat ->
        [ mkNode "ViewPat"
        , toHie expr
        , toHie $ PS rsp scope pscope pat
        ]
      SplicePat _ sp ->
        [ mkNode "SplicePat"
        , toHie $ L ospan sp
        ]
      LitPat _ _ ->
        [ mkNode "LitPat"
        ]
      NPat _ _ _ _ ->
        [ mkNode "NPat"
        ]
      NPlusKPat _ n _ _ _ _ ->
        [ mkNode "NPlusKPat"
        , toHie $ C (PatternBind scope pscope rsp) n
        ]
      SigPat sig pat ->
        [ mkNode "SigPat"
        , toHie $ PS rsp scope pscope pat
        , let cscope = mkLScope pat in
            toHie $ TS (ResolvedScopes [cscope, scope, pscope]) (protectSig @a cscope sig)
              -- See Note [Scoping Rules for SigPat]
        ]
      CoPat _ _ _ _ ->
        [ mkNode "CoPat"
        ]
      XPat _ -> []
    where mkNode cons = getTypeNode lpat cons
          contextify (PrefixCon args) = PrefixCon $ patScopes rsp scope pscope args
          contextify (InfixCon a b) = InfixCon a' b'
            where [a', b'] = patScopes rsp scope pscope [a,b]
          contextify (RecCon r) = RecCon $ RC RecFieldMatch $ contextify_rec r
          contextify_rec (HsRecFields fields a) = HsRecFields (map go $ scoped_fields) a
            where
              go (RS fscope (L spn (HsRecField lbl pat pun))) =
                L spn $ HsRecField lbl (PS rsp scope fscope pat) pun
              scoped_fields = listScopes pscope fields

instance ( ToHie body
         , ToHie (LGRHS a body)
         , ToHie (RScoped (LHsLocalBinds a))
         ) => ToHie (GRHSs a body) where
  toHie grhs = concatM $ case grhs of
    GRHSs _ grhss binds ->
     [ toHie grhss
     , toHie $ RS (mkScope $ grhss_span grhs) binds
     ]
    XGRHSs _ -> []

instance ( ToHie (Located body)
         , ToHie (RScoped (GuardLStmt a))
         ) => ToHie (LGRHS a (Located body)) where
  toHie (L span g) = concatM $ case g of
    GRHS _ guards body ->
      [ makeNode "GRHS" span "GRHS"
      , toHie $ listScopes (mkLScope body) guards
      , toHie body
      ]
    XGRHS _ -> []

instance ( ToHie (Context (Located (IdP a)))
         , HasType (LHsExpr a)
         , ToHie (PScoped (LPat a))
         , ToHie (MatchGroup a (LHsExpr a))
         , ToHie (LGRHS a (LHsExpr a))
         , ToHie (RContext (HsRecordBinds a))
         , ToHie (RFContext (Located (AmbiguousFieldOcc a)))
         , ToHie (ArithSeqInfo a)
         , ToHie (LHsCmdTop a)
         , ToHie (RScoped (GuardLStmt a))
         , ToHie (RScoped (LHsLocalBinds a))
         , ToHie (TScoped (XAppTypeE a))
         , ToHie (TScoped (XExprWithTySig a))
         ) => ToHie (LHsExpr a) where
  toHie e@(L mspan oexpr) = concatM $ case oexpr of
      HsVar _ (L _ var) ->
        [ mkNode "HsVar"
        , toHie $ C Use (L mspan var) -- Patch up var location since typechecker removes it
        ]
      HsUnboundVar _ _ ->
        [ mkNode "HsUnboundVar"
        ]
      HsConLikeOut _ con ->
        [ mkNode "ConLikeOut"
        , toHie $ C Use $ L mspan $ conLikeName con
        ]
      HsRecFld _ fld ->
        [ mkNode "HsRecFld"
        , toHie $ RFC RecFieldOcc Nothing (L mspan fld)
        ]
      HsOverLabel _ _ _ ->
        [ mkNode "HsOverLable"
        ]
      HsIPVar _ _ ->
        [ mkNode "HsIPVar"
        ]
      HsOverLit _ _ ->
        [ mkNode "HsOverLit"
        ]
      HsLit _ _ ->
        [ mkNode "HsLit"
        ]
      HsLam _ mg ->
        [ mkNode "HsLam"
        , toHie mg
        ]
      HsLamCase _ mg ->
        [ mkNode "HsLamCase"
        , toHie mg
        ]
      HsApp _ a b ->
        [ mkNode "HsApp"
        , toHie a
        , toHie b
        ]
      HsAppType sig expr ->
        [ mkNode "HsAppType"
        , toHie expr
        , toHie $ TS (ResolvedScopes []) sig
        ]
      OpApp _ a b c ->
        [ mkNode "OpApp"
        , toHie a
        , toHie b
        , toHie c
        ]
      NegApp _ a _ ->
        [ mkNode "NegApp"
        , toHie a
        ]
      HsPar _ a ->
        [ mkNode "HsPar"
        , toHie a
        ]
      SectionL _ a b ->
        [ mkNode "SectionL"
        , toHie a
        , toHie b
        ]
      SectionR _ a b ->
        [ mkNode "SectionR"
        , toHie a
        , toHie b
        ]
      ExplicitTuple _ args _ ->
        [ mkNode "ExplicitTuple"
        , toHie args
        ]
      ExplicitSum _ _ _ expr ->
        [ mkNode "ExplicitSum"
        , toHie expr
        ]
      HsCase _ expr matches ->
        [ mkNode "HsCase"
        , toHie expr
        , toHie matches
        ]
      HsIf _ _ a b c ->
        [ mkNode "HsIf"
        , toHie a
        , toHie b
        , toHie c
        ]
      HsMultiIf _ grhss ->
        [ mkNode "HsMultiIf"
        , toHie grhss
        ]
      HsLet _ binds expr ->
        [ mkNode "HsLet"
        , toHie $ RS (mkLScope expr) binds
        , toHie expr
        ]
      HsDo _ _ (L ispan stmts) ->
        [ mkNode "HsDo"
        , pure $ locOnly ispan
        , toHie $ listScopes NoScope stmts
        ]
      ExplicitList _ _ exprs ->
        [ mkNode "ExplicitList"
        , toHie exprs
        ]
      RecordCon {rcon_con_name = name, rcon_flds = binds}->
        [ mkNode "RecordCon"
        , toHie $ C Use name
        , toHie $ RC RecFieldAssign $ binds
        ]
      RecordUpd {rupd_expr = expr, rupd_flds = upds}->
        [ mkNode "RecordUpd"
        , toHie expr
        , toHie $ map (RC RecFieldAssign) upds
        ]
      ExprWithTySig sig expr ->
        [ mkNode "ExprWithTySig"
        , toHie expr
        , toHie $ TS (ResolvedScopes [mkLScope expr]) sig
        ]
      ArithSeq _ _ info ->
        [ mkNode "ArithSeq"
        , toHie info
        ]
      HsSCC _ _ _ expr ->
        [ mkNode "HsSCC"
        , toHie expr
        ]
      HsCoreAnn _ _ _ expr ->
        [ mkNode "HsCoreAnn"
        , toHie expr
        ]
      HsProc _ pat cmdtop ->
        [ mkNode "HsProc"
        , toHie $ PS Nothing (mkLScope cmdtop) NoScope pat
        , toHie cmdtop
        ]
      HsStatic _ expr ->
        [ mkNode "HsStatic"
        , toHie expr
        ]
      HsArrApp _ a b _ _ ->
        [ mkNode "HsArrApp"
        , toHie a
        , toHie b
        ]
      HsArrForm _ expr _ cmds ->
        [ mkNode "HsArrForm"
        , toHie expr
        , toHie cmds
        ]
      HsTick _ _ expr ->
        [ mkNode "HsTick"
        , toHie expr
        ]
      HsBinTick _ _ _ expr ->
        [ mkNode "HsBinTick"
        , toHie expr
        ]
      HsTickPragma _ _ _ _ expr ->
        [ mkNode "HsTickPragma"
        , toHie expr
        ]
      HsWrap _ _ a ->
        [ mkNode "HsWrap"
        , toHie $ L mspan a
        ]
      HsBracket _ b ->
        [ mkNode "HsBracket p"
        , toHie b
        ]
      HsRnBracketOut _ b p ->
        [ mkNode "HsRnBracketOut"
        , toHie b
        , toHie p
        ]
      HsTcBracketOut _ b p ->
        [ mkNode "HsTcBracketOut"
        , toHie b
        , toHie p
        ]
      HsSpliceE _ x ->
        [ mkNode "HsSpliceE"
        , toHie $ L mspan x
        ]
      EWildPat _ ->
        [ mkNode "EWildPat"
        ]
      EAsPat _ a b ->
        [ mkNode "EAsPat"
        , toHie $ C Use a
        , toHie b
        ]
      EViewPat _ a b ->
        [ mkNode "EViewPat"
        , toHie a
        , toHie b
        ]
      ELazyPat _ a ->
        [ mkNode "ELazyPat"
        , toHie a
        ]
      XExpr _ -> []
    where
      mkNode cons = getTypeNode e cons

instance ( ToHie (LHsExpr a)
         ) => ToHie (LHsTupArg a) where
  toHie (L span arg) = concatM $ case arg of
    Present _ expr ->
      [ mkNode "Present"
      , toHie expr
      ]
    Missing _ -> [ mkNode "Missing" ]
    XTupArg _ -> []
    where mkNode = makeNode "HsTupArg" span

instance ( ToHie (PScoped (LPat a))
         , ToHie (LHsExpr a)
         , ToHie (SigContext (LSig a))
         , ToHie (RScoped (LHsLocalBinds a))
         , ToHie (RScoped (ApplicativeArg a))
         , ToHie (Located body)
         ) => ToHie (RScoped (LStmt a (Located body))) where
  toHie (RS scope (L span stmt)) = concatM $ case stmt of
      LastStmt _ body _ _ ->
        [ mkNode "LastStmt"
        , toHie body
        ]
      BindStmt _ pat body _ _ ->
        [ mkNode "BindStmt"
        , toHie $ PS (getRealSpan $ getLoc body) scope NoScope pat
        , toHie body
        ]
      ApplicativeStmt _ stmts _ ->
        [ mkNode "ApplicativeStmt"
        , concatMapM (toHie . RS scope . snd) stmts
        ]
      BodyStmt _ body _ _ ->
        [ mkNode "BodyStmt"
        , toHie body
        ]
      LetStmt _ binds ->
        [ mkNode "LetStmt"
        , toHie $ RS scope binds
        ]
      ParStmt _ parstmts _ _ ->
        [ mkNode "ParStmt"
        , concatMapM (\(ParStmtBlock _ stmts _ _) -> toHie $ listScopes NoScope stmts) parstmts
        ]
      TransStmt {trS_stmts = stmts, trS_using = using, trS_by = by} ->
        [ mkNode "TransStmt"
        , toHie $ listScopes scope stmts
        , toHie using
        , toHie by
        ]
      RecStmt {recS_stmts = stmts} ->
        [ mkNode "RecStmt"
        , toHie $ map (RS $ combineScopes scope (mkScope span)) stmts
        ]
      XStmtLR _ -> []
    where mkNode = makeNode "StmtLR" span

instance ( ToHie (LHsExpr a)
         , ToHie (PScoped (LPat a))
         , ToHie (BindContext (LHsBind a))
         , ToHie (SigContext (LSig a))
         , ToHie (RScoped (HsValBindsLR a a))
         ) => ToHie (RScoped (LHsLocalBinds a)) where
  toHie (RS scope (L span binds)) = concatM $ case binds of
      EmptyLocalBinds _ -> [mkNode "EmptyLocalBinds"]
      HsIPBinds _ _ -> [mkNode "HsIPBinds"]
      HsValBinds _ valBinds ->
        [ mkNode "HsValBinds"
        , toHie $ RS (combineScopes scope $ mkScope span)
                      valBinds
        ]
      XHsLocalBindsLR _ -> []
    where mkNode = makeNode "HsLocalBindsLR" span

instance ( ToHie (BindContext (LHsBind a))
         , ToHie (SigContext (LSig a))
         , ToHie (RScoped (XXValBindsLR a a))
         ) => ToHie (RScoped (HsValBindsLR a a)) where
  toHie (RS sc v) = concatM $ case v of
    ValBinds _ binds sigs ->
      [ toHie $ fmap (BC RegularBind sc) binds
      , toHie $ fmap (SC (SI BindSig Nothing)) sigs
      ]
    XValBindsLR x -> [ toHie $ RS sc x ]

instance ToHie (RScoped (NHsValBindsLR GhcTc)) where
  toHie (RS sc (NValBinds binds sigs)) = concatM $
    [ toHie (concatMap (map (BC RegularBind sc) . bagToList . snd) binds)
    , toHie $ fmap (SC (SI BindSig Nothing)) sigs
    ]
instance ToHie (RScoped (NHsValBindsLR GhcRn)) where
  toHie (RS sc (NValBinds binds sigs)) = concatM $
    [ toHie (concatMap (map (BC RegularBind sc) . bagToList . snd) binds)
    , toHie $ fmap (SC (SI BindSig Nothing)) sigs
    ]

instance ( ToHie (RContext (LHsRecField a arg))
         ) => ToHie (RContext (HsRecFields a arg)) where
  toHie (RC c (HsRecFields fields _)) = toHie $ map (RC c) fields

instance (ToHie (RFContext (Located label))
         , ToHie arg
         , HasLoc arg
         ) => ToHie (RContext (LHsRecField' label arg)) where
  toHie (RC c (L span recfld)) = concatM $ case recfld of
    HsRecField label expr _ ->
      [ makeNode "HsRecField" span "HsRecField'"
      , toHie $ RFC c (getRealSpan $ loc expr) label
      , toHie expr
      ]

removeDefSrcSpan :: Name -> Name
removeDefSrcSpan n = setNameLoc n noSrcSpan

instance ToHie (RFContext (LFieldOcc GhcRn)) where
  toHie (RFC c rhs (L nspan f)) = concatM $ case f of
    FieldOcc name _ ->
      [ toHie $ C (RecField c rhs) (L nspan $ removeDefSrcSpan name)
      ]
    XFieldOcc _ -> []

instance ToHie (RFContext (LFieldOcc GhcTc)) where
  toHie (RFC c rhs (L nspan f)) = concatM $ case f of
    FieldOcc var _ ->
      [ toHie $ C (RecField c rhs) (L nspan $ setVarName var (removeDefSrcSpan $ varName var))
      ]
    XFieldOcc _ -> []

instance ToHie (RFContext (Located (AmbiguousFieldOcc GhcRn))) where
  toHie (RFC c rhs (L nspan afo)) = concatM $ case afo of
    Unambiguous name _ ->
      [ toHie $ C (RecField c rhs) $ L nspan $ removeDefSrcSpan name
      ]
    Ambiguous _name _ ->
      [ ]
    XAmbiguousFieldOcc _ -> []

instance ToHie (RFContext (Located (AmbiguousFieldOcc GhcTc))) where
  toHie (RFC c rhs (L nspan afo)) = concatM $ case afo of
    Unambiguous var _ ->
      [ toHie $ C (RecField c rhs) (L nspan $ setVarName var (removeDefSrcSpan $ varName var))
      ]
    Ambiguous var _ ->
      [ toHie $ C (RecField c rhs) (L nspan $ setVarName var (removeDefSrcSpan $ varName var))
      ]
    XAmbiguousFieldOcc _ -> []

instance ( ToHie (PScoped (LPat a))
         , ToHie (BindContext (LHsBind a))
         , ToHie (LHsExpr a)
         , ToHie (SigContext (LSig a))
         , ToHie (RScoped (HsValBindsLR a a))
         ) => ToHie (RScoped (ApplicativeArg a)) where
  toHie (RS sc (ApplicativeArgOne _ pat expr _)) = concatM
    [ toHie $ PS Nothing sc NoScope pat
    , toHie expr
    ]
  toHie (RS sc (ApplicativeArgMany _ stmts _ pat)) = concatM
    [ toHie $ listScopes NoScope stmts
    , toHie $ PS Nothing sc NoScope pat
    ]
  toHie (RS _ (XApplicativeArg _)) = pure []

instance (ToHie arg, ToHie rec) => ToHie (HsConDetails arg rec) where
  toHie (PrefixCon args) = toHie args
  toHie (RecCon rec) = toHie rec
  toHie (InfixCon a b) = concatM [ toHie a, toHie b]

instance ( ToHie (LHsCmd a)
         ) => ToHie (LHsCmdTop a) where
  toHie (L span top) = concatM $ case top of
    HsCmdTop _ cmd ->
      [ makeNode "HsCmdTop" span "HsCmdTop"
      , toHie cmd
      ]
    XCmdTop _ -> []

instance ( ToHie (PScoped (LPat a))
         , ToHie (BindContext (LHsBind a))
         , ToHie (LHsExpr a)
         , ToHie (MatchGroup a (LHsCmd a))
         , ToHie (SigContext (LSig a))
         , ToHie (RScoped (HsValBindsLR a a))
         ) => ToHie (LHsCmd a) where
  toHie (L span cmd) = concatM $ case cmd of
      HsCmdArrApp _ a b _ _ ->
        [ mkNode "HsCmdArrApp"
        , toHie a
        , toHie b
        ]
      HsCmdArrForm _ a _ _ cmdtops ->
        [ mkNode "HsCmdArrForm"
        , toHie a
        , toHie cmdtops
        ]
      HsCmdApp _ a b ->
        [ mkNode "HsCmdApp"
        , toHie a
        , toHie b
        ]
      HsCmdLam _ mg ->
        [ mkNode "HsCmdLam"
        , toHie mg
        ]
      HsCmdPar _ a ->
        [ mkNode "HsCmdPar"
        , toHie a
        ]
      HsCmdCase _ expr alts ->
        [ mkNode "HsCmdCase"
        , toHie expr
        , toHie alts
        ]
      HsCmdIf _ _ a b c ->
        [ mkNode "HsCmdIf"
        , toHie a
        , toHie b
        , toHie c
        ]
      HsCmdLet _ binds cmd' ->
        [ mkNode "HsCmdLet"
        , toHie $ RS (mkLScope cmd') binds
        , toHie cmd'
        ]
      HsCmdDo _ (L ispan stmts) ->
        [ mkNode "HsCmdDo"
        , pure $ locOnly ispan
        , toHie $ listScopes NoScope stmts
        ]
      HsCmdWrap _ _ _ ->
        [ mkNode "HsCmdWrap"
        ]
      XCmd _ -> []
    where mkNode = makeNode "HsCmd" span

instance ToHie (TyClGroup GhcRn) where
  toHie (TyClGroup _ classes roles instances) = concatM
    [ toHie classes
    , toHie roles
    , toHie instances
    ]
  toHie (XTyClGroup _) = pure []

instance ToHie (LTyClDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      FamDecl {tcdFam = fdecl} ->
        [ mkNode "FamDecl"
        , toHie (L span fdecl)
        ]
      SynDecl {tcdLName = name, tcdTyVars = vars, tcdRhs = typ} ->
        [ mkNode "SynDecl"
        , toHie $ C (Decl SynDec $ getRealSpan span) name
        , toHie $ TS (ResolvedScopes [mkScope $ getLoc typ]) vars
        , toHie typ
        ]
      DataDecl {tcdLName = name, tcdTyVars = vars, tcdDataDefn = defn} ->
        [ mkNode "DataDecl"
        , toHie $ C (Decl DataDec $ getRealSpan span) name
        , toHie $ TS (ResolvedScopes [quant_scope, rhs_scope]) vars
        , toHie defn
        ]
        where
          quant_scope = mkLScope $ dd_ctxt defn
          rhs_scope = combineScopes sig_scope (combineScopes constr_scope deriving_scope)
          sig_scope = maybe NoScope mkLScope $ dd_kindSig defn
          constr_scope = foldr combineScopes NoScope $ map mkLScope $ dd_cons defn
          deriving_scope = mkLScope $ dd_derivs defn
      ClassDecl { tcdCtxt = context
                , tcdLName = name
                , tcdTyVars = vars
                , tcdFDs = deps
                , tcdSigs = sigs
                , tcdMeths = meths
                , tcdATs = typs
                , tcdATDefs = deftyps
                } ->
        [ mkNode "ClassDecl"
        , toHie $ C (Decl ClassDec $ getRealSpan span) name
        , toHie context
        , toHie $ TS (ResolvedScopes [context_scope, rhs_scope]) vars
        , toHie deps
        , toHie $ map (SC $ SI ClassSig $ getRealSpan span) sigs
        , toHie $ fmap (BC InstanceBind ModuleScope) meths
        , toHie typs
        , concatMapM (pure . locOnly . getLoc) deftyps
        , toHie $ map (go . unLoc) deftyps
        ]
        where
          context_scope = mkLScope context
          rhs_scope = foldl1' combineScopes $ map mkScope
            [ loc deps, loc sigs, loc (bagToList meths), loc typs, loc deftyps]
          go :: TyFamDefltEqn GhcRn -> FamEqn GhcRn (TScoped (LHsQTyVars GhcRn)) (LHsType GhcRn)
          go (FamEqn a var pat b rhs) = FamEqn a var (TS (ResolvedScopes [mkLScope rhs]) pat) b rhs
          go (XFamEqn NoExt) = XFamEqn NoExt
      XTyClDecl _ -> []
    where mkNode = makeNode "TyClDecl" span

instance ToHie (LFamilyDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      FamilyDecl _ info name vars _ sig inj ->
        [ mkNode "FamilyDecl"
        , toHie $ C (Decl FamDec $ getRealSpan span) name
        , toHie $ TS (ResolvedScopes [rhsSpan]) vars
        , toHie info
        , toHie $ RS injSpan sig
        , toHie inj
        ]
        where
          rhsSpan = sigSpan `combineScopes` injSpan
          sigSpan = mkScope $ getLoc sig
          injSpan = maybe NoScope (mkScope . getLoc) inj
      XFamilyDecl _ -> []
    where mkNode = makeNode "FamilyDecl" span

instance ToHie (FamilyInfo GhcRn) where
  toHie (ClosedTypeFamily (Just eqns)) = concatM $
    [ concatMapM (pure . locOnly . getLoc) eqns
    , toHie $ map go eqns
    ]
    where
      go (L l ib) = TS (ResolvedScopes [mkScope l]) ib
  toHie _ = pure []

instance ToHie (RScoped (LFamilyResultSig GhcRn)) where
  toHie (RS sc (L span sig)) = concatM $ case sig of
      NoSig _ ->
        [ mkNode "NoSig" ]
      KindSig _ k ->
        [ mkNode "KindSig"
        , toHie k
        ]
      TyVarSig _ bndr ->
        [ mkNode "TyVarSig"
        , toHie $ TVS (ResolvedScopes [sc]) NoScope bndr
        ]
      XFamilyResultSig _ -> []
    where mkNode = makeNode "FamilyResultSig" span

instance ToHie (Located (FunDep (Located Name))) where
  toHie (L span (lhs, rhs)) = concatM $
    [ mkNode "FunDep"
    , toHie $ map (C Use) lhs
    , toHie $ map (C Use) rhs
    ]
    where mkNode = makeNode "FunDep" span

instance (ToHie pats, ToHie rhs, HasLoc pats, HasLoc rhs)
    => ToHie (TScoped (FamEqn GhcRn pats rhs)) where
  toHie (TS _ f) = toHie f

instance (ToHie pats, ToHie rhs, HasLoc pats, HasLoc rhs) => ToHie (FamEqn GhcRn pats rhs) where
  toHie fe@(FamEqn _ var pats _ rhs) = concatM $
    [ toHie $ C (Decl InstDec $ getRealSpan $ loc fe) var
    , toHie pats
    , toHie rhs
    ]
  toHie (XFamEqn _) = pure []

instance ToHie (LInjectivityAnn GhcRn) where
  toHie (L span ann) = concatM $ case ann of
      InjectivityAnn lhs rhs ->
        [ mkNode "InjectivityAnn"
        , toHie $ C Use lhs
        , toHie $ map (C Use) rhs
        ]
    where mkNode = makeNode "InjectivityAnn" span

instance ToHie (HsDataDefn GhcRn) where
  toHie (HsDataDefn _ _ ctx _ mkind cons derivs) = concatM
    [ toHie ctx
    , toHie mkind
    , toHie cons
    , toHie derivs
    ]
  toHie (XHsDataDefn _) = pure []

instance ToHie (HsDeriving GhcRn) where
  toHie (L span clauses) = concatM
    [ pure $ locOnly span
    , toHie clauses
    ]

instance ToHie (LHsDerivingClause GhcRn) where
  toHie (L span cl) = concatM $ case cl of
      HsDerivingClause _ strat (L ispan tys) ->
        [ mkNode "HsDerivingClause"
        , toHie strat
        , pure $ locOnly ispan
        , toHie $ map (TS (ResolvedScopes [])) tys
        ]
      XHsDerivingClause _ -> []
    where mkNode = makeNode "HsDerivingClause" span

instance ToHie (Located (DerivStrategy GhcRn)) where
  toHie (L span strat) = concatM $ case strat of
      StockStrategy ->
        [ mkNode "StockStrategy"
        ]
      AnyclassStrategy ->
        [ mkNode "AnyclassStrategy"
        ]
      NewtypeStrategy ->
        [ mkNode "NewtypeStrategy"
        ]
      ViaStrategy s ->
        [ mkNode "ViaStrategy"
        , toHie $ TS (ResolvedScopes []) s
        ]
    where mkNode = makeNode "DerivStrategy" span

instance ToHie (Located OverlapMode) where
  toHie (L span _) = pure $ locOnly span

instance ToHie (LConDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      ConDeclGADT{con_names=names, con_qvars=qvars, con_mb_cxt=ctx, con_args=args, con_res_ty=typ} ->
        [ mkNode "ConDeclGADT"
        , toHie $ map (C (Decl ConDec $ getRealSpan span)) names
        , toHie $ TS (ResolvedScopes [ctxScope, rhsScope]) qvars
        , toHie ctx
        , toHie args
        , toHie typ
        ]
        where
          rhsScope = combineScopes argsScope tyScope
          ctxScope = maybe NoScope mkLScope ctx
          argsScope = condecl_scope args
          tyScope = mkLScope typ
      ConDeclH98{con_name=name, con_ex_tvs=qvars, con_mb_cxt=ctx, con_args=dets} ->
        [ mkNode "ConDeclH98"
        , toHie $ C (Decl ConDec $ getRealSpan span) name
        , toHie $ tvScopes (ResolvedScopes []) rhsScope qvars
        , toHie ctx
        , toHie dets
        ]
        where
          rhsScope = combineScopes ctxScope argsScope
          ctxScope = maybe NoScope mkLScope ctx
          argsScope = condecl_scope dets
      XConDecl _ -> []
    where mkNode = makeNode "ConDecl" span
          condecl_scope args = case args of
            PrefixCon xs -> foldr combineScopes NoScope $ map mkLScope xs
            InfixCon a b -> combineScopes (mkLScope a) (mkLScope b)
            RecCon x -> mkLScope x

instance ToHie (Located [LConDeclField GhcRn]) where
  toHie (L span decls) = concatM $
    [ pure $ locOnly span
    , toHie decls
    ]

instance (HasLoc thing, ToHie (TScoped thing)) => ToHie (TScoped (HsImplicitBndrs GhcRn thing)) where
  toHie (TS sc (HsIB ibrn a)) = concatM $
      [ pure $ bindingsOnly $ map (C $ TyVarBind (mkScope span) sc) ibrn
      , toHie $ TS sc a
      ]
    where span = loc a
  toHie (TS _ (XHsImplicitBndrs _)) = pure []

instance (HasLoc thing, ToHie (TScoped thing)) => ToHie (TScoped (HsWildCardBndrs GhcRn thing)) where
  toHie (TS sc (HsWC names a)) = concatM $
      [ pure $ bindingsOnly $ map (C $ TyVarBind (mkScope span) sc) names
      , toHie $ TS sc a
      ]
    where span = loc a
  toHie (TS _ (XHsWildCardBndrs _)) = pure []

instance ToHie (SigContext (LSig GhcRn)) where
  toHie (SC (SI styp msp) (L span sig)) = concatM $ case sig of
      TypeSig _ names typ ->
        [ mkNode "TypeSig"
        , toHie $ map (C TyDecl) names
        , toHie $ TS (UnresolvedScope (map unLoc names) Nothing) typ
        ]
      PatSynSig _ names typ ->
        [ mkNode "PatSynSig"
        , toHie $ map (C TyDecl) names
        , toHie $ TS (UnresolvedScope (map unLoc names) Nothing) typ
        ]
      ClassOpSig _ _ names typ ->
        [ mkNode "ClassOpSig"
        , case styp of
            ClassSig -> toHie $ map (C $ ClassTyDecl $ getRealSpan span) names
            _  -> toHie $ map (C $ TyDecl) names
        , toHie $ TS (UnresolvedScope (map unLoc names) msp) typ
        ]
      IdSig _ _ -> []
      FixSig _ fsig ->
        [ mkNode "FixSig"
        , toHie $ L span fsig
        ]
      InlineSig _ name _ ->
        [ mkNode "InlineSig"
        , toHie $ (C Use) name
        ]
      SpecSig _ name typs _ ->
        [ mkNode "SpecSig"
        , toHie $ (C Use) name
        , toHie $ map (TS (ResolvedScopes [])) typs
        ]
      SpecInstSig _ _ typ ->
        [ mkNode "SpecInstSig"
        , toHie $ TS (ResolvedScopes []) typ
        ]
      MinimalSig _ _ form ->
        [ mkNode "MinimalSig"
        , toHie form
        ]
      SCCFunSig _ _ name mtxt ->
        [ mkNode "SCCFunSig"
        , toHie $ (C Use) name
        , pure $ maybe [] (locOnly . getLoc) mtxt
        ]
      CompleteMatchSig _ _ (L ispan names) typ ->
        [ mkNode "CompleteMatchSig"
        , pure $ locOnly ispan
        , toHie $ map (C Use) names
        , toHie $ fmap (C Use) typ
        ]
      XSig _ -> []
    where mkNode = makeNode "Sig" span

instance ToHie (LHsType GhcRn) where
  toHie x = toHie $ TS (ResolvedScopes []) x

instance ToHie (TScoped (LHsType GhcRn)) where
  toHie (TS tsc (L span t)) = concatM $ case t of
      HsForAllTy _ bndrs body ->
        [ mkNode "HsForAllTy"
        , toHie $ tvScopes tsc (mkScope $ getLoc body) bndrs
        , toHie body
        ]
      HsQualTy _ ctx body ->
        [ mkNode "HsQualTy"
        , toHie ctx
        , toHie body
        ]
      HsTyVar _ _ var ->
        [ mkNode "HsTyVar"
        , toHie $ C Use var
        ]
      HsAppTy _ a b ->
        [ mkNode "HsAppTy"
        , toHie a
        , toHie b
        ]
      HsFunTy _ a b ->
        [ mkNode "HsFunTy"
        , toHie a
        , toHie b
        ]
      HsListTy _ a ->
        [ mkNode "HsListTy"
        , toHie a
        ]
      HsTupleTy _ _ tys ->
        [ mkNode "HsTupleTy"
        , toHie tys
        ]
      HsSumTy _ tys ->
        [ mkNode "HsSymTy"
        , toHie tys
        ]
      HsOpTy _ a op b ->
        [ mkNode "HsOpTy"
        , toHie a
        , toHie $ C Use op
        , toHie b
        ]
      HsParTy _ a ->
        [ mkNode "HsParTy"
        , toHie a
        ]
      HsIParamTy _ ip ty ->
        [ mkNode "IParamTy"
        , toHie ip
        , toHie ty
        ]
      HsKindSig _ a b ->
        [ mkNode "HsKindSig"
        , toHie a
        , toHie b
        ]
      HsSpliceTy _ a ->
        [ mkNode "HsSpliceTy"
        , toHie $ L span a
        ]
      HsDocTy _ a _ ->
        [ mkNode "HsDocTy"
        , toHie a
        ]
      HsBangTy _ _ ty ->
        [ mkNode "HsBangTy"
        , toHie ty
        ]
      HsRecTy _ fields ->
        [ mkNode "HsRecTy"
        , toHie fields
        ]
      HsExplicitListTy _ _ tys ->
        [ mkNode "HsExplicitListTy"
        , toHie tys
        ]
      HsExplicitTupleTy _ tys ->
        [ mkNode "HsExplicitTupleTy"
        , toHie tys
        ]
      HsTyLit _ _ ->
        [ mkNode "HsTyLit"
        ]
      HsWildCardTy e ->
        [ mkNode "HsWildCardTy"
        , toHie e
        ]
      HsStarTy _ _ -> []
      XHsType _ -> []
    where mkNode = makeNode "HsType" span

instance ToHie HsWildCardInfo where
  toHie (AnonWildCard name) = toHie $ C Use name

instance ToHie (TVScoped (LHsTyVarBndr GhcRn)) where
  toHie (TVS tsc sc (L span bndr)) = concatM $ case bndr of
      UserTyVar _ var ->
        [ mkNode "UserTyVar"
        , toHie $ C (TyVarBind sc tsc) var
        ]
      KindedTyVar _ var kind ->
        [ mkNode "KindedTyVar"
        , toHie $ C (TyVarBind sc tsc) var
        , toHie kind
        ]
      XTyVarBndr _ -> []
    where mkNode = makeNode "HsTyVarBndr" span

instance ToHie (TScoped (LHsQTyVars GhcRn)) where
  toHie (TS sc (HsQTvs (HsQTvsRn implicits _) vars)) = concatM $
    [ pure $ bindingsOnly bindings
    , toHie $ tvScopes sc NoScope vars
    ]
    where
      varLoc = loc vars
      bindings = map (C $ TyVarBind (mkScope varLoc) sc) implicits
  toHie (TS _ (XLHsQTyVars _)) = pure []

instance ToHie (LHsContext GhcRn) where
  toHie (L span tys) = concatM $
      [ pure $ locOnly span
      , toHie tys
      ]

instance ToHie (LConDeclField GhcRn) where
  toHie (L span field) = concatM $ case field of
      ConDeclField _ fields typ _ ->
        [ mkNode "ConDeclField"
        , toHie $ map (RFC RecFieldDecl (getRealSpan $ loc typ)) fields
        , toHie typ
        ]
      XConDeclField _ -> []
    where mkNode = makeNode "HsConDeclField" span

instance ToHie (LHsExpr a) => ToHie (ArithSeqInfo a) where
  toHie (From expr) = toHie expr
  toHie (FromThen a b) = concatM $
    [ toHie a
    , toHie b
    ]
  toHie (FromTo a b) = concatM $
    [ toHie a
    , toHie b
    ]
  toHie (FromThenTo a b c) = concatM $
    [ toHie a
    , toHie b
    , toHie c
    ]

instance ToHie (LSpliceDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      SpliceDecl _ splice _ ->
        [ mkNode "SpliceDecl"
        , toHie splice
        ]
      XSpliceDecl _ -> []
    where mkNode = makeNode "SpliceDecl" span

instance ToHie (HsBracket a) where
  toHie _ = pure []

instance ToHie PendingRnSplice where
  toHie _ = pure []

instance ToHie PendingTcSplice where
  toHie _ = pure []

instance ToHie (LBooleanFormula (Located Name)) where
  toHie (L span form) = concatM $ case form of
      Var a ->
        [ mkNode "Var"
        , toHie $ C Use a
        ]
      And forms ->
        [ mkNode "And"
        , toHie forms
        ]
      Or forms ->
        [ mkNode "Or"
        , toHie forms
        ]
      Parens f ->
        [ mkNode "Parens"
        , toHie f
        ]
    where mkNode = makeNode "BooleanFormula" span

instance ToHie (Located HsIPName) where
  toHie (L span _) = makeNode "HsIPName" span "HsIPName"

instance ToHie (LHsExpr a) => ToHie (Located (HsSplice a)) where
  toHie (L span sp) = concatM $ case sp of
      HsTypedSplice _ _ _ expr ->
        [ mkNode "HsTypedSplice"
        , toHie expr
        ]
      HsUntypedSplice _ _ _ expr ->
        [ mkNode "HsUnTypedSplice"
        , toHie expr
        ]
      HsQuasiQuote _ _ _ ispan _ ->
        [ mkNode "HsQuasiQuote"
        , pure $ locOnly ispan
        ]
      HsSpliced _ _ _ ->
        [ mkNode "HsSpliced"
        ]
      XSplice _ -> []
    where mkNode = makeNode "HsSplice" span

instance ToHie (LRoleAnnotDecl GhcRn) where
  toHie (L span annot) = concatM $ case annot of
      RoleAnnotDecl _ var roles ->
        [ mkNode "RoleAnnotDecl"
        , toHie $ C Use var
        , concatMapM (pure . locOnly . getLoc) roles
        ]
      XRoleAnnotDecl _ -> []
    where mkNode = makeNode "RoleAnnotDecl" span

instance ToHie (LInstDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      ClsInstD _ d ->
        [ mkNode "ClsInstD"
        , toHie $ L span d
        ]
      DataFamInstD _ d ->
        [ mkNode "DataFamInstD"
        , toHie $ L span d
        ]
      TyFamInstD _ d ->
        [ mkNode "TyFamInstD"
        , toHie $ L span d
        ]
      XInstDecl _ -> []
    where mkNode = makeNode "InstDecl" span

instance ToHie (LClsInstDecl GhcRn) where
  toHie (L span decl) = concatM
    [ toHie $ TS (ResolvedScopes [mkScope span]) $ cid_poly_ty decl
    , toHie $ fmap (BC InstanceBind ModuleScope) $ cid_binds decl
    , toHie $ map (SC $ SI InstSig $ getRealSpan span) $ cid_sigs decl
    , pure $ concatMap (locOnly . getLoc) $ cid_tyfam_insts decl
    , toHie $ cid_tyfam_insts decl
    , pure $ concatMap (locOnly . getLoc) $ cid_datafam_insts decl
    , toHie $ cid_datafam_insts decl
    , toHie $ cid_overlap_mode decl
    ]

instance ToHie (LDataFamInstDecl GhcRn) where
  toHie (L sp (DataFamInstDecl d)) = toHie $ TS (ResolvedScopes [mkScope sp]) d

instance ToHie (LTyFamInstDecl GhcRn) where
  toHie (L sp (TyFamInstDecl d)) = toHie $ TS (ResolvedScopes [mkScope sp]) d

instance ToHie (Context a) => ToHie (PatSynFieldContext (RecordPatSynField a))where
  toHie (PSC sp (RecordPatSynField a b)) = concatM $
    [ toHie $ C (RecField RecFieldDecl sp) a
    , toHie $ C Use b
    ]

instance ToHie (LDerivDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      DerivDecl _ typ strat overlap ->
        [ mkNode "DerivDecl"
        , toHie $ TS (ResolvedScopes []) typ
        , toHie strat
        , toHie overlap
        ]
      XDerivDecl _ -> []
    where mkNode = makeNode "DerivDecl" span

instance ToHie (LFixitySig GhcRn) where
  toHie (L span sig) = concatM $ case sig of
      FixitySig _ vars _ ->
        [ mkNode "FixitySig"
        , toHie $ map (C Use) vars
        ]
      XFixitySig _ -> []
    where mkNode = makeNode "FixitySig" span

instance ToHie (LDefaultDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      DefaultDecl _ typs ->
        [ mkNode "DefaultDecl"
        , toHie typs
        ]
      XDefaultDecl _ -> []
    where mkNode = makeNode "DefaultDecl" span

instance ToHie (LForeignDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      ForeignImport {fd_name = name, fd_sig_ty = sig, fd_fi = fi} ->
        [ mkNode "ForeignImport"
        , toHie $ C (ValBind RegularBind ModuleScope $ getRealSpan span) name
        , toHie $ TS (ResolvedScopes []) sig
        , toHie fi
        ]
      ForeignExport {fd_name = name, fd_sig_ty = sig, fd_fe = fe} ->
        [ mkNode "ForeignExport"
        , toHie $ C Use name
        , toHie $ TS (ResolvedScopes []) sig
        , toHie fe
        ]
      XForeignDecl _ -> []
    where mkNode = makeNode "ForeignDecl" span

instance ToHie ForeignImport where
  toHie (CImport (L a _) (L b _) _ _ (L c _)) = pure $ concat $
    [ locOnly a
    , locOnly b
    , locOnly c
    ]

instance ToHie ForeignExport where
  toHie (CExport (L a _) (L b _)) = pure $ concat $
    [ locOnly a
    , locOnly b
    ]

instance ToHie (LWarnDecls GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      Warnings _ _ warnings ->
        [ mkNode "Warning"
        , toHie warnings
        ]
      XWarnDecls _ -> []
    where mkNode = makeNode "WarnDecls" span

instance ToHie (LWarnDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      Warning _ vars _ ->
        [ mkNode "Warning"
        , toHie $ map (C Use) vars
        ]
      XWarnDecl _ -> []
    where mkNode = makeNode "WarnDecl" span

instance ToHie (LAnnDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      HsAnnotation _ _ prov expr ->
        [ mkNode "HsAnnotation"
        , toHie prov
        , toHie expr
        ]
      XAnnDecl _ -> []
    where mkNode = makeNode "AnnDecl" span

instance ToHie (Context (Located a)) => ToHie (AnnProvenance a) where
  toHie (ValueAnnProvenance a) = toHie $ C Use a
  toHie (TypeAnnProvenance a) = toHie $ C Use a
  toHie ModuleAnnProvenance = pure []

instance ToHie (LRuleDecls GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      HsRules _ _ rules ->
        [ mkNode "HsRules"
        , toHie rules
        ]
      XRuleDecls _ -> []
    where mkNode = makeNode "RuleDecls" span

instance ToHie (LRuleDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      HsRule _ rname _ bndrs exprA exprB ->
        [ mkNode "HsRule"
        , pure $ locOnly $ getLoc rname
        , toHie $ map (RS $ mkScope span) bndrs
        , toHie exprA
        , toHie exprB
        ]
      XRuleDecl _ -> []
    where mkNode = makeNode "RuleDecl" span

instance ToHie (RScoped (LRuleBndr GhcRn)) where
  toHie (RS sc (L span bndr)) = concatM $ case bndr of
      RuleBndr _ var ->
        [ mkNode "RuleBndr"
        , toHie $ C (ValBind RegularBind sc Nothing) var
        ]
      RuleBndrSig _ var typ ->
        [ mkNode "RuleBndrSig"
        , toHie $ C (ValBind RegularBind sc Nothing) var
        , toHie $ TS (ResolvedScopes [sc]) typ
        ]
      XRuleBndr _ -> []
    where mkNode = makeNode "RuleBndr" span

instance ToHie (LImportDecl GhcRn) where
  toHie (L span decl) = concatM $ case decl of
      ImportDecl { ideclName = name, ideclAs = as, ideclHiding = hidden } ->
        [ mkNode "ImportDecl"
        , toHie $ IEC Import name
        , toHie $ fmap (IEC ImportAs) as
        , maybe (pure []) goIE hidden
        ]
      XImportDecl _ -> []
    where
      mkNode = makeNode "ImportDecl" span
      goIE (hiding, (L sp liens)) = concatM $
        [ pure $ locOnly sp
        , toHie $ map (IEC c) liens
        ]
        where
         c = if hiding then ImportHiding else Import

instance ToHie (IEContext (LIE GhcRn)) where
  toHie (IEC c (L span ie)) = concatM $ case ie of
      IEVar _ n ->
        [ mkNode "IEVar"
        , toHie $ IEC c n
        ]
      IEThingAbs _ n ->
        [ mkNode "IEThingAbs"
        , toHie $ IEC c n
        ]
      IEThingAll _ n ->
        [ mkNode "IEThingAll"
        , toHie $ IEC c n
        ]
      IEThingWith _ n _ ns flds ->
        [ mkNode "IEThingWith"
        , toHie $ IEC c n
        , toHie $ map (IEC c) ns
        , toHie $ map (IEC c) flds
        ]
      IEModuleContents _ n ->
        [ mkNode "IEModuleContents"
        , toHie $ IEC c n
        ]
      IEGroup _ _ _ ->
        [ mkNode "IEGroup"
        ]
      IEDoc _ _ ->
        [ mkNode "IEDoc"
        ]
      IEDocNamed _ _ ->
        [ mkNode "IEDocNamed"
        ]
      XIE _ -> []
    where mkNode = makeNode "IE" span

instance ToHie (IEContext (LIEWrappedName Name)) where
  toHie (IEC c (L span iewn)) = concatM $ case iewn of
      IEName n ->
        [ mkNode "IEName"
        , toHie $ C (IEThing c) n
        ]
      IEPattern p ->
        [ mkNode "IEPattern"
        , toHie $ C (IEThing c) p
        ]
      IEType n ->
        [ mkNode "IEType"
        , toHie $ C (IEThing c) n
        ]
    where mkNode = makeNode "IEWrappedName" span

instance ToHie (IEContext (Located (FieldLbl Name))) where
  toHie (IEC c (L span lbl)) = concatM $ case lbl of
      FieldLabel _ _ n ->
        [ mkNode "FieldLabel"
        , toHie $ C (IEThing c) $ L span n
        ]
    where mkNode = makeNode "FieldLbl" span
