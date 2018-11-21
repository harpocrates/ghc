{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module HieTypes where

import TyCoRep
import FastString
import Binary
import Outputable hiding ((<>))

import Data.Array (Array)
import Data.Map (Map)
import Data.Set (Set)
import Data.ByteString (ByteString)
import Data.Word
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Monoid
import Data.Semigroup
import GHC.Show
import SrcLoc
import GhcPrelude
import Name
import Type
import Module (ModuleName)
import Control.Applicative ((<|>))
import IfaceType
import Data.Coerce

type Span = RealSrcSpan

{-
Note [Efficient serialization of redundant type info]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The type information in .hie files is highly repetitive and redundant. For
example, consider the expression

    const True 'a'

There is a lot of shared structure between the types of subterms:

  * const True 'a' ::                    Boolean
  * const True     ::            Char -> Boolean
  * const          :: Boolean -> Char -> Boolean

Since all 3 of these types need to be stored in the .hie file, it is worth
making an effort to deduplicate this shared structure. The trick is to define
a new data type that is a flattened version of 'Type':

    data HieType a = HAppTy a a  -- data Type = AppTy Type Type
                   | HFunTy a a  --           | FunTy Type Type
                   | ...

    type TypeIndex = Int

Types in the final AST are stored in an 'Array TypeIndex (HieType TypeIndex)',
where the 'TypeIndex's in the 'HieType' are references to other elements of the
array. Types recovered from GHC are deduplicated and stored in this compressed
form with sharing of subtrees.
-}

type TypeIndex = Int

-- | A flattened version of 'Type'.
--
-- See Note [Efficient serialization of redundant type info]
data HieType a
  = HTyVarTy Name
  | HAppTy a (HieArgs a)
  | HTyConApp IfaceTyCon (HieArgs a)
  | HForAllTy ((Name, a),ArgFlag) a
  | HFunTy Bool {-^ is this @a ->@ or @a =>@ -} a a
  | HLitTy IfaceTyLit
  | HCastTy a
  | HCoercionTy
    deriving (Functor, Foldable, Traversable, Eq)

type HieTypeFlat = HieType TypeIndex

-- | Roughly isomorphic to the original core 'Type'.
newtype HieTypeFix = Roll (HieType (HieTypeFix))

instance Binary (HieType TypeIndex) where
  put_ bh (HTyVarTy n) = do
    putByte bh 0
    put_ bh n
  put_ bh (HAppTy a b) = do
    putByte bh 1
    put_ bh a
    put_ bh b
  put_ bh (HTyConApp n xs) = do
    putByte bh 2
    put_ bh n
    put_ bh xs
  put_ bh (HForAllTy bndr a) = do
    putByte bh 3
    put_ bh bndr
    put_ bh a
  put_ bh (HFunTy k a b) = do
    putByte bh 4
    put_ bh k
    put_ bh a
    put_ bh b
  put_ bh (HLitTy l) = do
    putByte bh 5
    put_ bh l
  put_ bh (HCastTy a) = do
    putByte bh 6
    put_ bh a
  put_ bh (HCoercionTy) = putByte bh 7

  get bh = do
    (t :: Word8) <- get bh
    case t of
      0 -> HTyVarTy <$> get bh
      1 -> HAppTy <$> get bh <*> get bh
      2 -> HTyConApp <$> get bh <*> get bh
      3 -> HForAllTy <$> get bh <*> get bh
      4 -> HFunTy <$> get bh <*> get bh <*> get bh
      5 -> HLitTy <$> get bh
      6 -> HCastTy <$> get bh
      7 -> return HCoercionTy
      _ -> panic "Binary (HieArgs Int): invalid tag"


-- | A list of type arguments along with their respective visibilities (ie. is
-- this an argument that would return 'True' for 'isVisibleArgFlag'?).
newtype HieArgs a = HieArgs [(Bool,a)]
  deriving (Functor, Foldable, Traversable, Eq)

instance Binary (HieArgs TypeIndex) where
  put_ bh (HieArgs xs) = put_ bh xs
  get bh = HieArgs <$> get bh




data Scope
  = NoScope
  | LocalScope Span
  | ModuleScope
    deriving (Eq, Ord, Show)

instance Outputable Scope where
  ppr NoScope = text "NoScope"
  ppr (LocalScope sp) = text "LocalScope" <+> ppr sp
  ppr ModuleScope = text "ModuleScope"

instance Binary Scope where
  put_ bh NoScope = putByte bh 0
  put_ bh (LocalScope span) = do
    putByte bh 1
    put_ bh span
  put_ bh ModuleScope = putByte bh 2

  get bh = do
    (t :: Word8) <- get bh
    case t of
      0 -> return NoScope
      1 -> LocalScope <$> get bh
      2 -> return ModuleScope
      _ -> panic "Binary Scope: invalid tag"


data TyVarScope
  = ResolvedScopes [Scope]
  | UnresolvedScope [Name] (Maybe Span)
    -- ^ The Span is the location of the instance/class declaration
    deriving (Eq, Ord)

instance Show TyVarScope where
  show (ResolvedScopes sc) = show sc
  show _ = error "UnresolvedScope"

instance Binary TyVarScope where
  put_ bh (ResolvedScopes xs) = do
    putByte bh 0
    put_ bh xs
  put_ bh (UnresolvedScope ns span) = do
    putByte bh 1
    put_ bh ns
    put_ bh span

  get bh = do
    (t :: Word8) <- get bh
    case t of
      0 -> ResolvedScopes <$> get bh
      1 -> UnresolvedScope <$> get bh <*> get bh
      _ -> panic "Binary TyVarScope: invalid tag"


curHieVersion :: Word8
curHieVersion = 0

data HieFile = HieFile
    { hieVersion :: Word8
    , ghcVersion :: ByteString
    , hsFile     :: FilePath
    , hieTypes   :: Array TypeIndex HieTypeFlat
    , hieAST     :: HieASTs TypeIndex
    , hsSrc      :: ByteString
    }

newtype HieASTs a = HieASTs { getAsts :: (Map FastString (HieAST a)) }
  deriving (Functor, Foldable, Traversable)

data HieAST a =
  Node
    { nodeInfo :: NodeInfo a
    , nodeSpan :: Span
    , nodeChildren :: [HieAST a]
    } deriving (Functor, Foldable, Traversable)

data NodeInfo a = NodeInfo
    { nodeAnnotations :: Set (FastString,FastString) -- Constr, Type
    , nodeType :: [a] -- The haskell type of this node, if any
    , nodeIdentifiers :: NodeIdentifiers a -- All the identifiers and their details
    } deriving (Functor, Foldable, Traversable)

type Identifier = Either ModuleName Name

type NodeIdentifiers a = Map Identifier (IdentifierDetails a)

data IdentifierDetails a = IdentifierDetails
  { identType :: Maybe a
  , identInfo :: Set ContextInfo
  } deriving (Eq, Functor, Foldable, Traversable)
-- ^ We need to include types with identifiers because sometimes multiple
-- identifiers occur in the same span(Overloaded Record Fields and so on)

instance Outputable a => Outputable (IdentifierDetails a) where
  ppr x = text "IdentifierDetails" <+> ppr (identType x) <+> ppr (identInfo x)

-- | Different contexts under which identifiers exist
data ContextInfo
  = Use
  | MatchBind
  | IEThing IEType
  | TyDecl
  | ValBind BindType Scope (Maybe Span) -- Span of entire binding
  | PatternBind Scope Scope (Maybe Span) -- Span of entire binding
  | ClassTyDecl (Maybe Span)
  | Decl DeclType (Maybe Span) -- Span of entire binding
  | TyVarBind Scope TyVarScope
  | RecField RecFieldContext (Maybe Span)
    deriving (Eq, Ord, Show)

instance Outputable ContextInfo where
  ppr = text . show

instance Binary ContextInfo where
  put_ bh Use = putByte bh 0
  put_ bh (IEThing t) = do
    putByte bh 1
    put_ bh t
  put_ bh TyDecl = putByte bh 2
  put_ bh (ValBind bt sc msp) = do
    putByte bh 3
    put_ bh bt
    put_ bh sc
    put_ bh msp
  put_ bh (PatternBind a b c) = do
    putByte bh 4
    put_ bh a
    put_ bh b
    put_ bh c
  put_ bh (ClassTyDecl sp) = do
    putByte bh 5
    put_ bh sp
  put_ bh (Decl a b) = do
    putByte bh 6
    put_ bh a
    put_ bh b
  put_ bh (TyVarBind a b) = do
    putByte bh 7
    put_ bh a
    put_ bh b
  put_ bh (RecField a b) = do
    putByte bh 8
    put_ bh a
    put_ bh b
  put_ bh MatchBind = putByte bh 9

  get bh = do
    (t :: Word8) <- get bh
    case t of
      0 -> return Use
      1 -> IEThing <$> get bh
      2 -> return TyDecl
      3 -> ValBind <$> get bh <*> get bh <*> get bh
      4 -> PatternBind <$> get bh <*> get bh <*> get bh
      5 -> ClassTyDecl <$> get bh
      6 -> Decl <$> get bh <*> get bh
      7 -> TyVarBind <$> get bh <*> get bh
      8 -> RecField <$> get bh <*> get bh
      9 -> return MatchBind
      _ -> panic "Binary ContextInfo: invalid tag"

-- | Different import-statement forms
data IEType
  = Import        -- ^ @import Foo@
  | ImportAs      -- ^ @import qualified Foo as S@
  | ImportHiding  -- ^ @import Foo hiding (..)@
  | Export        -- ^ name in an export list
    deriving (Eq, Enum, Ord, Show)

instance Binary IEType where
  put_ = putEnum
  get = getEnum

data RecFieldContext
  = RecFieldDecl
  | RecFieldAssign
  | RecFieldMatch
  | RecFieldOcc
    deriving (Eq, Enum, Ord, Show)

instance Binary RecFieldContext where
  put_ = putEnum
  get = getEnum

data BindType
  = RegularBind
  | InstanceBind
    deriving (Eq, Ord, Show, Enum)

instance Binary BindType where
  put_ = putEnum
  get = getEnum

data DeclType
  = FamDec     -- ^ type or data family
  | SynDec     -- ^ type synonym
  | DataDec    -- ^ data declaration
  | ConDec     -- ^ constructor declaration ???
  | PatSynDec  -- ^ pattern synonym
  | ClassDec   -- ^ class declaration
  | InstDec    -- ^ instance declaration
    deriving (Eq, Ord, Show, Enum)

instance Binary DeclType where
  put_ = putEnum
  get = getEnum

instance Ord a => Semigroup (NodeInfo a) where
  (NodeInfo as ai ad) <> (NodeInfo bs bi bd) =
    NodeInfo (S.union as bs) (snub ai bi) (combineNodeIdentifiers ad bd)
instance Ord a => Monoid (NodeInfo a) where
  mempty = NodeInfo S.empty [] M.empty

instance Semigroup (IdentifierDetails a) where
  d1 <> d2 =
    IdentifierDetails (identType d1 <|> identType d2) (S.union (identInfo d1) (identInfo d2))
instance Monoid (IdentifierDetails a) where
  mempty = IdentifierDetails Nothing S.empty

snub :: Ord a => [a] -> [a] -> [a]
snub as bs = S.toAscList $ S.union (S.fromAscList as) (S.fromAscList bs)

combineNodeIdentifiers :: NodeIdentifiers a -> NodeIdentifiers a -> NodeIdentifiers a
combineNodeIdentifiers i1 i2 = M.unionWith (<>) i1 i2

newtype CmpType = CmpType Type

instance Eq CmpType where (==) = coerce eqType
instance Ord CmpType where compare = coerce nonDetCmpType


putEnum :: Enum a => BinHandle -> a -> IO ()
putEnum bh = putByte bh . fromIntegral . fromEnum

getEnum :: Enum a => BinHandle -> IO a
getEnum bh = toEnum . fromIntegral <$> getByte bh

instance Binary (IdentifierDetails TypeIndex) where
  put_ bh dets = do
    put_ bh $ identType dets
    put_ bh $ S.toAscList $ identInfo dets
  get bh =  IdentifierDetails
    <$> get bh
    <*> fmap (S.fromAscList) (get bh)

instance Binary (NodeInfo TypeIndex) where
  put_ bh ni = do
    put_ bh $ S.toAscList $ nodeAnnotations ni
    put_ bh $ nodeType ni
    put_ bh $ M.toList $ nodeIdentifiers ni
  get bh = NodeInfo
    <$> fmap (S.fromAscList) (get bh)
    <*> get bh
    <*> fmap (M.fromList) (get bh)

instance Binary (HieAST TypeIndex) where
  put_ bh ast = do
    put_ bh $ nodeInfo ast
    put_ bh $ nodeSpan ast
    put_ bh $ nodeChildren ast

  get bh = Node
    <$> get bh
    <*> get bh
    <*> get bh

instance Binary (HieASTs TypeIndex) where
  put_ bh asts =
    put_ bh $ M.toAscList $ getAsts asts
  get bh =
    HieASTs <$> fmap M.fromAscList (get bh)

instance Binary HieFile where
  put_ bh hf = do
    put_ bh $ hieVersion hf
    put_ bh $ ghcVersion hf
    put_ bh $ hsFile hf
    put_ bh $ hieTypes hf
    put_ bh $ hieAST hf
    put_ bh $ hsSrc hf

  get bh = HieFile
    <$> get bh
    <*> get bh
    <*> get bh
    <*> get bh
    <*> get bh
    <*> get bh
