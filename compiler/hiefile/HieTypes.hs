{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
module HieTypes where

import TyCoRep
import FastString

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

newtype HieArgs a = HieArgs [(Bool,a)]
  deriving (Functor, Foldable, Traversable,Eq)

data HieType a
  = HTyVarTy Name
  | HAppTy a (HieArgs a)
  | HTyConApp IfaceTyCon (HieArgs a)
  | HForAllTy ((Name, a),ArgFlag) a
  | HFunTy Bool a a -- Bool - Is this a -> or a =>
  | HLitTy IfaceTyLit
  | HCastTy a
  | HCoercionTy
    deriving (Functor, Foldable, Traversable,Eq)

type HieTypeFlat = HieType TypeIndex

newtype HieTypeFix = Roll (HieType (HieTypeFix))

data HieTypeInline
  = Reference TypeIndex
  | Inline (HieType HieTypeInline)

type TypeIndex = Int

data ContextInfo =
    Use
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

data IEType
  = Import
  | ImportAs
  | ImportHiding
  | Export
    deriving (Eq, Enum, Ord, Show)

data RecFieldContext
  = RecFieldDecl
  | RecFieldAssign
  | RecFieldMatch
  | RecFieldOcc
    deriving (Eq, Enum, Ord, Show)

data BindType =
    RegularBind
  | InstanceBind
    deriving (Eq, Ord, Show, Enum)

data DeclType =
    FamDec
  | SynDec
  | DataDec
  | ConDec
  | PatSynDec
  | ClassDec
  | InstDec
    deriving (Eq, Ord, Show, Enum)

data Scope =
    NoScope
  | LocalScope Span
  | ModuleScope
    deriving (Eq, Ord, Show)

data TyVarScope =
    ResolvedScopes [Scope]
  | UnresolvedScope [Name] (Maybe Span)
    -- ^ The Span is the location of the instance/class declaration
    deriving (Eq, Ord)

instance Show TyVarScope where
  show (ResolvedScopes sc) = show sc
  show _ = error "UnresolvedScope"

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
