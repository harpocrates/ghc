
module HaddockUtils where

import GhcPrelude

import HsSyn
import SrcLoc
import qualified Data.Map.Strict as M

import Control.Monad

-- | A mapping from source locations to a list of tokens. The main use case is
-- when @tok ~ Located Token@ and the tokens are Haddock comments.
newtype DocStore tok = DocStore { unDocStore :: M.Map RealSrcLoc [tok] }

-- | An empty 'DocStore'.
emptyDocStore :: DocStore tok
emptyDocStore = DocStore M.empty

-- | Get all of the entries in the 'DocStore'.
docStoreElts :: DocStore tok -> [tok]
docStoreElts = join . M.elems . unDocStore

-- | Modify the entries keyed under a certain entry in the 'DocStore'.
docStoreAdjust :: ([tok] -> (a, [tok]))   -- ^ what to return and how to adjust
               -> RealSrcLoc              -- ^ key at which to adjust
               -> DocStore tok
               -> (Maybe a, DocStore tok) -- ^ returned value (if key was
                                          -- found)  and the new store
docStoreAdjust func loc = fmap DocStore . M.alterF func' loc . unDocStore
  where func' Nothing = (Nothing, Nothing)
        func' (Just val) = let (x, val') = func val
                           in (Just x, if null val' then Nothing else Just val')

-- | Insert into the 'DocStore' entries all keyed under a single location.
addToDocStore :: RealSrcLoc
              -> [tok]
              -> DocStore tok
              -> DocStore tok
addToDocStore loc val
  | null val = id
  | otherwise = DocStore . M.insertWith (++) loc val . unDocStore


-- -----------------------------------------------------------------------------
-- Adding documentation to record fields (used in parsing).

addFieldDoc :: LConDeclField a -> Maybe LHsDocString -> LConDeclField a
addFieldDoc (L l fld) doc
  = L l (fld { cd_fld_doc = cd_fld_doc fld `mplus` doc })

addFieldDocs :: [LConDeclField a] -> Maybe LHsDocString -> [LConDeclField a]
addFieldDocs [] _ = []
addFieldDocs (x:xs) doc = addFieldDoc x doc : xs


addConDoc :: LConDecl a -> Maybe LHsDocString -> LConDecl a
addConDoc decl    Nothing = decl
addConDoc (L p c) doc     = L p ( c { con_doc = con_doc c `mplus` doc } )

addConDocs :: [LConDecl a] -> Maybe LHsDocString -> [LConDecl a]
addConDocs [] _ = []
addConDocs [x] doc = [addConDoc x doc]
addConDocs (x:xs) doc = x : addConDocs xs doc

addConDocFirst :: [LConDecl a] -> Maybe LHsDocString -> [LConDecl a]
addConDocFirst [] _ = []
addConDocFirst (x:xs) doc = addConDoc x doc : xs
