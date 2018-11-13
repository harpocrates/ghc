{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
module HieBin where

import GhcPrelude
import Data.IORef
import Data.Word
import Data.List
import Control.Monad

import Binary
import PrelInfo
import Outputable

import Module
import SrcLoc
import Name
import FastMutInt
import Unique
import UniqFM
import NameCache
import FastString
import UniqSupply
import BinIface (getDictFastString)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Array as A

import HieTypes

data HieName
  = ExternalName !Module !OccName !SrcSpan
  | LocalName !OccName !SrcSpan
  | KnownKeyName !Unique
  deriving (Eq)

instance Ord HieName where
  compare (ExternalName a b c) (ExternalName d e f) = compare (a,b,c) (d,e,f)
  compare (LocalName a b) (LocalName c d) = compare (a,b) (c,d)
  compare (KnownKeyName a) (KnownKeyName b) = nonDetCmpUnique a b
    -- Not actually non determinstic as it is a KnownKey
  compare ExternalName{} _ = LT
  compare LocalName{} ExternalName{} = GT
  compare LocalName{} _ = LT
  compare KnownKeyName{} _ = GT

data HieSymbolTable = HieSymbolTable
  { hie_symtab_next :: !FastMutInt
  , hie_symtab_map  :: !(IORef (UniqFM (Int, HieName)))
  }

data HieDictionary = HieDictionary
  { hie_dict_next :: !FastMutInt -- The next index to use
  , hie_dict_map  :: !(IORef (UniqFM (Int,FastString))) -- indexed by FastString
  }

initBinMemSize :: Int
initBinMemSize = 1024*1024

writeHieFile :: Binary a => FilePath -> a -> IO ()
writeHieFile filename hiefile = do
  bh0 <- openBinMem initBinMemSize

  -- remember where the dictionary pointer will go
  dict_p_p <- tellBin bh0
  put_ bh0 dict_p_p

  -- remember where the symbol table pointer will go
  symtab_p_p <- tellBin bh0
  put_ bh0 symtab_p_p

  -- Make some intial state
  symtab_next <- newFastMutInt
  writeFastMutInt symtab_next 0
  symtab_map <- newIORef emptyUFM
  let hie_symtab = HieSymbolTable {
                      hie_symtab_next = symtab_next,
                      hie_symtab_map  = symtab_map }
  dict_next_ref <- newFastMutInt
  writeFastMutInt dict_next_ref 0
  dict_map_ref <- newIORef emptyUFM
  let hie_dict = HieDictionary {
                      hie_dict_next = dict_next_ref,
                      hie_dict_map  = dict_map_ref }

  -- put the main thing
  let bh = setUserData bh0 $ newWriteState (putName hie_symtab)
                                           (putName hie_symtab)
                                           (putFastString hie_dict)
  put_ bh hiefile

  -- write the symtab pointer at the front of the file
  symtab_p <- tellBin bh
  putAt bh symtab_p_p symtab_p
  seekBin bh symtab_p

  -- write the symbol table itself
  symtab_next' <- readFastMutInt symtab_next
  symtab_map'  <- readIORef symtab_map
  putSymbolTable bh symtab_next' symtab_map'

  -- write the dictionary pointer at the fornt of the file
  dict_p <- tellBin bh
  putAt bh dict_p_p dict_p
  seekBin bh dict_p

  -- write the dictionary itself
  dict_next <- readFastMutInt dict_next_ref
  dict_map  <- readIORef dict_map_ref
  putDictionary bh dict_next dict_map

  -- and send the result to the file
  writeBinMem bh filename
  return ()

readHieFile :: Binary a => NameCache -> FilePath -> IO (a, NameCache)
readHieFile nc file = do
  bh0 <- readBinMem file

  dict  <- get_dictionary bh0

  -- read the symbol table so we are capable of reading the actual data
  (bh1, nc') <- do
      let bh1 = setUserData bh0 $ newReadState (error "getSymtabName")
                                               (getDictFastString dict)
      (nc', symtab) <- get_symbol_table bh1
      let bh1' = setUserData bh1
               $ newReadState (getSymTabName symtab)
                              (getDictFastString dict)
      return (bh1', nc')

  -- load the actual data
  hiefile <- get bh1
  return (hiefile, nc')
  where
    get_dictionary bin_handle = do
      dict_p <- get bin_handle
      data_p <- tellBin bin_handle
      seekBin bin_handle dict_p
      dict <- getDictionary bin_handle
      seekBin bin_handle data_p
      return dict

    get_symbol_table bh1 = do
      symtab_p <- get bh1
      data_p'  <- tellBin bh1
      seekBin bh1 symtab_p
      (nc', symtab) <- getSymbolTable bh1 nc
      seekBin bh1 data_p'
      return (nc', symtab)

putFastString :: HieDictionary -> BinHandle -> FastString -> IO ()
putFastString HieDictionary { hie_dict_next = j_r,
                              hie_dict_map  = out_r}  bh f
  = do
    out <- readIORef out_r
    let unique = getUnique f
    case lookupUFM out unique of
        Just (j, _)  -> put_ bh (fromIntegral j :: Word32)
        Nothing -> do
           j <- readFastMutInt j_r
           put_ bh (fromIntegral j :: Word32)
           writeFastMutInt j_r (j + 1)
           writeIORef out_r $! addToUFM out unique (j, f)

putSymbolTable :: BinHandle -> Int -> UniqFM (Int,HieName) -> IO ()
putSymbolTable bh next_off symtab = do
  put_ bh next_off
  let names = A.elems (A.array (0,next_off-1) (nonDetEltsUFM symtab))
  mapM_ (serializeHieName bh) names

getSymbolTable :: BinHandle -> NameCache -> IO (NameCache, SymbolTable)
getSymbolTable bh namecache = do
  sz <- get bh
  od_names <- replicateM sz (getHieName bh)
  let arr = A.listArray (0,sz-1) names
      (namecache', names) = mapAccumR fromHieName namecache od_names
  return (namecache', arr)

getSymTabName :: SymbolTable -> BinHandle -> IO Name
getSymTabName st bh = do
  i :: Word32 <- get bh
  return $ st A.! (fromIntegral i)

putName :: HieSymbolTable -> BinHandle -> Name -> IO ()
putName (HieSymbolTable next ref) bh name = do
  symmap <- readIORef ref
  case lookupUFM symmap name of
    Just (off, ExternalName mod occ (UnhelpfulSpan _))
      | isGoodSrcSpan (nameSrcSpan name) -> do
      writeIORef ref $! addToUFM symmap name (off, ExternalName mod occ (nameSrcSpan name))
      put_ bh (fromIntegral off :: Word32)
    Just (off, LocalName{})
      | notLocal (toHieName name) -> do
      writeIORef ref $! addToUFM symmap name (off, toHieName name)
      put_ bh (fromIntegral off :: Word32)
    Just (off, _) -> put_ bh (fromIntegral off :: Word32)
    Nothing -> do
        off <- readFastMutInt next
        writeFastMutInt next (off+1)
        writeIORef ref $! addToUFM symmap name (off, toHieName name)
        put_ bh (fromIntegral off :: Word32)

notLocal :: HieName -> Bool
notLocal LocalName{} = False
notLocal _ = True

toHieName :: Name -> HieName
toHieName name
  | isKnownKeyName name = KnownKeyName $ nameUnique name
  | isExternalName name = ExternalName (nameModule name) (nameOccName name) (nameSrcSpan name)
  | otherwise = LocalName (nameOccName name) (nameSrcSpan name)

fromHieName :: NameCache -> HieName -> (NameCache, Name)
fromHieName nc (ExternalName mod occ span) =
    let cache = nsNames nc
    in case lookupOrigNameCache cache mod occ of
         Just name -> (nc, name)
         Nothing ->
           let (uniq, us) = takeUniqFromSupply (nsUniqs nc)
               name       = mkExternalName uniq mod occ span
               new_cache  = extendNameCache cache mod occ name
           in ( nc{ nsUniqs = us, nsNames = new_cache }, name )
fromHieName nc (LocalName occ span) =
    let (uniq, us) = takeUniqFromSupply (nsUniqs nc)
        name       = mkInternalName uniq occ span
    in ( nc{ nsUniqs = us }, name )
fromHieName nc (KnownKeyName u) = case lookupKnownKeyName u of
    Nothing -> pprPanic "fromHieName:unknown known-key unique"
                        (ppr (unpkUnique u))
    Just n -> (nc, n)

serializeHieName :: BinHandle -> HieName -> IO ()
serializeHieName bh (ExternalName mod occ span) = do
  putByte bh 0
  put_ bh (mod, occ, span)
serializeHieName bh (LocalName occName span) = do
  putByte bh 1
  put_ bh (occName, span)
serializeHieName bh (KnownKeyName uniq) = do
  putByte bh 2
  put_ bh $ unpkUnique uniq

getHieName :: BinHandle -> IO HieName
getHieName bh = do
  t <- getByte bh
  case t of
    0 -> do
      (modu, occ, span) <- get bh
      return $ ExternalName modu occ span
    1 -> do
      (occ, span) <- get bh
      return $ LocalName occ span
    2 -> do
      (c,i) <- get bh
      return $ KnownKeyName $ mkUnique c i

putEnum :: Enum a => BinHandle -> a -> IO ()
putEnum bh = putByte bh . fromIntegral . fromEnum

getEnum :: Enum a => BinHandle -> IO a
getEnum bh = toEnum . fromIntegral <$> getByte bh

instance Binary (HieArgs Int) where
  put_ bh (HieArgs xs) = put_ bh xs
  get bh = HieArgs <$> get bh

instance Binary (HieType Int) where
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

instance Binary BindType where
  put_ = putEnum
  get = getEnum

instance Binary RecFieldContext where
  put_ = putEnum
  get = getEnum

instance Binary DeclType where
  put_ = putEnum
  get = getEnum

instance Binary IEType where
  put_ = putEnum
  get = getEnum

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

instance Binary (IdentifierDetails Int) where
  put_ bh dets = do
    put_ bh $ identType dets
    put_ bh $ S.toAscList $ identInfo dets
  get bh =  IdentifierDetails
    <$> get bh
    <*> fmap (S.fromAscList) (get bh)

instance Binary (NodeInfo Int) where
  put_ bh ni = do
    put_ bh $ S.toAscList $ nodeAnnotations ni
    put_ bh $ nodeType ni
    put_ bh $ M.toList $ nodeIdentifiers ni
  get bh = NodeInfo
    <$> fmap (S.fromAscList) (get bh)
    <*> get bh
    <*> fmap (M.fromList) (get bh)

instance Binary RealSrcSpan where
  put_ bh ss = do
    put_ bh (srcSpanFile ss)
    put_ bh (srcSpanStartLine ss)
    put_ bh (srcSpanStartCol ss)
    put_ bh (srcSpanEndLine ss)
    put_ bh (srcSpanEndCol ss)
  get bh = do
    f <- get bh
    [sl,sc,el,ec] <- replicateM 4 $ get bh
    return $ mkRealSrcSpan (mkRealSrcLoc f sl sc) (mkRealSrcLoc f el ec)

instance Binary (HieAST Int) where
  put_ bh ast = do
    put_ bh $ nodeInfo ast
    put_ bh $ nodeSpan ast
    put_ bh $ nodeChildren ast

  get bh = Node
    <$> get bh
    <*> get bh
    <*> get bh

instance Binary a => Binary (A.Array TypeIndex a) where
  put_ bh arr = do
    put_ bh $ A.bounds arr
    put_ bh $ A.elems arr
  get bh = do
    bounds <- get bh
    xs <- get bh
    return $ A.listArray bounds xs

instance Binary (HieASTs Int) where
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
