%
% (c) The University of Glasgow, 1997-2006
%
\begin{code}
{-
FastString:	A compact, hash-consed, representation of character strings.
		Comparison is O(1), and you can get a Unique from them.
		Generated by the FSLIT macro
		Turn into SDoc with Outputable.ftext

LitString:	Just a wrapper for the Addr# of a C string (Ptr CChar).
		Practically no operations
		Outputing them is fast
		Generated by the SLIT macro
		Turn into SDoc with Outputable.ptext

Use LitString unless you want the facilities of FastString
-}
module FastString
       (
	-- * FastStrings
	FastString(..),     -- not abstract, for now.

	-- ** Construction
        mkFastString,
	mkFastStringBytes,
        mkFastStringByteList,
	mkFastStringForeignPtr,
	mkFastString#,
	mkZFastString,
	mkZFastStringBytes,

	-- ** Deconstruction
	unpackFS,	    -- :: FastString -> String
	bytesFS,	    -- :: FastString -> [Word8]

	-- ** Encoding
	isZEncoded,
	zEncodeFS,

	-- ** Operations
        uniqueOfFS,
	lengthFS,
	nullFS,
	appendFS,
        headFS,
        tailFS,
	concatFS,
        consFS,
	nilFS,

	-- ** Outputing
        hPutFS,

	-- ** Internal
	getFastStringTable,
	hasZEncoding,

	-- * LitStrings
	LitString, 
	mkLitString#,
	strLength
       ) where

-- This #define suppresses the "import FastString" that
-- HsVersions otherwise produces
#define COMPILING_FAST_STRING
#include "HsVersions.h"

import Encoding

import Foreign
import Foreign.C
import GHC.Exts
import System.IO.Unsafe ( unsafePerformIO )
import Control.Monad.ST	( stToIO )
import Data.IORef	( IORef, newIORef, readIORef, writeIORef )
import System.IO	( hPutBuf )
import Data.Maybe	( isJust )

import GHC.ST
import GHC.IOBase	( IO(..) )
import GHC.Ptr		( Ptr(..) )

#define hASH_TBL_SIZE          4091
#define hASH_TBL_SIZE_UNBOXED  4091#


{-|
A 'FastString' is an array of bytes, hashed to support fast O(1)
comparison.  It is also associated with a character encoding, so that
we know how to convert a 'FastString' to the local encoding, or to the
Z-encoding used by the compiler internally.

'FastString's support a memoized conversion to the Z-encoding via zEncodeFS.
-}

data FastString = FastString {
      uniq    :: {-# UNPACK #-} !Int,       -- unique id
      n_bytes :: {-# UNPACK #-} !Int,       -- number of bytes
      n_chars :: {-# UNPACK #-} !Int,	  -- number of chars
      buf     :: {-# UNPACK #-} !(ForeignPtr Word8),
      enc     :: FSEncoding
  }

data FSEncoding
  = ZEncoded
 	-- including strings that don't need any encoding
  | UTF8Encoded {-# UNPACK #-} !(IORef (Maybe FastString))
	-- A UTF-8 string with a memoized Z-encoding

instance Eq FastString where
  f1 == f2  =  uniq f1 == uniq f2

instance Ord FastString where
	-- Compares lexicographically, not by unique
    a <= b = case cmpFS a b of { LT -> True;  EQ -> True;  GT -> False }
    a <	 b = case cmpFS a b of { LT -> True;  EQ -> False; GT -> False }
    a >= b = case cmpFS a b of { LT -> False; EQ -> True;  GT -> True  }
    a >	 b = case cmpFS a b of { LT -> False; EQ -> False; GT -> True  }
    max x y | x >= y	=  x
            | otherwise	=  y
    min x y | x <= y	=  x
            | otherwise	=  y
    compare a b = cmpFS a b

instance Show FastString where
   show fs = show (unpackFS fs)

cmpFS :: FastString -> FastString -> Ordering
cmpFS (FastString u1 l1 _ buf1 _) (FastString u2 l2 _ buf2 _) =
  if u1 == u2 then EQ else
  case unsafeMemcmp buf1 buf2 (min l1 l2) `compare` 0 of
     LT -> LT
     EQ -> compare l1 l2
     GT -> GT

unsafeMemcmp :: ForeignPtr a -> ForeignPtr b -> Int -> Int
unsafeMemcmp buf1 buf2 l =
      inlinePerformIO $
        withForeignPtr buf1 $ \p1 ->
        withForeignPtr buf2 $ \p2 ->
          memcmp p1 p2 l

#ifndef __HADDOCK__
foreign import ccall unsafe "ghc_memcmp" 
  memcmp :: Ptr a -> Ptr b -> Int -> IO Int
#endif

-- -----------------------------------------------------------------------------
-- Construction

{-
Internally, the compiler will maintain a fast string symbol
table, providing sharing and fast comparison. Creation of
new @FastString@s then covertly does a lookup, re-using the
@FastString@ if there was a hit.
-}

data FastStringTable = 
 FastStringTable
    {-# UNPACK #-} !Int
    (MutableArray# RealWorld [FastString])

{-# NOINLINE string_table #-}
string_table :: IORef FastStringTable
string_table = 
 unsafePerformIO $ do
   tab <- IO $ \s1# -> case newArray# hASH_TBL_SIZE_UNBOXED [] s1# of
                           (# s2#, arr# #) ->
                               (# s2#, FastStringTable 0 arr# #)
   newIORef tab

lookupTbl :: FastStringTable -> Int -> IO [FastString]
lookupTbl (FastStringTable _ arr#) (I# i#) =
  IO $ \ s# -> readArray# arr# i# s#

updTbl :: IORef FastStringTable -> FastStringTable -> Int -> [FastString] -> IO ()
updTbl fs_table_var (FastStringTable uid arr#) (I# i#) ls = do
  (IO $ \ s# -> case writeArray# arr# i# ls s# of { s2# -> (# s2#, () #) })
  writeIORef fs_table_var (FastStringTable (uid+1) arr#)

mkFastString# :: Addr# -> FastString
mkFastString# a# = mkFastStringBytes ptr (strLength ptr)
  where ptr = Ptr a#

mkFastStringBytes :: Ptr Word8 -> Int -> FastString
mkFastStringBytes ptr len = unsafePerformIO $ do
  ft@(FastStringTable uid tbl#) <- readIORef string_table
  let
   h = hashStr ptr len
   add_it ls = do
	fs <- copyNewFastString uid ptr len
	updTbl string_table ft h (fs:ls)
	{- _trace ("new: " ++ show f_str)   $ -}
	return fs
  --
  lookup_result <- lookupTbl ft h
  case lookup_result of
    [] -> add_it []
    ls -> do
       b <- bucket_match ls len ptr
       case b of
	 Nothing -> add_it ls
	 Just v  -> {- _trace ("re-use: "++show v) $ -} return v

mkZFastStringBytes :: Ptr Word8 -> Int -> FastString
mkZFastStringBytes ptr len = unsafePerformIO $ do
  ft@(FastStringTable uid tbl#) <- readIORef string_table
  let
   h = hashStr ptr len
   add_it ls = do
	fs <- copyNewZFastString uid ptr len
	updTbl string_table ft h (fs:ls)
	{- _trace ("new: " ++ show f_str)   $ -}
	return fs
  --
  lookup_result <- lookupTbl ft h
  case lookup_result of
    [] -> add_it []
    ls -> do
       b <- bucket_match ls len ptr
       case b of
	 Nothing -> add_it ls
	 Just v  -> {- _trace ("re-use: "++show v) $ -} return v

-- | Create a 'FastString' from an existing 'ForeignPtr'; the difference
-- between this and 'mkFastStringBytes' is that we don't have to copy
-- the bytes if the string is new to the table.
mkFastStringForeignPtr :: Ptr Word8 -> ForeignPtr Word8 -> Int -> IO FastString
mkFastStringForeignPtr ptr fp len = do
  ft@(FastStringTable uid tbl#) <- readIORef string_table
--  _trace ("hashed: "++show (I# h)) $
  let
    h = hashStr ptr len
    add_it ls = do
	fs <- mkNewFastString uid ptr fp len
	updTbl string_table ft h (fs:ls)
	{- _trace ("new: " ++ show f_str)   $ -}
	return fs
  --
  lookup_result <- lookupTbl ft h
  case lookup_result of
    [] -> add_it []
    ls -> do
       b <- bucket_match ls len ptr
       case b of
	 Nothing -> add_it ls
	 Just v  -> {- _trace ("re-use: "++show v) $ -} return v

mkZFastStringForeignPtr :: Ptr Word8 -> ForeignPtr Word8 -> Int -> IO FastString
mkZFastStringForeignPtr ptr fp len = do
  ft@(FastStringTable uid tbl#) <- readIORef string_table
--  _trace ("hashed: "++show (I# h)) $
  let
    h = hashStr ptr len
    add_it ls = do
	fs <- mkNewZFastString uid ptr fp len
	updTbl string_table ft h (fs:ls)
	{- _trace ("new: " ++ show f_str)   $ -}
	return fs
  --
  lookup_result <- lookupTbl ft h
  case lookup_result of
    [] -> add_it []
    ls -> do
       b <- bucket_match ls len ptr
       case b of
	 Nothing -> add_it ls
	 Just v  -> {- _trace ("re-use: "++show v) $ -} return v


-- | Creates a UTF-8 encoded 'FastString' from a 'String'
mkFastString :: String -> FastString
mkFastString str = 
  inlinePerformIO $ do
    let l = utf8EncodedLength str
    buf <- mallocForeignPtrBytes l
    withForeignPtr buf $ \ptr -> do
      utf8EncodeString ptr str
      mkFastStringForeignPtr ptr buf l 

-- | Creates a 'FastString' from a UTF-8 encoded @[Word8]@
mkFastStringByteList :: [Word8] -> FastString
mkFastStringByteList str = 
  inlinePerformIO $ do
    let l = Prelude.length str
    buf <- mallocForeignPtrBytes l
    withForeignPtr buf $ \ptr -> do
      pokeArray (castPtr ptr) str
      mkFastStringForeignPtr ptr buf l 

-- | Creates a Z-encoded 'FastString' from a 'String'
mkZFastString :: String -> FastString
mkZFastString str = 
  inlinePerformIO $ do
    let l = Prelude.length str
    buf <- mallocForeignPtrBytes l
    withForeignPtr buf $ \ptr -> do
      pokeCAString (castPtr ptr) str
      mkZFastStringForeignPtr ptr buf l 

bucket_match [] _ _ = return Nothing
bucket_match (v@(FastString _ l _ buf _):ls) len ptr
      | len == l  =  do
	 b <- cmpStringPrefix ptr buf len
	 if b then return (Just v)
	      else bucket_match ls len ptr
      | otherwise = 
	 bucket_match ls len ptr

mkNewFastString uid ptr fp len = do
  ref <- newIORef Nothing
  n_chars <- countUTF8Chars ptr len
  return (FastString uid len n_chars fp (UTF8Encoded ref))

mkNewZFastString uid ptr fp len = do
  return (FastString uid len len fp ZEncoded)


copyNewFastString uid ptr len = do
  fp <- copyBytesToForeignPtr ptr len
  ref <- newIORef Nothing
  n_chars <- countUTF8Chars ptr len
  return (FastString uid len n_chars fp (UTF8Encoded ref))

copyNewZFastString uid ptr len = do
  fp <- copyBytesToForeignPtr ptr len
  return (FastString uid len len fp ZEncoded)


copyBytesToForeignPtr ptr len = do
  fp <- mallocForeignPtrBytes len
  withForeignPtr fp $ \ptr' -> copyBytes ptr' ptr len
  return fp

cmpStringPrefix :: Ptr Word8 -> ForeignPtr Word8 -> Int -> IO Bool
cmpStringPrefix ptr fp len =
  withForeignPtr fp $ \ptr' -> do
    r <- memcmp ptr ptr' len
    return (r == 0)


hashStr  :: Ptr Word8 -> Int -> Int
 -- use the Addr to produce a hash value between 0 & m (inclusive)
hashStr (Ptr a#) (I# len#) = loop 0# 0#
   where 
    loop h n | n ==# len# = I# h
	     | otherwise  = loop h2 (n +# 1#)
	  where c = ord# (indexCharOffAddr# a# n)
		h2 = (c +# (h *# 128#)) `remInt#` hASH_TBL_SIZE#

-- -----------------------------------------------------------------------------
-- Operations

-- | Returns the length of the 'FastString' in characters
lengthFS :: FastString -> Int
lengthFS f = n_chars f

-- | Returns 'True' if the 'FastString' is Z-encoded
isZEncoded :: FastString -> Bool
isZEncoded fs | ZEncoded <- enc fs = True
		| otherwise          = False

-- | Returns 'True' if this 'FastString' is not Z-encoded but already has
-- a Z-encoding cached (used in producing stats).
hasZEncoding :: FastString -> Bool
hasZEncoding fs@(FastString uid n_bytes _ fp enc) =
  case enc of
    ZEncoded -> False
    UTF8Encoded ref ->
      inlinePerformIO $ do
        m <- readIORef ref
	return (isJust m)

-- | Returns 'True' if the 'FastString' is empty
nullFS :: FastString -> Bool
nullFS f  =  n_bytes f == 0

-- | unpacks and decodes the FastString
unpackFS :: FastString -> String
unpackFS (FastString _ n_bytes _ buf enc) = 
  inlinePerformIO $ withForeignPtr buf $ \ptr ->
    case enc of
	ZEncoded      -> peekCAStringLen (castPtr ptr,n_bytes)
	UTF8Encoded _ -> utf8DecodeString ptr n_bytes

bytesFS :: FastString -> [Word8]
bytesFS (FastString _ n_bytes _ buf enc) = 
  inlinePerformIO $ withForeignPtr buf $ \ptr ->
    peekArray n_bytes ptr

-- | returns a Z-encoded version of a 'FastString'.  This might be the
-- original, if it was already Z-encoded.  The first time this
-- function is applied to a particular 'FastString', the results are
-- memoized.
--
zEncodeFS :: FastString -> FastString
zEncodeFS fs@(FastString uid n_bytes _ fp enc) =
  case enc of
    ZEncoded -> fs
    UTF8Encoded ref ->
      inlinePerformIO $ do
        m <- readIORef ref
        case m of
	  Just fs -> return fs
	  Nothing -> do
            let efs = mkZFastString (zEncodeString (unpackFS fs))
	    writeIORef ref (Just efs)
	    return efs

appendFS :: FastString -> FastString -> FastString
appendFS fs1 fs2 = mkFastString (unpackFS fs1 ++ unpackFS fs2)

concatFS :: [FastString] -> FastString
concatFS ls = mkFastString (Prelude.concat (map unpackFS ls)) -- ToDo: do better

headFS :: FastString -> Char
headFS (FastString _ n_bytes _ buf enc) = 
  inlinePerformIO $ withForeignPtr buf $ \ptr -> do
    case enc of
      ZEncoded -> do 
	 w <- peek (castPtr ptr)
	 return (castCCharToChar w)
      UTF8Encoded _ -> 
	 return (fst (utf8DecodeChar ptr))

tailFS :: FastString -> FastString
tailFS (FastString _ n_bytes _ buf enc) = 
  inlinePerformIO $ withForeignPtr buf $ \ptr -> do
    case enc of
      ZEncoded -> do
	return $! mkZFastStringBytes (ptr `plusPtr` 1) (n_bytes - 1)
      UTF8Encoded _ -> do
	 let (_,ptr') = utf8DecodeChar ptr
	 let off = ptr' `minusPtr` ptr
	 return $! mkFastStringBytes (ptr `plusPtr` off) (n_bytes - off)

consFS :: Char -> FastString -> FastString
consFS c fs = mkFastString (c : unpackFS fs)

uniqueOfFS :: FastString -> Int#
uniqueOfFS (FastString (I# u#) _ _ _ _) = u#

nilFS = mkFastString ""

-- -----------------------------------------------------------------------------
-- Stats

getFastStringTable :: IO [[FastString]]
getFastStringTable = do
  tbl <- readIORef string_table
  buckets <- mapM (lookupTbl tbl) [0 .. hASH_TBL_SIZE]
  return buckets

-- -----------------------------------------------------------------------------
-- Outputting 'FastString's

-- |Outputs a 'FastString' with /no decoding at all/, that is, you
-- get the actual bytes in the 'FastString' written to the 'Handle'.
hPutFS handle (FastString _ len _ fp _)
  | len == 0  = return ()
  | otherwise = do withForeignPtr fp $ \ptr -> hPutBuf handle ptr len

-- ToDo: we'll probably want an hPutFSLocal, or something, to output
-- in the current locale's encoding (for error messages and suchlike).

-- -----------------------------------------------------------------------------
-- LitStrings, here for convenience only.

type LitString = Ptr ()

mkLitString# :: Addr# -> LitString
mkLitString# a# = Ptr a#

foreign import ccall unsafe "ghc_strlen" 
  strLength :: Ptr () -> Int

-- -----------------------------------------------------------------------------
-- under the carpet

-- Just like unsafePerformIO, but we inline it.
{-# INLINE inlinePerformIO #-}
inlinePerformIO :: IO a -> a
inlinePerformIO (IO m) = case m realWorld# of (# _, r #)   -> r

-- NB. does *not* add a '\0'-terminator.
pokeCAString :: Ptr CChar -> String -> IO ()
pokeCAString ptr str =
  let
	go [] n     = return ()
    	go (c:cs) n = do pokeElemOff ptr n (castCharToCChar c); go cs (n+1)
  in
  go str 0

#if __GLASGOW_HASKELL__ <= 602
peekCAStringLen = peekCStringLen
#endif
\end{code}
