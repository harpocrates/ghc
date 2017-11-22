{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE TemplateHaskell #-}

import Language.Haskell.TH.Syntax
import System.IO (hFlush, stdout)

foreign import ccall fc :: Int -> IO Int

do fpIn <- addTempFile "c"
   let cSrc = (unlines [ "#include <stdio.h>"
                       , "int foo(int x) {"
                       , "  printf(\"calling f(%d)\\n\",x);"
                       , "  fflush(stdout);"
                       , "  return 1 + x;"
                       , "}"
                       ])
   runIO $ writeFile fpIn cSrc
   addForeignFilePath LangC cSrc
   return []

main :: IO ()
main = do
  fc 2 >>= print
  hFlush stdout
