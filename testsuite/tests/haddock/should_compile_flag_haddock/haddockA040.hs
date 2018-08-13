module MisplacedHadddocks where

data A = A
data B = B

f1 -- | misplaced 1
   :: A -- ^ comment 1
   -> B -- ^ comment 2
f1 {-^ misplaced 2 -} A = B

