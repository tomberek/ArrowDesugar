{-# LANGUAGE QuasiQuotes #-}
module Examples where
import Language.Haskell.TH.Arrow
import Control.Arrow
import Control.Category
import Prelude hiding (id,(.))
import Language.Haskell.Meta.Syntax.Translate.Arrow

example1 :: (Arrow a,Category a) => a b b
example1 = [arrow|
    proc x -> id -< x
    |]

example2 :: (Num b, Arrow a) => a b b
example2 = [arrow|
    proc x -> do
        y <- id -< x
        id -< x + y
    |]

example3 :: Arrow a => a b b
example3 = [arrow|
    proc x -> do
        y <- id -< x
        z <- id -< (x,y)
        arr fst -< z
    |]

example4 :: Arrow a => a b (b,b)
example4 = [arrow|
    proc x -> do
        y <- arr (*2) -< x
        let z = y + x
        returnA -< (y,z)
    |]