{-# LANGUAGE QuasiQuotes #-}
module Examples where
import Language.Haskell.TH.Arrow
import Control.Arrow
import Control.Category
import Prelude hiding (id,(.))
import Language.Haskell.Meta.Syntax.Translate.Arrow

example1 :: Arrow a => a b b
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

example4 :: (Num b,Arrow a) => a b (b,b)
example4 = [arrow|
    proc x -> do
        y <- arr (*2) -< x
        let z = y + x
        returnA -< (y,z)
    |]

-- | From http://haskell.cs.yale.edu/wp-content/uploads/2011/01/ICFP-CCA.pdf
example5 :: ArrowInit a => a () Double
example5 = [arrow|
    proc () -> do
        rec
            let e = 1 + i
            i <- integral -< e
        returnA -< e
        |]
integral :: ArrowInit a => a Double Double
integral = [arrow| proc n -> do
    rec
        v <- delay 0 -< i + (0.01) * n
        i <- id -< v
    returnA -< i
    |]

example6 :: ArrowChoice a => a (Int,Int) Int
example6 = [arrow|
    proc (x,y) ->
         if x == y
         then arr (*2) -< x+1
         else arr (*3) -< y+2
         |]

example7 :: ArrowChoice a => a (Maybe Int) Int
example7 = [arrow|
    proc n -> case n of
        Just a -> id -< a
        _ -> id -< 1
        |]

class ArrowLoop a => ArrowInit a where
    delay :: b -> a b b

newtype SF a b = SF { unSF :: a -> (b, SF a b) }
instance Arrow SF where
    arr f = SF h
        where h x = (f x, SF h)
    first f = SF (h f)
        where h f (x, z) = let ~(y, f') = unSF f x
                           in ((y, z), SF (h f'))
instance Category SF where
    id = SF (\a -> (a,id))
    g . f = SF (h f g)
          where h f g x = let ~(y, f') = unSF f x
                              ~(z, g') = unSF g y
                          in (z, SF (h f' g'))
instance ArrowLoop SF where
    loop f = SF (\a -> let ((b,d),f') = unSF f (a,d) in (b,loop f'))

instance ArrowInit SF where
    delay i =SF (\x -> (i,delay x))

runSF :: (Show a,Show b) => SF a b -> [a] -> [b]
runSF = g
    where
        g _ [] = []
        g f (x:xs) = let (y, f') = unSF f x
                       in y : g f' xs
