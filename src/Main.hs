-- | Main entry point to the application.
module Main where
import Language.Haskell.Meta.Syntax.Translate.Arrow
import qualified Language.Haskell.Exts.Parser as Hs
import Examples
import Debug.Trace
import Language.Haskell.TH(pprint,Exp(..))
import Language.Haskell.TH.Rule
import Language.Haskell.TH.Desugar.Sweeten

import Data.Char(isAlpha)

-- | The main entry point.
main :: IO ()
main = do
    --print $ fst $ unSF example5 ()
    --print $ take 4 $ runSF example5 $ repeat ()
    --print $ example6 (3,3)
    --print $ example2 5
    --putStrLn $ pprint g
    --e3 <- fixArr (unD (example3 :: DExpCat Int Int))
    let e3 = (unD (example3 :: DExpCat Int Int))
    print e3
    print $ simplify $ pprint $ expToTH e3

simplify :: String -> String
simplify = unwords . map (unwords . map aux . words) . lines
    where aux (c:x) | not (isAlpha c) = c : aux x
          aux x = let (_, v) = break (=='.') x
            in if length v > 1 then aux (tail v)
                               else x


g :: Exp
g = toExpA res
    where Hs.ParseOk res = parseA $ unlines
              ["proc x ->",
               "case x of",
               "Just a ->  arr (*2) -< a",
               "_ -> arr (*3) -< x"
               ]
