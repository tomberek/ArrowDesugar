-- | Main entry point to the application.
module Main where
import Language.Haskell.Meta.Syntax.Translate.Arrow
import Language.Haskell.Meta.Utils
import qualified Language.Haskell.Exts.Parser as Hs
import Examples
import Debug.Trace

-- | The main entry point.
main :: IO ()
main = do
    print $ fst $ unSF example5 ()
    print $ take 10 $ runSF example5 $ repeat ()
    print $ example6 (3,3)
    print $ pp g
inp = (trace "made ()" ()) : inp

-- g :: Hs.ParseResult Hs.Exp
g = toExpA res
    where Hs.ParseOk res = parseA $ unlines
              ["proc x ->",
               "case x of",
               "Just a ->  arr (*2) -< a",
               "_ -> arr (*3) -< x"
               ]

