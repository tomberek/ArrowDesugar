-- | Main entry point to the application.
module Main where
import Language.Haskell.Meta.Syntax.Translate.Arrow
import Language.Haskell.Meta.Utils
import qualified Language.Haskell.Exts.Parser as Hs

-- | The main entry point.
main :: IO ()
main = do
    print $ pp g

-- g :: Hs.ParseResult Hs.Exp
g = toExpA res
    where Hs.ParseOk res = parseA $ unlines
              ["proc x -> do",
               "y <- id -< x",
               "z <- id -< x",
               "returnA -< z + y"]

