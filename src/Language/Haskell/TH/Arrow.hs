module Language.Haskell.TH.Arrow where
import Language.Haskell.TH.Quote
import Language.Haskell.TH
import Language.Haskell.Meta.Utils
import qualified Language.Haskell.Exts as E
import Language.Haskell.Meta.Syntax.Translate.Arrow
import Data.Char (isAlpha)


parseMode :: E.ParseMode
parseMode = E.defaultParseMode{E.extensions=[E.EnableExtension E.Arrows],E.fixities=Just E.baseFixities}

arrow :: QuasiQuoter
arrow = QuasiQuoter {
  quoteExp = \input -> case E.parseExpWithMode parseMode input of
      E.ParseOk result -> do
          let res = toExpA result
          reportWarning $ simplify $ pp res
          return res
      E.ParseFailed l err -> error $ "arrow QuasiQuoter: " ++ show l ++ " " ++ show err
  , quotePat = error "arrow QuasiQuoter cannot be used for patterns."
  , quoteDec = \input -> case E.parseDeclWithMode parseMode input of
      E.ParseOk _ -> error "arrow quasiQuoter for Dec not defined"
      E.ParseFailed l err -> error $ "arrow QuasiQuoter in Decl cannot parse: " ++ show l ++ " " ++ show err
  , quoteType = error "arrow QuasiQuoter cannot be used for types."
    }

simplify :: String -> String
simplify = unwords . map (unwords . map aux . words) . lines
  where aux (c:x) | not (isAlpha c) = c : aux x
        aux x = let (_, v) = break (=='.') x
                in if length v > 1 then aux (tail v)
                                   else x