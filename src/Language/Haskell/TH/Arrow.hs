module Language.Haskell.TH.Arrow where
import Language.Haskell.TH.Quote
import Language.Haskell.TH
import qualified Language.Haskell.Exts as E
import Language.Haskell.Meta.Syntax.Translate.Arrow
import Language.Haskell.Meta.Utils

parseMode :: E.ParseMode
parseMode = E.defaultParseMode{E.extensions=[E.EnableExtension E.Arrows],E.fixities=Just E.baseFixities}

arrow :: QuasiQuoter
arrow = QuasiQuoter {
  quoteExp = \input -> case E.parseExpWithMode parseMode input of
      E.ParseOk result -> do
          let res = toExpA result
          --reportError $ pp res
          return res
      E.ParseFailed l err -> error $ "arrow QuasiQuoter: " ++ show l ++ " " ++ show err
  , quotePat = error "cannot be patterns."
  , quoteDec = \input -> case E.parseDeclWithMode parseMode input of
      E.ParseOk _ -> error "arrow quasiQuoter for Dec not defined"
      E.ParseFailed l err -> error $ "arrow QuasiQuoter in Decl: " ++ show l ++ " " ++ show err
  , quoteType = error "cannot be types."
    }