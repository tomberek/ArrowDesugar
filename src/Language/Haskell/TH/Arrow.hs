{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
module Language.Haskell.TH.Arrow where
import Language.Haskell.TH.Quote
import Language.Haskell.TH

import qualified Language.Haskell.Exts as E
import Language.Haskell.Meta.Syntax.Translate.Arrow
import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Desugar.Sweeten
import Data.Generics
import Language.Haskell.TH.Rule
import Rule

parseMode :: E.ParseMode
parseMode = E.defaultParseMode{E.extensions=[E.EnableExtension E.Arrows],E.fixities=Just E.baseFixities}

arrow :: QuasiQuoter
arrow = QuasiQuoter {
  quoteExp = \input -> case E.parseExpWithMode parseMode input of
      E.ParseOk result -> do
          let res = fixFixityTuples $ toExpA result
          res3 <- dsExp res
          res4 <- rewriteM rasdf res3
          reportWarning . pprint $ expToTH $ res4
          return $ expToTH res3
      E.ParseFailed l err -> error $ "arrow QuasiQuoter: " ++ show l ++ " " ++ show err
  , quotePat = error "arrow QuasiQuoter cannot be used for patterns."
  , quoteDec = error "arrow QuasiQuoter cannot be used for declarations."
  , quoteType = error "arrow QuasiQuoter cannot be used for types."
    }
fixFixityTuples :: Data a => a -> a
fixFixityTuples = everywhere (id `extT` (\case
                     UInfixE l o r -> InfixE (Just l) o (Just r)
                     TupE [a] -> a
                     a -> a)
                     `extT` \case
                     TupP [a] -> a
                     a -> a)
