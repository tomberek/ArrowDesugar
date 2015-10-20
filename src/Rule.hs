{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

module Rule where
import Language.Haskell.TH.Desugar
import Language.Haskell.TH
import Language.Haskell.TH.Rule
import Control.Arrow
import Control.Monad.Maybe

rasdf :: DExp -> MaybeT Q DExp
rasdf [rule| id >>> t |] = into [| $t |]
rasdf [rule| t >>> id |] = into [| $t |]
rasdf [rule| a >>> (b >>> c) |] = into [| ($a >>> $b) >>> $c |]
rasdf _ = nothing

nothing :: Monad m => MaybeT m a
nothing = MaybeT (return Nothing)
into :: Q Exp -> MaybeT Q DExp
into f = MaybeT $ fmap Just $ f >>= dsExp

