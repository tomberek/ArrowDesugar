{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

module Rule where
import Language.Haskell.TH.Desugar
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Rule
import Control.Arrow
import Control.Monad.Maybe
import Control.Category
import Prelude hiding (id,(.))
import Data.Generics (everywhere,mkT,extT)

rasdf :: DExp -> MaybeT Q DExp
{-
rasdf [rule| id >>> t |] =  into $ t_ -- $ into [| $t |]
rasdf [rule| t >>> id |] =  into $ t_ -- $ into [| $t |]
rasdf [rule| a >>> (b >>> c) |] = into $ (a_ >>> b_) >>> c_
-}
rasdf [rule| t >>> id |] = into' [| $t |]
rasdf [rule| arr (\x -> y) |] | x_ == y_ = into' [| id |]
rasdf [rule| arr (\(a,b) -> c) |] | c_ == b_ = into' $ [| arr snd |]
rasdf [rule| (a &&& b) >>> arr fst |] = into' [| $a |]
rasdf [rule| (a &&& b) >>> arr snd |] = into' [| $b |]
rasdf [rule| arr (\g -> case f of y -> z) |] | g_ == f_ && y_ == z_ = into' [| id |]
rasdf [rule| a `bind` f |] = into' [| id &&& $a >>> $f |]
rasdf [rule| (a >>> b) >>> (c >>> d) |] = into' [| $a >>> (($b >>> $c) >>> $d) |]
rasdf [rule| a >>> (b >>> c) |] = into' [| ($a >>> $b) >>> $c |]
rasdf (DVarE (Name s t)) = MaybeT (fmap Just $ reportWarning (show (s,t))) >> nothing
rasdf a = nothing -- MaybeT (fmap Just $ reportWarning (show a)) >> nothing
instance Show NameFlavour where
    show NameS = "NameS"
    show (NameQ n)= "Mod: " ++ show n
    show (NameU n)= "Uniqu: "
    show (NameL n)= "Lit: "
    show (NameG n n2 n3)= "Mod: " ++ show (n2,n3)


into' :: Q Exp -> MaybeT Q DExp
into' f = MaybeT $ fmap Just $ f >>= dsExp >>= return . everywhere (mkT cleanLet)
into :: DExpCat a b -> MaybeT Q DExp
into = MaybeT . return. Just . unD

--cleanLet a@(DLamE [n1] (DLetE _ _))  = undefined -- DCaseE (DVarE n1) expr

nothing :: Monad m => MaybeT m a
nothing = MaybeT (return Nothing)

