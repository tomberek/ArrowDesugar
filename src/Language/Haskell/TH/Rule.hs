{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE IncoherentInstances #-}
module Language.Haskell.TH.Rule where
import Language.Haskell.TH.Quote
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Desugar.Sweeten
import Language.Haskell.Meta.Parse(parseExp)
import Data.Generics
import Data.Char (isLower)
import Control.Arrow (Arrow,arr,first,second,(***),(&&&))
import Control.Category
import Prelude hiding (id,(.))
import Control.Monad.Maybe
import Control.Monad
import Control.Category
import Prelude hiding (id,(.))
import Language.Haskell.TH.Desugar.Lift

newtype DExpCat b c = DExpCat {unD::DExp}
instance Category DExpCat where
    id = DExpCat (DVarE (mkName "id"))
    DExpCat b . DExpCat a = DExpCat $ DAppE (DAppE (DVarE $ mkName ".") b) a
class Arrow a => Arrow' a where
    arr' :: DExp -> (b -> c) -> a b c
instance Arrow DExpCat where
    arr = error "use arr' instead"
    first (DExpCat f) = DExpCat $ DAppE (DVarE $ mkName "first") f
    second (DExpCat f) = DExpCat $ DAppE (DVarE $ mkName "second") f
    (DExpCat f) &&& (DExpCat g) = DExpCat $ DAppE (DAppE (DVarE $ mkName "&&&") f) g
    (DExpCat f) *** (DExpCat g) = DExpCat $ DAppE (DAppE (DVarE $ mkName "***") f) g
instance (ArrowPred a ~ HFalse,Arrow a) => Arrow' a where
    arr' _ f = error "bing"
instance Arrow' DExpCat where
    arr' f _ = DExpCat $ DAppE (DVarE $ mkName "arr'") f
instance Show (DExpCat b c) where
    show (DExpCat a) = "DExpCat " ++ show a
data HTrue
data HFalse
type family ArrowPred a where
    ArrowPred DExpCat    = HTrue
    ArrowPred a     = HFalse

fixArr :: (Quasi q) => DExp -> q (DExp)
fixArr expr = everywhereM (mkM (\case
    DAppE (DVarE (Name (OccName "arr") nametype)) expression -> do
        exp' <- runQ (lift expression) >>= dsExp
        return $ DAppE (DAppE (DVarE (Name (OccName "arr'") NameS)) exp') expression
    DVarE (Name (OccName "returnA") nametype) -> do
       id' <- runQ (lift $ DVarE $ mkName "id") >>= dsExp
       return $ DAppE (DAppE (DVarE (Name (OccName "arr'") NameS)) id') (DVarE $ mkName "id")
    a -> return a
    )) expr

pattern NameT s = Name (OccName s) NameS

rule :: QuasiQuoter
rule = QuasiQuoter{
      quoteExp = \input -> case parseExp input of
           Right b -> error "Good parse of rule exp" --dataToExpQ (const Nothing `extQ` updateNameE) b
           Left err -> error $ "Exp: cannot parse rule pattern: " ++ show err ++ " " ++ input
      ,quotePat = \input -> case parseExp input of
           Right (everywhere (mkT updateFixityParens) -> b) -> dsExp b >>= dataToPatQ (const Nothing `extQ` updateNameP `extQ` updatePat) . everywhere (mkT cleanLet)
           Left err -> error $ "cannot parse rule pattern: " ++ show err  ++ " " ++ input
      ,quoteDec = error "cannot be declarations."
      ,quoteType = error "cannot be types."
              }
cleanLet a@(DLamE [n1] (DLetE [DValD (DVarPa n2) (DVarE n3)] (DCaseE (DVarE n4) expr))) | n1 == n3 && n2 == n4 = DLamE [n1] (DCaseE (DVarE n3) expr)
cleanLet a@(DLetE [DValD (DVarPa n1) (DVarE n2)] (DCaseE (DVarE n3) expr)) | n1 == n3 = DCaseE (DVarE n2) expr
                                                                           | otherwise = a
cleanLet (DVarE n@(Name s (NameQ _))) = DVarE (Name s NameS)
cleanLet (DVarE n@(Name s (NameG _ _ _))) = DVarE (Name s NameS)
cleanLet a = a

type RuleE = Exp -> Q (Maybe Exp)
rewriteM :: forall m a. (Data a,Monad m) => (a -> MaybeT m a) -> a -> m a
rewriteM f it = everywhereM (mkM  (\x -> runMaybeT (f x) >>= maybe (return x) (rewriteM f))) it

updateNameP :: DExp -> Maybe (Q Pat)
updateNameP (DVarE n@(Name (OccName [s]) NameS))
    -- | isLower s = Just $ [p| (returnQ . expToTH -> $(varP n)) |] >>= return . AsP (NameT [s,'_'])
    | isLower s = Just $ [p| (expToTH -> $([p| (returnQ -> $(varP n)) |] >>= return . AsP (Name (OccName [s,'_']) NameS))) |]
    | otherwise = Nothing
updateNameP (DLamE [n@(Name (OccName [s]) NameS)] expr) = Just [p| DLamE [$pat'] $(dataToPatQ (const Nothing `extQ` updateNameP `extQ` updatePat) expr) |]
    where pat' = [p| (expToTH . DVarE -> $( [p| (returnQ -> $(varP $ NameT $ s:"__")) |]
                    >>= return . AsP (NameT $ s:"_" ))
                                                 ) |]
                    >>= return. AsP (NameT $ s:"___" )
updateNameP (DLamE [n] (DCaseE (DVarE n2) [DMatch pat expr])) | n == n2 = Just [p| DLamE _ (DCaseE _ [DMatch $(dataToPatQ (const Nothing `extQ` updateNameP `extQ` updatePat) pat)
                                                                                                             $(dataToPatQ (const Nothing `extQ` updateNameP `extQ` updatePat) expr)] ) |]
updateNameP n = Nothing

updatePat :: DPat -> Maybe (Q Pat)
updatePat (DVarPa n@(Name s (NameU _))) = Just $ [p| _ |]
updatePat (DVarPa (NameT s@[t])) = Just $
    [p| ((expToTH . dPatToDExp) &&& (returnQ . patToTH) -> ( $( [p| (returnQ -> $(varP $ NameT $ s ++ "__")) |]
                                                                             >>= return . AsP (NameT $ s ++ "_")), $(varP $ NameT s)
                                                                                                         )) |]
                                                                             >>= return. AsP (NameT $ s ++ "___" )
updatePat _ = Nothing

updateNameE :: Exp -> Maybe ExpQ
updateNameE (VarE n@(Name (OccName [s]) NameS))
    | isLower s = Just $ varE n
    | otherwise = Nothing
updateNameE n = Nothing

-- | Cannot cope with un-handled fixities, ensure all rules have clearly resolved fixity
updateFixityParens :: Exp -> Exp
updateFixityParens (UInfixE l o r) = InfixE (Just l) o (Just r)
updateFixityParens (ParensE e@(LamE _ _)) = e
updateFixityParens (ParensE (UInfixE a b c)) = InfixE (Just a) b (Just c)
updateFixityParens (ParensE (AppE a b)) = AppE a b
updateFixityParens n = n