{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
module Language.Haskell.TH.Rule where
import Language.Haskell.TH.Quote
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Desugar.Sweeten
import Language.Haskell.Meta.Parse(parseExp)
import Data.Generics
import Data.Char (isLower)
import Control.Arrow ((&&&))
import Control.Monad.Maybe

pattern NameT s = Name (OccName s) NameS

rule :: QuasiQuoter
rule = QuasiQuoter{
      quoteExp = \input -> case parseExp input of
           Right b -> dataToExpQ (const Nothing `extQ` updateNameE) b
           Left err -> error $ "Exp: cannot parse rule pattern: " ++ show err ++ " " ++ input
      ,quotePat = \input -> case parseExp input of
           Right (everywhere (mkT updateFixityParens) -> b) -> dsExp b >>= dataToPatQ (const Nothing `extQ` updateNameP `extQ` updatePat)
           Left err -> error $ "cannot parse rule pattern: " ++ show err  ++ " " ++ input
      ,quoteDec = error "cannot be declarations."
      ,quoteType = error "cannot be types."
              }
type RuleE = Exp -> Q (Maybe Exp)
rewriteM :: forall m a. (Data a,Monad m) => (a -> MaybeT m a) -> a -> m a
rewriteM f it = everywhereM (mkM  (\x -> runMaybeT (f x) >>= maybe (return x) (rewriteM f))) it

updateNameP :: DExp -> Maybe (Q Pat)
updateNameP (DVarE n@(Name (OccName [s]) NameS))
    -- | isLower s = Just $ [p| (returnQ . expToTH -> $(varP n)) |] >>= return . AsP (NameT [s,'_'])
    | isLower s = Just $ [p| (expToTH -> $([p| (returnQ -> $(varP n)) |] >>= return . AsP (Name (OccName [s,'_']) NameS))) |]
    | otherwise = Nothing
updateNameP n = Nothing

updatePat :: DPat -> Maybe (Q Pat)
updatePat (DVarPa (NameT s@[t])) = Just $
    [p| (dPatToDExp &&& returnQ -> ( $( [p| (returnQ . expToTH -> $(varP $ NameT $ s ++ "__")) |]
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