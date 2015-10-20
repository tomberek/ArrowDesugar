{-# LANGUAGE LambdaCase #-}
module Language.Haskell.Meta.Syntax.Translate.Arrow where

import Language.Haskell.TH.Syntax
import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Parser as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.Extension as Hs
import Language.Haskell.Meta.Syntax.Translate
import Control.Arrow
import Language.Haskell.TH.Desugar
import Data.List(intersect)
import qualified Data.Set(toList,unions,member,map)
import Data.Set(Set)
import Data.Generics


-- | Adds arrow notation translation to haskell-src-meta
-- Used the translations provided in http://staff.city.ac.uk/~ross/papers/notation.pdf
toExpA :: Hs.Exp -> Exp
toExpA (Hs.Proc _ pat (Hs.LeftArrApp e1 e2))
        | null $ allNamesIn pat `intersect` allNamesIn e1 = InfixE
                       (Just $ AppE (VarE $ mkName "arr") (LamE [toPat pat] (toExp e2)))
                       (VarE $ mkName ">>>")
                       (Just $ toExp e1)
        | otherwise = InfixE
                (Just $ AppE (VarE $ mkName "arr") (LamE [toPat pat] $ TupE [toExp e1,toExp e2]))
                (VarE $ mkName ">>>")
                (Just $ VarE $ mkName "app")

toExpA (Hs.Proc src pat expr@(Hs.App _ _)) = appsE' $ toExpA op : map (toExpA . Hs.Proc src pat) exprs
    where op:exprs = unwindExp expr

toExpA (Hs.Proc src pat (Hs.InfixApp c1 op c2)) = toExpA (Hs.Proc src pat (Hs.appFun (qop op) [c1,c2]))
    where qop (Hs.QVarOp a) = Hs.Var a
          qop (Hs.QConOp a) = Hs.Con a

toExpA (Hs.Proc _ pat (Hs.Lambda src [p'] c)) = toExpA $ Hs.Proc src (Hs.PTuple Hs.Boxed [pat',p']) c --correction needed for rec
    where pat' =  fixPat pat patNames
          patNames = extractBoundNamesPat $ toPat p'

toExpA (Hs.Proc src pat (Hs.Let d@(Hs.BDecls decls) expr)) = InfixE
                (Just arrLet)
                (VarE $ mkName ">>>")
                (Just $ toExpA $ Hs.Proc src (Hs.PTuple Hs.Boxed [pat',Hs.PTuple Hs.Boxed $ map (Hs.PVar . translateName) vs]) expr)
    where patNames = Data.Set.unions $ map (extractBoundNamesDec . toDec) decls
          vs = Data.Set.toList patNames
          arrLet = AppE (VarE $ mkName "arr") (LamE [toPat pat]
                       $ LetE (hsBindsToDecs d) (TupE [toExp $ promoteE pat,TupE $ map VarE vs]))
          pat' =  fixPat pat patNames

toExpA (Hs.Proc src pat (Hs.Do stmts)) = toExpA $ Hs.Proc src pat (toExpDo stmts)

toExpA (Hs.Proc src pat (Hs.If cond resultT resultF)) = InfixE (Just arrIf)
                (VarE $ mkName ">>>")
                (Just $ InfixE (Just $ toExpA $ Hs.Proc src pat resultT)
                               (VarE $ mkName "|||")
                               (Just $ toExpA $ Hs.Proc src pat resultF))
    where
          arrIf = AppE (VarE $ mkName "arr")
                      $ LamE [toPat pat] $ CondE (toExp cond)
                          (AppE (ConE $ mkName "Left") (toExp $ promoteE pat))
                          (AppE (ConE $ mkName "Right") (toExp $ promoteE pat))
toExpA (Hs.Proc src pat (Hs.Case expr alts)) = InfixE (Just arrCase)
                (VarE $ mkName ">>>")
                (Just choiceE)
    where
          eitherFunc a = go a 0 where
              go [] _ = []
              go (p:ps) 0 = AppE (ConE $ mkName "Left") p : go ps 1
              go [p] x = [iter (AppE (ConE $ mkName "Right")) x p]
              go (p:ps) x = iter (AppE (ConE $ mkName "Right")) x (AppE (ConE $ mkName "Left") p) : go ps (x-1)
          alts' = eitherFunc alts''
          alts'' = map (\(Hs.Alt _ pat2 _ _) -> TupE [toExp $ promoteE pat,toExp $ promoteE pat2]) alts
          altRun = zip alts' alts
          arrCase = AppE (VarE $ mkName "arr") $ LamE [toPat pat] $
              CaseE (toExpA expr) (map (\(expression,Hs.Alt _ pat' _ _) -> Match (toPat pat') (NormalB expression) []) altRun)
          choiceE = foldl1 (\a b -> InfixE
                    (Just a)
                    (VarE $ mkName "|||")
                    (Just b)) alternates
                  where alternates' = map (\(Hs.Alt _ pat2 (Hs.UnGuardedAlt rhs) _) -> (rhs,Hs.PTuple Hs.Boxed [pat,flattenE pat2])) alts
                        alternates = map (\(rhs,pat') -> toExpA $ Hs.Proc src pat' rhs) alternates'
-- Catch-all
toExpA a = toExp a

iter :: (b -> b) -> Int -> b -> b
iter _ 0 b = b
iter f x b = iter f (x-1) (f b)

toMatch' :: Hs.Alt -> Match
toMatch' (Hs.Alt _ p rhs ds) = Match (toPat p) (toBody' rhs) (toDecs ds)

toBody' :: Hs.GuardedAlts -> Body
toBody' (Hs.UnGuardedAlt e) = NormalB $ toExp e
toBody' (Hs.GuardedAlts rhss) = GuardedB $ map toGuard rhss

toGuard' :: Hs.GuardedRhs -> (Guard, Exp)
toGuard' (Hs.GuardedRhs _ stmts e) = (g, toExp e)
  where
    g = case map toStmt stmts of
      [NoBindS x] -> NormalG x
      xs -> PatG xs

fixPat :: Data a => a -> Set Name -> a
fixPat pat pats =  everywhere (id `extT` \a -> case a of
                                      (Hs.PVar b) -> if Data.Set.member b pats' then Hs.PWildCard else a
                                      _ -> a) pat
                                   where pats' = Data.Set.map translateName pats

flattenE :: Hs.Pat -> Hs.Pat
flattenE pat = case listify (const False `extQ` \case
                        Hs.PVar _ -> True
                        _ -> False) pat
                of
                    [a] -> a
                    a -> Hs.PTuple Hs.Boxed a

toExpDo :: [Hs.Stmt] -> Hs.Exp
toExpDo [Hs.Qualifier expr] = expr
toExpDo (Hs.Qualifier expr:rest) = Hs.InfixApp expr
        (Hs.QVarOp (Hs.UnQual $ Hs.name "bind_"))
        $ toExpDo rest
toExpDo (Hs.Generator src pat expr:rest) = Hs.InfixApp expr
        (Hs.QVarOp (Hs.UnQual $ Hs.name "bind"))
        $ Hs.Lambda src [pat] $ toExpDo rest
toExpDo (Hs.LetStmt binds:rest) = Hs.Let binds $ toExpDo rest
toExpDo (Hs.RecStmt stmts : rest) = Hs.InfixApp
           (Hs.App (Hs.Var $ Hs.UnQual $ Hs.name "loop")
            (Hs.Lambda undefSrc [Hs.PIrrPat $ Hs.PTuple Hs.Boxed $ map Hs.PVar vs] $ toExpDo (stmts ++ [
             Hs.Qualifier $ Hs.LeftArrApp (Hs.Var $ Hs.UnQual $ Hs.name "returnA") (Hs.Tuple Hs.Boxed [Hs.varTuple vs,Hs.varTuple vs])])))
           (Hs.QVarOp (Hs.UnQual $ Hs.name "bind"))
           $ Hs.Lambda undefSrc [Hs.pvarTuple vs] $ toExpDo rest
        where vs = map translateName $
                    Data.Set.toList $ Data.Set.unions $ map (extractBoundNamesStmt . toStmt) stmts
              undefSrc = Hs.SrcLoc "RecStatement" 0 0
toExpDo _ =error "Invalid syntax, check that last command is a qualifier"

translateName :: Name -> Hs.Name
translateName n = Hs.Ident (nameBase n)

ifThenElseA :: ArrowChoice a => a (e,s) r -> a (e,s) r -> a (e,(Bool,s)) r
ifThenElseA thenPart elsePart = arr split >>> thenPart ||| elsePart
  where
    split (e, (True, s)) = Left (e, s)
    split (e, (False, s)) = Right (e, s)

{-# INLINE bind #-}
bind :: Arrow a => a b c -> a (b,c) d -> a b d
u `bind` f = arr id &&& u >>> f

{-# INLINE bind_ #-}
bind_ :: Arrow a => a b c -> a b d -> a b d
u `bind_` v = u `bind` (arr fst >>> v)

fixA :: ArrowLoop a => a (e,(b,s)) b -> a (e,s) b
fixA f = loop (arr (\ ((e,s),b) -> (e,(b,s))) >>> f >>> arr (\ b -> (b,b)))

appsE' :: [Exp] -> Exp
appsE' [] = error "appsE []"
appsE' [x] = x
appsE' (x:y:zs) = appsE' ( AppE x y : zs )

unwindExp :: Hs.Exp -> [Hs.Exp]
unwindExp = go []
  where go acc (e `Hs.App` e') = go (e':acc) e
        go acc e = e:acc

promoteE :: Hs.Pat -> Hs.Exp
promoteE (Hs.PApp _ [pat]) = promoteE pat
promoteE (Hs.PApp _ pats) = Hs.Tuple Hs.Boxed $ map promoteE pats
promoteE (Hs.PVar n) = Hs.Var $ Hs.UnQual n
promoteE (Hs.PLit n) = Hs.Lit n
promoteE (Hs.PTuple Hs.Boxed pats) = Hs.Tuple Hs.Boxed $ map promoteE pats
promoteE (Hs.PParen pat) = Hs.Paren $ promoteE pat
promoteE (Hs.PList pats) = Hs.List $ map promoteE pats
promoteE (Hs.PWildCard) = Hs.Tuple Hs.Boxed [] -- Hs.Var $ Hs.Special Hs.UnitCon
promoteE (Hs.PIrrPat pat) = promoteE pat
promoteE x = error $ "pattern promotion not supported for: " ++ show x

parseA :: String -> Hs.ParseResult Hs.Exp
parseA = Hs.parseWithMode Hs.defaultParseMode{Hs.extensions = [Hs.EnableExtension Hs.Arrows]}