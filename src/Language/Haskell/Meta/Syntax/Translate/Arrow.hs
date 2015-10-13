{-# LANGUAGE TemplateHaskell#-}
module Language.Haskell.Meta.Syntax.Translate.Arrow where

import Data.Char (ord)
import Data.Typeable
import Data.List (foldl', nub, (\\))
import Language.Haskell.TH.Syntax
import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.Parser as Hs
import qualified Language.Haskell.Exts.Build as Hs
import qualified Language.Haskell.Exts.Extension as Hs
import Language.Haskell.Meta.Syntax.Translate
import Language.Haskell.Meta.Utils
import Control.Arrow
import Language.Haskell.TH
import Language.Haskell.TH.Desugar
import Data.List(intersect)
import qualified Data.Set(toList,unions)

{-
proc p ! if e then c1 else c2 =
arr (p ! if e then Left p else Right p)o
(proc p ! c1) jjj (proc p ! c2)


do { rec { ss }; ss' } =
    do { vs <- (| fixA (\ ~vs -> do { ss; returnA -< vs })|); ss' }

do { p <- cmd; ss } = cmd `bind` \ p -> do { ss }
do { cmd; ss } = cmd `bind_` do { ss }
do { let defs; ss } = let defs in do { ss }
do { cmd } = cmd
if exp then cmd1 else cmd2 = (| ifThenElseA cmd1 cmd2 |) exp

-}

toExpA (Hs.Proc _ pat (Hs.LeftArrApp e1 e2))
        | allNamesIn pat `intersect` allNamesIn e1 == [] = InfixE
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
toExpA (Hs.Proc src pat (Hs.Lambda _ p' c)) = toExpA $ Hs.Proc src (Hs.PTuple Hs.Boxed $ pat:p') c
toExpA (Hs.Proc src pat (Hs.Do stmts)) = toExpA $ Hs.Proc src pat (toExpDo stmts)
toExpA a = toExp a

toExpDo [Hs.Qualifier expr] = expr
toExpDo (Hs.Qualifier expr:rest) = Hs.InfixApp expr
        (Hs.QVarOp (Hs.Qual (Hs.ModuleName "Language.Haskell.Meta.Syntax.Translate.Arrow") $ Hs.name "bind_"))
        $ toExpDo rest
toExpDo (Hs.Generator src pat expr:rest) = Hs.Lambda src [pat] $ Hs.InfixApp expr
        (Hs.QVarOp (Hs.Qual (Hs.ModuleName "Language.Haskell.Meta.Syntax.Translate.Arrow") $ Hs.name "bind"))
        $ Hs.Lambda src [pat] $ toExpDo rest
toExpDo (Hs.LetStmt binds:rest) = Hs.Let binds $ toExpDo rest
toExpDo (Hs.RecStmt stmts:rest) = toExpDo $
        Hs.Generator undefined (Hs.pvarTuple vs)
           (Hs.App (Hs.Var $ Hs.Qual (Hs.ModuleName "Language.Haskell.Meta.Syntax.Translate.Arrow") $ Hs.name "fixA")
            (Hs.Lambda undefined [Hs.PIrrPat $ Hs.pvarTuple vs] $ toExpDo (stmts ++ [
             Hs.Qualifier $ Hs.LeftArrApp (Hs.Var $ Hs.Qual (Hs.ModuleName "Control.Arrow") $ (Hs.name "returnA")) (Hs.varTuple vs)
             ])))
             : rest
        where vs = map translateName $
                    Data.Set.toList $ Data.Set.unions $ map extractBoundNamesStmt (map toStmt stmts)
toExpDo _ =error "Invalid syntax, check that last command is a qualifier"

translateName n = Hs.Ident (nameBase n)

ifThenElseA :: ArrowChoice a => a (e,s) r -> a (e,s) r -> a (e,(Bool,s)) r
ifThenElseA thenPart elsePart = arr split >>> thenPart ||| elsePart
  where
    split (e, (True, s)) = Left (e, s)
    split (e, (False, s)) = Right (e, s)

bind :: Arrow a => a (e,s) b -> a (e,(b,s)) c -> a (e,s) c
u `bind` f = arr id &&& u >>> arr (\ ((e,s),b) -> (e,(b,s))) >>> f

bind_ :: Arrow a => a (e,s) b -> a (e,s) c -> a (e,s) c
u `bind_` v = arr id &&& u >>> arr fst >>> v

fixA :: ArrowLoop a => a (e,(b,s)) b -> a (e,s) b
fixA f = loop (arr (\ ((e,s),b) -> (e,(b,s))) >>> f >>> arr (\ b -> (b,b)))





appsE' :: [Exp] -> Exp
appsE' [] = error "appsE []"
appsE' [x] = x
appsE' (x:y:zs) = appsE' ( (AppE x y) : zs )

unwindExp :: Hs.Exp -> [Hs.Exp]
unwindExp = go []
  where go acc (e `Hs.App` e') = go (e':acc) e
        go acc e = e:acc


g :: Hs.ParseResult Hs.Exp
g = parseA "proc x -> id &&& id -< x"

parseA :: String -> Hs.ParseResult Hs.Exp
parseA = Hs.parseWithMode Hs.defaultParseMode{Hs.extensions = [Hs.EnableExtension Hs.Arrows]}
{-
Proc SrcLoc Pat Exp

arrows proc: proc pat -> exp
LeftArrApp Exp Exp

arrow application (from left): exp -< exp
RightArrApp Exp Exp

arrow application (from right): exp >- exp
-}