{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell#-}
{-# LANGUAGE PatternSynonyms #-}
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

pattern P pat  <- (returnQ . toPat -> pat)
pattern E expr <- (returnQ . toExp -> expr)

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
        Hs.Generator undefined pB
           (Hs.App (Hs.Var $ Hs.Qual (Hs.ModuleName "Language.Haskell.Meta.Syntax.Translate.Arrow") $ Hs.name "fixA")
            (Hs.Lambda undefined [Hs.PIrrPat pB] $ toExpDo (ss ++ [Hs.

           )
        : rest
        where pB = undefined

toExpDo _ =error "Invalid syntax, check that last command is a qualifier"

bind :: Arrow a => a (e,s) b -> a (e,(b,s)) c -> a (e,s) c
u `bind` f = arr id &&& u >>> arr (\ ((e,s),b) -> (e,(b,s))) >>> f

bind_ :: Arrow a => a (e,s) b -> a (e,s) c -> a (e,s) c
u `bind_` v = arr id &&& u >>> arr fst >>> v
{-
do { rec { ss }; ss' } =
    do { vs <- (| fixA (\ ~vs -> do { ss; returnA -< vs })|); ss' }

do { p <- cmd; ss } = cmd `bind` \ p -> do { ss }
do { cmd; ss } = cmd `bind_` do { ss }
do { let defs; ss } = let defs in do { ss }
do { cmd } = cmd
if exp then cmd1 else cmd2 = (| ifThenElseA cmd1 cmd2 |) exp

fixA :: ArrowLoop a => a (e,(b,s)) b -> a (e,s) b
fixA f = loop (arr (\ ((e,s),b) -> (e,(b,s))) >>> f >>> arr (\ b -> (b,b)))

ifThenElseA :: ArrowChoice a => a (e,s) r -> a (e,s) r -> a (e,(Bool,s)) r
ifThenElseA thenPart elsePart = arr split >>> thenPart ||| elsePart
  where
    split (e, (True, s)) = Left (e, s)
    split (e, (False, s)) = Right (e, s)
-}




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