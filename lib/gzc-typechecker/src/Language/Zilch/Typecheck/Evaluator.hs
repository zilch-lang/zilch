module Language.Zilch.Typecheck.Evaluator where

import qualified Data.HashMap as Hash
import Data.Located (Located ((:@)), unLoc)
import Data.Maybe (fromJust)
import Language.Zilch.Syntax.Core.AST (Definition (..), Expression (..), Parameter (..))
import Language.Zilch.Typecheck.Core.Eval

-- | Extend the given environment by one entry.
extend :: Environment -> Name -> Value -> Environment
extend env name val = Hash.insert name val env

eval :: Environment -> Expression -> Value
eval _ (EInteger e) = VInteger undefined -- parse Text into Integer
eval env (EIdentifier n) = fromJust $ Hash.lookup (unLoc n) env
eval env (EApplication (e1 :@ _) (e2 :@ _)) = case (eval env e1, eval env e2) of
  (VLam clos, u) -> clos u
  (t, u) -> VApplication t u
eval env (ELet (Let True name ty val :@ _) u) = eval (extend env (unLoc name) (eval env $ unLoc val)) (unLoc u)
eval env (ELet (Let False name ty val :@ _) u) = eval env (unLoc u)
eval env (EPi (Parameter _ name ty1 :@ _) ty2) = VPi (unLoc name) (maybe undefined (eval env . unLoc) ty1) (\u -> eval (extend env (unLoc name) u) $ unLoc ty2)

-- flemme
