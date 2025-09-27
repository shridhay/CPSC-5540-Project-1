module Verifier.GC (GuardedCommand(..)) where

import Language
import Control.Applicative
import Control.Monad ( join )
import Data.Maybe
import qualified Data.Traversable as T
import Z3.Monad
import Control.Monad.State.Lazy

data GuardedCommand = Assume Assertion
              | Assert Assertion
              | Havoc Name
              | NonDet GuardedCommand GuardedCommand
              | Compose GuardedCommand GuardedCommand

subs :: ArithExp -> Name -> Name -> ArithExp
subs (Num n) _ _ = (Num n)
subs (Var varName) x tmp = if (varName == x) then (Var tmp) else (Var varName)
subs (Read arrName idx) x tmp = Read arrName (subs idx x tmp)
subs (Add l r) x tmp = Add (subs l x tmp) (subs r x tmp)
subs (Sub l r) x tmp = Sub (subs l x tmp) (subs r x tmp)
subs (Mul l r) x tmp = Mul (subs l x tmp) (subs r x tmp)
subs (Div l r) x tmp = Div (subs l x tmp) (subs r x tmp)
subs (Mod l r) x tmp = Mod (subs l x tmp) (subs r x tmp)
subs (Parens p) x tmp = Parens (subs p x tmp)

boolToAssertion :: BoolExp -> Assertion
boolToAssertion (BCmp b) = ACmp b
boolToAssertion (BNot b) = ANot (boolToAssertion b)
boolToAssertion (BDisj b1 b2) = ADisj (boolToAssertion b1) (boolToAssertion b2)
boolToAssertion (BConj b1 b2) = AConj (boolToAssertion b1) (boolToAssertion b2)
boolToAssertion (BParens b) = AParens (boolToAssertion b)

compileCommand :: Statement -> State Int GuardedCommand
compileCommand (Assign x e) = do
    tmp <- freshVar "num"
    return (Compose (Assume (ACmp(Eq (Var tmp) (Var x))))
        (Compose (Havoc x)
            (Assume (ACmp(Eq (Var x) (subs e x tmp))))))

compileCommand (Write a i v) = do
    tmpA <- freshVar "arr"
    return (Compose (Assume (AForall "idx" (ACmp (Eq (Read tmpA (Var "idx")) (Read a (Var "idx"))))))
        (Compose (Havoc a)
            (Assume (AForall "idx" (ACmp (Eq (Read a (Var "idx")) (Read (Write tmpA i v) (Var "idx"))))))))

compileCommand (If b c1 c2) = do
    return (NonDet (Compose (Assume (boolToAssn b)) (compileCommand c1))
        (Compose (Assume (ANot (boolToAssn b))) (compileCommand c2)))

compileCommand (ParAssign x1 x2 e1 e2) = do
    tmp1 <- freshVar "num" 
    tmp2 <- freshVar "num"
    Compose (Assume (ACmp(Eq (Var tmp1) (Var x1))))
        (Compose (Assume (ACmp(Eq (Var tmp2) (Var x2))))
            (Compose (Havoc x1)
                (Compose (Havoc x2)
                    (Compose (Assume (ACmp(Eq (Var x1) (subs (subs e1 x1 tmp1) x2 tmp2))))
                        (Assume (ACmp(Eq (Var x2) (subs (subs e2 x1 tmp1) x2 tmp2))))))))

compileCommand (While g invs cmds) = do
    cleanBody <- havocBody cmds
    Compose (combineAssertions invs)       --- TODO
        (Compose cleanBody                 --- TODO
            (Compose (combineAssumes invs) --- TODO
                (NonDet 
                    (Compose (Assume (ACmp g)) 
                        (Compose (compileBody cmds)
                            (Compose (combineAssertions invs)
                                (Assume (ACmp (Neq (Num 0) (Num 0)))))))
                    (Assume (ACmp (BNot g))))))

compilePre :: [Assertion] -> GuardedCommand
compilePre [] = Assume (ACmp (Eq (Num 0) (Num 0)))
compilePre [a1] = Assume a1
comiplePre (a:as) = Compose (Assume a) (compilePre as) 
    
compileBody :: Block -> State Int GuardedCommand
compileBody [] = return (Assume (ACmp (Eq (Num 0) (Num 0))))
compileBody [c1] = return (compileCommand c1)
compileBody (c:cs) = do 
    firstCmd <- compileCommand c
    restCmds <- compileBody cs
    return (Compose firstCmd restCmds)

compilePost :: [Assertion] -> GuardedCommand
compilePost [] = Assume (ACmp (Eq (Num 0) (Num 0)))
compilePost [a1] = Assert a1
compilePost (a:as) = Compose (Assert a) (compilePost as) 

compileGCM :: Program -> State Int GuardedCommand
compileGCM (_, pre, post, body) = do
    compiledBody <- (compileBody body)
    return Compose (compilePre pre) (Compose compiledBody (compilePost post))

compileGC :: Program -> GuardedCommand
compileGC program = evalState (compileGCM program) 0

{-

--TODO: 
-- compileCommand While
-- Array Implementations









-}

freshVar :: String -> State Int Name
freshVar prefix = do
  n <- get
  put (n + 1)
  return (prefix ++ "--temp--" ++ show n)
