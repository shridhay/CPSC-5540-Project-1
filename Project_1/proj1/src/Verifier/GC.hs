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

-- does nothing
assumeTrue :: GuardedCommand
assumeTrue = Assume (ACmp (Eq (Num 0) (Num 0)))

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
    return (Compose (Assume (ACmp (Eq (Var tmp) (Var x))))
        (Compose (Havoc x)
            (Assume (ACmp (Eq (Var x) (subs e x tmp))))))

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
    Compose (Assume (ACmp (Eq (Var tmp1) (Var x1))))
        (Compose (Assume (ACmp (Eq (Var tmp2) (Var x2))))
            (Compose (Havoc x1)
                (Compose (Havoc x2)
                    (Compose (Assume (ACmp (Eq (Var x1) (subs (subs e1 x1 tmp1) x2 tmp2))))
                        (Assume (ACmp (Eq (Var x2) (subs (subs e2 x1 tmp1) x2 tmp2))))))))

compileCommand (While g invs cmds) = do
    Compose (combineAssertions invs)      
        (Compose (havocBlock cmds)                 
            (Compose (combineAssumes invs)
                (NonDet 
                    (Compose (Assume (ACmp g)) 
                        (Compose (compileBody cmds)
                            (Compose (combineAssertions invs)
                                (Assume (ACmp (Neq (Num 0) (Num 0)))))))
                    (Assume (ACmp (BNot g))))))

havocArith :: ArithExp -> GuardedCommand 
havocArith (Num n) = assumeTrue
havocArith (Var varName) = Havoc varName
havocArith (Read arrName idx) = Compose (Havoc arrName) (havocArith idx)
havocArith (Add l r) = Compose (havocArith l) (havocArith r)
havocArith (Sub l r) = Compose (havocArith l) (havocArith r)
havocArith (Mul l r) = Compose (havocArith l) (havocArith r)
havocArith (Div l r) = Compose (havocArith l) (havocArith r)
havocArith (Mod l r) = Compose (havocArith l) (havocArith r)
havocArith (Parens p) = havocArith p

havocAssert :: Assertion -> GuardedCommand
havocAssert (ACmp comparison) = havocComp comparison
havocAssert (ANot a) = havocAssert a
havocAssert (ADisj a1 a2) = Compose (havocAssert a1) (havocAssert a2)
havocAssert (AConj a1 a2) = Compose (havocAssert a1) (havocAssert a2)
havocAssert (AImpl a1 a2) = Compose (havocAssert a1) (havocAssert a2)
havocAssert (AForall n a) = Compose (havocNameList n) (havocAssert a)
havocAssert (AExists n a) = Compose (havocNameList n) (havocAssert a)
havocAssert (AParens p) = havocAssert p

havocAssertionBlock :: [Assertion] -> GuardedCommand
havocAssertionBlock [] = assumeTrue
havocAssertionBlock [a1] = havocAssert a1
havocAssertionBlock (a:as) = Compose (havocAssert a) (havocAssertionBlock cs)

havocBool :: BoolExp -> GuardedCommand 
havocBool (BCmp comparison) = havocComp comparison
havocBool (BNot b) = havocBool b
havocBool (BDisj b1 b2) = Compose (havocBool b1) (havocBool b2)
havocBool (BConj b1 b2) = Compose (havocBool b1) (havocBool b2)
havocBool (BParens p) = havocBool p

havocBlock :: Block -> GuardedCommand
havocBlock [] = assumeTrue
havocBlock [c1] = havocCommand c1
havocBlock (c:cs) = Compose (havocCommand c) (havocBlock cs)

havocCommand :: Statement -> GuardedCommand
havocCommand (Assign x e) = Compose (Havoc x) (havocArith e)
havocCommand (Write a i v) = Compose (Havoc a) (Compose (havocArith i) (havocArith v))
havocCommand (If b c1 c2) = Compose (havocBool b) (Compose (havocBlock c1) (havocBlock c2))
havocCommand (ParAssign x1 x2 e1 e2) = 
    Compose (Havoc x1) (Compose (Havoc x2) (Compose (havocArith e1) (havocArith e2)))
havocCommand (While g invs cmds) = Compose (havocAssertionBlock g) (havocBlock cmds)

havocComp :: Comparison -> GuardedCommand
havocComp (Eq a1 a2) = Compose (havocArith a1) (havocArith a2)
havocComp (Neq a1 a2) = Compose (havocArith a1) (havocArith a2)
havocComp (Le a1 a2) = Compose (havocArith a1) (havocArith a2)
havocComp (Lt a1 a2) = Compose (havocArith a1) (havocArith a2)
havocComp (Gt a1 a2) = Compose (havocArith a1) (havocArith a2)

havocNameList :: [Name] -> GuardedCommand
havocNameList [] = assumeTrue
havocNameList [c1] = Havoc c1
havocNameList (c:cs) = Compose (Havoc c) (havocNameList cs)

combineAssumes :: [Assertion] -> GuardedCommand
combineAssumes [] = assumeTrue
combineAssumes [a1] = Assume a1
combineAssumes (a:as) = Compose (Assume a) (compilePre as) 
    
compileBody :: Block -> State Int GuardedCommand
compileBody [] = return assumeTrue
compileBody [c1] = return (compileCommand c1)
compileBody (c:cs) = do 
    firstCmd <- compileCommand c
    restCmds <- compileBody cs
    return (Compose firstCmd restCmds)

combineAssertions :: [Assertion] -> GuardedCommand
combineAssertions [] = assumeTrue
combineAssertions [a1] = Assert a1
combineAssertions (a:as) = Compose (Assert a) (compilePost as) 

compileGCM :: Program -> State Int GuardedCommand
compileGCM (_, pre, post, body) = do
    compiledBody <- (compileBody body)
    return Compose (combineAssumes pre) (Compose compiledBody (combineAssertions post))

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