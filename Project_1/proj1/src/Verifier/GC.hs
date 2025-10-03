module Verifier.GC (GuardedCommand(..), getZ3String) where

import Language
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State.Lazy

data VarT = IntT | ArrT

data GuardedCommand = Assume Assertion
              | Assert Assertion
              | Havoc Name
              | NonDet GuardedCommand GuardedCommand
              | Compose GuardedCommand GuardedCommand
              deriving (Show)

getZ3String :: Program -> String
getZ3String p = wpToZ3 (wp (compileGC p))

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

subsArr :: ArithExp -> Name -> Name -> ArithExp
subsArr (Num n) _ _ = (Num n)
subsArr (Var varName) _ _ = (Var varName)
subsArr (Read arrName idx) x tmp = 
    if (arrName == x) then (Read tmp (subsArr idx x tmp)) else (Read arrName (subsArr idx x tmp))
subsArr (Add l r) x tmp = Add (subsArr l x tmp) (subsArr r x tmp)
subsArr (Sub l r) x tmp = Sub (subsArr l x tmp) (subsArr r x tmp)
subsArr (Mul l r) x tmp = Mul (subsArr l x tmp) (subsArr r x tmp)
subsArr (Div l r) x tmp = Div (subsArr l x tmp) (subsArr r x tmp)
subsArr (Mod l r) x tmp = Mod (subsArr l x tmp) (subsArr r x tmp)
subsArr (Parens p) x tmp = Parens (subsArr p x tmp)

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
    tmpB <- freshVar "idx"
    tmpC <- freshVar "idx"
    return (Compose (Assume (AForall [tmpB] (ACmp (Eq (Read tmpA (Var tmpB)) (Read a (Var tmpB))))))
        (Compose (Havoc a)
            (Assume (AConj 
                (AForall [tmpC] 
                    (AImpl (ACmp (Neq (Var tmpC) i)) 
                        (ACmp (Eq (Read a (Var tmpC)) (Read tmpA (Var tmpC))))))
                (ACmp (Eq (Read a i)  (subsArr v a tmpA)))))))

compileCommand (If b c1 c2) = do
    c1GC <- (compileBlock c1)
    c2GC <- (compileBlock c2)
    return (NonDet (Compose (Assume (boolToAssertion b)) c1GC)
        (Compose (Assume (ANot (boolToAssertion b))) c2GC))

compileCommand (ParAssign x1 x2 e1 e2) = do
    tmp1 <- freshVar "num" 
    tmp2 <- freshVar "num"
    return (Compose (Assume (ACmp (Eq (Var tmp1) (Var x1))))
        (Compose (Assume (ACmp (Eq (Var tmp2) (Var x2))))
            (Compose (Havoc x1)
                (Compose (Havoc x2)
                    (Compose (Assume (ACmp (Eq (Var x1) (subs (subs e1 x1 tmp1) x2 tmp2))))
                        (Assume (ACmp (Eq (Var x2) (subs (subs e2 x1 tmp1) x2 tmp2)))))))))

compileCommand (While g invs cmds) = do
    whileBodyCmds <- (compileBlock cmds)
    return (Compose (combineAssertions invs)      
        (Compose (havocBlock cmds)                 
            (Compose (combineAssumes invs)
                (NonDet 
                    (Compose (Assume (boolToAssertion g)) 
                        (Compose whileBodyCmds
                            (Compose (combineAssertions invs)
                                (Assume (ACmp (Neq (Num 0) (Num 0)))))))
                    (Assume (boolToAssertion (BNot g)))))))

havocArith :: ArithExp -> GuardedCommand 
havocArith (Num _) = assumeTrue
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
havocAssertionBlock (a:as) = Compose (havocAssert a) (havocAssertionBlock as)

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
havocCommand (While g invs cmds) = Compose (havocBool g) (Compose (havocAssertionBlock invs) (havocBlock cmds))

havocComp :: Comparison -> GuardedCommand
havocComp (Eq a1 a2) = Compose (havocArith a1) (havocArith a2)
havocComp (Neq a1 a2) = Compose (havocArith a1) (havocArith a2)
havocComp (Le a1 a2) = Compose (havocArith a1) (havocArith a2)
havocComp (Ge a1 a2) = Compose (havocArith a1) (havocArith a2)
havocComp (Lt a1 a2) = Compose (havocArith a1) (havocArith a2)
havocComp (Gt a1 a2) = Compose (havocArith a1) (havocArith a2)

havocNameList :: [Name] -> GuardedCommand
havocNameList [] = assumeTrue
havocNameList [c1] = Havoc c1
havocNameList (c:cs) = Compose (Havoc c) (havocNameList cs)

combineAssumes :: [Assertion] -> GuardedCommand
combineAssumes [] = assumeTrue
combineAssumes [a1] = Assume a1
combineAssumes (a:as) = Compose (Assume a) (combineAssumes as) 
    
compileBlock :: Block -> State Int GuardedCommand
compileBlock [] = return assumeTrue
compileBlock [c1] = compileCommand c1
compileBlock (c:cs) = do 
    firstCmd <- compileCommand c
    restCmds <- compileBlock cs
    return (Compose firstCmd restCmds)

combineAssertions :: [Assertion] -> GuardedCommand
combineAssertions [] = assumeTrue
combineAssertions [a1] = Assert a1
combineAssertions (a:as) = Compose (Assert a) (combineAssertions as) 

compileGCM :: Program -> State Int GuardedCommand
compileGCM (_, pre, post, body) = do
    compiledBody <- (compileBlock body)
    return (Compose (combineAssumes pre) (Compose compiledBody (combineAssertions post)))

compileGC :: Program -> GuardedCommand
compileGC program = evalState (compileGCM program) 0

freshVar :: String -> State Int Name
freshVar prefix = do
  n <- get
  put (n + 1)
  return (prefix ++ "--temp--" ++ show n)

wpSubsAssert :: Assertion -> Name -> Name -> Assertion
wpSubsAssert (ACmp comparison) x xa = ACmp (wpSubsComp comparison x xa)
wpSubsAssert (ANot a) x xa = ANot (wpSubsAssert a x xa)
wpSubsAssert (ADisj a1 a2) x xa = ADisj (wpSubsAssert a1 x xa) (wpSubsAssert a2 x xa)
wpSubsAssert (AConj a1 a2) x xa = AConj (wpSubsAssert a1 x xa) (wpSubsAssert a2 x xa)
wpSubsAssert (AImpl a1 a2) x xa = AImpl (wpSubsAssert a1 x xa) (wpSubsAssert a2 x xa)
wpSubsAssert (AForall n a) x xa = AForall (wpSubsNameList n x xa) (wpSubsAssert a x xa)
wpSubsAssert (AExists n a) x xa = AExists (wpSubsNameList n x xa) (wpSubsAssert a x xa)
wpSubsAssert (AParens p) x xa = AParens (wpSubsAssert p x xa)

wpSubsComp :: Comparison -> Name -> Name -> Comparison
wpSubsComp (Eq a1 a2) x xa = Eq (wpSubsArith a1 x xa) (wpSubsArith a2 x xa)
wpSubsComp (Neq a1 a2) x xa = Neq (wpSubsArith a1 x xa) (wpSubsArith a2 x xa)
wpSubsComp (Le a1 a2) x xa = Le (wpSubsArith a1 x xa) (wpSubsArith a2 x xa)
wpSubsComp (Ge a1 a2) x xa = Ge (wpSubsArith a1 x xa) (wpSubsArith a2 x xa)
wpSubsComp (Lt a1 a2) x xa = Lt (wpSubsArith a1 x xa) (wpSubsArith a2 x xa)
wpSubsComp (Gt a1 a2) x xa = Gt (wpSubsArith a1 x xa) (wpSubsArith a2 x xa)

wpSubsArith :: ArithExp -> Name -> Name -> ArithExp
wpSubsArith (Num n) _ _ = (Num n)
wpSubsArith (Var varName) x xa = if (varName == x) then (Var xa) else (Var varName)
wpSubsArith (Add l r) x xa = Add (wpSubsArith l x xa) (wpSubsArith r x xa)
wpSubsArith (Sub l r) x xa = Sub (wpSubsArith l x xa) (wpSubsArith r x xa)
wpSubsArith (Mul l r) x xa = Mul (wpSubsArith l x xa) (wpSubsArith r x xa)
wpSubsArith (Div l r) x xa = Div (wpSubsArith l x xa) (wpSubsArith r x xa)
wpSubsArith (Mod l r) x xa = Mod (wpSubsArith l x xa) (wpSubsArith r x xa)
wpSubsArith (Parens p) x xa = Parens (wpSubsArith p x xa)
wpSubsArith (Read arrName idx) x xa = 
    if (arrName == x) then (Read xa (wpSubsArith idx x xa)) else (Read arrName (wpSubsArith idx x xa))

wpSubsNameList :: [Name] -> Name -> Name -> [Name]
wpSubsNameList [] _ _ = []
wpSubsNameList [c1] x xa = if (c1 == x) then [xa] else [c1]
wpSubsNameList (c:cs) x xa = if (c == x) then (xa : (wpSubsNameList cs x xa)) else (c : (wpSubsNameList cs x xa))

wpM :: GuardedCommand -> Assertion -> State Int Assertion
wpM (Assume assertion) b = return (AImpl assertion b)
wpM (Assert assertion) b = return (AConj assertion b)
wpM (Havoc x) b = do 
    xa <- freshVar (x ++ "a")
    return (wpSubsAssert b x xa)
wpM (Compose c1 c2) b = do 
    r2 <- (wpM c2 b)
    r1 <- (wpM c1 r2)
    return r1
wpM (NonDet c1 c2) b = do
    r1 <- (wpM c1 b)
    r2 <- (wpM c2 b)
    return (AConj r1 r2)

wp :: GuardedCommand -> Assertion
wp gc = evalState (wpM gc (ACmp (Eq (Num 0) (Num 0)))) 0

wpToZ3 :: Assertion -> String
wpToZ3 a = varMapToZ3String (getVar a) ++ "(assert (not " ++ assertToZ3 a ++ "))(check-sat)"

assertToZ3 :: Assertion -> String
assertToZ3 (ACmp comparison) = comparisonToZ3 comparison
assertToZ3 (ANot a) = "(not " ++ assertToZ3 a ++ ")"
assertToZ3 (ADisj a1 a2) = "(or " ++ assertToZ3 a1 ++ " " ++ assertToZ3 a2 ++ ")"
assertToZ3 (AConj a1 a2) = "(and " ++ assertToZ3 a1 ++ " " ++ assertToZ3 a2 ++ ")"
assertToZ3 (AImpl a1 a2) = "(=> " ++ assertToZ3 a1 ++ " " ++ assertToZ3 a2 ++ ")"
assertToZ3 (AForall n a) = "(forall (" ++ forallVarString n ++ ") " ++ assertToZ3 a ++ ")"
assertToZ3 (AExists n a) = "(exists (" ++ forallVarString n ++ ") " ++ assertToZ3 a ++ ")"
assertToZ3 (AParens p) = assertToZ3 p

forallVarString :: [Name] -> String 
forallVarString [] = ""
forallVarString [n] = "(" ++ n ++ " Int)"
forallVarString (n:ns) = "(" ++ n ++ " Int)" ++ forallVarString ns

comparisonToZ3 :: Comparison -> String
comparisonToZ3 (Eq a1 a2) = "(= " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
comparisonToZ3 (Neq a1 a2) = "(not (= " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ "))"
comparisonToZ3 (Le a1 a2) = "(<= " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
comparisonToZ3 (Ge a1 a2) = "(>= " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
comparisonToZ3 (Lt a1 a2) = "(< " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
comparisonToZ3 (Gt a1 a2) = "(> " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"

arithToZ3 :: ArithExp -> String
arithToZ3 (Num n) = show n
arithToZ3 (Var v) = v 
arithToZ3 (Read a i) = "(select " ++ a ++ " " ++ arithToZ3 i ++ ")"
arithToZ3 (Add a1 a2) = "(+ " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
arithToZ3 (Sub a1 a2) = "(- " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
arithToZ3 (Mul a1 a2) = "(* " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
arithToZ3 (Div a1 a2) = "(/ " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
arithToZ3 (Mod a1 a2) = "(mod " ++ arithToZ3 a1 ++ " " ++ arithToZ3 a2 ++ ")"
arithToZ3 (Parens a) = arithToZ3 a

getVar :: Assertion -> Map Name VarT
getVar (ACmp c) = getVarCmp c
getVar (ANot a) = getVar a
getVar (ADisj a1 a2) = Map.union (getVar a1) (getVar a2)
getVar (AConj a1 a2) = Map.union (getVar a1) (getVar a2)
getVar (AImpl a1 a2) = Map.union (getVar a1) (getVar a2)
getVar (AForall n a) = Map.union (getVarNameList n) (getVar a) 
getVar (AExists n a) = Map.union (getVarNameList n) (getVar a)
getVar (AParens a) = getVar a

getVarCmp :: Comparison -> Map Name VarT
getVarCmp (Eq a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarCmp (Neq a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarCmp (Le a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarCmp (Ge a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarCmp (Lt a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarCmp (Gt a1 a2) = Map.union (getVarArith a1) (getVarArith a2)

getVarArith :: ArithExp -> Map Name VarT
getVarArith (Num _) = Map.empty 
getVarArith (Var n) = Map.singleton n IntT
getVarArith (Read n a) = Map.union (Map.singleton n ArrT) (getVarArith a)
getVarArith (Add a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarArith (Sub a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarArith (Mul a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarArith (Div a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarArith (Mod a1 a2) = Map.union (getVarArith a1) (getVarArith a2)
getVarArith (Parens a) = getVarArith a

getVarNameList :: [Name] -> Map Name VarT
getVarNameList [] = Map.empty
getVarNameList [n] = Map.singleton n IntT
getVarNameList (n:ns) = Map.union (Map.singleton n IntT) (getVarNameList ns) 

varTasString :: VarT -> String
varTasString IntT = "Int"
varTasString ArrT = "(Array Int Int)"

varToZ3String :: Name -> VarT -> String
varToZ3String k v = "(declare-const " ++ k ++ " " ++ (varTasString v) ++ ")"

varMapToZ3String :: Map Name VarT -> String
varMapToZ3String m = (Map.foldr (++) "" (Map.mapWithKey varToZ3String m))
