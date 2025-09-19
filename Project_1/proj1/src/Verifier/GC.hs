module Verifier.GC (GuardedCommand(..)) where

import Language

data GuardedCommand = Assume Assertion
              | Assert Assertion
              | Havoc Name
              | NonDet GuardedCommand GuardedCommand
              | Compose GuardedCommand GuardedCommand
              deriving (Show) 

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

boolToAssn :: BoolExp -> Assertion
boolToAssn (BCmp b) = ACmp b
boolToAssn (BNot b) = ANot (boolToAssn b)
boolToAssn (BDisj b1 b2) = ADisj (boolToAssn b1) (boolToAssn b2)
boolToAssn (BConj b1 b2) = AConj (boolToAssn b1) (boolToAssn b2)
boolToAssn (BParens b) = AParens (boolToAssn b)

compileCommand :: Statement -> GuardedCommand
compileCommand (Assign x e) = 
    Compose (Assume (Eq (Var tmp) (Var x)))
        (Compose (Havoc x))
            (Assume (Eq (Var x) (subs e x tmp)))

compileCommand (If b c1 c2) = 
    NonDet (Compose (Assume (boolToAssn b)) (compileCommand c1))
        (Compose (Assume (ANot (boolToAssn b))) (compileCommand c2))

compileCommand (ParAssign x1 x2 e1 e2) =
    Compose (Assume (Eq (Var tmp1) (Var x1)))
        (Compose (Assume (Eq (Var tmp2) (Var x2)))
            (Compose (Havoc x1)
                (Compose (Havoc x2)
                    (Compose (Assume (Eq (Var x1) (subs (subs e1 x1 tmp1) x2 tmp2)))
                        (Assume (Eq (Var x2) (subs (subs e2 x1 tmp1) x2 tmp2)))))))
    
--TODO: 
-- compileCommand Write
-- compileCommand While
--
--
-- 
    
compileBody :: Block -> GuardedCommand
compileBody [] = Assume (ACmp (Eq (Num 0) (Num 0)))
compileBody [c1] = compileCommand c1
compileBody (c:cs) = Compose (compileCommand c) (compileBody cs)

compilePre :: [Assertion] -> GuardedCommand
compilePre [] = Assume (ACmp (Eq (Num 0) (Num 0)))
compilePre [a1] = Assume a1
comiplePre [a:as] = Compose (Assume a) (compilePre as) 

compilePost :: [Assertion] -> GuardedCommand
compilePost [] = Assume (ACmp (Eq (Num 0) (Num 0)))
compilePost [a1] = Assert a1
compilePost [a:as] = Compose (Assert a) (compilePost as) 

-- collapse :: [Maybe GuardedCommand] -> GuardedCommand
-- collapse [] = Assume (ACmp (Eq (Num 0) (Num 0))) --True
-- collapse [gc] = case gc of
--     Nothing -> 


compileGC :: Program -> GuardedCommand
compileGC (_, pre, post, body) = 
    Compose (compilePre pre) (Compose (compileBody body) (compilePost post))