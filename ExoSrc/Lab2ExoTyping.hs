
-- This work is licensed under a Creative Commons Attribution-NonCommercial-NoDerivs License 
-- https://creativecommons.org/licenses/by-nc-nd/4.0/
-- Remi Douence

-- Please do not distribute solutions but let people learn by doing the exercices.

{-# OPTIONS_GHC -Wno-x-partial #-} 

import Data.Char (ord,chr)
import Data.Maybe (isJust,fromJust)

-- TYPE SYSTEM 

{-
  LAMBDA CALCULUS and INTEGERS

  E ::= i
      | E + E
      | E E 
      | \x -> E
      | x 

  TYPE 
 
  T ::= Int 
      | T -> T
      | a 

  TYPE SYSTEM (when a function meets its argument)
  
  --------------------------------------------Cte
  env |- i :: TInt


  env |- e1 :: TInt         env |- e2 :: TInt
  --------------------------------------------Add
  env |- e1 + e2 :: TInt


  env |- e1 :: t2 -> t0       env |- e2 :: t2
  --------------------------------------------App
  env |- e1 e2 :: t0


  ((x,t1):env) |- e :: t2
  --------------------------------------------Lam 
  env |- \x -> e :: t1 -> t2 


  (x,t1) `elem` env 
  --------------------------------------------Var
  env |- x :: t1 


  TYPE CHECKING (argument annotated with type)

  ((x,t1):env) |- e :: t2
  --------------------------------------------Lam 
  env |- \(x::t1) -> e :: t1 -> t2 
  

  TYPE INFERENCE (invent type variables and constraints ti == tj)

  ((x,t1):env) |- e :: t2
  --------------------------------------------Lam 
  env |- \x -> e :: t1 -> t2           new t1


  env |- e1 :: t1             env |- e2 :: t2
  --------------------------------------------App 
  env |- e1 e2 :: t0   constraint t1 = t2->t0 

-}

-- TYPE 

type Index = Int -- represent type variables a, b, c...

data Type 
  = TInt -- type Int
  | TVar Index -- type variable a, b, c...
  | TArr Type Type -- type function t1 -> t2 
  deriving (Show,Eq) 

showType :: Type -> String
showType TInt = "Int"
showType (TVar n) = [chr (ord 'a' + n)] -- show n 
showType (TArr (TArr t11 t12) t2) = "(" ++ showType (TArr t11 t12) ++ ") -> " ++ showType t2
showType (TArr t1 t2) = showType t1 ++ " -> " ++ showType t2

t0 = TArr (TArr (TVar 2) (TVar 2)) (TArr TInt TInt)

test_showType = showType t0 == "(c -> c) -> Int -> Int"

substType :: (Index,Type) -> Type -> Type 
-- substType (i,t) t2 = in t2 replace VarT i by t
substType (i,t) t2 = undefined

test_substType = 
  substType (2,TVar 0) t0 
  == TArr (TArr (TVar 0) (TVar 0)) (TArr TInt TInt)

type Subst = [(Index,Type)] -- several substitutions

substS :: Subst -> Type -> Type
substS s t = foldr substType t s

-- SIMPLY TYPED LAMBDA CALCULUS

type Var = String

data Exp 
  = Cte Int
  | Add Exp Exp 
  | Lam Var Type Exp -- the argument Var is annotated with its Type
  | Var Var 
  | App Exp Exp 
  deriving (Show,Eq)

showExp :: Exp -> String
showExp (Cte n) = show n
showExp (Add e1 e2) = "(" ++ showExp e1 ++ " + " ++ showExp e2 ++ ")"
showExp (Lam x t e) = "(\\(" ++ x ++ "::" ++ showType t ++ ") -> " ++ showExp e ++ ")" 
showExp (Var x) = x
showExp (App e1 (App e21 e22)) = showExp e1 ++ " (" ++ showExp (App e21 e22) ++ ")"
showExp (App e1 e2) = showExp e1 ++ " " ++ showExp e2

-- TYPE CHECKING

-- typing environment (each argument is associated with a type)

type Env a = [(Var,a)]

get :: Var -> Env a -> a 
get x ((y,a):env) 
  | x == y = a 
  | otherwise = get x env

-- this function force evaluation of its first argument 
ifThen :: Bool -> a -> a 
ifThen True x = x 

check :: Env Type -> Exp -> Type 
--check env e = return the type of e (with the help of argument anotation)
check env (Cte n) = TInt 
check env (Add e1 e2) = 
  let t1 = check env e1 
      t2 = check env e2
  in ifThen (t1 == TInt && t2 == TInt) TInt
check env e = undefined 

-- examples 

e1 = Cte 1 
e2 = Add (Cte 1) (Cte 2)
e3 = Lam "x" (TVar 0) (Var "x") 
e4 = App (Lam "x" TInt (Var "x")) e1
e5 = let apply = Lam "f" (TArr TInt TInt) (Lam "x" TInt (App (Var "f") (Var "x"))) 
     in App (App apply (Lam "x" TInt (Var "x"))) e2

test1_showExp = showExp e1 == "1"
test2_showExp = showExp e2 == "(1 + 2)"
test3_showExp = showExp e3 == "(\\(x::a) -> x)"
test4_showExp = showExp e4 == "(\\(x::Int) -> x) 1"
test5_showExp = showExp e5 == "(\\(f::Int -> Int) -> (\\(x::Int) -> f x)) (\\(x::Int) -> x) (1 + 2)"

t1 = TInt
t2 = TInt
t3 = TArr (TVar 0) (TVar 0)
t4 = TInt
t5 = TInt

test1_check = check [] e1 == t1
test2_check = check [] e2 == t2
test3_check = check [] e3 == t3
test4_check = check [] e4 == t4 
test5_check = check [] e5 == t5

-- TYPE INFERENCE 

-- type unification (equality of two types which contain variables)

invariant_unification :: Type -> Type -> Bool
invariant_unification t1 t2 =
  let Just s = unify t1 t2
  in substS s t1 == substS s t2 

unify :: Type -> Type -> Maybe [(Index,Type)]
--unify t1 t2 = return (when it is possible) a substitution that makes t1 == t2
unify TInt TInt = Just []
unify (TArr t11 t12) (TArr t21 t22) = undefined 
unify (TVar i1) t2 = Just [(i1,t2)]
unify t1 (TVar i2) = Just [(i2,t1)]
unify _ _ = Nothing

test1_unify = 
  unify (TArr (TVar 0) TInt) (TArr TInt (TVar 0)) 
  == Just [(0,TInt)]

test2_unify = 
  unify (TArr (TVar 0) TInt) (TArr (TArr TInt TInt) (TVar 0)) 
  == Nothing

-- (lazy) generator of fresh integers

type Gen = [Index]

g0 :: Gen 
g0 = [0..]

splitG :: Gen -> (Gen,Gen)
splitG (i1:i2:is) = 
  let (is1,is2) = splitG is 
  in (i1:is1,i2:is2)

-- type equality constraint

type Constraint = (Type,Type) -- (t1,t2) means t1 should be equal to t2

-- make constraints

mkConstraints :: Gen -> Env Type -> Exp -> (Type,[Constraint]) 
-- mkConstraints g env e = return the type of e and the corresponding constraints
mkConstraints g env (Cte n) = (TInt,[]) 
mkConstraints g env (Add e1 e2) = 
  let (g1,g2) = splitG g 
      (t1,eq1) = mkConstraints g1 env e1
      (t2,eq2) = mkConstraints g2 env e2
  in (TInt,eq1++[(t1,TInt)]++eq2++[(t2,TInt)]) 
mkConstraints g env e = undefined 

cs1 = (TInt,[])
cs2 = (TInt,[(TInt,TInt),(TInt,TInt)])
cs3 = (TArr (TVar 0) (TVar 0),[])
cs4 = (TVar 0,[(TArr (TVar 1) (TVar 1),TArr TInt (TVar 0))])
cs5 = (TVar 0,[(TVar 3,TArr (TVar 7) (TVar 11))
              ,(TArr (TVar 3) (TArr (TVar 7) (TVar 11)),TArr (TArr (TVar 5) (TVar 5)) (TVar 1))
              ,(TInt,TInt)
              ,(TInt,TInt)
              ,(TVar 1,TArr TInt (TVar 0))])
      
test1_mkConstraints = 
  mkConstraints g0 [] e1 == cs1

test2_mkConstraints = 
  mkConstraints g0 [] e2 == cs2
  
test3_mkConstraints = 
  mkConstraints g0 [] e3 == cs3

test4_mkConstraints = 
  mkConstraints g0 [] e4 == cs4

test5_mkConstraints = 
  mkConstraints g0 [] e5 == cs5

-- constraint solver (aka unify)

solve :: (Type,[Constraint]) -> Type 
solve (t,(t1,t2):cs) = 
  let Just s = unify t1 t2
  in solve (substS s t,[ (substS s t1,substS s t2) | (t1,t2) <- cs ])
solve (t,[]) = t

test1_solve = solve cs1 == t1

test2_solve = solve cs2 == t2

test3_solve = solve cs3 == t3

test4_solve = solve cs4 == t4

test5_solve = solve cs5 == t5

infer :: Exp -> Type
infer = solve . (mkConstraints g0 [])

test1_infer = infer e1 == t1

test2_infer = infer e2 == t2

test3_infer = infer e3 == t3

test4_infer = infer e4 == t4

test5_infer = infer e5 == t5
