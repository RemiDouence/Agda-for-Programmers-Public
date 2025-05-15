```
-- This work is licensed under a Creative Commons Attribution-NonCommercial-NoDerivs License
-- https://creativecommons.org/licenses/by-nc-nd/4.0/
-- Remi Douence
```
# Imperative languages 

## Key Points
- difference functional versus imperative
- trace/small step semantics 
- program refinment
- non termination
- certified optimizations
```

{-# OPTIONS --allow-unsolved-metas #-}

module Lab9 where  
```
## Old stuff from previous labs
```
-- old stuff from previous labs

-- natural numbers

data Nat : Set where 
  Z : Nat 
  S : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat 
Z + n2 = n2
(S n1) + n2 = S (n1 + n2) 

infixl 6 _+_
{-# BUILTIN NATPLUS _+_ #-}

_-_ : Nat -> Nat -> Nat
Z    - n2   = Z
S n1 - Z    = S n1
S n1 - S n2 = n1 - n2

-- lower than

data _<_ : Nat -> Nat -> Set where 
  case0 : {n2 : Nat} -> Z < (S n2) 
  case1 : {n1 n2 : Nat} -> n1 < n2 -> (S n1) < (S n2)

-- equality

data _==_ {A : Set} (n : A) : A -> Set where 
  case0 : n == n

infix 4 _==_
{-# BUILTIN EQUALITY _==_ #-}  

-- == is reflexive
==refl : {A : Set}(n : A) -> n == n
==refl n = case0

-- == is symmetric
==sym : {A : Set}{n1 n2 : A} -> n1 == n2 -> n2 == n1
==sym case0 = case0

-- == is transitive
==trans : {A : Set}{n1 n2 n3 : A} -> n1 == n2 -> n2 == n3 -> n1 == n3
==trans case0 p23 = p23 

-- == is equivalence (refl + trans + sym)

-- == is congruent 
cong : {A B : Set} {x y : A} -> (f : A -> B) -> x == y -> f x == f y
cong f case0 = case0

-- addition and substraction properties

+Z : (n : Nat) -> (n + Z) == n
+Z Z = case0
+Z (S n) = cong S (+Z n)

+assoc : (n1 n2 n3 : Nat) -> (n1 + n2) + n3 == n1 + (n2 + n3)
+assoc Z n2 n3 = case0
+assoc (S n1) n2 n3 = cong S (+assoc n1 n2 n3)

+S : (n1 n2 : Nat) -> n1 + (S n2) == S (n1 + n2)
+S Z n2 = case0
+S (S n1) n2 = cong S (+S n1 n2)

-Z : (n : Nat) -> n - 0 == n
-Z Z = case0
-Z (S n) = case0

n-n : (n : Nat) -> n - n == 0
n-n Z = case0
n-n (S n) = n-n n

-- maybe

data Maybe (A : Set) : Set where
  nothing : Maybe A 
  just : A -> Maybe A 

-- memory (aka vector)

data Memory : Nat -> Set where
  [] : Memory 0 
  _::_ : {n : Nat} -> Nat -> Memory n -> Memory (1 + n)

infixr 5 _::_ 

data Index : Nat -> Set where 
  Z : {n : Nat} -> Index (S n)
  S : {n : Nat} -> Index n -> Index (S n)

get : {n : Nat} -> Memory n -> Index n -> Nat
get (x :: xs) Z = x
get (x :: xs) (S i) = get xs i 

-- logic

data _And_ (A B : Set) : Set where
  _and_ : A -> B -> A And B

-- false, negation, decidable

data False : Set where 

absurd : {A : Set} -> False -> A
absurd ()

neg : Set -> Set
neg A = A -> False

data Dec (A : Set) : Set where
  yes : A -> Dec A
  no : neg A -> Dec A 

```
## New stuff starts here 
```
-- new stuff

-- cast for specifying implicit arguments

cast : (A : Set) -> A -> A
cast t x = x

```
### Expression
```
-- arithmetic expression
-- the index `n` corresponds to the size of the memory (number of different variables)
-- hence variable `Index` cannot be out of bounds

data Exp (n : Nat) : Set where
  Cte : Nat -> Exp n
  Var : Index n -> Exp n
  Add : Exp n -> Exp n -> Exp n
  Sub : Exp n -> Exp n -> Exp n

-- interpreter (purely function: immutable memory)

eval : {n : Nat} -> Memory n -> Exp n -> Nat
eval m c = ?

-- optimization of expressions: statically remove constant 0

isCte0 : {n : Nat} -> (e : Exp n) -> Dec (e == Cte 0)
isCte0 (Cte 0) = yes case0
isCte0 (Cte (S x)) = no \()
isCte0 (Var x) = no \()
isCte0 (Add e e₁) = no \()
isCte0 (Sub e e₁) = no \()

optim1Exp : {n : Nat} -> Exp n -> Exp n
optim1Exp (Cte n) = Cte n
optim1Exp (Var i) = Var i
optim1Exp (Add e1 e2) with isCte0 e1 | isCte0 e2
... | yes p1 | yes p2 = Cte 0
... | yes p1 | no np2 = optim1Exp e2
... | no np1 | yes p2 = optim1Exp e1
... | no np1 | no np2 = Add (optim1Exp e1) (optim1Exp e2)
optim1Exp (Sub e1 e2) with isCte0 e1 | isCte0 e2
... | yes p1 | h2 = Cte 0
... | no np1 | yes p2 = optim1Exp e1
... | no np1 | no np2 = Sub (optim1Exp e1) (optim1Exp e2)

_ : optim1Exp {0} (Add (Cte 0) (Add (Cte 1) (Cte 0))) == Cte 1
_ = case0

-- optim1Exp does not change the semantics

optim1ExpCorrect : {n : Nat} -> (m : Memory n) -> (e : Exp n) -> eval m e == eval m (optim1Exp e)
optim1ExpCorrect m e = ?

-- could optimize more
_ : optim1Exp {0} (Add (Cte 1) (Add (Cte 0) (Cte 0))) == Add (Cte 1) (Cte 0)
_ = case0

optim2Exp : {n : Nat} -> Exp n -> Exp n
optim2Exp (Cte n) = Cte n
optim2Exp (Var i) = Var i
optim2Exp (Add e1 e2) with isCte0 (optim2Exp e1) | isCte0 (optim2Exp e2)
... | yes p1 | yes p2 = Cte 0
... | yes p1 | no p2 = optim2Exp e2
... | no p1 | yes p2 = optim2Exp e1
... | no p1 | no p2 = Add (optim2Exp e1) (optim2Exp e2)
optim2Exp (Sub e1 e2) with isCte0 (optim2Exp e1) | isCte0 (optim2Exp e2)
... | yes p1 | _ = Cte 0
... | no p1 | yes p2 = optim2Exp e1
... | no p1 | no p2 = Sub (optim2Exp e1) (optim2Exp e2)

_ : optim2Exp {0} (Add (Cte 1) (Add (Cte 0) (Cte 0))) == Cte 1
_ = case0

optim2ExpCorrect : {n : Nat} -> (m : Memory n) -> (e : Exp n) -> eval m e == eval m (optim2Exp e)
optim2ExpCorrect m e = ?

-- could optimize even more with a second pass: e - e = Cte 0

_==Nat?_ : (n1 n2 : Nat) -> Dec (n1 == n2)
Z ==Nat? Z = yes case0
Z ==Nat? S n2 = no \()
S n1 ==Nat? Z = no \()
S n1 ==Nat? S n2 with n1 ==Nat? n2
... | yes p = yes (cong S p)
... | no np = no (\{ case0 → np case0})

_==Index?_ : {n : Nat} (n1 n2 : Index n) -> Dec (n1 == n2)
Z ==Index? Z = yes case0
Z ==Index? S n2 = no \()
S n1 ==Index? Z = no \()
S n1 ==Index? S n2 with n1 ==Index? n2
... | yes p = yes (cong S p)
... | no np = no (\{ case0 → np case0})

_==Exp?_ : {n : Nat} -> (e1 e2 : Exp n) -> Dec (e1 == e2)
e1 ==Exp? e2 = ?

optim3Exp : {n : Nat} -> Exp n -> Exp n
optim3Exp (Cte x) = Cte x
optim3Exp (Var x) = Var x
optim3Exp (Add e1 e2) = Add (optim3Exp e1) (optim3Exp e2)
optim3Exp (Sub e1 e2) with e1 ==Exp? e2
... | yes p = Cte 0
... | no np = Sub (optim3Exp e1) (optim3Exp e2)

optim3ExpCorrect : {n : Nat} -> (m : Memory n) -> (e : Exp n) -> eval m e == eval m (optim3Exp e)
optim3ExpCorrect m e = ?

```
### Imperative Language
```
-- imperative command 

data Cmd (n : Nat) : Set where
  Nop : Cmd n
  Put : Index n -> Exp n -> Cmd n
  Seq : Cmd n -> Cmd n -> Cmd n 
  Whl : Exp n -> Cmd n -> Cmd n

-- mutable memory

put : {n : Nat} -> Index n -> Nat -> Memory n -> Memory n
put Z v (x :: xs) = v :: xs
put (S i) v (x :: xs) = x :: put i v xs 

```
#### Interpreter is not possible because of non termination 
```
-- recursive interpreter: result is the mutable memory

run : {n : Nat} -> Cmd n -> Memory n -> Memory n
run c m = ?

-- fuel interpreter: a maximum number of "steps"

-- nb: fuel is not steps, it is more like depth, see Seq
runFuel : {n : Nat} -> Nat -> Cmd n -> Memory n -> Maybe (Memory n)
runFuel Z c m = nothing
runFuel (S f) Nop m = just m 
runFuel (S f) (Put i e) m = just (put i (eval m e) m)
runFuel (S f) (Seq c1 c2) m with runFuel f c1 m
... | nothing = nothing
... | just m1 = runFuel f c2 m1
runFuel (S f) (Whl e c) m with eval m e
... | Z = just m
... | S n with runFuel f c m
... | nothing = nothing
... | just m1 = runFuel f (Whl e c) m1

sumC : Cmd (S (S Z))
sumC = Whl (Var x)
  (Seq (Put y (Add (Var x) (Var y)))
       (Put x (Sub (Var x) (Cte 1))))
  where x = Z
        y = S Z

_ : runFuel 5 sumC (3 :: 0 :: []) == just (0 :: 6 :: [])
_ = case0

_ : runFuel 4 sumC (3 :: 0 :: []) == nothing -- not enough fuel
_ = case0

-- in general the fuel is undecidable

```
#### Axioms about memory for non while programs
```
-- mutable memory properties

getPut : {n v : Nat} -> (m : Memory n) -> (x : Index n) -> get (put x v m) x == v
getPut m x = ?

getPut' : {n v : Nat} -> (m : Memory n) -> (x y : Index n) -> neg (x == y) -> get (put y v m) x == get m x
getPut' m x y h = ?

putPut : {n v1 v2 : Nat} -> (m : Memory n) -> (x : Index n) -> put x v2 (put x v1 m) == put x v2 m
putPut m x = ?

putPut' : {n v1 v2 : Nat} -> (m : Memory n) -> (x1 x2 : Index n) -> neg (x1 == x2) -> put x2 v2 (put x1 v1 m) == put x1 v1 (put x2 v2 m)
putPut' m x1 x2 h = ?

-- prove program semantics 

swapC : {n : Nat} -> Index n -> Index n -> Index n -> Cmd n
swapC x y z = Seq (Put z (Var x)) (Seq (Put x (Var y)) (Put y (Var z)))

-- failed proof: only two different variable (missing hypothesis)

swapCCorrect : {n : Nat} -> (x y z : Index n) -> neg (z == x) And neg (y == z) -> (m1 m2 : Memory n) -> runFuel 3 (swapC x y z) m1 == just m2 -> (get m1 x == get m2 y) And (get m1 y == get m2 x)
swapCCorrect x y z (hxz and hyz) m1 .(put y (eval (put x (eval (put z (eval m1 (Var x)) m1) (Var y)) (put z (eval m1 (Var x)) m1)) (Var z)) (put x (eval (put z (eval m1 (Var x)) m1) (Var y)) (put z (eval m1 (Var x)) m1))) case0
  = ==sym (==trans (getPut (put x (get (put z (get m1 x) m1) y) (put z (get m1 x) m1)) y) (==trans (getPut' (put z (get m1 x) m1) z x hxz) (==trans (getPut m1 z) case0))) and ==sym (==trans (getPut' (put x (get (put z (get m1 x) m1) y) (put z (get m1 x) m1)) x y {!!}) (==trans (getPut (put z (get m1 x) m1) x) (==trans (getPut' m1 y z hyz) case0)))

-- complete proof with three different variables hypothesis

swapCCorrect' : {n : Nat} -> (x y z : Index n) -> neg (z == x) And neg (y == z) -> neg (x == y) -> (m1 m2 : Memory n) -> runFuel 3 (swapC x y z) m1 == just m2 -> (get m1 x == get m2 y) And (get m1 y == get m2 x)
swapCCorrect' x y z h1 h2 m1 m2 h = ?

-- prove program equivalence

```
#### Trace/Small Steps Semantics
```
-- how to prove this optimization is correct?
-- in general the code is not statically known (becase of while dynamic unfolding)
-- so we cannot do the same than for swapC

-- the idea: a type with finite trace (and infinite trace = no trace) 

data MicroTrace : Nat -> Set where
  Stop : MicroTrace 0
  Cont : MicroTrace 0 -> MicroTrace 1
  More : {n m : Nat} -> MicroTrace (S n) -> MicroTrace n

finiteTrace0 : MicroTrace 0
finiteTrace0 = Stop

finiteTrace1 : MicroTrace 1
finiteTrace1 = Cont Stop

infiniteTrace : {n : Nat} -> MicroTrace (S (S n)) -> False
infiniteTrace (More t) = infiniteTrace t

-- trace/small step semantics
-- a data type = a trace of steps (whose types specify the memory mutations)

data Trace {n : Nat} (m : Memory n) : Cmd n -> Memory n -> Set where
  nopTrace : Trace m Nop m
  
  putTrace : {v : Index n} {e : Exp n} {m1 : Memory n}
    -> m1 == put v (eval m e) m
    -> Trace m (Put v e) m1

  seqTrace : {p1 p2 : Cmd n}
    -> {m1 m2 : Memory n}
    -> Trace m  p1          m1
    -> Trace m1 p2          m2
    -> Trace m  (Seq p1 p2) m2

  whZTrace : {e : Exp n} {c : Cmd n}
    -> eval m e == 0
    -> Trace m (Whl e c) m

  whSTrace : {e : Exp n} {p : Cmd n}
    -> neg (eval m e == 0)
    -> {m1 m2 : Memory n}
    -> Trace m  p         m1
    -> Trace m1 (Whl e p) m2
    -> Trace m  (Whl e p) m2

-- simple examples 

c2 : Cmd 1
c2 = Seq (Put Z (Add (Var Z) (Cte 1))) (Put Z (Sub (Var Z) (Cte 1)))

c2Trace : Trace (0 :: []) c2 (0 :: [])
c2Trace = ?

c3 : Cmd 1
c3 = Whl (Var Z) (Put Z (Sub (Var Z) (Cte 1)))

c3Trace : (n : Nat) -> Trace (n :: []) c3 (0 :: [])
c3Trace n = ?

-- loop examples

loop1C : {n : Nat} -> Cmd n
loop1C = Whl (Cte 1) Nop 

-- no trace for non terminating program
loop1CDoesNotTerminate : {n : Nat}{m m1 : Memory n} -> neg (Trace m loop1C m1)
loop1CDoesNotTerminate t = ?

loop2C : Cmd 1
loop2C = Whl (Var Z) (Put Z (Add (Var Z) (Cte 1)))

loop2CDoesNotTerminate : {m0 m1 : Memory 1} -> (0 < get m0 Z) -> neg (Trace m0 loop2C m1)
loop2CDoesNotTerminate h t = ?

loop3C : Cmd 1
loop3C = Seq (Put Z (Cte 1)) loop2C

loop3CDoesNotTerminate : {m0 m1 : Memory 1} -> neg (Trace m0 loop3C m1)
loop3CDoesNotTerminate t = ?
  
```
##### Program Refinement
```
-- program refinement

-- the trace of c2 has the same initial and final memory than c1
infix 10 _==>_
_==>_ : {n : Nat} -> (c1 c2 : Cmd n) -> Set
(c1 ==> c2) = {m m1 : Memory _} -> Trace m c1 m1 -> Trace m c2 m1

c1 : Cmd (S Z)
c1 = Put Z (Cte 1)

c6 : {n : Nat} -> Cmd (S n)
c6 = Seq Nop (Put Z (Cte 1))

c1c6 : c1 ==> c6
c1c6 t = ?

c6c1 : c6 ==> c1
c6c1 t = ?

c0 : {n : Nat} -> Cmd n
c0 = Nop

c7 : {n : Nat} -> Cmd n
c7 = Whl (Cte 1) Nop

--c0c7 : Cmd 0 c0 ==> c7
-- cast of specify the length of the memory
c0c7 : cast (Cmd 0) c0 ==> c7
c0c7 nopTrace = {!!} -- no (finite) trace

noTraceC7 : {n : Nat}{m m1 : Memory n} -> neg (Trace m c7 m1)
noTraceC7 t = ?

c7c0 : cast (Cmd 0) c7 ==> c0
c7c0 (whSTrace x nopTrace t2) = c7c0 t2

-- in fact a looping program is refined by any program

loop==> : {n : Nat} -> (p : Cmd n) -> c7 ==> p
loop==> p t = ?

-- but a program refined by loop has no trace 

refinedByLoop : {n : Nat}{c : Cmd n}{m m1 : Memory n}
  -> c ==> c7 -> neg (Trace m c m1)
refinedByLoop hc t = ?

-- ==> properties 

==>refl : {n : Nat} -> (c : Cmd n) -> c ==> c
==>refl c t = t

==>trans : {n : Nat} -> {c1 c2 c3 : Cmd n}
  -> c1 ==> c2 -> c2 ==> c3 -> c1 ==> c3
==>trans h12 h23 t = h23 (h12 t) 

Seq==> : {n : Nat}{c1 c2 c1' c2' : Cmd n}
  -> c1 ==> c1'
  -> c2 ==> c2'
  -> Seq c1 c2 ==> Seq c1' c2'
Seq==> hc1 hc2 (seqTrace t1 t2) = seqTrace (hc1 t1) (hc2 t2)

NopSeq==> : {n : Nat}{c : Cmd n} -> Seq Nop c ==> c
NopSeq==> (seqTrace nopTrace t) = t

SeqNop==> : {n : Nat}{c : Cmd n} -> Seq c Nop ==> c
SeqNop==> (seqTrace t nopTrace) = t

Whl==> : {n : Nat}{e : Exp n} {c1 c2 : Cmd n}
  -> c1 ==> c2 -> Whl e c1 ==> Whl e c2
Whl==> h12 (whZTrace h)       = whZTrace h
Whl==> h12 (whSTrace h t1 t2) = whSTrace h (h12 t1) (Whl==> h12 t2)

NopWhl==> : {n : Nat}{e : Exp n} -> Whl e Nop ==> Nop
NopWhl==> (whZTrace h)            = nopTrace
NopWhl==> (whSTrace h nopTrace t) = NopWhl==> t

example==> :
  cast (Cmd 1) (Seq (Whl (Var Z) Nop) (Put Z (Cte 1)))
  ==>
  Put Z (Cte 1)
example==> = ?

-- imperative add: prove this program is correct

addC : Cmd (S (S Z))
addC = Whl (Var x)
  (Seq (Put x (Sub (Var x) (Cte 1)))
       (Put y (Add (Cte 1) (Var y))))
  where x = Z
        y = S Z

-- note that: a while step = a recursive call => simple invariant 
-- usually this is more difficult 

-- step: (S n0 , n1) -> (n0 , S n1)
-- invariant: (n0 , n1) -> (0 , n0 + n1)

addCCorrect : (n0 n1 : Nat) -> Trace (n0 :: n1 :: []) addC (0 :: (n0 + n1) :: [])
addCCorrect n0 n1 = ?

-- imperative sum: prove this program is correct 

sum : Nat -> Nat
sum 0 = 0
sum (S n) = sum n + S n

-- step (S n0 , n1) = (n0 , S n0 + n1)
-- invariant (n0 , n1) = (0 , sum n0 + n1)

sumCCorrect : (n0 n1 : Nat) -> Trace (n0 :: n1 :: []) sumC (0 :: sum n0 + n1 :: [])
sumCCorrect n0 n1 = ?


```
#### Program optimization: remove `nop`
```
-- command optimization: remove nop 

-- this function enable to factorize pattern matching (less cases) in optimCmd below
nop? : {n : Nat} -> (c : Cmd n) -> Dec (c == Nop)
nop? Nop = yes case0
nop? (Put i e) = no \()
nop? (Seq c1 c2) = no \()
nop? (Whl e c) = no \()

optimCmd : {n : Nat} -> Cmd n -> Cmd n
optimCmd Nop = Nop
optimCmd (Put i e) = Put i e
optimCmd (Seq c1 c2) with nop? (optimCmd c1) | nop? (optimCmd c2)
... | yes p1 | _ = optimCmd c2
... | no np1 | yes p2 = optimCmd c1
... | no np1 | no np2 = Seq (optimCmd c1) (optimCmd c2) 
optimCmd (Whl e c) with nop? (optimCmd c)
... | yes p = Nop
... | no np = Whl e (optimCmd c) 

-- a single pass is enough 
optimCmdIdempotent : {n : Nat} -> (c : Cmd n) -> optimCmd (optimCmd c) == optimCmd c
optimCmdIdempotent c = ?

-- finally, we prove optimCmd is correct

optimCmdCorrect : {n : Nat} (c : Cmd n) -> c ==> optimCmd c
optimCmdCorrect c = ?

-- but the reverse is not true in general: because optim can introduce termination

loopCmd : Cmd 0
loopCmd = Whl (Cte 1) Nop

example : loopCmd ==> optimCmd loopCmd
example (whSTrace x nopTrace t2) = example t2

counterExample : optimCmd loop1C ==> loopCmd
counterExample t = ?

noInfiniteTrace : {m0 m1 : Memory 0} -> neg (Trace m0 loopCmd m1)
noInfiniteTrace (whSTrace x nopTrace t2) = noInfiniteTrace t2

```
