```
-- This work is licensed under a Creative Commons Attribution-NonCommercial-NoDerivs License
-- https://creativecommons.org/licenses/by-nc-nd/4.0/
-- Remi Douence

-- Please do not distribute solutions but let people learn by doing the exercices.
```
# Lab2

## Key Points
- `<` type 
- `<=` types 
- `==` type
- `rewrite` 
- mixfix notation

```
{-# OPTIONS --allow-unsolved-metas #-}

module Lab2 where  
```
## Import Module
- we import definitions of the first module (`Bool`, `Nat`, ...)
```
open import Lab1 public
```
- the keyword `public` means that when the module `m2` is imported, the definitions of `m1` will also be visible
## Builtin
- we have defined `Nat` as a sequence of `S` ending with one `Z`
- we can link this definition with a primitive type
    - this enables efficient computation (e.g., addition) in the Agda typechecker
    - this enables simple literal notation: `0`, `1`, `2`, `42`...
- we can do the same for booleans 
```
-- optimization: binding to primitive types

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN BOOL Bool  #-}
{-# BUILTIN FALSE false #-}
{-# BUILTIN TRUE true  #-}
```
## Mixfix notation
- functions can be prefix, for instance we can write `add 10 20`
- functions can also be infix or suffix with the mixfix notation
- when a function is defined, underscore `_` in its identifier are placeholders for arguments
- for instance, an infix addition can be defined as
```
-- mixfix syntax : arguments denoted by "_" 

_+_ : Nat -> Nat -> Nat 
Z + n2 = n2
(S n1) + n2 = S (n1 + n2) 
```
- the conditional can be defined as
```
if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true then a1 else a2 = a1
if false then a1 else a2 = a2 
```
### Infix Declaration
- binary infix functions can be declared left associative with the `infixl`
- when you read/write `1 + 1 + 1`, you read/write `(1 + 1) + 1`
- `infixl` is followed by the priority of the function (multiplication's priority should be higher than addition's priority)
- we also link this definition to the primitive efficient addition used the Agda typechecker
```
infixl 6 _+_
{-# BUILTIN NATPLUS _+_ #-}

three' : Nat 
three' = 1 + 1 + 1 

three'' : Nat 
three'' = (1 + 1) + 1 
```
## Natural Order `n1 < n2`
### Boolean Predicate 
- the predicate "lower than" can be defined as:
```
-- lower 

_<b_ : Nat -> Nat -> Bool 
Z <b Z = false
Z <b (S n2) = true
S n1 <b Z = false
S n1 <b S n2 = n1 <b n2
```
### Inductive Type `n1 < n2`
- the corresponding type is: 
```
data _<_ : Nat -> Nat -> Set where 
  case0 : {n2 : Nat} -> Z < (S n2) 
  case1 : {n1 n2 : Nat} -> n1 < n2 -> (S n1) < (S n2)
```
- with `case0` the distance between `n1` and `n2` is arbitrary (but a least 1)
- with `case1` the distance between `n1` and `n2` is maintained (both are shifted by 1)
```
test7 : 2 < 42
test7 = case1 (case1 case0)

test7' : 3 < 42
test7' = case1 (case1 (case1 case0))

test7'' : 4 < 3
test7'' = case1 (case1 (case1 {!!}))

-- Q) n1 < n2, how many case1? 
-- A) n1 (at most)
```

#### Lower is transitive
```
<trans : {n1 n2 n3 : Nat} -> n1 < n2 -> n2 < n3 -> n1 < n3
<trans p12 p23 = ?
```
## Natural Order `n1 <= n2`
### Boolean Predicate 
- the predicate "lower or equal" can be defined as:
```
-- lower or equal 

_<=b_ : Nat -> Nat -> Bool 
Z <=b n2 = true
S n1 <=b Z = false
S n1 <=b S n2 = n1 <=b n2 
```
### Inductive Type `n1 <= n2`
- the corresponding type is: 
```
data _<=_ : Nat -> Nat -> Set where 
  case0 : {n2 : Nat} -> Z <= n2 
  case1 : {n1 n2 : Nat} -> n1 <= n2 -> (S n1) <= (S n2)
```
- with `case0` the distance between `n1` and `n2` is arbitrary 
- with `case1` the distance between `n1` and `n2` is maintained (both are shifted by 1)
```
test8 : 2 <= 42
test8 = case1 (case1 case0)

test8' : 3 <= 42
test8' = case1 (case1 (case1 case0))

test8'' : 4 <= 3
test8'' = case1 (case1 (case1 {!!}))

-- Q) n1 <= n2, how many case1? 
-- A) n1 (at most)
```
### Another Inductive Type `n1 <=' n2`
```
data _<='_ : Nat -> Nat -> Set where 
  case0 : {n : Nat} -> n <=' n 
  case1 : {n1 n2 : Nat} -> n1 <=' n2 -> n1 <=' (S n2)
```
- with `case0` the distance between `n1` and `n2` is 0 
- with `case1` the distance between `n1` and `n2` is increased by 1
```
test9 : 40 <=' 42
test9 = case1 (case1 case0)

test9' : 41 <=' 42
test9' = case1 case0

test9'' : 42 <=' 3
test9'' = case1 (case1 (case1 {!!}))

-- Q) n1 <=' n2, how many case1? 
-- A) n2 - n1 (at most)
```
- `case0` corresponds to `n1` equals `n2`
- **`case0` corresponds to `n1` equals `n2`** !
## Another definition of equal
### Boolean predicate 
```
-- another syntax for equal

_==b_ : Nat -> Nat -> Bool 
Z ==b Z = true
Z ==b (S n2) = false
(S n1) ==b Z = false
(S n1) ==b (S n2) = n1 ==b n2 

infix 4 _==b_
{-# BUILTIN NATEQUALS _==b_ #-}

testA : Bool 
testA = (40 + 2) ==b 42
```
### Inductive Type 
#### Version 1: Indexed Type
- rely on the unification of the type checker
```
data _=='_ : Nat -> Nat -> Set where 
  case0 : {n : Nat} -> n ==' n   

-- Q) n1 ==' n2, how many case0? 
-- A) 1

_ : (40 + 2) ==' 42
_ = case0
```
#### Version 2: Generic Indices (Polymorhpism)
```
data _==''_ : {A : Set} -> A -> A -> Set where 
  case0 : {A : Set}{n : A} -> n =='' n   

_ : (40 + 2) =='' 42
_ = case0
```
#### Version 3: Parameter
- a parameter does not change in the full `data` definition (`n` everywhere)
```
data _==_ {A : Set} (n : A) : A -> Set where 
  case0 : n == n
```
- a test is simply a proof of equality
- there is no need to name the tests (`_`is enough)
```
_ : 0 == 0  
_ = case0

_ : 1 == 1   
_ = case0

_ : 2 == (1 + 1)  
_ = case0

_ : 2 == 1
_ = {!   !}

-- Q) how many types? 
-- A) infinity

-- Q) how many values?
-- A) at most one per type, 
--    but an infinity (one of each non empty type)

infix 4 _==_
{-# BUILTIN EQUALITY _==_ #-} -- required for rewrite 
``` 
##### Properties of `==`
```
-- == is reflexive
==refl : {A : Set}(n : A) -> n == n
==refl n = ?

-- == is symmetric
==sym : {A : Set}{n1 n2 : A} -> n1 == n2 -> n2 == n1
==sym p12 = ?

-- == is transitive
==trans : {A : Set}{n1 n2 n3 : A} -> n1 == n2 -> n2 == n3 -> n1 == n3
==trans p12 p23 = ?

-- == is equivalence (refl + trans + sym)

-- == is congruent 
cong : {A B : Set} {x y : A} -> (f : A -> B) -> x == y -> f x == f y
cong f pxy = ?
```
- use `==sym` when the goal or a rule is not in the "right" side
- use `==trans` when the goal requires a sequence of transformations (each `==trans` introduce an intermediate step)
- use `cong` when both the roots of terms (left hand side and right hand side of `==`) are identical and you must transform subterms. For instance `cong S` is quite common to "go below S"
- or simply use `rewrite` with an term of type `T1 == T2`, this replaces `T1` by `T2` everywhere in the goal (no `cong` required)
## Properties of `+`
```
-- (cong proof) Z neutral right for + 
+Z : (n : Nat) -> (n + Z) == n
+Z n = ?

-- (rewrite proof) Z neutral right for + 
+Z' : (n : Nat) -> (n + Z) == n
+Z' n = ?

-- (cong proof) + is associative 
+assoc : (n1 n2 n3 : Nat) -> (n1 + n2) + n3 == n1 + (n2 + n3)
+assoc n1 n2 n3 = ?

-- (rewrite proof) + is associative
+assoc' : (n1 n2 n3 : Nat) -> (n1 + n2) + n3 == n1 + (n2 + n3)
+assoc' n1 n2 n3 = ?

-- (cong proof) S jumps
+S : (n1 n2 : Nat) -> n1 + (S n2) == S (n1 + n2)
+S n1 n2 = ?

-- (rewrite proof) S jumps 
+S' : (n1 n2 : Nat) -> n1 + (S n2) == S (n1 + n2)
+S' n1 n2 = ?

-- (cong proof) + is commutative
+commut : (n1 n2 : Nat) -> n1 + n2 == n2 + n1
+commut n1 n2 = ?

-- (rewrite proof) + is commutative 
+commut' : (n1 n2 : Nat) -> n1 + n2 == n2 + n1
+commut n1 n2 = ?
``` 
## Properties of `+I`
```

-- properties of +I (proofs with rewrite)

_+I_ : Nat -> Nat -> Nat 
Z +I n2 = n2
(S n1) +I n2 = n1 +I (S n2) 

+IS : (n1 n2 : Nat) -> n1 +I (S n2) == S (n1 +I n2)
+IS n1 n2 = ?

+IZ : (n : Nat) -> n +I Z == n
+IZ n = ?

+Icommut : (n1 n2 : Nat) -> n1 +I n2 == n2 +I n1
+Icommut n1 n2 = ?

n1==n2+I : (n1 n2 n3 : Nat) -> n1 == n2 -> n1 +I n3 == n2 +I n3
n1==n2+I n1 n2 n3 p12 = ?

+Iassoc : (n1 n2 n3 : Nat) -> (n1 +I n2) +I n3 == n1 +I (n2 +I n3)
+Iassoc n1 n2 n3 = ?

-- equivalence of + and +I 
+I+ : (n1 n2 : Nat) -> n1 +I n2 == n1 + n2
+I+ n1 n2 = ?

-- + is a pivot (use +commut)
+Icommut' : (n1 n2 : Nat) -> n1 +I n2 == n2 +I n1
+Icommut' n1 n2 = ?

-- properties of <= (refl + trans + antisym = partial order)

<=refl : (n : Nat) -> n <= n
<=refl n = ?

<=trans : {n1 n2 n3 : Nat} -> n1 <= n2 -> n2 <= n3 -> n1 <= n3
<=trans p12 p23 = ?

<=antisym : {n1 n2 : Nat} -> n1 <= n2 -> n2 <= n1 -> n1 == n2
<=antisym p12 p21 = ?

<=SS : {n1 n2 : Nat} -> n1 <= n2 -> (S n1) <= (S n2)
<=SS p12 = ?

SS<= : {n1 n2 : Nat} -> (S n1) <= (S n2) -> n1 <= n2
SS<= p12 = ?

<=nS : {n1 n2 : Nat} -> n1 <= n2 -> n1 <= (S n2)
<=nS p12 = ?

Sn<= : {n1 n2 : Nat} -> (S n1) <= n2 -> n1 <= n2
Sn<= p12 = ?

-- properties of <=' (refl + trans + antisym = partial order)

<='refl : (n : Nat) -> n <=' n
<='refl n = ?

<='trans : {n1 n2 n3 : Nat} -> n1 <=' n2 -> n2 <=' n3 -> n1 <=' n3
<='trans p12 p23 = ?

Z<=' : (n : Nat) -> Z <=' n
Z<=' n = ?

<='SS : {n1 n2 : Nat} -> n1 <=' n2 -> (S n1) <=' (S n2)
<='SS p12 = ?

Sn<=' : {n1 n2 : Nat} -> (S n1) <=' n2 -> n1 <=' n2
Sn<=' p12 = ?

SS<=' : {n1 n2 : Nat} -> (S n1) <=' (S n2) -> n1 <=' n2
SS<=' p12 = ?

<='antisym : {n1 n2 : Nat} -> n1 <=' n2 -> n2 <=' n1 -> n1 == n2
<='antisym p12 p21 = ?

-- equivalence of <= with <='

<=<=' : {n1 n2 : Nat} -> n1 <= n2 -> n1 <=' n2
<=<=' p12 = ?

<='<= : {n1 n2 : Nat} -> n1 <=' n2 -> n1 <= n2
<='<= p12 = ?

-- prove addR Z n = n, addR assoc, addR commut, add = addR 

_+R_ : Nat -> Nat -> Nat 
n1 +R Z = n1
n1 +R (S n2) = S (n1 +R n2) 

Z+R : (n : Nat) -> Z +R n == n
Z+R n = ?

+Rassoc : (n1 n2 n3 : Nat) -> (n1 +R n2) +R n3 == n1 +R (n2 +R n3)
+Rassoc n1 n2 n3 = ?

+RS : (n1 n2 : Nat) -> (S n1) +R n2 == S (n1 +R n2)
+RS n1 n2 = ?

+Rcommut : (n1 n2 : Nat) -> n1 +R n2 == n2 +R n1
+Rcommut n1 n2 = ?

++R : (n1 n2 : Nat) -> n1 + n2 == n1 +R n2
++R n1 n2 = ?
```
