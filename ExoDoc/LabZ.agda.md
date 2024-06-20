```
-- This work is licensed under a Creative Commons Attribution-NonCommercial-NoDerivs License
-- https://creativecommons.org/licenses/by-nc-nd/4.0/
-- Remi Douence

-- Please do not distribute solutions but let people learn by doing the exercices.
```
# LabZ

## Key Points
- what is a (semi) ring
- are two expression equal?
- transform two expressions to normal forms and compare them   
- Horner normal form 
- correct arithmetic in Horner
- reify an expression as an abstract syntax tree
- the magic trick to generate a proof 
```
module LabZ where 

open import Lab2 public 

```
# Multiplication of naturals
```

_*_ : Nat -> Nat -> Nat
Z * n2 = Z
S n1 * n2 = n2 + (n1 * n2)

infixl 7 _*_
{-# BUILTIN NATTIMES _*_ #-}

```
## Multiplication properties
```

*Z : (n : Nat) -> n * Z == Z
*Z Z = case0
*Z (S n) = *Z n

*distrib+ : (n1 n2 n3 : Nat) -> (n1 + n2) * n3 == n1 * n3 + n2 * n3
*distrib+ Z n2 n3 = case0
*distrib+ (S n1) n2 n3
  rewrite *distrib+ n1 n2 n3
  rewrite +assoc n3  (n1 * n3) (n2 * n3)
  = case0

*assoc : (n1 n2 n3 : Nat) -> (n1 * n2) * n3 == n1 * (n2 * n3)
*assoc Z n2 n3 = case0
*assoc (S n1) n2 n3
  rewrite *distrib+ n2 (n1 * n2) n3
  rewrite *assoc n1 n2 n3
  = case0

*1 : (n : Nat) -> S Z * n == n
*1 Z = case0
*1 (S n) = cong S (*1 n)

*S : (n1 n2 : Nat) -> n1 * S n2 == n1 + n1 * n2
*S Z n2 = case0
*S (S n1) n2
  rewrite *S n1 n2
  rewrite ==sym (+assoc n2 n1 (n1 * n2))
  rewrite +commut n2 n1
  rewrite +assoc n1 n2 (n1 * n2)
  = case0

*commut : (n1 n2 : Nat) -> n1 * n2 == n2 * n1
*commut n1 Z = *Z n1
*commut n1 (S n2)
  rewrite *commut n2 n1
  rewrite *S n1 n2
  = case0

```
# (semi) RING
- something you already know and use
- but we generalize it
- `+ assoc commut e+0=0+e=e` 
- `* assoc commut e*1=1*e=e e*0=0*e=0 *distrib+`
- semi because we do not have `e-e=0`
- objective: decide if two expressions are equivalent
```

```
## A few examples with manual proofs
```

test1Manual : (x : Nat) -> x == x
test1Manual x -- 0 rewrite
  = ?

test2Manual : (x : Nat) -> x + 1 == 1 + x
test2Manual x -- 1 rewrite 
  = ?

test3Manual : (x : Nat) -> x * (x + 1) == x + x * x
test3Manual x -- 4 rewrites
  = ?

test4Manual : (x : Nat) -> 2 + x * (x * (2 * x + 1)) + 1 == x * x + x * x * x * 2 + 3
test4Manual x -- 14 rewrites
  = ?

```
## RING SOLVER
- prove `e1 == e2` by verifiying `normalForm e1 == normalForm e2`
- adapted from the book "certainty by construction" of Sandy Maguire
- specialisation for a single variable
```

```
### Standard (not normal) form
- not normal = several ways to define a given expression
- to manipulate an expression it must be reified
```

data Exp : Set where 
  var  : Exp 
  k    : Nat -> Exp 
  _:+_ : Exp -> Exp -> Exp
  _:*_ : Exp -> Exp -> Exp

infixl 5 _:+_
infixl 6 _:*_

evalExp : Nat -> Exp -> Nat
evalExp x e = ?

_ : evalExp 2 (var :* var :+ k 1) == 5
  = ?

```
### Horner Normal Form
- a unique way to define a given expression
- a minimum number of multiplication `*`
```

data HNF : Set where 
  k : Nat -> HNF 
  _*x+_ : HNF -> Nat -> HNF 

infixr 5 _*x+_

evalHNF : Nat -> HNF -> Nat
evalHNF x h = ?

_ : evalHNF 2 ((k 1 *x+ 0) *x+ 1) == 5
  = ?

```
#### The addition of two Horners is an Horner
```

_+H_ : HNF -> HNF -> HNF
k c1 +H k c2 = k (c1 + c2)
k c1 +H (h2 *x+ c2) = h2 *x+ (c1 + c2)
(h1 *x+ c1) +H k c2 = h1 *x+ (c1 + c2)
(h1 *x+ c1) +H (h2 *x+ c2) = (h1 +H h2) *x+ (c1 + c2)

infixr 5 _+H_

```
#### The multiplication of two Horners is an Horner
```

_*H_ : HNF -> HNF -> HNF
k c1 *H k c2 = k (c1 * c2)
k c1 *H (h2 *x+ c2) = (k c1 *H h2) *x+ (c1 * c2)
(h1 *x+ c1) *H k c2 = (h1 *H k c2) *x+ (c1 * c2)
(h1 *x+ c1) *H (h2 *x+ c2) = (((h1 *H h2) *x+ 0) *x+ 0) +H (((h1 *H k c2) +H (h2 *H k c1)) *x+ 0) +H k (c1 * c2)

infixr 6 _*H_

```
#### The addition of Horners is correct
- the solver algorithm is hidden here
```

+Hcorrect : (h1 h2 : HNF) -> (n : Nat) -> evalHNF n (h1 +H h2) == evalHNF n h1 + evalHNF n h2
+Hcorrect h1 h2 n = ? -- 13 rewrites 

```
#### The multiplication of Horners is correct
- the solver algorithm is hidden here
```

*Hcorrect : (h1 h2 : HNF) -> (n : Nat) -> evalHNF n (h1 *H h2) == evalHNF n h1 * evalHNF n h2
*Hcorrect h1 h2 n = ? -- 43 rewrites (and change (cong))

```
### standard form to normal form
- conversion to normal form
```

ExpToHNF : Exp -> HNF
ExpToHNF e = ?

_ : ExpToHNF (var :* var :+ k 1) == ((k 1 *x+ 0) *x+ 1)
  = ?

```
### conversion is correct
- the value of an expression is maintained
```

ExpToHNFcorrect : (x : Nat) -> (e : Exp) -> evalExp x e == evalHNF x (ExpToHNF e)
ExpToHNFcorrect x e = ?

```
### Solve
- if normal forms are equal, then their evaluation/they are equal
- observe the return type: it is the proof we want
```

solve : (e1 e2 : Exp) -> ExpToHNF e1 == ExpToHNF e2 -> (x : Nat) -> evalExp x e1 == evalExp x e2
solve e1 e2 h x = ?

```
### Let us revisit the examples
- replace manual proofs by automatized proofs
```

test1Solve : (x : Nat) -> x == x
test1Solve = solve var var ?

test2Solve : (x : Nat) -> x + 1 == 1 + x 
test2Solve = solve (var :+ (k 1)) ((k 1) :+ var) ?

test3Solve : (x : Nat) -> x * (x + 1) == x + x * x
test3Solve = solve (var :* (var :+ (k 1))) (var :+ (var :* var)) ?

test4Solve : (x : Nat) -> 2 + x * (x * (2 * x + 1)) + 1 == x * x + x * x * x * 2 + 3
test4Solve = solve ((k 2) :+ var :* (var :* ((k 2) :* var :+ (k 1))) :+ (k 1)) (var :* var :+ var :* var :* var :* (k 2) :+ (k 3)) ?
```
