```
-- This work is licensed under a Creative Commons Attribution-NonCommercial-NoDerivs License
-- https://creativecommons.org/licenses/by-nc-nd/4.0/
-- Remi Douence

-- Please do not distribute solutions but let people learn by doing the exercices.
```
# Lab6
## Key Points
- Agda detects termination
- termination is required
- inline function to ge a big while
- fuel and enough
- tailored inductive type 
```
{-# OPTIONS --allow-unsolved-metas #-}

module Lab6 where  

open import Lab5 public 
```
## Agda Can Check Termination
- Primitive Recursion
- at least one constructor smaller 
- `n` is smaller than `S n`
- most of the definitions we have seen
## Agda Cannot Check Termination
- unsafe pragma `TERMINATING`
```
{-# TERMINATING #-} -- really ? 
nbBits : Nat -> Nat 
nbBits 0 = 1
nbBits 1 = 1
nbBits n = S (nbBits (half n)) 

_ : nbBits 255 == 8
_ = case0

_ : nbBits 256 == 9
_ = case0
```
- termination is not trivial
```
{-# TERMINATING #-} -- really ? 
-- https://en.wikipedia.org/wiki/Collatz_conjecture
syracuse : Nat -> Nat 
syracuse (S Z) = S Z 
syracuse n with even n 
... | true = syracuse (half n) 
... | false = syracuse (S (n + n + n))

_ : syracuse 14 == 1 
_ = case0
```
- termination is undecidable
- termination is mandatory
```
{-# TERMINATING #-} 
loop : {A : Set} -> Nat -> A 
loop n = loop (S n)

_ : 1 == 2
_ = ?
```
- we do not use pragma `TERMINATING`
## Inline `half` in `nbBits`
```
nbBits' : Nat -> Nat -> Nat -> Nat
nbBits' 0 0    (S acc) = acc 
nbBits' 1 0    (S acc) = acc 
nbBits' 0 half (S acc) = nbBits' half Z acc
nbBits' 1 half (S acc) = nbBits' half Z acc
nbBits' (S (S n)) half acc = nbBits' n (S half) acc  
nbBits' _ _ 0 = 1 -- dummy

_-_ : Nat -> Nat -> Nat 
Z      - n2     = Z 
(S n1) - Z      = S n1
(S n1) - (S n2) = n1 - n2 

nbBits2 : Nat -> Nat
nbBits2 n = (S n) - nbBits' n Z (S n)

_ : nbBits2 255 == 8
_ = case0

_ : nbBits2 256 == 9
_ = case0
```
## Introduce `fuel`
- `fuel` is an extra `Nat` argument that decreases at each recursive call
```
nbBits3'' : Nat -> Nat -> Nat 
nbBits3'' n 0 = 1 -- hum, out of gas, should never happens
nbBits3'' 0 f = 1
nbBits3'' 1 f = 1
nbBits3'' (S (S n)) (S f) = S (nbBits3'' (half (S (S n))) f) 
```
- we must prove the initial value of `fuel` is enough (never out of gas)
```
half<= : {n1 n2 : Nat} -> n1 <= n2 -> (half n1) <= n2
half<= p12 = ?

enoughNbBits : {n f : Nat} -> (S n) <= (S f) -> (half (S n)) <= f
enoughNbBits p = ?
```
- invariant: n is always smaller than fuel 
```
nbBits3' : (n : Nat) -> (f : Nat) -> n <= f -> Nat 
nbBits3' n 0 p = 1 -- break p to check this cannot happen
nbBits3' 0 f p = 1
nbBits3' 1 f p = 1
nbBits3' (S n) (S f) p = 
  S (nbBits3' (half (S n)) f (enoughNbBits p)) 

nbBits3 : Nat -> Nat 
nbBits3 n = nbBits3' n n (<=refl n)

_ : nbBits3 255 == 8
_ = case0

_ : nbBits3 256 == 9
_ = case0
```
## Tailored Inductive Type
- `Bin` is a sequence of bits
- `Bin` is structured from right to left (so you read it from left to right but you access the rightmost bit)
```
data Bin : Set where 
  BO : Bin
  BI : Bin
  _O : Bin -> Bin 
  _I : Bin -> Bin 

lengthBin : Bin -> Nat
lengthBin bs = ?
```
- add 1 (and propagate carry)
```
suc : Bin -> Bin
suc bs = ?
```
- there is now a bridge from `Nat` to `Bin`
```
natToBin : Nat -> Bin
natToBin n = ?

nbBits4 : Nat -> Nat 
nbBits4 n = lengthBin (natToBin n)

_ : nbBits4 255 == 8
_ = case0

_ : nbBits4 256 == 9
_ = case0
```
## Euclidian Division
- we assume div n Z = Z and nobody should call this
### Unsafe Version for Reference Only
```
{-# TERMINATING #-} 
div : Nat -> Nat -> Nat 
div n1 Z = Z -- error div by Z
div n1 n2 with n1 <b n2
... | true = Z
... | false = S (div (n1 - n2) n2) 

_ : div 14 3 == 4
_ = case0

_ : div 15 3 == 5
_ = case0
```
### Inline `-` in `divI'`
- first argument `n1` 
- second argument `n2` (this is constant arg does not change)
- third argument `n2` 
- trick: compute `n1 - n2` one `S` at a time 
```
div2' : Nat -> Nat -> Nat -> Nat
div2' n1 n2Original n2 = ?

div2 : Nat -> Nat -> Nat 
div2 n1 n2 = div2' n1 n2 n2 

_ : div2 14 3 == 4
_ = case0

_ : div2 15 3 == 4
_ = case0
```
### `fuel`-based version
- fuel invariant: `n1 <= (S f) -> n1 - n2 <= f`
```
-Z : (n : Nat) -> n - Z == n
-Z n = ?

p43 : {n1 f : Nat} -> n1 <= S f -> (n1 - 1) <= f
p43 p = ?

enoughDiv : (n1 n2 f : Nat) -> n1 <= S f -> (n1 - S n2) <= f
enoughDiv n1 n2 f p = ?

div3' : (n1 n2 f : Nat) -> n1 <= f -> Nat
div3' n1 n2 f p = ?

div3 : (n1 n2 : Nat) -> Nat
div3 n1 Z = Z -- div by Z
div3 n1 (S n2) = div3' n1 n2 n1 (<=refl n1) - 1

_ : div3 14 4 == 4
_ = case0

_ : div3 15 4 == 4
_ = case0
```
### Inductive Type Version
- a pair with `r`emainder and `q`uotient
```
data Div : Nat -> Nat -> Set where 
  case0 : {n m : Nat} -> (r q : Nat) -> n == (S m) * q + r -> Div n (S m)

sucDiv : {n m : Nat} -> Div n m -> Div (S n) m
sucDiv n m dnm = ?

div4' : (n m : Nat) -> Div n (S m)
div4' n m = ?

div4 : (n m : Nat) -> Nat 
div4 n m with div4' n m 
... | case0 r q h = q

_ : div4 14 2 == 4
_ = case0

_ : div4 15 2 == 5
_ = case0
```
