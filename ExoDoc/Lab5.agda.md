```
-- This work is licensed under a Creative Commons Attribution-NonCommercial-NoDerivs License
-- https://creativecommons.org/licenses/by-nc-nd/4.0/
-- Remi Douence

-- Please do not distribute solutions but let people learn by doing the exercices.
```
# Lab5
## Key Points
- curry-howard isomorphism
- `And`
- `Or`
- `True`
- `False`
- `Neg`
- `Dec` 
- `Exist`
```
{-# OPTIONS --allow-unsolved-metas #-}

module Lab5 where  

open import Lab4 public 
```
## Curry-Howard Isomophism
- property = type = property 
- proof = function = proof 
- logic = program = logic 
## forall = function parameter = forall
- a proof of an universally quantified property is a function
- (Lab2) `==refl : (n : Nat) -> n == n`
- equality is a reflexive relation
- `==refl` is a function that takes `n` as an argument and returns a value of type `n == n` 
## imply = function type = imply
- a proof of an implication is a function 
- (Lab2) `==sym : {n1 n2 : Nat} -> n1 == n2 -> n2 == n1`
- `n1 == n2` implies `n2 == n1`
- `==sym` is a function from `n1 == n2` to `n2 == n1`
### The imply predicate `=>` 
- you already know boolean function in Java/Haskell: `&&`, `||`
```
_=>_ : Bool -> Bool -> Bool 
true  => true  = true 
false => true  = true 
false => false = true 
true  => false = false
```
- from `true` hypothesis I can deduce `true` conclusion
- from `false` hypothesis I can deduce anything
- from `true` hypothesis I **cannot** deduce `false` conclusion
## conjunction = pair = conjunction
- a proof of a conjunction is a pair of proofs
```
data _And_ (A B : Set) : Set where 
  _and_ : A -> B -> A And B 

Between : Nat -> Nat -> Nat -> Set 
Between low n high = (low < n) And (n < high)

b123 : Between 1 2 3
b123 = ?
```
## disjunction = sum (Haskell) / union (C) = disjunction 
- a proof of a disjunction is a single proof (among two)
- either a proof of the left property
- or a proof of the right property
```
data _Or_ (A B : Set) : Set where
  orL : A -> A Or B  
  orR : B -> A Or B  

_<=''_ : Nat -> Nat -> Set 
n1 <='' n2 = (n1 == n2) Or (n1 < n2) 

0<='' : (n : Nat) -> 0 <='' n
0<='' n = ?
```
## True = a type singleton = True
- a proof of `True` is a value `true`
- `True` is a singleton type (only one value)
```
data True : Set where 
  T : True
```
- first equation of `=>` 
```
_ : True -> True
_ = ?
```
## False = an empty type = False
- **there is NO proof of `False`**
- `False` is an empty type (with no value)
```
data False : Set where 
```
- second equation of `=>` 
```
_ : False -> True
_ = ?
```
- third equation of `=>` 
```
_ : False -> False
_ = ?
```
- fourth equation of `=>` 
```
_ : True -> False
_ = ?
```
### negation = function that returns False = negation
- **there is NO proof of `False`**
- `neg A` is function from `A` to `False`
- `neg A` is function that takes a **counter example** `A` and returns `False`
```
neg : Set -> Set
neg A = A -> False

_ : 2 == 2
_ = ?
```
- when there is no well-typed value, use the empty pattern `()`
```
_ : neg (2 == 3)
_ = ?

_ : 2 <= 3 
_ = ?
```
- when there is no well typed value, use the empty pattern `()`
- but only when there is no well-typed value
- here we have to introduce two `case1` in order to make it clear there is no well-typed value
```
_ : neg (3 <=' 2)
_ = ?
```
- when a branch in a function makes no sense (hyoptheses can lead to `False`) you can end it by calling `absurd` with the right argument
```
absurd : {A : Set} -> False -> A
absurd ()
```
### a proof = a term
- Agda is based on intuitionistic (constructive) logic
- intutionistic logic requires to actually build a proof
- excluded middle states `A or neg A` holds
- but we don't know which one (`A` or `neg A`) holds
- so excluded middle cannot be proved in Agda
    ```
   ExcludedMiddle : (A : Set) -> A Or (neg A) 
   ExcludedMiddle A = {!   !}
    ```
- it must be admitted as an axiom
```
postulate ExcludedMiddle : (A : Set) -> A Or (neg A) 
```
- do not try this at home (this is dangerous and can ve quite subtle)
```
postulate Crazy : 1 == 2 
```
### Decidable
- give me two naturals `n1` and `n2`
- I can always automatically (there is an algorithm) prove either `n1 < n2` or prove `neg (n1 < n2)`
- `<` is a decidable property
- decidable = boolean + proof
```
data Dec (A : Set) : Set where
  yes : A -> Dec A 
  no : (neg A) -> Dec A 

_<?_ : (n1 n2 : Nat) -> Dec (n1 < n2)
n1 <? n2 = ?
```
## exist = pair (value , proof) = exist
- in order to prove an exist property holds, give me:
    - a value (witness)
    - a proof this value satisfies the property
### Pair 
- a `Pair` of value is an agreagate of two values
- this is similar to `And`
```
data Pair (A B : Set) : Set where 
  _,_ : A -> B -> Pair A B

fst : {A B : Set} -> Pair A B -> A 
fst (a , _) = a 

snd : {A B : Set} -> Pair A B -> B 
snd (_ , b) = b 

_ : snd (1 , 2) == 2 
_ = case0
```
### Dependent Pair
- a dependent pair is a pair
- but the type of the second element depends on the value of the first element
```
data PairD (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) -> (b : B a) -> PairD A B  

fstD : {A : Set}{B : A -> Set} -> PairD A B -> A 
fstD (a , _) = a 

sndD : {A : Set}{B : A -> Set} -> (p : PairD A B) -> B (fstD p)  
sndD (_ , b) = b

p1 : PairD Nat (\ n -> Odd n)
p1 = ?
```
### exist = dependent pair (witness,proof) = exist
- exist is a dependent pair whose type expose only the type of snd (i.e., the property proved by the second element)
```
data Exist {A : Set} (B : A -> Set) : Set where
  exist : (a : A) -> B a -> Exist B  

witness : {A : Set}{B : A -> Set} -> Exist B -> A 
witness (exist a b) = a 

proof : {A : Set}{B : A -> Set} -> (e : Exist B) -> B (witness e) 
proof (exist a b) = b 

_ : Exist Even
_ = ?

_ : Exist Even 
_ = ?

_<='''_ : Nat -> Nat -> Set
n1 <=''' n2 = Exist (\ delta -> delta + n1 == n2)

<='''-refl : (n : Nat) -> n <=''' n
<='''-refl n = ?
```
## TODO 
### `And` 
```
AndCommut : {A B : Set} -> A And B -> B And A
AndCommut pab = ?

curry : {A B C : Set} -> (A And B -> C) -> (A -> B -> C)
curry f a b = ?

uncurry : {A B C : Set} -> (A -> B -> C) -> (A And B -> C)
uncurry f ab = ?

_<=>_ : Set -> Set -> Set 
a <=> b = (a -> b) And (b -> a)

curryUncurry : {A B C : Set} -> ((A And B) -> C) <=> (A -> B -> C)
curryUncurry = ? 
```
### `Or` 
```
<=''S : {n1 n2 : Nat} -> n1 <='' n2 -> (S n1) <='' (S n2)
<='' p12 = ?

<=<='' : {n1 n2 : Nat} -> n1 <= n2 -> n1 <='' n2
<=<='' p12 = ?

<=''trans : {n1 n2 n3 : Nat} -> n1 <='' n2 -> n2 <='' n3 -> n1 <='' n3
<=''trans p12 p23 = ? 

OrCommut : {A B : Set} -> A Or B -> B Or A
OrCommut ab = ?

_ : {A B : Set} -> (A -> A) Or (B -> B -> B)
_ = ? 

_ : {A B : Set} -> (A -> A) Or (B -> B -> B) 
_ = ? 

_ : {A B : Set} -> (A -> A) Or (A -> B) 
_ = ? 

distrib->Or : {A B C : Set} -> ((A Or B) -> C) -> ((A -> C) Or (B -> C))
distrib->Or f = ?

distrib->Or' : {A B C : Set} -> ((A Or B) -> C) -> ((A -> C) Or (B -> C))
distrib->Or' f = ?
```
### `True` 
```
t2 : True -> True -> True
t2 x y = ?

t3 : (True -> True) -> True 
t3 f = ?

-- t4 is the same property than t3 but a different proof
t4 : (True -> True) -> True
t4 f = ?
```
### `neg` and `Dec` 
```
<irreflexive : (n : Nat) -> neg (n < n)
<irreflexive n = ?

_<=?_ : (n1 n2 : Nat) -> Dec (n1 <= n2)
n1 <=? n2 = ?

_==?_ : (n1 n2 : Nat) -> Dec (n1 == n2)
n1 ==? n2 = ?

Z<='S : (n : Nat) -> Z <=' (S n)
Z<='S n = ?

_<='?_ : (n1 n2 : Nat) -> Dec (n1 <=' n2)
n1 <='? n2 = ?

neg< : {n1 n2 : Nat} -> neg (n1 < n2) -> n2 <= n1
neg< p = ?

neg<=< : {n1 n2 : Nat} -> n1 <= n2 -> neg (n2 == n1) -> n1 < n2
neg<=< le12 neq12 = ?

<connected : {n1 n2 : Nat} -> neg (n1 == n2) -> (n1 < n2) Or (n2 < n1)
<connected neq12 = ?
```
### `Exist` 
```
Z<=''' : (n : Nat) -> Z <=''' n
Z<=''' n = ?

<='''trans : {n1 n2 n3 : Nat} -> n1 <=''' n2 -> n2 <=''' n3 -> n1 <=''' n3
<='''trans p12 p23 = ?

existHalf : (n : Nat) -> Even n -> Exist (\ h -> h + h == n)
existHalf n pn = ?
```
