```
-- This work is licensed under a Creative Commons Attribution-NonCommercial-NoDerivs License
-- https://creativecommons.org/licenses/by-nc-nd/4.0/
-- Remi Douence

-- Please do not distribute solutions but let people learn by doing the exercices.
```
# Lab4
## Key Points
- name a `with` expression to reference it later 
- subset definition
- intrinsic proof
  - list + length = vector 
  - no out of bound for vector rank 
```
{-# OPTIONS --allow-unsolved-metas #-}

module Lab4 where  

open import Lab3 public 
```
## Name a `with` expression
```
filter-idempotent : {A : Set} -> (f : A -> Bool) -> (l : [ A ]) -> filter f (filter f l) == filter f l 
filter-idempotent f [] = case0
filter-idempotent f (x :: l) with f x in p  
... | false = filter-idempotent f l 
... | true rewrite p | filter-idempotent f l = case0 
```
- `p` remembers `f x` so that it can be used by a rewrite in the last equation
## Subset
### Boolean Predicate
- a predicate is an algorithm
- a predicate is a boolean function
- a predicate is true for a subset of its argument type 
```
even : Nat -> Bool 
even Z = true
even (S (S n)) = even n 
even (S Z) = false
```
### Subset Inductive Type
- a type is a Set of values
- `Nat` is `Z`, `S Z`, `S (S Z)`, etc.
- a subset is an unary relation defined for elements in the subset
- the type `Even Z` is **not** empty so `Z` is even 
- the type `Even (S Z)` is empty, so `Z` is **not** even
- the type `Even (S (S Z))` is **not** empty, so `S (S Z)` is even
- etc.
- a non empty type = an inhabited type 
```
data Even : Nat -> Set where 
  case0 : Even Z 
  case1 : {n : Nat} -> Even n -> Even (S (S n))
```
- `Even n` is non empty only when `even n` is `true`
- note how `case0` in `Even` corresponds to the first equation of `even`
- note how `case1` in `Even` corresponds to the second equation of `even`
- the third equation of `even` returns `false` (i.e., out of the subset); it corresponds to no case in `Even`
### proof: even + even = even ?
```
even+even=even : {n1 n2 : Nat} -> Even n1 -> Even n2 -> Even (n1 + n2)
even+even=even p1 p2 = ?
```
- when we break a value of type `Even (S (S n))` we get a value of type `Even n` (the index is decremented twice)
- the proof jumps from an even natural to another 
- the proof skip/does not consider odd naturals
## Extrinsic versus Intrisic Proof 
### Extrinsic Proof
- until now: function/algorithm/computation definitions, then proofs of its properties
- a function definition = code **without** dependent type  
    ```
    _+_ : Nat -> Nat -> Nat    -- non dependent type 
    Z      + n2 = n2           -- definition
    (S n1) + n2 = S (n1 + n2)  -- definition
    ```
- a proof of property = code **with** dependent type 
    ```
    -- +commut is a property of the algorithm _+_
    +commut' : (n1 n2 : Nat) -> n1 + n2 == n2 + n1               -- dependent type = property
    +commut' Z n2 rewrite +right n2 = case0                      -- proof
    +commut' (S n1) n2 rewrite +S n2 n1 | +commut' n2 n1 = case0 -- proof
    ```
- remember : a dependent type = an arrow `->` type (for function or `data`) where the value of an argument is used in the type of another argument
- for instance, in `<` in the constructor `case1 : {n1 n2 : Nat} -> n1 < n2 -> S n1 < S n2` the values of the first and second (implicit) arguments `n1` and `n2` occurs in the type of the third argument `n1 < n2` and in the result `S n1 < S n2`
- `(x : T1) -> T2` the scope of `x` is `T2`, so the value of an argument can only be used in the type of a later argument
### Intrinsic Proof
- function definition **and** proof of property **at the same time**
- we will see complex example later with `Exist`
- for now, a simple example: `Vector A` = `[A]` + `length`
#### Vector
```
data Vec (A : Set) : Nat -> Set where
  [] : Vec A 0 
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (1 + n)

v1 : Vec Nat 3
v1 = 1 :: 2 :: 3 :: []
```
##### Vector Functions
```
_++V_ : {A : Set}{n1 n2 : Nat} -> Vec A n1 -> Vec A n2 -> Vec A (n1 + n2)
xs ++V ys = ?

_ : v1 ++V v1 == 1 :: 2 :: 3 :: 1 :: 2 :: 3 :: [] 
_ = case0 
```
- type mismatch
    ```
    reverseV : {A : Set}{n : Nat} -> Vec A n -> Vec A n 
    reverseV [] = []
    reverseV (x :: xs) = reverseV xs ++ (x :: []) 
    ```
- `reverseV` does **not** type checks
- the type of `reverseV (x :: xs)` is `Vec A (1 + n)`
- the type of `(reverseV xs) ++ (x :: [])` is `Vec A (n + 1)`
- we have to prove these two types are equivalent
- **interactive definition** of the hole helps us to plug the right type/transform the intended type
```
vec-commut : {A : Set}{n : Nat} -> Vec A (n + 1) -> Vec A (1 + n)
vec-commut xs = ?

reverseV : {A : Set}{n : Nat} -> Vec A n -> Vec A n
reverseV xs = ?

_ : reverseV v1 == 3 :: 2 :: 1 :: []
_ = case0
```
- the last equation of `reverseV` can also be writen with a `rewrite`
- this requires to break (`C-c C-c`) twice the implicit argument `n`
    - the first break makes `n` explicit
    - the second break actually breaks `n` as `S n'` 
```
reverseV' : {A : Set}{n : Nat} -> Vec A n -> Vec A n
reverseV' xs = ?
```
- we can also specialize the `++V (x :: [])` as `snocV`
```
snocV : {A : Set}{n : Nat} -> Vec A n -> A -> Vec A (1 + n)
snocV xs y = ?

_ : snocV v1 4 == 1 :: 2 :: 3 :: 4 :: []
_ = case0 

reverseV'' : {A : Set}{n : Nat} -> Vec A n -> Vec A n
reverseV'' xs = ?

_ : reverseV v1 == 3 :: 2 :: 1 :: [] 
_ = case0 
```
- we can also define an iterative `reverseV'''` with the iterative addition `+I`
- both iteration `reverseV'''` and `+I` have the same recursion scheme
```
reverseV''' : {A : Set}{n1 n2 : Nat} -> Vec A n1 -> Vec A n2 -> Vec A (n1 +I n2)
reverseV''' xs ys = ?

_ : reverseV''' v1 [] == 3 :: 2 :: 1 :: []
_ = case0
```
- we can also jump the successor from on argument to the other
```
reverseV'''' : {A : Set}{n1 n2 : Nat} -> Vec A n1 -> Vec A n2 -> Vec A (n1 + n2)
reverseV'''' xs ys = ?

_ : reverseV'''' v1 [] == 3 :: 2 :: 1 :: []
_ = case0
```
- it would be a very bad idea to define `Vec` as follows because the structure of the "list" and the structure of the index mismatch:
    ```
    data Vec (A : Set) : Nat -> Set where
      [] : Vec A 0 
      _::_ : {n : Nat} -> A -> Vec A n -> Vec A (n + 1)
    ```
- as the length is maintained, it can be made explicit (break it twice) to access it
```
lengthV : {A : Set}{n : Nat} -> Vec A n -> Nat
lengthV xs = ?

_ : lengthV v1 == 3 
_ = case0 
```
- `headV` is now a total function (the type of its argument rules out empty list) 
```
headV : {A : Set}{n : Nat} -> Vec A (1 + n) -> A
headV xs = ?

_ : headV v1 == 1 
_ = case0 
```
- `tailV` is now a total function (the type of its argument rules out empty list) 
```
tailV : {A : Set}{n : Nat} -> Vec A (1 + n) -> Vec A n
tailV xs = ?

_ : tailV v1 == 2 :: 3 :: [] 
_ = case0 
```
- `lastV` is now a total function
```
lastV : {A : Set}{n : Nat} -> Vec A (1 + n)-> A
lastV xs = ?

_ : lastV v1 == 3
_ = case0 
```
- `initV` is now a total function
```
initV : {A : Set}{n : Nat} -> Vec A (1 + n)-> Vec A n
initV xs = ?

_ : initV v1 == 1 :: 2 :: []
_ = case0 
```
- the return type of `ListToVec` depends on the value of its argument `xs` (in particluar of its length)
```
ListToVec : {A : Set} (xs : [ A ]) -> Vec A (length xs)
ListToVec xs = ?

_ : ListToVec (1 :: 2 :: 3 :: []) == 1 :: 2 :: 3 :: []
_ = case0 
```
- the return type of `VecToList` is not dependent because we lose the length in the type `[_]`
```
VecToList : {A : Set}{n : Nat} -> (xs : Vec A n) -> [ A ]
VecToList xs = ?

_ : VecToList (1 :: 2 :: 3 :: []) == 1 :: 2 :: 3 :: []
_ = case0 
```
- the first element of a vector is at rank `Z` 
- the second element of a vector is at rank `S Z` 
- the third element of a vector is at rank `S (S Z)`
- ... 
- the last element of a vector `Vec A (S n)` is at rank `n`
- this can be defined as a `data`
```
data Rank : Nat -> Set where 
  Z : {n : Nat} -> Rank n
  S : {n : Nat} -> Rank n -> Rank (S n)
```
- let us saturate the different types/sets of values 
  - `Z` is in `Rank n` for all `n`
  - `S Z` is in `Rank (S n)` for all `n`
  - `S (S Z)` is in `Rank (S (S n))` for all `n`
  - ...
- in other words:
  - `Rank Z` contains a single value `Z`
  - `Rank (S Z)` contains two values `Z` and `S Z`
  - `Rank (S (S Z))` contains three values `Z`, `S Z` and `S (S Z)`
  - ...
- the function `!!V` is total (compare with `!!` in Lab3)
```
_!!V_ : {A : Set}{n : Nat} -> Vec A (S n) -> Rank n -> A
xs !!V r = ?

_ : v1 !!V (S Z) == 2
_ = case0 
```
- `Rank n` is a different type from `Nat`
- `Z` is overloaded, they are an infinite number of different values noted `Z` (one value is a `Nat`, one value is a `Rank Z`, one value is a `Rank (S Z)`, etc.) 
- `S Z` is overloaded, they are an infinite number of different values noted `S Z` (one value is a `Nat`, one value is a `Rank (S Z)`, one value is a `Rank (S (S Z))`, etc.) 
- but `0` is a `Nat`, `1` is a `Nat`, `2` is a `Nat`, etc.
- so we cannot write `v1 !!V 1`
--MD
### Matrix
- a rectangular matrix is a vector of vectors 
```
Mat : Set -> Nat -> Nat -> Set 
Mat A n1 n2 = Vec (Vec A n1) n2

m1 : Mat Nat 3 2 
m1 = (1 :: 2 :: 3 :: []) :: (4 :: 5 :: 6 :: []) :: []

replicateV : {A : Set} (n : Nat) -> A -> Vec A n
replicateV n x = ?

_ : replicateV 3 2 == 2 :: 2 :: 2 :: []
_ = case0 

applyV : {A B : Set} {n : Nat} -> Vec (A -> B) n -> Vec A n -> Vec B n
applyV fs xs = ?

not : Bool -> Bool
not true = false
not false = true 

odd : Nat -> Bool 
odd n = not (even n)

_ : applyV (even :: odd :: even :: []) v1 == false :: false :: false :: []
_ = case0 

transposeV : {A : Set}{n1 n2 : Nat} -> Mat A n1 n2 -> Mat A n2 n1
transposeV vs = ?

_ : transposeV m1 == (1 :: 4 :: []) :: (2 :: 5 :: []) :: (3 :: 6 :: []) :: []
_ = case0 
```
## `Odd` Subset 
```
data Odd : Nat -> Set where 
  case0 : Odd 1 
  case1 : {n : Nat} -> Odd n -> Odd (S (S n))

odd+odd=even : {n1 n2 : Nat} -> Odd n1 -> Odd n2 -> Even (n1 + n2)
odd+odd=even p1 p2 = ?

twice : Nat -> Nat 
twice Z = Z
twice (S n) = S (S (twice n)) 

half : Nat -> Nat 
half Z = Z
half (S Z) = Z
half (S (S n)) = S (half n)

half-twice : (n : Nat) -> half (twice n) == n
half-twice n = ?

-- false property when n is odd, explore when the proof gets impossible 
twice-half' : (n : Nat) -> twice (half n) == n
twice-half' n = ?

-- true property when is even (an extra hypothesis) 
twice-half : (n : Nat) -> Even n -> twice (half n) == n
twice-half n = ?
```
## An Alternative Definition `<'` 
- propose an alternative definition `data _<'_`
```
data _<'_ : Nat -> Nat -> Set where 
  case0 : {n : Nat} -> n <' (S n) 
  case1 : {n1 n2 : Nat} -> n1 <' n2 -> n1 <' (S n2) 
```
- with `case0` the distance between `n1` and `n2` is 1
- with `case1` the distance between `n1` and `n2` is increased by 1
- examplify it with: `1 <' 2`, `4 <' 5`, `0 <' 5`, `100 <' 1` (this last one should not be possible)
```
_ : 1 <' 2
_ = ?

_ : 4 <' 5
_ = ?

_ : 0 <' 5
_ = ?

_ : 100 <' 0
_ = ?
```
- prove that `<'` is transitive (this may require to define and prove an auxiliary lemma)
```
<'Sn : {n1 n2 : Nat} -> (S n1) <' n2 -> n1 <' n2
<'Sn p = ? 

<'-trans : {n1 n2 n3 : Nat} -> n1 <' n2 -> n2 <' n3 -> n1 <' n3
<'-trans p12 p23 = ?
```
## A few more `Vec` functions 
- define `concatV` (similar to `concat` but for `Vec`)  
- define `zipWithV` (similar to `zipWith` but for `Vec`)
```
_*_ : Nat -> Nat -> Nat 
n1 * Z = Z
n1 * S n2 = n1 + (n1 * n2) 

concatV : {A : Set}{n m : Nat} -> Vec (Vec A n) m -> Vec A (n * m)
concatV vs = ?

zipWithV : {A B C : Set}{n : Nat} -> (A -> B -> C) -> Vec A n -> Vec B n -> Vec C n
zipWithV f xs ys = ?
```
