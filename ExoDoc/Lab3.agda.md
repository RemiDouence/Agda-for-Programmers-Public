```
-- This work is licensed under a Creative Commons Attribution-NonCommercial-NoDerivs License
-- https://creativecommons.org/licenses/by-nc-nd/4.0/
-- Remi Douence

-- Please do not distribute solutions but let people learn by doing the exercices.
```
# Lab3
## Key Points
- anonymous function: `\ arg -> return` 
- list: `[_]`
- match on extra computation:
    f : type
    f args = exp

    f : type 
    f args with exp
    f args | pat1 = exp
    f args | pat2 = exp

    f : type 
    f args with exp
    ... | pat1 = exp
    ... | pat2 = exp
- partial function wannabe total: `Maybe`
```
{-# OPTIONS --allow-unsolved-metas #-}

module Lab3 where  

open import Lab2 public 
```
## Anonymous Functions (Lambda)
- it is sometimes quite convenient to define a disposable (anonymous) function
- remember anonymous classes in AWT Java
- when no pattern is involved, simply write:
```
-- \ args -> return
 
-- identity
_ : (\x -> x) (2 + 3) == 5
_ = case0

-- apply twice
_ : (\f x -> f (f x)) S Z == S (S Z)
_ = case0
```
- when pattern matching is involved, write:
```
-- \ { pat-1 -> return-1 ; pat-2 -> return-2 ; pat-3 -> return-3 } 

-- boolean or 
_ : (\ { true _ -> true ; false b2 -> b2 }) false false == false
_ = case0

-- predecessor
_ : (\ { Z -> Z ; (S n) -> n }) 3 == 2
_ = case0
```
Agda displays messages about `Sort` (we can ignore them)
## Inductive Principle for `Nat` 
- the inductive principle is a function that computes a propery for any natural `i`
- its argumenys are: 
    - the property to be computed 
    - the property for `Z`
    - a function that perform one computation step
    - a natural `i`
```
ind-nat : (P : Nat -> Set) -> 
          P Z -> 
          ((n : Nat) -> P n -> P (S n)) -> 
          (i : Nat) -> P i
ind-nat P pZ pS Z     = pZ
ind-nat P pZ pS (S i) = pS i (ind-nat P pZ pS i)

+0 : (n : Nat) -> n + Z == n
+0 = ind-nat (\ n -> n + Z == n) case0 (\ n pn -> cong S pn) 
```
- the inductive principle can also be seen as a proof scheme for `(i : Nat) -> P i`
- its arguments are:
    - the property `P` to be proven
    - the proof the property holds for `Z`
    - the proof that if the property holds for `n` then it holds for `S n`
## List
- a generic list is a parametrized inductive type
```
data [_] (A : Set) : Set where
  [] : [ A ] 
  _::_ : A -> [ A ] -> [ A ] 

infixr 5 _::_ 

l1 : [ Nat ] 
l1 = 1 :: 2 :: 3 :: []
```
- beware `[ A ]` is the type "generic list of `A`s", but `[A]` is an unknown identifier
- parameter = the same type `A` is used for every occurrences of `[_]` is this definition
- in (Lab2) `case1 : {n1 n2 : Nat} -> n1 < n2 -> (S n1) < (S n2)` the occurences of `<` have different arguments (`n1`, `S n1`, `n2`, `S n2`), so the arguments of `<` are not parameters but they are indices
- when you can choose between a parameter and an index, you should use a parameter (the unification algorithm in the Agda type checker deals with parameters efficiently)
## Function Definitions for List
- remember Haskell
```
length : {A : Set} -> [ A ] -> Nat
length [] = 0
length (x :: xs) = 1 + length xs 

_ : length l1 == 3 
_ = case0

_++_ : {A : Set} -> [ A ] -> [ A ] -> [ A ] 
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

infixr 5 _++_

reverse : {A : Set} -> [ A ] -> [ A ] 
reverse [] = []
reverse (x :: xs) = reverse xs ++ (x :: []) 

_ : reverse l1 == 3 :: 2 :: 1 :: []
_ = case0

reverseIt' : {A : Set} -> [ A ] -> [ A ] -> [ A ] 
reverseIt' [] a = a
reverseIt' (x :: xs) a = reverseIt' xs (x :: a)

_ : reverseIt' (2 :: 1 :: []) (3 :: []) == l1 
_ = case0

reverseIt : {A : Set} -> [ A ] -> [ A ] 
reverseIt xs = reverseIt' xs []

_ : reverseIt l1 == 3 :: 2 :: 1 :: []
_ = case0

map : {A B : Set} -> (A -> B) -> [ A ] -> [ B ]
map f [] = []
map f (x :: xs) = f x :: map f xs 

_ : map S l1 == 2 :: 3 :: 4 :: []
_ = case0

filter : {A : Set} -> (A -> Bool) -> [ A ] -> [ A ] 
filter f [] = []
filter f (x :: xs) with f x 
... | true  = x :: filter f xs 
... | false = filter f xs 

_ : filter (_==b_ 2) l1 == 2 :: []
_ = case0

concat : {A : Set} -> [ [ A ] ] -> [ A ] 
concat [] = []
concat (xs :: xss) = xs ++ concat xss 

_ : concat (l1 :: l1 :: []) == 1 :: 2 :: 3 :: 1 :: 2 :: 3 :: []
_ = case0

snoc : {A : Set} -> [ A ] -> A -> [ A ]
snoc [] y = y :: []
snoc (x :: xs) y = x :: (snoc xs y) 

_ : snoc l1 4 == 1 :: 2 :: 3 :: 4 :: []
_ = case0 
```
### Partial Functions 
- remember in Agda functions must be total
- in order to transform a partial function into a total function: 
    - approach 1: a partial function could take a default return value as a paramater
```
head' : {A : Set} -> A -> [ A ] -> A
head' default xs = ?

_ : head' 42 l1 == 1
_ = case0

_ : head' 42 [] == 42
_ = case0
```
    - approach 2: a partial function either returns just a result or nothing
    - the type `Maybe` makes it explicit
```
data Maybe (A : Set) : Set where
  nothing : Maybe A 
  just : A -> Maybe A 

head : {A : Set} -> [ A ] -> Maybe A
head xs = ?

_ : head l1 == just 1
_ = case0

tail : {A : Set} -> [ A ] -> Maybe ([ A ])
tail xs = ?

_ : tail l1 == just (2 :: 3 :: [])
_ = case0

last : {A : Set} -> [ A ] -> Maybe A
last xs = ?

_ : last l1 == just 3 
_ = case0  

init : {A : Set} -> [ A ] -> Maybe ([ A ])
init xs = ?

_ : init l1 == just (1 :: 2 :: [])
_ = case0 
```
- the second argument of the lookup function `!!`  is the index of the element (`Z` denotes the first element, `S Z` denotes the second element... this is similar to arrays index in Java/C) 
```
_!!_ : {A : Set} -> [ A ] -> Nat -> Maybe A
xs !! n = ?

_ : l1 !! 1 == just 2 
_ = case0 
```
## Proofs for List Functions
```
length-distrib++ : {A : Set} -> (l1 l2 : [ A ]) -> length (l1 ++ l2) == length l1 + length l2 
length-distrib++ l1 l2 = ?
```
- `length-distrib++` it is the property we have quickchecked in the Haskell course
```
length-map : {A B : Set} -> (f : A -> B) -> (xs : [ A ]) -> length (map f xs) == length xs
length-map f xs = ?

length-reverse : {A : Set} -> (l : [ A ]) -> length (reverse l) == length l
length-reverse l = ?

++assoc : {A : Set} -> (l1 l2 l3 : [ A ]) -> (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3)
++assoc l1 l2 l3 = ?

++[] : {A : Set} -> (xs : [ A ]) -> xs ++ [] == xs
++[] xs = ?

reverse-append : {A : Set} -> (l1 l2 : [ A ]) -> reverse (l1 ++ l2) == reverse l2 ++ reverse l1
reverse-append l1 l2 = ? 

reverse-involutive : {A : Set} -> (l : [ A ]) -> reverse (reverse l) == l
reverse-involutive l = ?

reverse-reverseIt' : {A : Set} -> (l a : [ A ]) -> reverseIt' l a == reverse l ++ a
reverse-reverseIt' l1 a = ?

reverse-reverseIt : {A : Set} -> (l : [ A ]) -> reverse l == reverseIt l
reverse-reverseIt l = ?

map-distrib++ : {A B : Set} -> (f : A -> B) -> (l1 l2 : [ A ]) -> map f (l1 ++ l2) == map f l1 ++ map f l2
map-distrib++ f l1 l2 = ?

map-merge : {A B C : Set} -> (f : A -> B) -> (g : B -> C) -> (l : [ A ]) -> map g (map f l) == map (λ x -> g (f x)) l
map-merge f g l = ?

-- propose and prove more properties for:
-- length wrt reverseIt
-- length wrt filter 

length-reverseIt : {A : Set} -> (l : [ A ]) -> length l == length (reverseIt l)
length-reverseIt l = ?

length-filter : {A : Set} -> (f : A -> Bool) -> (l : [ A ]) -> (length (filter f l)) <= (length l)
length-filter f l = ?
```
