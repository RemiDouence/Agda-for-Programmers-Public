
-- This work is licensed under a Creative Commons Attribution-NonCommercial-NoDerivs License
-- https://creativecommons.org/licenses/by-nc-nd/4.0/
-- Remi Douence

-- Please do not distribute solutions but let people learn by doing the exercices.

{-# OPTIONS --allow-unsolved-metas #-}

module Lab4 where  

open import Lab3 public 

filter-idempotent : {A : Set} -> (f : A -> Bool) -> (l : [ A ]) -> filter f (filter f l) == filter f l 
filter-idempotent f [] = case0
filter-idempotent f (x :: l) with f x in p  
... | false = filter-idempotent f l 
... | true rewrite p | filter-idempotent f l = case0 

even : Nat -> Bool 
even Z = true
even (S (S n)) = even n 
even (S Z) = false

data Even : Nat -> Set where 
  case0 : Even Z 
  case1 : {n : Nat} -> Even n -> Even (S (S n))

even+even=even : {n1 n2 : Nat} -> Even n1 -> Even n2 -> Even (n1 + n2)
even+even=even p1 p2 = ?

data Vec (A : Set) : Nat -> Set where
  [] : Vec A 0 
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (1 + n)

v1 : Vec Nat 3
v1 = 1 :: 2 :: 3 :: []

_++V_ : {A : Set}{n1 n2 : Nat} -> Vec A n1 -> Vec A n2 -> Vec A (n1 + n2)
xs ++V ys = ?

_ : v1 ++V v1 == 1 :: 2 :: 3 :: 1 :: 2 :: 3 :: [] 
_ = case0 

vec-commut : {A : Set}{n : Nat} -> Vec A (n + 1) -> Vec A (1 + n)
vec-commut xs = ?

reverseV : {A : Set}{n : Nat} -> Vec A n -> Vec A n
reverseV xs = ?

_ : reverseV v1 == 3 :: 2 :: 1 :: []
_ = case0

reverseV' : {A : Set}{n : Nat} -> Vec A n -> Vec A n
reverseV' xs = ?

snocV : {A : Set}{n : Nat} -> Vec A n -> A -> Vec A (1 + n)
snocV xs y = ?

_ : snocV v1 4 == 1 :: 2 :: 3 :: 4 :: []
_ = case0 

reverseV'' : {A : Set}{n : Nat} -> Vec A n -> Vec A n
reverseV'' xs = ?

_ : reverseV'' v1 == 3 :: 2 :: 1 :: [] 
_ = case0 

reverseV''' : {A : Set}{n1 n2 : Nat} -> Vec A n1 -> Vec A n2 -> Vec A (n1 +I n2)
reverseV''' xs ys = ?

_ : reverseV''' v1 [] == 3 :: 2 :: 1 :: []
_ = case0

reverseV'''' : {A : Set}{n1 n2 : Nat} -> Vec A n1 -> Vec A n2 -> Vec A (n1 + n2)
reverseV'''' xs ys = ?

_ : reverseV'''' v1 [] == 3 :: 2 :: 1 :: []
_ = case0

lengthV : {A : Set}{n : Nat} -> Vec A n -> Nat
lengthV xs = ?

_ : lengthV v1 == 3 
_ = case0 

headV : {A : Set}{n : Nat} -> Vec A (1 + n) -> A
headV xs = ?

_ : headV v1 == 1 
_ = case0 

tailV : {A : Set}{n : Nat} -> Vec A (1 + n) -> Vec A n
tailV xs = ?

_ : tailV v1 == 2 :: 3 :: [] 
_ = case0 

lastV : {A : Set}{n : Nat} -> Vec A (1 + n)-> A
lastV xs = ?

_ : lastV v1 == 3
_ = case0 

initV : {A : Set}{n : Nat} -> Vec A (1 + n)-> Vec A n
initV xs = ?

_ : initV v1 == 1 :: 2 :: []
_ = case0 

ListToVec : {A : Set} (xs : [ A ]) -> Vec A (length xs)
ListToVec xs = ?

_ : ListToVec (1 :: 2 :: 3 :: []) == 1 :: 2 :: 3 :: []
_ = case0 

VecToList : {A : Set}{n : Nat} -> (xs : Vec A n) -> [ A ]
VecToList xs = ?

_ : VecToList (1 :: 2 :: 3 :: []) == 1 :: 2 :: 3 :: []
_ = case0 

data Rank : Nat -> Set where 
  Z : {n : Nat} -> Rank n
  S : {n : Nat} -> Rank n -> Rank (S n)

_!!V_ : {A : Set}{n : Nat} -> Vec A (S n) -> Rank n -> A
xs !!V r = ?

_ : v1 !!V (S Z) == 2
_ = case0 

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

data _<'_ : Nat -> Nat -> Set where 
  case0 : {n : Nat} -> n <' (S n) 
  case1 : {n1 n2 : Nat} -> n1 <' n2 -> n1 <' (S n2) 

_ : 1 <' 2
_ = ?

_ : 4 <' 5
_ = ?

_ : 0 <' 5
_ = ?

_ : 100 <' 0
_ = ?

<'Sn : {n1 n2 : Nat} -> (S n1) <' n2 -> n1 <' n2
<'Sn p = ? 

<'-trans : {n1 n2 n3 : Nat} -> n1 <' n2 -> n2 <' n3 -> n1 <' n3
<'-trans p12 p23 = ?

_*_ : Nat -> Nat -> Nat 
n1 * Z = Z
n1 * S n2 = n1 + (n1 * n2) 

concatV : {A : Set}{n m : Nat} -> Vec (Vec A n) m -> Vec A (n * m)
concatV vs = ?

zipWithV : {A B C : Set}{n : Nat} -> (A -> B -> C) -> Vec A n -> Vec B n -> Vec C n
zipWithV f xs ys = ?
