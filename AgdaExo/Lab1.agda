
-- This work is licensed under a Creative Commons Attribution-NonCommercial-NoDerivs License
-- https://creativecommons.org/licenses/by-nc-nd/4.0/
-- Remi Douence

-- Please do not distribute solutions but let people learn by doing the exercices.

{-# OPTIONS --allow-unsolved-metas #-}

module Lab1 where 

-- here is a single line comment
{- here is 
a {- nested 
-} multi 
lines 
comment -}

data Bool : Set where 
  true : Bool 
  false : Bool 

data Nat : Set where 
  Z : Nat 
  S : Nat -> Nat 

equal : Nat -> Nat -> Bool
equal Z Z = true 
equal Z (S n2) = false
equal (S n1) Z = false
equal (S n1) (S n2) = equal n1 n2

equal' : Nat -> Nat -> Bool
equal' Z Z = true 
equal' Z (S _) = false
equal' (S _) Z = false
equal' (S n1) (S n2) = equal' n1 n2

equal'' : Nat -> Nat -> Bool
equal'' Z Z = true 
equal'' (S n1) (S n2) = equal'' n1 n2
equal'' n1 n2 = false

equal''' : Nat -> Nat -> Bool
equal''' Z Z = true 
equal''' (S n1) (S n2) = equal''' n1 n2
equal''' _ _ = false

data Equal : Nat -> Nat -> Set where 
  case0 : Equal Z Z 
  case1 : (n1 n2 : Nat) -> Equal n1 n2 -> Equal (S n1) (S n2)

l00 : Equal Z Z
l00 = ?

l11 : Equal (S Z) (S Z)
l11 = ?

data Equal' : Nat -> Nat -> Set where 
  case0 : Equal' Z Z 
  case1 : {n1 n2 : Nat} -> Equal' n1 n2 -> Equal' (S n1) (S n2)

l00' : Equal' Z Z
l00' = ?

l11' : Equal' (S Z) (S Z)
l11' = ?

l22' : Equal' (S (S Z)) (S (S Z))
l22' = ?

Equal'-refl : (n : Nat) -> Equal' n n
Equal'-refl n = ?

Equal'-sym : {n1 n2 : Nat} -> Equal' n1 n2 -> Equal' n2 n1
Equal'-sym p = ?

Equal'-trans : {n1 n2 n3 : Nat} -> Equal' n1 n2 -> Equal' n2 n3 -> Equal' n1 n3
Equal'-trans p12 p23 = ?

add : Nat -> Nat -> Nat 
add Z n2 = n2 
add (S n1) n2 = S (add n1 n2)

add-left : (n : Nat) -> Equal' (add Z n) n
add-left n = ?

add-right : (n : Nat) -> Equal' (add n Z) n
add-right n = ?

add-assoc : (n1 n2 n3 : Nat) -> Equal' (add (add n1 n2) n3) (add n1 (add n2 n3))
add-assoc n1 n2 n3 = ?

add-S : (n1 n2 : Nat) -> Equal' (add n1 (S n2)) (S (add n1 n2))
add-S n1 n2 = ?

add-commut : (n1 n2 : Nat) -> Equal' (add n1 n2) (add n2 n1)
add-commut n1 n2 = ?

addI : Nat -> Nat -> Nat 
addI Z n2 = n2
addI (S n1) n2 = addI n1 (S n2) 

addI-S : (n1 n2 : Nat) -> Equal' (addI n1 (S n2)) (S (addI n1 n2))
addI-S n1 n2 = ?

addI-left : (n : Nat) -> Equal' (addI Z n) n
addI-left n = ?

addI-right : (n : Nat) -> Equal' (addI n Z) n
addI-right n = ?

addI-commut : (n1 n2 : Nat) -> Equal' (addI n1 n2) (addI n2 n1)
addI-commut n1 n2 = ?

addI-n1 : (n1 n2 n3 : Nat) -> Equal' n1 n2 -> Equal' (addI n1 n3) (addI n2 n3)
addI-n1 n1 n2 n3 p12 = ?

addI-assoc : (n1 n2 n3 : Nat) -> Equal' (addI (addI n1 n2) n3) (addI n1 (addI n2 n3))
addI-assoc n1 n2 n3 = ?

addI-add : (n1 n2 : Nat) -> Equal' (addI n1 n2) (add n1 n2)
addI-add n1 n2 = ?

addI-commut' : (n1 n2 : Nat) -> Equal' (addI n1 n2) (addI n2 n1)
addI-commut' n1 n2 = ?

addR : Nat -> Nat -> Nat 
addR n1 Z = n1
addR n1 (S n2) = S (addR n1 n2) 

addR-left : (n : Nat) -> Equal' (addR Z n) n
addR-left n = ?

addR-assoc : (n1 n2 n3 : Nat) -> Equal' (addR (addR n1 n2) n3) (addR n1 (addR n2 n3))
addR-assoc n1 n2 n3 = ?

addR-S : (n1 n2 : Nat) -> Equal' (addR (S n1) n2) (S (addR n1 n2))
addR-S n1 n2 = ?

addR-commut : (n1 n2 : Nat) -> Equal' (addR n1 n2) (addR n2 n1)
addR-commut n1 n2 = ?

add-addR : (n1 n2 : Nat) -> Equal' (add n1 n2) (addR n1 n2)
add-addR n1 n2 = ?
