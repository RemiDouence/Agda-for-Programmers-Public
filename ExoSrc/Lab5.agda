
-- This work is licensed under a Creative Commons Attribution-NonCommercial-NoDerivs License
-- https://creativecommons.org/licenses/by-nc-nd/4.0/
-- Remi Douence

-- Please do not distribute solutions but let people learn by doing the exercices.

{-# OPTIONS --allow-unsolved-metas #-}

module Lab5 where  

open import Lab4 public 

_=>_ : Bool -> Bool -> Bool 
true  => true  = true 
false => true  = true 
false => false = true 
true  => false = false

data _And_ (A B : Set) : Set where 
  _and_ : A -> B -> A And B 

Between : Nat -> Nat -> Nat -> Set 
Between low n high = (low < n) And (n < high)

b123 : Between 1 2 3
b123 = ?

data _Or_ (A B : Set) : Set where
  orL : A -> A Or B  
  orR : B -> A Or B  

_<=''_ : Nat -> Nat -> Set 
n1 <='' n2 = (n1 == n2) Or (n1 < n2) 

0<='' : (n : Nat) -> 0 <='' n
0<='' n = ?

data True : Set where 
  T : True

_ : True -> True
_ = ?

data False : Set where 

_ : False -> True
_ = ?

_ : False -> False
_ = ?

_ : True -> False
_ = ?

neg : Set -> Set
neg A = A -> False

_ : 2 == 2
_ = ?

_ : neg (2 == 3)
_ = ?

_ : 2 <= 3 
_ = ?

_ : neg (3 <=' 2)
_ = ?

absurd : {A : Set} -> False -> A
absurd ()

postulate ExcludedMiddle : (A : Set) -> A Or (neg A) 

postulate Crazy : 1 == 2 

data Dec (A : Set) : Set where
  yes : A -> Dec A 
  no : (neg A) -> Dec A 

_<?_ : (n1 n2 : Nat) -> Dec (n1 < n2)
n1 <? n2 = ?

data Pair (A B : Set) : Set where 
  _,_ : A -> B -> Pair A B

fst : {A B : Set} -> Pair A B -> A 
fst (a , _) = a 

snd : {A B : Set} -> Pair A B -> B 
snd (_ , b) = b 

_ : snd (1 , 2) == 2 
_ = case0

data PairD (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) -> (b : B a) -> PairD A B  

fstD : {A : Set}{B : A -> Set} -> PairD A B -> A 
fstD (a , _) = a 

sndD : {A : Set}{B : A -> Set} -> (p : PairD A B) -> B (fstD p)  
sndD (_ , b) = b

p1 : PairD Nat (\ n -> Odd n)
p1 = ?

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

t2 : True -> True -> True
t2 x y = ?

t3 : (True -> True) -> True 
t3 f = ?

-- t4 is the same property than t3 but a different proof
t4 : (True -> True) -> True
t4 f = ?

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

Z<=''' : (n : Nat) -> Z <=''' n
Z<=''' n = ?

<='''trans : {n1 n2 n3 : Nat} -> n1 <=''' n2 -> n2 <=''' n3 -> n1 <=''' n3
<='''trans p12 p23 = ?

existHalf : (n : Nat) -> Even n -> Exist (\ h -> h + h == n)
existHalf n pn = ?
