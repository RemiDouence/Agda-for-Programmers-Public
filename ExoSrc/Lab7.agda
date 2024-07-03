
-- This work is licensed under a Creative Commons Attribution-NonCommercial-NoDerivs License
-- https://creativecommons.org/licenses/by-nc-nd/4.0/
-- Remi Douence

-- Please do not distribute solutions but let people learn by doing the exercices.

module Lab7 where 

-- from Lab1

data Nat : Set where 
  Z : Nat 
  S : Nat -> Nat 

-- from Lab2

{-# BUILTIN NATURAL Nat #-}

data _==_ {A : Set} (n : A) : A -> Set where 
  case0 : n == n   

infix 4 _==_

data _<=_ : Nat -> Nat -> Set where 
  case0 : {n2 : Nat} -> Z <= n2 
  case1 : {n1 n2 : Nat} -> n1 <= n2 -> (S n1) <= (S n2)

<=refl : {x : Nat} -> x <= x
<=refl {Z} = case0
<=refl {S x} = case1 <=refl

<=trans : {n1 n2 n3 : Nat} -> n1 <= n2 -> n2 <= n3 -> n1 <= n3 
<=trans case0 p23 = case0
<=trans (case1 p12) (case1 p23) = case1 (<=trans p12 p23) 

-- from Lab3

data [_] (A : Set) : Set where
  [] : [ A ] 
  _::_ : A -> [ A ] -> [ A ]

infixr 5 _::_ 

-- from Lab5

data True : Set where 
  T : True

data _And_ (A B : Set) : Set where 
  _and_ : A -> B -> A And B 

getAndL : {A B : Set} -> A And B -> A 
getAndL (a and b) = a 

getAndR : {A B : Set} -> A And B -> B 
getAndR (a and b) = b

data False : Set where 

neg : Set -> Set
neg A = A -> False

absurd : {A : Set} -> False -> A
absurd ()

data Dec (A : Set) : Set where
  yes : A -> Dec A 
  no : neg A -> Dec A 

_<=?_ : (n1 n2 : Nat) -> Dec (n1 <= n2)
Z <=? n2 = yes case0
S n1 <=? Z = no (\ ())
S n1 <=? S n2 with n1 <=? n2 
... | yes p = yes (case1 p) 
... | no np = no (\ { (case1 p) -> np p })  

data Exist {A : Set} (B : A -> Set) : Set where
  exist : (a : A) -> B a -> Exist B  

witness : {A : Set}{B : A -> Set} -> Exist B -> A 
witness (exist a b) = a 

proof : {A : Set}{B : A -> Set} -> (e : Exist B) -> B (witness e) 
proof (exist a b) = b 

insert : Nat -> [ Nat ] -> [ Nat ] 
insert x [] = x :: []
insert x (y :: ys) with x <=? y 
... | yes p = x :: y :: ys 
... | no np = y :: insert x ys 

_ : insert 5 (4 :: 3 :: 2 :: 1 :: []) == 4 :: 3 :: 2 :: 1 :: 5 :: []
_ = case0 

insertSort : [ Nat ] -> [ Nat ]
insertSort [] = []
insertSort (x :: xs) = insert x (insertSort xs)

_ : insertSort (5 :: 4 :: 3 :: 2 :: 1 :: []) == 1 :: 2 :: 3 :: 4 :: 5 :: []  
_ = case0  

smallest : Nat -> [ Nat ] -> Set 
smallest n [] = True 
smallest n (x :: xs) = (n <= x) And (smallest n xs)

smallestTrans : {y x : Nat}{xs : [ Nat ]} -> y <= x -> smallest x xs -> smallest y xs
smallestTrans pxy pyxs = ?

smallestInsert : {y x : Nat}{xs : [ Nat ]} -> x <= y -> smallest x xs -> smallest x (insert y xs)
smallestInsert pxy pxxs = ?

sorted : [ Nat ] -> Set 
sorted [] = True 
sorted (x :: xs) = (smallest x xs) And (sorted xs) 

neg<= : {x y : Nat} -> neg (y <= x) -> x <= y
neg<= p = ?

sortedInsert : (y : Nat) -> (xs : [ Nat ]) -> sorted xs -> sorted (insert y xs)
sortedInsert y xs h = ?

sortedInsertSort : (l : [ Nat ]) -> sorted (insertSort l)
sortedInsertSort xs = ?

data Permut {A : Set} : [ A ] -> [ A ] -> Set where 
  case0 : Permut [] []
  case1 : {x : A} {l1 l2 : [ A ]} -> Permut l1 l2 -> Permut (x :: l1) (x :: l2)
  case2 : {x y : A} {l : [ A ]} -> Permut (x :: y :: l) (y :: x :: l)
  case3 : {l1 l2 l3 : [ A ]} -> Permut l1 l2 -> Permut l2 l3 -> Permut l1 l3

permutInsert : (y : Nat) (xs : [ Nat ]) -> Permut (y :: xs) (insert y xs)
permutInsert y xs = ?

permutInsertSort : (xs : [ Nat ]) -> Permut xs (insertSort xs)
permutInsertSort xs = ?

data SortedList : Set
data Smallest : Nat -> SortedList -> Set 

data SortedList where 
  [] : SortedList 
  _::_when_ : (x : Nat) -> (xs : SortedList) -> (p : Smallest x xs) -> SortedList 

data Smallest where 
  [] : {x : Nat} -> Smallest x []
  _::_ : {x y : Nat} {xs : SortedList} -> x <= y -> (p : Smallest y xs) -> Smallest x (y :: xs when p)

SmallestTrans : {y x : Nat}{xs : SortedList} -> y <= x -> Smallest x xs -> Smallest y xs
SmallestTrans pyx pxxs = ?

insertI : (y : Nat) -> (xs : SortedList) -> Exist (\ l -> {x : Nat} -> x <= y -> Smallest x xs -> Smallest x l)
insertI y xs = ?

insertSortI : (xs : [ Nat ]) -> SortedList
insertSortI xs = ?

permutRefl : {A : Set} (l : [ A ]) -> Permut l l
permutRefl l = ?

permutSym : {A : Set} {l1 l2 : [ A ]} -> Permut l1 l2 -> Permut l2 l1
permutSym p12 = ?

permutTrans : {A : Set} {l1 l2 l3 : [ A ]} -> Permut l1 l2 -> Permut l2 l3 -> Permut l1 l3
permutTrans p12 p23 = ?



-- josselin's version

data Where {A : Set} : [ A ] -> Set where
  here : {xs : [ A ]} -> Where xs
  there : {x : A} {xs : [ A ]} -> Where xs -> Where (x :: xs)

_ : Where (1 :: 3 :: [])
_ = here 

_ : Where (1 :: 3 :: [])
_ = there (there here) 


mkWhere : (x : Nat) (xs : [ Nat ]) -> Where xs
mkWhere x ys = ? 

_ : mkWhere 1 (1 :: 3 :: []) == here
_ = case0

_ : mkWhere 2 (1 :: 3 :: []) == there here
_ = case0


insert'At : {A : Set} -> A -> (xs : [ A ]) -> Where xs -> [ A ]
insert'At x ys loc = ?

_ : insert'At 0 (1 :: 3 :: []) here == 0 :: 1 :: 3 :: []
_ = case0

_ : insert'At 0 (1 :: 3 :: []) (there here) == 1 :: 0 :: 3 :: []
_ = case0


insert' : Nat -> [ Nat ] -> [ Nat ]
insert' y l = insert'At y l (mkWhere y l)

_ : insert' 1 (1 :: 3 :: []) == 1 :: 1 :: 3 :: []
_ = case0

_ : insert' 2 (1 :: 3 :: []) == 1 :: 2 :: 3 :: []
_ = case0


data _Smaller_ (x : Nat) : [ Nat ] -> Set where
  [] : x Smaller []
  _::_ : {y : Nat} {ys : [ Nat ]} -> x <= y -> x Smaller ys -> x Smaller (y :: ys)

_ : 1 Smaller (1 :: 3 :: [])
_ = (case1 case0) :: (case1 case0) :: []

_ : 2 Smaller (3 :: [])
_ = case1 (case1 case0) :: []


data Sorted : [ Nat ] -> Set where
  [] : Sorted []
  _::_ : {x : Nat} {xs : [ Nat ]} -> x Smaller xs -> Sorted xs -> Sorted (x :: xs)

_ : Sorted (1 :: 3 :: [])
_ = (case1 case0 :: []) :: [] :: []

_ : Sorted (1 :: 2 :: 3 :: [])
_ = (case1 case0 :: case1 case0 :: []) :: (case1 (case1 case0) :: []) :: [] :: []


insert'At<= : {x y : Nat} {ys : [ Nat ]} {loc : Where ys}
  -> x <= y
  -> x Smaller ys
  -> x Smaller (insert'At y ys loc)
insert'At<= p isSmaller = ?


<=Smaller : {x y : Nat} { ys : [ Nat ]} -> x <= y -> y Smaller ys -> x Smaller ys
<=Smaller p isSmaller = ?

insert'Sorted : (x : Nat) (ys : [ Nat ]) -> Sorted ys -> Sorted (insert' x ys)
insert'Sorted x ys ysSorted = ?

data Permut' {A : Set} : [ A ] -> [ A ] -> Set where
  case0 : Permut' [] []
  case1 : {x : A} {xs ys : [ A ]}
    -> Permut' xs ys
    -> (loc : Where ys)
    -> Permut' (x :: xs) (insert'At x ys loc)

record SortedOf (xs : [ Nat ]) : Set where
  constructor sortedOf
  field
    sortedList : [ Nat ]
    isSorted : Sorted sortedList
    isPermut' : Permut' xs sortedList

insert'SortProof : (xs : [ Nat ]) -> SortedOf xs
insert'SortProof xs = ?



-- define `bubble` and `bubbleSort`
-- `bubble` post condition: the bigest natural is last
-- `bubbleSort` cursively repeat on `initV`
-- use `Vec` to proove Agda your algorithm terminate
-- prove `bubbleSort` is correct
