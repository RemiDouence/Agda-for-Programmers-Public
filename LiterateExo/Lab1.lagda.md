```
-- This work is licensed under a Creative Commons Attribution-NonCommercial-NoDerivs License
-- https://creativecommons.org/licenses/by-nc-nd/4.0/
-- Remi Douence

-- Please do not distribute solutions but let people learn by doing the exercices.
```
# Agda for programmers 

## Key Points
- functional programmnig with `Nat` and `Bool` 
- dependent types

## Disclaimer 

- I am a teacher, so I have to lie to you in order to introduce concepts incrementally

## Agda

- Agda = Haskell + dependent types 
- Agda is a blank slate: no type or function is predefined 
- Agda offers a very nice standard library, but I will not use it 
- Agda can use rich identifiers with almost any characters (and unicode), but I will not use them

## Module 

- a module is a sequence of definitions 
- a module has a name matching the source code file (please see the source file your are reading)
- literate Agda file format is markdown comments separated by blocks of Agda code (starting and ending with ``` on their own lines)
- a literate Agda file suffix is `.lagda.md` for literate Agda and markdown 
- a literate Agda file can be nicely rendered on github (or with markdown tools) as well as loaded in Agda
- module are good for modularity, but also for separate type checking (when there is numerous definitions)
- modules (loading) with incomplete definitions are allowed with an `OPTIONS` command (so you can skip exercises)

```
{-# OPTIONS --allow-unsolved-metas #-}

module Lab1 where 
```

## Editor 

- you must use an editor with an Agda mode 
    - vscode has caused me a lot of troubles with Agda (vanishing key bindings)
    - emacs is much more stable 
- you must load a file to let Agda typechecks it 
- load = Control-c Control-l, noted C-c C-l from here on
- another buffer opens and displays the result of the type checking
- result of type checking 
    - either a type error message 
    - or the types of the missing code of the program to be completed

## Comments

- Agda blocks of code can contain comments
- a single line comment starts with `--`
- a multi lines comment starts with `{-` and ends with `-}`
- multi lines comments can be nested 

```
-- here is a single line comment
{- here is 
a {- nested 
-} multi 
lines 
comment -}
```


## Functional Programming (prerequisite)

- go learn Haskell, then come back, I am waiting for you here
- functional programming in a two principles:

### First Principle : inductive data types

- here is a type definition for booleans:

```
data Bool : Set where 
  true : Bool 
  false : Bool 
```

- `Bool` is a type 
- `Set` is the type of types 
- `Bool` has two values (think about Enum in Java)
- `Bool` has two values: `true` and `false`

- here is a type definition for naturals: 

```
data Nat : Set where 
  Z : Nat 
  S : Nat -> Nat 
```

- `Nat` is a type 
- `Set` is the type of type 
- `Z` is a value 
- `S` is a constructor (apply it to a value of type `Nat` and you get a value of type `Nat`)
- `Nat` has an infinite number of values: `Z`, `S Z`, `S (S Z)`, `S (S (S Z))`, ...
- `Nat` defines a set of values: start from the value `Z`, then apply constructor the `S`, then apply the constructor `S` again, then... until you reach a fix point, and tada... here is the set of all values of this type

- most of the time in my code: a type identifier starts with a capital letter, a value identifier starts with lowercase letter... hum, most of the time

- induction from particular to general: start from simple values and apply the constructors to saturate the set
- induction from particular to general: a bottom-up approach

### second principle: recursive functions = type + equations with pattern matching

- here is the function definition for checking if two naturals are equal:

```
equal : Nat -> Nat -> Bool
equal Z Z = true 
equal Z (S n2) = false
equal (S n1) Z = false
equal (S n1) (S n2) = equal n1 n2
```

- a function is a type and a sequence of equations
- the left hand side (before =) of an equation can use pattern to match values of its arguments 
- if the pattern matching fails, the next equation is tested (so the order of equation is important)
- in Agda functions are total:
    - a function must be defined for every possible values of its arguments 
    - whatever the value of the arguments there is always at least one equation that matches
- a function can be recursive and calls itself on the right hand side (after =)
- in Agda functions must terminate (in particular recursive functions must be applied to smaller arguments, more on this latter)
- when an argument (piece) is not used in the right hand side, there is no need to name it, you can use `_` as a wildcard placeholder

```
equal' : Nat -> Nat -> Bool
equal' Z Z = true 
equal' Z (S _) = false
equal' (S _) Z = false
equal' (S n1) (S n2) = equal' n1 n2
```

- the order of the equations is important, below the most general pattern must be last because it matches every arguments values

```
equal'' : Nat -> Nat -> Bool
equal'' Z Z = true 
equal'' (S n1) (S n2) = equal'' n1 n2
equal'' n1 n2 = false
```

- the same definition with wildcard underscores

```
equal''' : Nat -> Nat -> Bool
equal''' Z Z = true 
equal''' (S n1) (S n2) = equal''' n1 n2
equal''' _ _ = false
```

## Function Programming with Dependent types  

### Dependent Types 

- here is an inductive type: 

```
data Equal : Nat -> Nat -> Set where 
  case0 : Equal Z Z 
  case1 : (n1 n2 : Nat) -> Equal n1 n2 -> Equal (S n1) (S n2)
```

- `Equal` is a type constructor
- once `Equal` is applied to two naturals you get a type 
- for instance: 
    - `Equal Z Z` is a type 
    - `Equal Z (S Z)` is a type 
    - `Equal (S Z) Z` is a type 
    - `Equal (S Z) (S Z)` is a type 
    - etc. 
- hence the definition of `Equal` defines a family of types 
- the two arguments of `Equal` are called indices
- `case0` is a value of type `Equal Z Z` 
- `case1` is a value constructor with three arguments 
    - the first argument `n1` is a natural
    - the second argument `n2` is a natural
    - the third argument must be of type `Equal n1 n2` 
    - the type of the third argument depends on the *values* of the previous arguments (it is a dependent type)
    - `case1` applied to three arguments is a value of type `Equal (S n1) (S n2)`

```
l00 : Equal Z Z
l00 = ?

l11 : Equal (S Z) (S Z)
l11 = ?
```

- in `case1`: 
  - the *values* of the first and second arguments of `case1` can be deduced from the type of the third argument of `case1` 
  - `n1` and `n2` can be deduced from the type `Equal n1 n2` 
  - `n1` and `n2` can be implicit (noted in curly brackets) 
  - in `Equal'` below we only have to provide one argument to `case1` (the other ones `n1` and `n2` are implicit for they can be deduced)

```
data Equal' : Nat -> Nat -> Set where 
  case0 : Equal' Z Z 
  case1 : {n1 n2 : Nat} -> Equal' n1 n2 -> Equal' (S n1) (S n2)

l00' : Equal' Z Z
l00' = ?

l11' : Equal' (S Z) (S Z)
l11' = ?

l22' : Equal' (S (S Z)) (S (S Z))
l22' = ?
```

- `case0` is a value of type `Equal Z Z` 
- `case0` is also a value of type `Equal' Z Z` 
- values can be overloaded 
- functions and types cannot be overloaded

- some types are empty (contains no value)
- `Equal' Z (S Z)` is empty 
- `Equal' (S Z) Z` is empty 
- `Equal' n1 n2` is empty when `n1` is different from `n2` 
- `Equal' n1 n2` contains a single value when `n1` is equal to `n2` 
    - such a value is a list of `case1` (`n1` occurences) ending with a `case0` 
    - the function `Equal-refl` returns such a value for any natural 

```
Equal'-refl : (n : Nat) -> Equal' n n
Equal'-refl n = ?
```

- the computer scientist reads the function `Equal-refl` as: "for any `n` return a value of type `Equal' n n`"
- the logician reads the function `Equal-refl` as: "for all n, n equals n"
- the mathematician reads the function Equal-refl as: "equality is a reflexive relation"
- it is the Curry-Howard isomorphism: 
    - a type corresponds to a property 
    - a function corresponds to a proof 
    - more on this latter 
- the type `Equal' n1 n2` represents the equality relation between `n1` and `n2` 
- when `n1` is not equal to `n2`:
    - the type `Equal' n1 n2` is empty
    - i.e., it is not possible to represent "n1 equals n2"  
    - i.e., there is no proof of "n1 equals n2"
    - i.e., the relation "n1 equals n2" does not hold
- this is a very poor definition of equality, more on this later 

## Agda in a nutshell 

- (dependent) types represents properties, 
- when a property holds the corresponding value can be defined/computed, 
- when a property does not hold the corresponding value cannot be defined/computed

## Boolean Predicate versus Inductive Type 

- the function `equal'''` defines an algorithm that decides wether or not its arguments are equal
- the type `Equal'` defines a family of types, each of these types are either a singleton, or they are empty
- the function `equal'''` matches (and deconstruct its natural arguments)
- the type `Equal'` construct values with `case1` and `case0`  
- `case0` in `Equal'` corresponds to the first equation of `equal'''` 
- `case1` in `Equal'` corresponds to the second equation of `equal'''` 
- the third equation of `equal'''` has no correspondance in `Equal'` (since `Equal'` represents when the relation holds) 

## Interactive Function Definition

- you must write type definition by yourselve
- but you do not want to write a function definition 
- **you do not want to write a function definition** 
- **YOU DO NOT WANT TO WRITE A FUNCTION DEFINITION**
- first you must write the type of a function
- then you must write the most general left hand side of the function definition and put a hole (noted "?") on the right hand side
- then you put the cursor in the hole and you build the function incrementaly with the following commands:
    - ? : introduce a hole
    - C-c C-l : (load) typecheck the program
    - C-c C-c : (case) break a variable 
    - C-c C-, : print the current hole type and the available variables
    - C-c C-r : (refine) refine the current hole
    - C-c C-d : (deduce) print the type of an expression
    - C-c C-n : (normalize) evaluate and print an expression

- here is an example :
    - I write:
    
    ``` 
    and : Bool -> Bool -> Bool
    and b1 b2 = ? 
    ```
    
    - I load the file (C-c C-l), the hole get numbered: 
    ```
    and : Bool -> Bool -> Bool
    and b1 b2 = { }0 
    ```
    - I put my cursor in the hole and break (C-c C-c) the variable `b1` to get two cases:
    ```
    and : Bool -> Bool -> Bool
    and true b2 = { }0 
    and false b2 = { }1 
    ```
    - I put my cursor in the first hole and ask its type (C-c C-,)
    - Agda tells the hole must be filled with a Bool
    - Agda tells `b2` is an available Bool
    - I type `b2` in the first hole and refine it (C-c C-r)
    ```
    and : Bool -> Bool -> Bool
    and true b2 = b2 
    and false b2 = { }1 
    ```
    - I refine the second hole with false `value` (C-c C-r)
    ```
    and : Bool -> Bool -> Bool
    and true b2 = b2 
    and false b2 = false 
    ```


## More equal properties and proofs

- let us compute a value of type `Equal' n2 n1` from a value of type `Equal' n1 n2`
- this can be reas as the relation `Equal'` is symmetric 
- the natural arguments `n1` and `n2` are implicit (deduced from the argument type `Equal' n1 n2`)
```
Equal'-sym : {n1 n2 : Nat} -> Equal' n1 n2 -> Equal' n2 n1
Equal'-sym p = ?
```

- let us compute a value of type `Equal' n1 n3` from a value of type `Equal' n1 n2` and a value of type `Equal' n2 n3`
- this can be fread as the realtion `Equal'` is transitive  
- the natural arguments `n1`, `n2` and `n3` are implicit (deduced from the argument types `Equal' n1 n2` and `Equal' n2 n3`)
```
Equal'-trans : {n1 n2 n3 : Nat} -> Equal' n1 n2 -> Equal' n2 n3 -> Equal' n1 n3
Equal'-trans p12 p23 = ?
```

- `Equal'` is an equivalence relation (reflexive + symetric + transitive)

## Addition 

- here is a function that computes the addition of two naturals
```
add : Nat -> Nat -> Nat 
add Z n2 = n2 
add (S n1) n2 = S (add n1 n2)
```

- prove this algorithm has the following properties:
  - `Z` is left neutral element for addition 
  - `Z` is right neutral element for addition
  - the addition is associative
  - the successor `S` can jump from one argument to the other
  - the addition is commutative
```
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
```

## Iterative addition 

- here is another algorithm that computes the addition of two naturals
```
addI : Nat -> Nat -> Nat 
addI Z n2 = n2
addI (S n1) n2 = addI n1 (S n2) 
```

- prove this algorithm has the following properties:
  - the successor `S` can jump from one argument to the other
  - `Z` is left neutral element for addition 
  - `Z` is right neutral element for addition
  - the addition is commutative
  - equality is transported from the second argument of the addition
  - the addition is associative
```
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
```

## Equivalence of add and addI

- we have proved from scratch properties for `addI`
- an alternative is to consider `add` as a pivot
    - properties are proved from scratch for `add`
    - prove `add` and `addI` are equivalent  
    - propreties can be transported from `add` to `addI`
    - for instance we can prove `addI` is commutative as follows:

```
addI-add : (n1 n2 : Nat) -> Equal' (addI n1 n2) (add n1 n2)
addI-add n1 n2 = ?

addI-commut' : (n1 n2 : Nat) -> Equal' (addI n1 n2) (addI n2 n1)
addI-commut' n1 n2 = ?
```

## Yet another definition of the addition 

- here is yet another definition of the addition
```
addR : Nat -> Nat -> Nat 
addR n1 Z = n1
addR n1 (S n2) = S (addR n1 n2) 
```

- prove the following properties 
- addR Z n = n
- addR assoc
- addR commut
- add = addR 

```
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
```
