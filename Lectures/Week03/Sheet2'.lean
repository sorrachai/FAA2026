/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivier Fischer, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false

/-! ## Inductive Types

An inductive type is defined by specifying its **constructors**. The constructors
describe all possible ways to create values of the new type.

A constructor may:
* take no arguments, such as `Color.Red`
* take arguments of another type, such as `Option.some 5`
* take arguments of the type currently being defined. Such a constructor is
  called *recursive* and can be used to build structures such as lists and
  binary trees.

Every value of an inductive type is obtained by applying one of its constructors
a finite number of times.
-/

-- # Inductive type: Color 🟥🟩🟦
inductive Color
| Red : Color
| Green : Color
| Blue : Color

#check Color
#check Color.Red

-- Lean can infer the type of the constructor
inductive Color'
| Red
| Green
| Blue

def favoriteColor : Color → String
| Color.Red   => "Red is lovely"
| Color.Green => "Green is calming."
| Color.Blue  => "Blue is clear."

#eval favoriteColor Color.Red

def favoriteColor2 (c : Color) : String :=
  match c with
  | .Red   => "Red is lovely"
  | .Green => "Green is calming."
  | .Blue  => "Blue is clear."


-- # Inductive type: Atomic element and a function
inductive OptionNat
| none
| some : ℕ → OptionNat

-- We can also define a new type called `MyOption` parameterized by a type α.
inductive MyOption (α : Type)
| none
| some : α → MyOption α

#check OptionNat

#check OptionNat.none
#check OptionNat.some
#check OptionNat.some 100

#check MyOption.some 50
#check MyOption.some "mystring"

-- Alternatively, some : α → MyOption α  can be written as some (a : α)
inductive MyOption' (α : Type)
| none
| some (a : α)


-- **Exercise 6**
-- Return the option's element if it has one and the default otherwise
def getOrElse {α : Type} (option : MyOption α) (default : α) : α :=
  match option with
  | .none   => default
  | .some x => x


-- # Recursive Inductive Type: Nat
inductive MyNat
| zero
| succ (n : MyNat)
-- terms of type MyNat: zero, succ zero, succ (succ zero) ...

#check MyNat.zero
#check MyNat.succ (.zero)
#check MyNat.succ (.succ (.zero))
#check MyNat.zero.succ.succ

#check Nat.zero
#check Nat.succ (Nat.zero)

-- Equivalently, we can write it with explicit constructor types
inductive MyNat2
| zero : MyNat2
| succ : MyNat2 → MyNat2


-- # Recursive Inductive Type: List
namespace MyList

-- We define a type `MyList.List` in the namespace here analogous
-- to the built-in type `List` to illustrate how it works
inductive List (α : Type)
| nil
| cons (a : α) (l : List α )
-- The type `List α` is either
-- 1. an empty list (`nil`) or
-- 2. `cons x xs` where `x : α` (head: first element) and `xs : List α` (tail)
-- terms of type List α: nil, cons x nil, cons x (cons y nil), ...

#check List ℕ
#check (List.nil : List ℕ) -- []
#check (List.cons 1 .nil) -- [1]
#check (List.cons 2 (.cons 1 (.nil))) -- [2, 1]

-- Equivalently, it can be written this way using arrow notation
inductive ListF (α : Type)
| nil : ListF α
| cons : α → ListF α → ListF α

#check List
#check List.nil
#check List.cons

-- Example: compute the length of a list
def len {α : Type} : List α → ℕ
| .nil => 0
| .cons _ xs => 1 + len xs

-- Example: append a list ys to a list xs
def append {α : Type} (l1 : List α) (l2 : List α) : List α :=
  match l1 with
  | .nil => l2
  | .cons head tail => .cons head (append tail l2)

-- Example: get i-th element (with MyOption.some) or MyOption.none if out of bounds
def get {α : Type} (l : List α) (i : ℕ) : MyOption α :=
  match l with
  | .nil => .none
  | .cons head tail =>
    match i with
    | 0 => .some head
    | j+1 => get tail j

def get' {α : Type} (l : List α) (i : ℕ) : MyOption α :=
  match l, i with
  | .nil        , _   => .none
  | .cons head _, 0   => .some head
  | .cons _ tail, j+1 => get tail j


-- **Exercise 7**
-- Define a type of binary tree:
-- a leaf without value or a node with a value and two subtrees

-- This is also how the Mathlib type BinaryTree is defined
inductive BinaryTree (α : Type)
| nil
| node  (value : α) (left : BinaryTree α) (right : BinaryTree α)

-- Count the number of (non-leaf) nodes of a binary tree
def num_nodes {α : Type} : BinaryTree α → ℕ
| .nil => 0
| .node _ left right => 1 + num_nodes left + num_nodes right

end MyList
