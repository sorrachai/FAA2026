/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false

-- Typeclass as polymorphism in functional programming languages

namespace FAA

-- Let's say we define a structure of combine operation:
structure Combine (α : Type) where
  combine : α → α → α

#check Combine.combine

-- define double that uses Combine operation
def double {α} (s : Combine α) (x : α) : α :=
  s.combine x x

#check double

def natadd : Combine ℕ := {combine := fun a ↦ fun b ↦ a+b}
def mul : Combine ℕ := {combine := fun a ↦ fun b ↦ a*b}
def string : Combine String := {combine := fun a ↦ fun b ↦ a++b}

#eval double natadd 10
#eval double mul 10
#eval double string "123"

-- Upshot: too much effort to pass around the implementation of combine all the time.
-- *Idea*: typeclass makes the operation `instance implicit` and let Lean figure out which instance
-- to instantiate through the process called `typeclass resolution`

namespace WithTypeClass

class Combine (α : Type) where
  combine : α → α → α

#check Combine.combine
-- now, combine as an implicit structure which depends on `α`

-- We can give each instantiation as a rule
instance instCombineNat : Combine Nat where
  combine := Nat.add

instance instCombineFloat : Combine Float where
  combine := fun a ↦ fun b ↦ a+b

instance instCombineStr : Combine String where
  combine := fun s t => s ++ t

-- We can use typeclass to overload the operation
def twice {α} [Combine α] (x : α) : α := Combine.combine x x

-- *Typeclass resolution* is Lean’s way of finding a term to
-- fill an instance-implicit argument, written [C]. This is similar to Prolog.
-- register instances using `instance` command

#eval twice 10
#eval twice (1.0)
#eval twice "test"
--#eval twice (-10)

-- Instance synthesis can be checked using the #synth command.
#synth Combine Nat
#synth Combine Float

-- We can define a product rule for the combine operation.
instance prodCombine {α β : Type} [Combine α] [Combine β] :
    Combine (α × β) where
  combine x y :=
    (Combine.combine x.1 y.1, Combine.combine x.2 y.2)

-- -- We can define a product rule for the combine operation.
-- instance prodCombine' {α β : Type} [Combine α] [Combine β] :
--     Combine (α × β) where
--   combine x y :=
--     (x.1, y.2)

#eval twice ((10 : Nat), "ha")   -- (20, "haha")
#check Combine (Nat × String)

set_option trace.Meta.synthInstance.answer true in
#synth Combine (Nat × String)

-- Explicitly select a rule
#eval
  letI : Combine (Nat × String) := prodCombine
  twice ((10 : Nat), "ha")
-- (20, "haha")

/-!
Exercise: Combining functions

Given f g : α → β, combine them by combining their outputs
at each input.

1. Complete the instance.
2. Predict the result of the #eval below.
3. Explain which instances Lean needs to construct.
-/

instance funCombine {α β : Type} [Combine β] :
    Combine (α → β) where
  combine f g := sorry

-- Hint: the result must be a function `fun x => ...`.
-- #eval (twice (fun n : Nat => (n, "ha"))) 10

set_option trace.Meta.synthInstance.answer true in
#synth Combine (Nat → Nat × String)

end WithTypeClass

-- Priority in typeclass
-- sometimes there are non-unique choices of available typeclasses
-- we can specify priority

class Point where
  a : ℕ
  b : ℕ

instance (priority := default + 1) i1 : Point where
  a := 1
  b := 1

instance i2 : Point where
  a := 2
  b := 2

example : Point.a = 1 :=
  rfl

#synth Point

instance (priority := default + 2) i3 : Point where
  a := 3
  b := 3

example : Point.a = 3 :=
  rfl

#synth Point


end FAA
