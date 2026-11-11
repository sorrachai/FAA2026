/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner
-/
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Optional Sheet for Week 8: Monads

In this sheet you will learn about monads, which also form the basis for many formal complexity
models (e.g., CSLib's `TimeM` or `FreeM`). The sheet has four parts:

1. **Monads:** what a monad is, some examples, and Lean's `do`-notation.
2. **Lawful monads:** the three monad laws. You show that `Option'` and `List'` are lawful
   (Exercises 1 and 2), and that not every monad is lawful (Exercise 3).
3. **The free monad:** programs as syntax trees that can be interpreted in different monads,
   and why this is a more trustworthy basis for complexity models than `TimeM`
   (Exercises 4 to 6). Understanding what a free monad is might be helpful for
   coming up with more convincing complexity models in the project.
4. **Verifying `do` programs:** you prove that bubble sort, written with two `for` loops,
   sorts its input (Exercise 7).

This sheet is optional.
-/

namespace Monad

/-!
## Part 1: Monads

On a high level, a monad `M : Type → Type` is a wrapper that takes a type `α`
and forms a type `M α` that contains elements of `α`, together with some additional
bookkeeping data. A monad is a structure that implements two functions:

* `pure : α → M α` takes an element of `α` and packages it into an element of `M α`.
* `bind : M α → (α → M β) → M β` takes a monadic element `ma : M α` and a function
  `f : α → M β`. It "extracts" an element `a : α` from `ma`, applies `f` to it to obtain
  `f a : M β`, and combines the bookkeeping data of `ma` with that of `f a`.

In Lean, (a simplified version of) the class `Monad` looks as follows. We call it `SimpleMonad`
so that it does not clash with Lean's `Monad`:
-/

class SimpleMonad (M : Type → Type) where
  pure {α : Type} : α → M α
  bind {α β : Type} : M α → (α → M β) → M β

/-!
The actual class `Monad` contains some further operations (e.g. `map : (α → β) → M α → M β`),
but they all have default implementations in terms of `pure` and `bind`. So to define a monad,
it suffices to give `pure` and `bind`.

From now on, we only use Lean's `Monad`, because Lean's notation is built on top of it:
`m >>= f` for `bind m f`, `return x` for `pure x` and the `do` notation (see below).
-/

/--
### Example: `Option α`

`Option α` is a monad that you should already know. It models a computation that either succeeds
and produces a value `some x` or fails and returns no value `none`. If a computation has failed
at some point, then we propagate the `none` value through any further computation.
-/
inductive Option' (α : Type) : Type where
  | some : α → Option' α
  | none : Option' α

instance : Monad Option' where
  pure x := .some x
  bind m f :=
    match m with
    | .some x => f x
    | .none => .none

/--
### Example: `List α`

`List α` is another monad that you have seen. It models computations with several possible
results (nondeterminism): `m >>= f` runs the computation `f` on every result of `m` and collects
all outcomes.
-/
inductive List' (α : Type) : Type where
  | nil : List' α
  | cons : α → List' α → List' α

namespace List'

/-- Appends two lists. -/
def append {α : Type} : List' α → List' α → List' α
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (append xs ys)

/-- Applies `f` to every element of the list and concatenates the results. -/
def flatMap {α β : Type} : List' α → (α → List' β) → List' β
  | .nil, _ => .nil
  | .cons x xs, f => append (f x) (flatMap xs f)

/-- Converts a Lean list into a `List'`. -/
def ofList {α : Type} : List α → List' α
  | [] => .nil
  | x :: xs => .cons x (ofList xs)

end List'

instance : Monad List' where
  pure x := .cons x .nil
  bind := List'.flatMap

/-! These two lemmas let you unfold `pure` and `>>=` for `List'`. -/
@[simp] theorem List'.pure_eq {α : Type} (x : α) : (pure x : List' α) = .cons x .nil := rfl

@[simp] theorem List'.bind_eq {α β : Type} (m : List' α) (f : α → List' β) :
    m >>= f = m.flatMap f := rfl

/--
### Example: `Writer α`

The writer monad stores a value together with a log of messages. The `bind` operation combines
the bookkeeping by concatenating the logs.
-/
structure Writer' (α : Type) : Type where
  ret : α
  log : List String

instance : Monad Writer' where
  pure x := ⟨x, []⟩
  bind m f :=
    let r := f m.ret
    ⟨r.ret, m.log ++ r.log⟩

/-- Writes the message `msg` to the log. -/
def Writer'.tell (msg : String) : Writer' Unit := ⟨(), [msg]⟩

/--
### Example: `TimeM`

`TimeM α` allows you to propagate an additional running time through your programs. The
`bind` operation combines the runtime values by adding them up.
-/
structure TimeM' (α : Type) : Type where
  ret : α
  time : ℕ

instance : Monad TimeM' where
  pure x := ⟨x, 0⟩
  bind m f :=
    let r := f m.ret
    ⟨r.ret, m.time + r.time⟩

/-- A computation that takes one unit of time. -/
def TimeM'.tick : TimeM' Unit := ⟨(), 1⟩

/--
  Inside a `do` block, `✓ x` first takes one unit of time and then runs `x`, i.e. it stands for
  `TimeM'.tick >>= fun _ ↦ x`. This is the same notation as for CSLib's `TimeM`.
-/
macro "✓" body:doElem : doElem => `(doElem| do TimeM'.tick; $body:doElem)

@[simp] theorem TimeM'.ret_pure {α : Type} (x : α) : (pure x : TimeM' α).ret = x := rfl
@[simp] theorem TimeM'.time_pure {α : Type} (x : α) : (pure x : TimeM' α).time = 0 := rfl
@[simp] theorem TimeM'.ret_bind {α β : Type} (m : TimeM' α) (f : α → TimeM' β) :
    (m >>= f).ret = (f m.ret).ret := rfl
@[simp] theorem TimeM'.time_bind {α β : Type} (m : TimeM' α) (f : α → TimeM' β) :
    (m >>= f).time = m.time + (f m.ret).time := rfl

/-!
  The notation `>>=` allows you to neatly compose monadic computations: in `m >>= f`, the
  computation `m` on the left is threaded through the function `f` on the right.
-/

/-- Division that fails when dividing by zero. -/
def safeDiv (a b : ℕ) : Option' ℕ :=
  if b = 0 then
    .none
  else
    .some (a / b)

/-- Computes `(((a / b) / c) / d) / e`, failing if one of the divisions fails. -/
def divDiv (a b c d e : ℕ) : Option' ℕ :=
  safeDiv a b
    >>= (safeDiv · c)
    >>= (safeDiv · d)
    >>= (safeDiv · e)

#eval divDiv 1000 5 2 4 5 -- some 5
#eval divDiv 1000 5 0 4 5 -- none

/-- All pairs `(x, y)` with `x` in `xs` and `y` in `ys`. -/
def pairs (xs ys : List' ℕ) : List' (ℕ × ℕ) :=
  xs >>= fun x ↦ ys >>= fun y ↦ pure (x, y)

#eval pairs (.ofList [1, 2]) (.ofList [3, 4]) -- (1, 3), (1, 4), (2, 3), (2, 4)

/-- Binary search from HW6, which now also counts the number of queries to `p`. -/
def binSearchT (p : ℕ → Bool) (lo hi : ℕ) : TimeM' ℕ :=
  if lo < hi then
    let mid := (lo + hi) / 2
    TimeM'.tick >>= fun _ ↦
      if p mid then binSearchT p lo mid else binSearchT p (mid + 1) hi
  else
    pure hi
termination_by hi - lo

#eval binSearchT (fun k ↦ 30 ≤ k) 0 100 -- { ret := 30, time := 7 }

/-!
  While `>>=` makes the composition of monadic computations significantly cleaner, Lean
  provides a domain-specific language (DSL) just for monadic computations.
  A monadic block is started with the keyword `do` (similar to how `by` starts a tactic block).
  Among others, a `do` block supports the following syntax:

  * `let x ← m` "runs" `m : M α` and names its result `x : α`.
    It stands for `m >>= fun x ↦ (rest of the block)`.
  * `m` on its own line (for `m : M Unit`) runs `m` and discards the result.
    It stands for `m >>= fun _ ↦ (rest of the block)`.
  * `let x := e` is an ordinary (non-monadic) `let`, a local definition.
  * `return e` stands for `pure e` at the end of a block. As in imperative languages, a
    `return` in the middle of a block exits the whole block early.
  * `✓ x` (only for `TimeM'`) takes one unit of time and then runs `x`.
  * `if`, `match`, and even `for` loops and mutable variables (`let mut`) can be used.

  The idea of `do` blocks is that you work with elements of `α` instead of `M α`, while the
  monadic bookkeeping happens implicitly. They also let you write programs in an imperative
  style, which Lean translates back into ordinary (functional) programs.
-/

def divDiv' (a b c d e : ℕ) : Option' ℕ := do
  let res1 := a
  let res2 ← safeDiv res1 b
  let res3 ← safeDiv res2 c
  let res4 ← safeDiv res3 d
  let res5 ← safeDiv res4 e
  return res5

def pairs' (xs ys : List' ℕ) : List' (ℕ × ℕ) := do
  let x ← xs
  let y ← ys
  return (x, y)

/-!
  Note that `divDiv'` is not literally the same term as `divDiv`: the `do` block nests the binds
  to the right (`safeDiv a b >>= fun res2 ↦ (safeDiv res2 c >>= ...)`), while `>>=` associates to
  the left. They are nonetheless equal: here we check this by a case distinction, but in general
  it is a consequence of the associativity law (Part 2).
-/
example (a b c d e : ℕ) : divDiv' a b c d e = divDiv a b c d e := by
  by_cases hb : b = 0 <;> by_cases hc : c = 0 <;> by_cases hd : d = 0 <;> by_cases he : e = 0 <;>
    simp only [divDiv, divDiv', safeDiv, hb, hc, hd, he, ↓reduceIte] <;> rfl
example : pairs' = pairs := rfl

def binSearchT' (p : ℕ → Bool) (lo hi : ℕ) : TimeM' ℕ := do
  if lo < hi then
    let mid := (lo + hi) / 2
    ✓ if p mid then
      binSearchT' p lo mid
    else
      binSearchT' p (mid + 1) hi
  else
    return hi
termination_by hi - lo

#eval binSearchT' (fun k ↦ 30 ≤ k) 0 100 -- { ret := 30, time := 7 }

/-- The factorial function, which logs its intermediate results. -/
def factLog : ℕ → Writer' ℕ
  | 0 => do
    Writer'.tell "0! = 1"
    return 1
  | n + 1 => do
    let r ← factLog n
    Writer'.tell s!"{n + 1}! = {(n + 1) * r}"
    return (n + 1) * r

#eval factLog 4 -- { ret := 24, log := ["0! = 1", "1! = 1", "2! = 2", "3! = 6", "4! = 24"] }

/-!
### Example: `Id α`

The simplest monad of all is the identity monad `Id α`: `Id α` is just `α`, `pure` is the
identity map and `>>=` is function application. Together with `Id.run : Id α → α`, it allows you
to write ordinary functions in an imperative style with mutable variables and `for` loops.

For example, we can implement bubble sort with two nested `for` loops (this would be more
cumbersome to write as a functional program). Here `[i:j]` is the range `i, i+1, ..., j-1`
(note that `j` is excluded) and `arr[j]!` is the `j`'th element of the array `arr`.
-/

/-- Sorts a list using bubble sort. -/
def bubbleSort (xs : List ℕ) : List ℕ := Id.run do
  let mut arr := xs.toArray
  let n := arr.size
  for i in [0:n] do
    for j in [0:n - 1 - i] do
      if arr[j]! > arr[j + 1]! then
        arr := arr.swapIfInBounds j (j + 1)
  return arr.toList

#eval bubbleSort [5, 2, 9, 1, 5, 6, 0] -- [0, 1, 2, 5, 5, 6, 9]

/-!
## Part 2: Lawful monads

The class `Monad` only fixes the *types* of `pure` and `bind`, so nothing prevents us from
writing nonsensical instances. Lean defines various additional notions of monads; we will only
look at what is called a **lawful monad**. A lawful monad encodes computations which satisfy
properties that we intuitively expect from (almost) all computations. Specifically, we call a
monad lawful if it satisfies the following properties:

  1) Left identity:

            pure x >>= f = f x

  2) Right identity:

            m >>= pure = m

  3) Associativity:

            (m >>= f) >>= g = m >>= (fun x ↦ f x >>= g)

Lean's actual class `LawfulMonad` additionally contains laws that relate `bind` to the other
operations of `Monad` (such as `map`). We call our simplified version `LawfulMonad'`.
-/

class LawfulMonad' (M : Type → Type*) [Monad M] : Prop where
  pure_bind {α β : Type} (x : α) (f : α → M β) : pure x >>= f = f x
  bind_pure {α : Type} (m : M α) : m >>= pure = m
  bind_assoc {α β γ : Type} (m : M α) (f : α → M β) (g : β → M γ) :
    (m >>= f) >>= g = m >>= fun x ↦ f x >>= g

/-!
  **Exercise 1**

  Show that `Option'` is a lawful monad.
-/
instance : LawfulMonad' Option' where
  pure_bind x f := by
    sorry
  bind_pure m := by
    sorry
  bind_assoc m f g := by
    sorry

/-!
  **Exercise 2**

  Show that `List'` is a lawful monad.

  Hint: Use `induction m with`. Note that the induction hypothesis is stated with `>>=`, while
  `simp` rewrites `>>=` to `List'.flatMap` in the goal (using `List'.bind_eq`). So either use
  `simp_all [...]`, which also simplifies the induction hypothesis, or first apply
  `simp only [List'.bind_eq] at ih`.
-/

-- You may freely use the following theorems in your solution:
theorem List'.append_nil {α : Type} (xs : List' α) : xs.append .nil = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List'.append, ih]

theorem List'.append_assoc {α : Type} (xs ys zs : List' α) :
    (xs.append ys).append zs = xs.append (ys.append zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List'.append, ih]

theorem List'.flatMap_append {α β : Type} (xs ys : List' α) (f : α → List' β) :
    (xs.append ys).flatMap f = (xs.flatMap f).append (ys.flatMap f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List'.append, List'.flatMap, ih, List'.append_assoc]

instance : LawfulMonad' List' where
  pure_bind x f := by
    sorry
  bind_pure m := by
    sorry
  bind_assoc m f g := by
    sorry

/-!
  **Exercise 3**

  Not every monad is lawful. Consider the following version of `TimeM'`, where `pure` already
  costs one unit of time. Show that it is not lawful.
-/

structure BadTimeM (α : Type) : Type where
  ret : α
  time : ℕ

instance : Monad BadTimeM where
  pure x := ⟨x, 1⟩
  bind m f :=
    let r := f m.ret
    ⟨r.ret, m.time + r.time⟩

theorem not_lawful_badTimeM : ¬ LawfulMonad' BadTimeM := by
  sorry

/-!
## Part 3: The free monad

Each monad we have seen so far models some additional aspect of computation:

* `Option α` models failing computations
* `List α` models nondeterminism (several possible results)
* `Writer α` models logging
* `TimeM α` models running time

The free monad doesn't execute anything. Instead, it records a program as a syntax tree of
abstract operations and leaves their meaning unspecified. We can later assign meaning to these
abstract operations by providing one (or several) interpreters.

The abstract operations are described by a signature `Sig : Type → Type`. An element
`op : Sig ι` for some type `ι` is an operation that, when performed, returns an answer of
type `ι`. For example, the following signature has a single abstract operation `query i`,
which asks an (unknown) predicate `p` whether `p i` holds and returns the answer as a `Bool`.
-/

inductive Sig : Type → Type where
  | query (i : ℕ) : Sig Bool

/-!
A program in the free monad over `Sig` is a tree, where

* a leaf `pure a` is a finished computation with result `a`
* an intermediate node `liftBind op cont` performs the operation `op : Sig ι` and,
  depending on its answer `i : ι`, continues with the program `cont i`.
-/

/--
  The free monad over a signature `F` (this is CSLib's `FreeM`).
-/
inductive FreeM (F : Type → Type) (α : Type) where
  | pure (a : α) : FreeM F α
  | liftBind {ι : Type} (op : F ι) (cont : ι → FreeM F α) : FreeM F α

namespace FreeM

variable {F : Type → Type}

/-- Replaces every leaf `pure a` of `m` by the tree `f a`. -/
def bind {α β : Type} : FreeM F α → (α → FreeM F β) → FreeM F β
  | .pure a, f => f a
  | .liftBind op cont, f => .liftBind op (fun i ↦ (cont i).bind f)

instance : Monad (FreeM F) where
  pure := .pure
  bind := FreeM.bind

/-! These two lemmas let you unfold `pure` and `>>=` for `FreeM F`. -/
@[simp] theorem pure_eq {α : Type} (a : α) : (return a : FreeM F α) = .pure a := rfl

@[simp] theorem bind_eq {α β : Type} (m : FreeM F α) (f : α → FreeM F β) :
    m >>= f = m.bind f := rfl

/-- The program that performs the single operation `op` and returns its answer. -/
def lift {ι : Type} (op : F ι) : FreeM F ι := .liftBind op .pure

/-!
  **Exercise 4**

  Show that `FreeM F` is a lawful monad.

  Hint: Use `induction m with` and `simp_all [FreeM.bind]` (see the hint of Exercise 2).
-/
instance : LawfulMonad' (FreeM F) where
  pure_bind x f := by
    sorry
  bind_pure m := by
    sorry
  bind_assoc m f g := by
    sorry

/-!
  The name "free" comes from algebra: just like the free group over a set `S` consists of all
  words over `S` and satisfies no equations except those forced by the group axioms, `FreeM F`
  consists of all programs over `F` and satisfies no equations except the monad laws.

  An interpreter gives meaning to a program in some monad `M`. It only has to know how to
  `handle` every single abstract operation, the rest is determined by the structure of the tree.
  (In CSLib, `interp` is called `FreeM.liftM`.)
-/
def interp {M : Type → Type} [Monad M] {α : Type} (handle : {ι : Type} → F ι → M ι) :
    FreeM F α → M α
  | .pure a => return a
  | .liftBind op cont => handle op >>= fun i ↦ (cont i).interp handle

/-!
  **Exercise 5**

  Show that interpreting a program into a *lawful* monad `M` respects the monad structure:
  a single operation is interpreted as itself, and interpreting `m >>= f` is the same as
  first interpreting `m` and then interpreting `f`. (Together with `interp handle (pure a) =
  pure a`, which holds by definition, this says that `interp handle` is a *monad morphism*.)

  Hint: In both proofs, you have to use the laws of `M`, i.e. `LawfulMonad'.pure_bind`,
  `LawfulMonad'.bind_pure` and `LawfulMonad'.bind_assoc`.
-/

-- **(a)** Prove the following theorem.
theorem interp_lift {M : Type → Type} [Monad M] [LawfulMonad' M]
    (handle : {ι : Type} → F ι → M ι) {ι : Type} (op : F ι) :
    (lift op).interp handle = handle op := by
  sorry

-- **(b)** Prove the following theorem.
theorem interp_bind {M : Type → Type} [Monad M] [LawfulMonad' M]
    (handle : {ι : Type} → F ι → M ι) {α β : Type} (m : FreeM F α) (f : α → FreeM F β) :
    (m >>= f).interp handle = m.interp handle >>= fun a ↦ (f a).interp handle := by
  sorry

end FreeM

/-!
  Binary search in the free monad: in contrast to `binSearchT` from Part 1, the program knows
  neither the predicate `p` nor the cost model. It can only ask queries.
-/
def binSearchQ (lo hi : ℕ) : FreeM Sig ℕ := do
  if lo < hi then
    let mid := (lo + hi) / 2
    -- model comparisons with abstract operations
    let b ← FreeM.lift (Sig.query mid)
    if b then
      binSearchQ lo mid
    else
      binSearchQ (mid + 1) hi
  else
    return hi
termination_by hi - lo

/-!
  So far, we have

  1. written a signature `Sig` of abstract operations, and
  2. written an algorithm `binSearchQ` that performs its elementary operations only through
     the abstract operations of `Sig`.

  Now we can give these operations any meaning we like by choosing an interpreter. Below are
  two examples, one that counts queries (time complexity) and one that logs them:
-/

/-- Answers queries using `p`, charging one unit of time per query. -/
def answerT (p : ℕ → Bool) : {ι : Type} → Sig ι → TimeM' ι
  | _, .query i => ⟨p i, 1⟩

/-- Answers queries using `p`, logging every query. -/
def answerW (p : ℕ → Bool) : {ι : Type} → Sig ι → Writer' ι
  | _, .query i => ⟨p i, [s!"p {i} = {p i}"]⟩

-- The same program, interpreted in two different monads:
#eval (binSearchQ 0 100).interp (answerT (fun k ↦ 30 ≤ k)) -- { ret := 30, time := 7 }
#eval (binSearchQ 0 100).interp (answerW (fun k ↦ 30 ≤ k)) -- { ret := 30, log := [...] }

/-!
  **Exercise 6**

  Show that interpreting `binSearchQ` with `answerT p` gives exactly `binSearchT p` from Part 1,
  i.e. the same result *and* the same running time.

  Hint: Use `fun_induction binSearchT p lo hi` and unfold `binSearchQ` once with
  `rw [binSearchQ]`. In the recursive case, distinguish the cases `p mid = false` and
  `p mid = true` with `cases hp : p mid`. The definitions `FreeM.lift`, `FreeM.bind`,
  `FreeM.interp` and `answerT` are useful for `simp`.
-/
theorem interp_binSearchQ (p : ℕ → Bool) (lo hi : ℕ) :
    (binSearchQ lo hi).interp (answerT p) = binSearchT p lo hi := by
  sorry

/-!
### Why the free monad? (`FreeM` vs. `TimeM`)

Compare `binSearchT` from Part 1 with `binSearchQ`. Both compute the same result and both
report 7 queries (by Exercise 6, they always agree), so why bother with the free monad?

**1. Cheating becomes much harder.** In `TimeM'` (and in CSLib's `TimeM`), the running time is
just a number that the *author of the algorithm* writes down using `tick`. Nothing checks that
the ticks match what the algorithm actually does (the documentation of CSLib's `TimeM` says
explicitly that time annotations are trusted). Additionally, the algorithm has full access to its
input. For example, the following "algorithm" returns the correct result and claims to need no
time at all:
-/

def binSearchCheat (p : ℕ → Bool) (lo hi : ℕ) : TimeM' ℕ :=
  pure (binSearchT p lo hi).ret

-- Wow, that's a really fast binary search
#eval binSearchCheat (fun k ↦ 30 ≤ k) 0 100 -- { ret := 30, time := 0 }

/-!
With the free monad, the model of computation and the algorithm are separated:

* The signature `Sig` together with the interpreter `answerT`, which fixes the cost of each
  operation, forms the *query model*. It can be specified once in a separate file, which is
  reviewed carefully and then trusted.
* An algorithm is just a term `prog : FreeM Sig ℕ`. It does not get `p` as an argument, so
  the *only* way to learn something about `p` is to ask `FreeM.lift (Sig.query i)`, and each
  such query is charged by the interpreter, not by the author of the algorithm. There is no
  `tick` that can be forgotten and no way to set the time to `0`.

So instead of trusting the ticks of every single algorithm, we only have to trust the (small)
file containing the model. Note that between two queries, a program can still do arbitrary
computations for free. Therefore, the time only counts how many queries to the abstract oracle
the computation makes.

**2. Universal quantification.** Since programs and their meaning are separate objects, we can
quantify over each of them:

* Over all *oracles*: a statement such as `∀ p, (prog.interp (answerT p)).time ≤ k` holds for
  *every* `p`, so it is a worst-case bound.
* Over all *interpreters*: Exercise 5 holds for *every* lawful monad `M` and every `handle`.
  We prove it once and can then reuse it for every cost model (counting, logging, ...).
* Over all *algorithms*: this makes **lower bounds** expressible. For example, the following
  proposition says that every program which finds the first `true` of a monotone `p` on
  `[0, n]` needs at least `log 2 (n + 1)` queries for some `p`:
-/

def SearchLowerBound (n : ℕ) : Prop :=
  ∀ prog : FreeM Sig ℕ,
    (∀ p : ℕ → Bool, Monotone p → p n = true →
      let r := (prog.interp (answerT p)).ret
      p r = true ∧ ∀ k < r, p k = false) →
    ∃ p : ℕ → Bool, Monotone p ∧ p n = true ∧
      Nat.log 2 (n + 1) ≤ (prog.interp (answerT p)).time

/-!
Why does this hold? Couldn't a program implement the comparisons itself, without asking any
queries? No, and the reason is the order of the quantifiers: `prog` is a *single fixed tree*
that is chosen before `p`, and it does not get `p` as an argument. To compare by itself, it
would have to evaluate `p mid`, but `p` is not in scope when we write `prog`. It only enters
through `prog.interp (answerT p)`, which uses `p` to answer the `query` nodes of the tree and
for nothing else.

* A program that hard-codes a predicate, e.g. `pure 30`, makes no queries, but it is only
  correct for `p = (30 ≤ ·)`. It returns the wrong result for `p = (31 ≤ ·)`, so it does not
  satisfy the correctness assumption, and `SearchLowerBound` says nothing about it.
* For a correct program, the result only depends on the answers (`true` or `false`) along the
  path that is taken through the tree. If `prog` made at most `d` queries for every `p`, it
  could reach at most `2 ^ d` leaves, so it would have at most `2 ^ d` different results.
  However, the `n + 1` predicates `p(t) = (t ≤ ·)` for `t = 0, ..., n` are monotone, satisfy
  `p(t) n = true` and need `n + 1` different results (namely `t`). Hence for some `p`, the
  program makes at least `log 2 (n + 1)` queries, and `answerT` charges one unit of time for
  each of them.

This is exactly what goes wrong with `TimeM'`: the analogous statement quantifies over all
algorithms `alg : (ℕ → Bool) → TimeM' ℕ`, which get `p` as an argument, and is simply *false*:
`binSearchCheat` evaluates `p` itself and solves the problem in time `0`. The same would happen
with the free monad if we allowed `prog : (ℕ → Bool) → FreeM Sig ℕ`: then the program
`fun p ↦ pure (binSearchT p 0 n).ret` is correct and makes no queries at all.

So lower bounds in a model based on the free monad are only meaningful if the program can access
its input *only* through the abstract operations defined in the signature. For comparison-based
sorting, for example, the program should only get the length `n` and an operation
`cmp i j : Sig Bool` that compares the elements at positions `i` and `j`, and it should return a
permutation. If it gets the list itself, it can compare (or even sort) the elements for free.

Proving `SearchLowerBound n` for all `n` is a challenge.
-/

/-!
## Part 4: Verifying `do` programs

Finally, we prove that `bubbleSort` from Part 1 sorts its input. To reason about a `do` block,
we have to understand what Lean translates it to. A loop `for x in l do body` becomes
`forIn l s f`, where `s` holds the current values (think of a state monad) of the mutable
variables and `f x s` runs `body` once and returns the new values of the mutable variables,
wrapped in `ForInStep.yield` (or in `ForInStep.done` if the loop is left with `break`).
For example, `forIn` on lists is defined as follows (we call it `forInList`):
-/

def forInList {M : Type → Type} [Monad M] {α σ : Type} :
    List α → σ → (α → σ → M (ForInStep σ)) → M σ
  | [], s, _ => pure s
  | x :: xs, s, f => do
    match ← f x s with
    | .done s' => pure s'
    | .yield s' => forInList xs s' f

/-!
In the identity monad, a loop without `break` is therefore just a fold (`List.foldl`).
To keep the proofs readable, we give names to the body of the inner loop and to the inner loop.
-/

/-- The body of the inner loop: swaps `arr[j]` and `arr[j + 1]`
if they are in the wrong order. -/
def bubbleStep (arr : Array ℕ) (j : ℕ) : Array ℕ :=
  if arr[j]! > arr[j + 1]! then
    arr.swapIfInBounds j (j + 1)
  else
    arr

/-- The inner loop: `bubbleStep` for `j = 0, 1, …, k - 1`. -/
def bubblePass (arr : Array ℕ) (k : ℕ) : Array ℕ :=
  (List.range k).foldl bubbleStep arr

/-!
  The following lemmas describe what `bubbleStep` and `bubblePass` do. You can use them without
  proving them. Note that `bubbleStep arr j` puts the minimum of `arr[j]!` and `arr[j + 1]!` at
  position `j` and their maximum at position `j + 1`.
-/

@[simp] theorem size_bubbleStep (arr : Array ℕ) (j : ℕ) :
    (bubbleStep arr j).size = arr.size := by
  unfold bubbleStep
  split <;> simp

theorem getElem!_bubbleStep (arr : Array ℕ) (j k : ℕ) (hj : j + 1 < arr.size) :
    (bubbleStep arr j)[k]! =
      if k = j then
        min arr[j]! arr[j + 1]!
      else if k = j + 1 then
        max arr[j]! arr[j + 1]!
      else arr[k]! := by
  have hj₀ : j < arr.size := by omega
  by_cases hk : k < arr.size
  · unfold bubbleStep
    split_ifs <;> simp_all [getElem!_pos] <;> omega
  · have hk' : ¬k < (bubbleStep arr j).size := by simp [hk]
    rw [getElem!_neg arr k hk, getElem!_neg (bubbleStep arr j) k hk']
    split_ifs <;> omega

theorem bubblePass_succ (arr : Array ℕ) (k : ℕ) :
    bubblePass arr (k + 1) = bubbleStep (bubblePass arr k) k := by
  simp [bubblePass, List.range_succ]

@[simp] theorem size_bubblePass (arr : Array ℕ) (k : ℕ) :
    (bubblePass arr k).size = arr.size := by
  induction k with
  | zero => rfl
  | succ k ih => simp [bubblePass_succ, ih]

/-!
  To prove that `bubbleSort` is correct, we use the following invariant for the outer loop:
  after `i` iterations, the last `i` elements are sorted, and each of them is at least as large
  as all elements in front of it. We express this as follows.
-/

/--
  Every element at a position `b ≥ m` is at least as large as all elements in front of it.
  In particular, `SortedFrom arr 0` says that `arr` is sorted.
-/
def SortedFrom (arr : Array ℕ) (m : ℕ) : Prop :=
  ∀ a b, a < b → m ≤ b → b < arr.size → arr[a]! ≤ arr[b]!

/-!
  **Exercise 7**

  Show that `bubbleSort` sorts its input. We call a list `l` sorted if `l.Pairwise (· ≤ ·)`,
  i.e. if `l[a] ≤ l[b]` for all positions `a < b`.
-/

/-- **(a)** Show that the two `for` loops of `bubbleSort` are two nested folds.
  Hint: `simp` knows the lemma `List.forIn_pure_yield_eq_foldl`, which turns a `for` loop whose
  body is of the form `pure (.yield _)` into a `List.foldl`. The body of the inner loop is
  an `if` whose two branches are of this form. You can pull `pure` and `.yield` out of the `if`
  with `simp only [bubbleSort, ←apply_ite]`. Lean unfolds `[0:n]` to `List.range' 0 n`, which
  is the same as `List.range n` by `List.range_eq_range'`. -/
theorem bubbleSort_eq (xs : List ℕ) :
    bubbleSort xs = ((List.range xs.length).foldl
      (fun arr i ↦ bubblePass arr (xs.length - 1 - i)) xs.toArray).toList := by
  sorry

/-- **(b)** Show that the inner loop moves the largest of `arr[0]!, ..., arr[k]!` to position `k`.
  Hint: Use induction on `k` together with `bubblePass_succ` and `getElem!_bubbleStep`.
  `omega` can deal with `min` and `max`. -/
theorem bubblePass_max (arr : Array ℕ) (k : ℕ) (hk : k < arr.size) (a : ℕ) (ha : a ≤ k) :
    (bubblePass arr k)[a]! ≤ (bubblePass arr k)[k]! := by
  sorry

/-- **(c)** Show that the inner loop does not destroy the invariant `SortedFrom arr m` as long as
  it only swaps elements in front of position `m`. -/
theorem sortedFrom_bubbleStep (arr : Array ℕ) (j m : ℕ) (hj : j + 1 < m)
    (h : SortedFrom arr m) : SortedFrom (bubbleStep arr j) m := by
  sorry

theorem sortedFrom_bubblePass (arr : Array ℕ) (k m : ℕ) (hk : k < m)
    (h : SortedFrom arr m) : SortedFrom (bubblePass arr k) m := by
  sorry

/-- **(d)** Show that one iteration of the outer loop extends the sorted part by one element. -/
theorem sortedFrom_bubblePass_self (arr : Array ℕ) (k : ℕ) (hk : k < arr.size)
    (h : SortedFrom arr (k + 1)) : SortedFrom (bubblePass arr k) k := by
  sorry

/-- **(e)** Conclude that `bubbleSort` sorts its input.
  Hint: Prove by induction on `i` that after `i ≤ n` iterations of the outer loop, the array
  has size `n` and satisfies `SortedFrom` for `n - i`. The lemmas `List.range_succ`,
  `List.foldl_append`, `List.pairwise_iff_getElem` and `getElem!_pos` might be useful. -/
theorem bubbleSort_sorted (xs : List ℕ) : (bubbleSort xs).Pairwise (· ≤ ·) := by
  sorry

end Monad
