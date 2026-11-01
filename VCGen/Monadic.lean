/-
# Exercises: verifying monadic programs

These follow the "Hoare Triples" and "Composing Specifications" sections of the tutorial.
Every program here is a `StateM` program, so assertions take the state:

    ⦃fun s => pre⦄ prog ⦃fun r s => post⦄

Two tools you'll use:
* `vcgen [f]` unfolds `f`. Leave `f` out to make `vcgen` use `f`'s `@[spec]` lemma instead.
* A loop invariant in `StateM` gets the state as its last argument:
  `fun pref suff vars state => ...`

From `pop_spec` on, each spec is described in English. Write the statement yourself,
then prove it.

Solutions are in `Solutions/Monadic.lean`. Try each exercise before looking.
-/
import Std.WP
import Std.Tactic.Do
open Std.WP Lean.Order

set_option experimental.vcgen true

namespace Monadic

abbrev Stack := StateM (List Nat)

def push (x : Nat) : Stack Unit := modify (fun y => x :: y)

def pop : Stack (Option Nat) := do
  let x ← get
  match x with
  | [] => pure none
  | x :: xs =>
    set xs
    pure (some x)


#eval (push 5).run [1, 2]                  -- ((), [5, 1, 2])
#eval pop.run [5, 1, 2]                    -- (some 5, [1, 2])
#eval pop.run []                           -- (none, [])
#eval (do push 3; push 4; pop).run [1]     -- (some 4, [3, 1])
#eval (do let _ ← pop; pop).run [1, 2, 3]  -- (some 2, [3])

/-- `push x` puts `x` on top of the stack. -/
@[spec]
theorem push_spec (x : Nat) (xs : List Nat) :
    ⦃fun s => s = xs⦄ push x ⦃fun _ s => s = x :: xs⦄ := by
  vcgen [push] with finish

/-- `pop` returns the top element (or `none` on an empty stack) and removes it. -/
@[spec]
theorem pop_spec (xs : List Nat) :
  ⦃fun s => s = xs⦄
  pop
  ⦃fun val s => (xs=[] → val = none ∧ s=[]) ∧ (∀ h tail, xs = h :: tail → val = some h ∧ s = tail)⦄ := by
  vcgen[pop] with finish

def swapTop : Stack Unit := do
  match ← pop, ← pop with
  | some a, some b => push a; push b
  | _, _ => pure ()

/-- On a stack with at least two elements, `swapTop` swaps the top two. -/
@[spec]
theorem swapTop_spec (a : Nat) (b : Nat) (rest : List Nat) :
  ⦃fun s => s = a :: b :: rest⦄
  swapTop
  ⦃fun _ s => s = b :: a :: rest⦄ := by
  vcgen[swapTop] with finish

def addAll (l : List Nat) : StateM Nat Unit := do
  for x in l do
    modify (· + x)

#eval (addAll [1,2,3]).run 12

/-- `addAll l` adds the sum of `l` to the state. -/
@[spec]
theorem addAll_spec (l : List Nat) (n : Nat) :
  ⦃fun s => s=n⦄
  addAll l
  ⦃fun _ t=> t = n + l.sum⦄ := by
  vcgen[addAll] invariants
  · fun pref suff _ s => s = n + pref.sum
  with finish

end Monadic
