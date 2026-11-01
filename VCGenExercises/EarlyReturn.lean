import Std.WP
import Std.Tactic.Do
import Std.Data.HashSet
open Std.WP Lean.Order

set_option experimental.vcgen true

-- Lets `grind` work with the lattice operations inside `withEarlyReturnNewDo`.
attribute [local grind norm] Lean.Order.ofProp_prop_eq Lean.Order.meet_prop_eq_and
  Lean.Order.join_prop_eq_or Lean.Order.iSup_prop_eq_exists

namespace EarlyReturn

/-! ## `findAbove`

Returns the first element that is `≥ n`.

Two theorems, each needing only one half of the invariant:
* `findAbove_some` is about the early exit. Which part of the invariant does the work?
  Can the other part be trivial?
* `findAbove_none` is about the normal exit.
-/

def findAbove (n : Nat) (l : List Nat) : Option Nat := Id.run do
  for x in l do
    if n ≤ x then return some x
  return none

theorem findAbove_some (n : Nat) (l : List Nat) (y : Nat) :
    findAbove n l = some y → y ∈ l ∧ n ≤ y := by
  generalize h : findAbove n l = x
  apply Id.of_run_eq_wp h
  vcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret _ => ∀y, ret = some y → y ∈ l ∧ n ≤ y)
      (onContinue := fun pref suff _ =>
        ∀ x, x ∈ pref → ¬(n ≤ x))
  with finish

theorem findAbove_none (n : Nat) (l : List Nat) :
    findAbove n l = none → ∀ x ∈ l, x < n := by
  generalize h : findAbove n l  = x
  apply Id.of_run_eq_wp h
  vcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret _ => ret.isSome)
      (onContinue := fun pref suff _ =>
        ∀x,  x ∈ pref → x < n)
  with finish

/-! ## `contains`
-/

def contains (x : Nat) (l : List Nat) : Bool := Id.run do
  for y in l do
    if y = x then return true
  return false

theorem contains_correct (x : Nat) (l : List Nat) : contains x l = true ↔ x ∈ l := by
  generalize h : contains x l = r
  apply Id.of_run_eq_wp h
  vcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret _ => ret=True ∧ x ∈ l)
      (onContinue := fun pref suff _ =>
      ∀ y, y ∈ pref → ¬ (y=x))
  with finish


/-! ## `firstDup`

Same loop shape as `nodup` in Tutorial.lean, but the early return carries the duplicate.
-/

def firstDup (l : List Int) : Option Int := Id.run do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return some x
    seen := seen.insert x
  return none

/-- `l` splits at one occurrence of `d`,
    and `d` also appears in the part before it (`pre`). So `d` occurs at least twice. -/
theorem firstDup_some (l : List Int) (d : Int) :
    firstDup l = some d → ∃ pre post, l = pre ++ d :: post ∧ d ∈ pre := by
  generalize h : firstDup l = r
  apply Id.of_run_eq_wp h
  vcgen invariants
  · Invariant.withEarlyReturnNewDo
    (onReturn := fun ret seen => ∀y, ret = some y → ∃ pre post, l = pre ++ y :: post ∧ y ∈ pre)
    (onContinue := fun pref suff seen =>
    (∀ x, x ∈ seen ↔ x ∈ pref) ∧ pref.Nodup)
  with finish

theorem firstDup_none (l : List Int) : firstDup l = none ↔ l.Nodup := by
  generalize h : firstDup l = r
  apply Id.of_run_eq_wp h
  vcgen invariants
  · Invariant.withEarlyReturnNewDo
    (onReturn := fun ret seen => ret.isSome ∧ ¬ l.Nodup)
    (onContinue := fun pref suff seen =>
    (∀x, x ∈ seen ↔ x ∈ pref) ∧ pref.Nodup)
  with finish

/-! ## `findIdx`: a counter alongside the loop

This program finds the index of the first element that satisfies a predicate p
-/

def findIdx (p : Nat → Bool) (l : List Nat) : Option Nat := Id.run do
  let mut i := 0
  for x in l do
    if p x then return some i
    i := i + 1
  return none

theorem findIdx_none (p : Nat → Bool) (l : List Nat) :
    findIdx p l = none → ∀ x ∈ l, p x = false := by
    generalize h : findIdx p l = r
    apply Id.of_run_eq_wp h
    vcgen invariants
    · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret i=> ret.isSome)
      (onContinue := fun pref suff i =>
      (∀ x, x ∈ pref → p x = false) ∧ (i = pref.length))
    with finish


theorem findIdx_some (p : Nat → Bool) (l : List Nat) (i : Nat) :
    findIdx p l = some i →
      ∃ h : i < l.length, p l[i] ∧ ∀ (j : Nat) (hj : j < i), p l[j] = false := by
  generalize h : findIdx p l = r
  apply Id.of_run_eq_wp h
  vcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret i => ∀y, ret = some y → ∃ h : y < l.length , p l[y] ∧ ∀ (j : Nat) (hj : j < y), p l[j] = false)
      (onContinue := fun pref suff i =>
      (∀ x, x ∈ pref → p x = false) ∧ (i = pref.length))
  with finish


/-! ## `isSorted`
The helper lemma below gives `grind` the fact it can't find alone.
Grind lemmas : `all_goals grind [pairwise_le_of_mem, List.Pairwise.nil]` instead of `with finish`.
-/

theorem pairwise_le_of_mem {pref suff : List Nat} {p c : Nat} (hp : p ∈ pref) (hlt : c < p) :
    ¬ (pref ++ c :: suff).Pairwise (· ≤ ·) := by
  intro h
  rw [List.pairwise_append] at h
  have := h.2.2 p hp c (by simp)
  omega

def isSorted (l : List Nat) : Bool := Id.run do
  let mut prev := 0
  for x in l do
    if x < prev then return false
    prev := x
  return true

theorem isSorted_correct (l : List Nat) : isSorted l = true ↔ l.Pairwise (· ≤ ·) := by
  generalize h : isSorted l = r
  apply Id.of_run_eq_wp h
  vcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret prev => (ret = false ∧ ¬l.Pairwise (· ≤ ·)))
      (onContinue := fun pref suff prev => (∀x, x ∈ pref → prev ≥ x) ∧ (prev=0 ∨ prev ∈ pref) ∧ (pref.Pairwise (· ≤ ·)))
  all_goals grind [pairwise_le_of_mem, List.Pairwise.nil]

/-! ## `hasPairSum`: 2SUM with a `HashSet`
Spec : `∃ a b, List.Sublist [a,b] l ∧ a+b = target`
Two grind lemmas `pair_sublist_of_mem` and `pair_sublist_append_singleton`
-/

theorem pair_sublist_of_mem {a c : Int} {pref suff : List Int} (h : a ∈ pref) :
    List.Sublist [a, c] (pref ++ c :: suff) := by
  grind

grind_pattern pair_sublist_of_mem => a ∈ pref, pref ++ c :: suff

theorem pair_sublist_append_singleton {a b c : Int} {l : List Int} :
    List.Sublist [a, b] (l ++ [c]) ↔ List.Sublist [a, b] l ∨ (a ∈ l ∧ b = c) := by
  induction l <;> grind

def hasPairSum (target : Int) (l : List Int) : Bool := Id.run do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if target - x ∈ seen then return true
    seen := seen.insert x
  return false

theorem hasPairSum_correct (target : Int) (l : List Int) :
    hasPairSum target l = true ↔ ∃ a b, List.Sublist [a, b] l ∧ a + b = target := by
  generalize h : hasPairSum target l = r
  apply Id.of_run_eq_wp h
  vcgen invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret seen => ret = true ∧ ∃ a b, List.Sublist [a, b] l ∧ a + b = target)
      (onContinue := fun pref suff seen =>
      (∀ a b, List.Sublist [a,b] pref → a+b ≠ target) ∧ (∀x, x ∈ pref ↔ x ∈ seen))
  all_goals grind [pair_sublist_of_mem, pair_sublist_append_singleton]
end EarlyReturn
