import Std.Data.HashSet
import Std.WP
import Std.Tactic.Do

open Std.WP Lean.Order


def mySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out


#eval mySum #[1, 2, 3, 4, 5]

theorem mySum_correct (l : Array Nat) : mySum l = l.sum := by
  generalize h : mySum l = x
  apply Id.of_run_eq_wp h
  vcgen
  case inv1 => exact fun pref suff out => pref.sum = out
  case vc1 => rfl
  case vc2 => grind
  case vc3 => grind

theorem mySum_correct_syntax (l : Array Nat) : mySum l = l.sum := by
  generalize h : mySum l = x
  apply Id.of_run_eq_wp h
  vcgen invariants
  · fun pref suff out => pref.sum = out
  with finish


theorem mySum_correct_vanilla (l : Array Nat) : mySum l = l.sum := by
  -- Turn the array into a list
  cases l with | mk l =>
  -- Unfold `mySum` and rewrite `forIn` to `foldl`
  simp [mySum]
  -- Generalize the inductive hypothesis
  suffices h : ∀ out, List.foldl (· + ·) out l = out + l.sum by simp [h]
  -- Grind away
  induction l with grind


def nodup (l : List Int) : Bool := Id.run do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

theorem nodup_correct (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_run_eq_wp h
  vcgen invariants
  ·  Invariant.withEarlyReturnNewDo
      (onReturn := fun ret seen => ret=false ∧ ¬l.Nodup)
      (onContinue := fun pref suff seen =>
      (∀ x, x ∈ seen ↔ x ∈ pref) ∧ pref.Nodup)
  with finish

structure Supply where
  counter : Nat
deriving Repr

def mkFresh : StateM Supply Nat := do
  let s ← get
  let n := s.counter
  modify fun s => { s with counter := s.counter + 1 }
  pure n


def mkFreshN (n : Nat) : StateM Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    let x ← mkFresh
    acc := acc.push x
  pure acc.toList


#eval mkFresh.run ⟨5⟩           -- (5, { counter := 6 })
#eval mkFresh.run' ⟨5⟩          -- 5
#eval (mkFreshN 3).run ⟨5⟩      -- ([5, 6, 7], { counter := 8 })
#eval (mkFreshN 3).run' ⟨0⟩     -- [0, 1, 2]
#eval (mkFreshN 0).run ⟨5⟩      -- ([], { counter := 5 })

theorem mkFreshN_correct (n : Nat) : ((mkFreshN n).run' s).Nodup := by
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_run'_eq_wp h
  vcgen[mkFreshN, mkFresh] invariants
  · fun pref suff acc state =>
      (∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup
  with finish

@[spec]
theorem mkFresh_spec (c : Nat) :
  ⦃fun state => state.counter = c⦄
  mkFresh
  ⦃fun r state => r = c ∧ c < state.counter⦄ := by
  vcgen [mkFresh] with finish



@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃fun _ => True⦄ mkFreshN n ⦃fun r _ => r.Nodup⦄ := by
  vcgen [mkFreshN] invariants
  · fun pref suff acc state =>
      (∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup
  with finish

theorem mkFreshN_correct_modular (n : Nat) :
    ((mkFreshN n).run' s).Nodup := by
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_run'_eq_wp h
  vcgen
