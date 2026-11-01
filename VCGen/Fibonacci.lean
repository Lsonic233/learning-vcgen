/-
# Memoized Fibonacci in `StateM`

`fibMemo` caches results in a `HashMap` held in the state.
-/
import Std.WP
import Std.Tactic.Do
import Std.Data.HashMap
open Std.WP Lean.Order
open Std (HashMap)

set_option experimental.vcgen true

namespace Fibonacci

@[simp]
def fib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def fibMemo (n : Nat) : StateM (HashMap Nat Nat) Nat := do
  match (← get).get? n with
  | some v => pure v
  | none =>
    match n with
    | 0 => modify (·.insert 0 1); pure 1
    | 1 => modify (·.insert 1 1); pure 1
    | n + 2 =>
      let a ← fibMemo (n + 1)
      let b ← fibMemo n
      modify (·.insert (n + 2) (a + b))
      pure (a + b)

/-- If every cached entry is correct, `fibMemo n` returns `fib n` and keeps every entry correct. -/
@[spec]
theorem fibMemo_spec (n : Nat) :
  ⦃fun cache => ∀x, cache.contains x = true → fib x = cache[x]!⦄
  fibMemo n
  ⦃fun val s => val = fib n ∧ ∀x, s.contains x = true → fib x = s[x]!⦄ := by
  fun_induction fibMemo n with
  | case1 t ih =>
    match t, ih with
    | 0, _ => vcgen[fibMemo] <;> grind[fib]
    | 1, _ => vcgen[fibMemo] <;> grind[fib]
    | n+2, ⟨h1, h2⟩ => vcgen[fibMemo] <;> grind[fib]

/-- Starting from an empty cache, `fibMemo n` computes `fib n`. -/
theorem fibMemo_correct (n : Nat) : (fibMemo n).run' ∅ = fib n := by
  generalize h : (fibMemo n).run' ∅ = x
  apply StateM.of_run'_eq_wp h
  vcgen with finish

end Fibonacci
