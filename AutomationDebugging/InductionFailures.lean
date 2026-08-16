/-
Copyright (c) 2026 lean4-automation-debugging contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Common

/-!
# Induction, quantifiers, and implication direction

Induction failures are usually a mismatch between the statement that
was inducted on and the statement that is needed. Quantifier-order
and implication-direction mistakes are semantic: the repaired proof
must not silently prove a different proposition.
-/

/-! ### C43. Induction hypothesis mismatch -/

/--
Goal / mathematical intent: `0 + n = n` by induction on `n`.

Broken candidate:
```
example (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      -- ih : 0 + n = n, but the user rewrites with add_assoc as if
      -- the IH were 0 + (n + 1) = n + 1 already
      rw [Nat.add_assoc]
```

Observed failure: `Nat.add_assoc` does not match `0 + n.succ`. The IH
is `0 + n = n`. The successor case needs `Nat.succ_eq_add_one` /
`Nat.add_succ` to expose `0 + n` inside `0 + n.succ`.

Failure classification: induction hypothesis mismatch.

Diagnostic procedure:
1. Print the IH: `0 + n = n`.
2. Unfold the successor in the *goal*, not in the IH.
3. `#check Nat.add_succ` — `a + n.succ = (a + n).succ`.
4. `rw [Nat.add_succ, ih]`.

Minimal repair: rewrite `add_succ`, then apply the IH.

Semantic faithfulness: same identity `0 + n = n`.

Robustness: `Nat.zero_add` is the library lemma; the inductive proof
is kept here to exhibit the IH.
-/
theorem CaseC43.zero_add (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.add_succ, ih]

#check Nat.add_succ
#check Nat.zero_add

/-! ### C44. Incorrect induction variable -/

/--
Goal / mathematical intent: `n + m = m + n` by induction on `n`.

Broken candidate:
```
example (n m : ℕ) : n + m = m + n := by
  induction m with
  | zero => rw [Nat.add_zero, Nat.zero_add]
  | succ m ih =>
      -- IH is n + m = m + n, but the goal after succ-on-m is
      -- n + m.succ = m.succ + n, which needs add_succ on *both* sides
      -- in a different pattern than induction on n.
      rw [ih]
```

Observed failure: `rw [ih]` looks for `n + m` as a subterm of
`n + m.succ = m.succ + n` and does not match the right-hand side.
The induction variable `m` is usable, but the rewrite of the IH is
the wrong shape. A common sibling mistake is to induct on a variable
that does not appear in the remaining goal.

Failure classification: incorrect induction variable / IH mismatch.

Diagnostic procedure:
1. Choose the variable whose constructor is unfolded by the library
   lemmas you have (`Nat.add_succ` unfolds the right argument).
2. For commutativity, induction on `n` plus `Nat.succ_add` /
   `Nat.add_succ` is the standard shape.
3. After `induction n`, the IH must be applied to the *same* `m`.

Minimal repair: induct on `n`, unfold `succ_add` and `add_succ`.
-/
theorem CaseC44.add_comm (n m : ℕ) : n + m = m + n := by
  induction n with
  | zero => rw [Nat.zero_add, Nat.add_zero]
  | succ n ih => rw [Nat.succ_add, Nat.add_succ, ih]

/-! ### C45. Wrong quantifier order -/

/--
Goal / mathematical intent: there is a bound `M` that dominates every
`n` — which is *false* on `ℕ`. The intended *true* statement is the
swapped quantifier: every `n` has some `M ≥ n` (for example `M = n`).

Broken candidate (false statement):
```
example : ∃ M : ℕ, ∀ n : ℕ, n ≤ M := by
  refine ⟨0, ?_⟩
  intro n
  omega
```

Observed failure: after choosing a witness `M`, `n` is still arbitrary.
`omega` cannot prove `n ≤ 0` for all `n`. Proving the swapped
`∀ n, ∃ M, n ≤ M` is *not* a proof of the original goal.

Failure classification: wrong quantifier order.

Diagnostic procedure:
1. Write the binders in order: `∃ M, ∀ n` vs `∀ n, ∃ M`.
2. A counterexample to `∃ M, ∀ n, n ≤ M` is unboundedness of `ℕ`.
3. Repair the *intent* (every natural is bounded by itself), not the
   false "global bound" statement.

Minimal repair: prove `∀ n, ∃ M, n ≤ M` with witness `n`.

Semantic faithfulness: the compiling theorem is the ∀∃ statement that
was intended. The ∃∀ statement is left unproved because it is false.
-/
theorem CaseC45.forall_exists_ge (n : ℕ) : ∃ M : ℕ, n ≤ M :=
  ⟨n, le_rfl⟩

/-! ### C46. Implication reversed -/

/-!
Goal / mathematical intent: `n = 0` implies `n ≤ 0`.

Broken candidate:
```
example (n : ℕ) : n ≤ 0 → n = 0 := by
  intro h
  exact Nat.eq_zero_of_le_zero h
```

That candidate actually proves the *converse*. If the *intent* was
`n = 0 → n ≤ 0`, then `exact Nat.eq_zero_of_le_zero` is the wrong
lemma: it reverses the implication.

A broken attempt at the intended direction:
```
example (n : ℕ) (h : n = 0) : n ≤ 0 := Nat.eq_zero_of_le_zero h
```
Observed failure: type mismatch, `n ≤ 0 → n = 0` applied to `n = 0`.

Failure classification: implication reversed.

Diagnostic procedure:
1. `#check Nat.eq_zero_of_le_zero` vs `#check Nat.le_zero_eq`.
2. Match implication direction to the goal.
3. For `n = 0 → n ≤ 0`, use `le_of_eq` or `rw [h]`.

Minimal repair: rewrite with `h`, then `Nat.le_refl`.
-/
#check Nat.eq_zero_of_le_zero
#check Nat.le_zero_eq

theorem CaseC46.eq_zero_imp_le_zero (n : ℕ) (h : n = 0) : n ≤ 0 := by
  rw [h]

/-- The converse is a different theorem and is recorded separately. -/
theorem CaseC46.le_zero_imp_eq_zero (n : ℕ) (h : n ≤ 0) : n = 0 :=
  Nat.eq_zero_of_le_zero h
