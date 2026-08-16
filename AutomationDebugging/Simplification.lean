/-
Copyright (c) 2026 lean4-automation-debugging contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring

/-!
# Simplification

`simp` is a directed rewrite engine. It is the right tool when a goal
is supposed to reduce along a known `[simp]` set. It is the wrong tool
when the identity is a polynomial ring equation, when the simp set
would unfold past the intended normal form, or when a single named
lemma already closes the goal.

Auditability rule used in this file: prefer `simp only [...]` once the
lemma list is known. Keep a full `simp` only as a search step, not as
the reviewed proof.
-/

/-! ### C17. Simplifier cannot close the goal -/

/--
Goal / mathematical intent: `(n + m) ^ 2 = n ^ 2 + 2 * n * m + m ^ 2`.

Broken candidate:
```
example (n m : ℕ) : (n + m) ^ 2 = n ^ 2 + 2 * n * m + m ^ 2 := by
  simp
```

Observed failure: `simp` reduces some numerals and constructors but
does not expand the binomial identity. The goal remains.

Failure classification: simplifier cannot close goal.

Diagnostic procedure:
1. The target is a polynomial identity, the problem class of `ring`.
2. `simp?` reports whatever `[simp]` lemmas fired; they are not the
   binomial theorem.
3. Switch problem class: `ring` (or an explicit expansion via
   `Nat.succ` / `mul_add`).

Minimal repair: `ring`.

Semantic faithfulness: same binomial identity on `ℕ`.

Robustness: `ring` is the decision procedure for this class. An
explicit expansion is more reviewable but longer.
-/
theorem CaseC17.binomial_sq (n m : ℕ) :
    (n + m) ^ 2 = n ^ 2 + 2 * n * m + m ^ 2 := by
  ring

/-! ### C18. Simplifier changes too much -/

/--
Goal / mathematical intent: keep `n + 0` as an `add_zero` redex in a
hypothesis while simplifying the goal `True`... more realistically:
prove `n + 1 = Nat.succ n` without unfolding `Nat.add` into a recursor
term that no longer matches library lemmas.

Broken candidate:
```
example (n : ℕ) (h : n + 0 = n) : n + 1 = n.succ := by
  simp [Nat.add] at *
```

Observed failure: unfolding `Nat.add` at `*` turns both the hypothesis
and the goal into recursor applications. Subsequent lemmas that match
`_+_` notation fail. The proof may still be closable by `rfl`, but the
context is no longer in library normal form.

Failure classification: simplifier changes too much.

Diagnostic procedure:
1. Identify the intended normal form: `n + 1` versus `n.succ`.
2. `#check Nat.succ_eq_add_one` — `n.succ = n + 1`, the library lemma.
3. Do not unfold the definition of `Nat.add`.

Minimal repair: `rw [Nat.succ_eq_add_one]`.

Semantic faithfulness: definitional relationship of `succ` and `+ 1`.

Robustness: lemma-based rewrite survives changes to the internal
definition of `Nat.add`.
-/
theorem CaseC18.succ_eq_add_one (n : ℕ) : n.succ = n + 1 :=
  Nat.succ_eq_add_one n

#check Nat.succ_eq_add_one

/-! ### C19. `simp only` for auditability -/

/--
Goal / mathematical intent: `¬ (True ∧ False)`.

Broken candidate:
```
example : ¬ (True ∧ False) := by
  simp
```

This often *succeeds*, which is the trap: a reviewed proof that says
only `simp` does not record which lemmas were used. A later change to
the simp set can keep the line compiling while changing *why* it
compiles.

Failure classification: brittle proof depending on incidental simp
behavior (the successful-but-opaque variant).

Diagnostic procedure:
1. Use `simp?` once to print the lemma list.
2. Replace with `simp only` of that list.
3. Confirm the list is the intended propositional reduction
   (`and_false`, `not_false_eq_true`, …).

Minimal repair: `simp only [and_false, not_false_eq_true]`.

Semantic faithfulness: classical propositional identity, unchanged.

Robustness: `simp only` is the auditable form of a successful `simp`.
-/
theorem CaseC19.not_true_and_false : ¬ (True ∧ False) := by
  simp only [and_false, not_false_eq_true]

/-! ### C20. Unnecessary `simpa` -/

/--
Goal / mathematical intent: from `P ∧ Q` conclude `P`.

Broken candidate:
```
example {P Q : Prop} (h : P ∧ Q) : P := by
  simpa using h.left
```

Observed failure: this compiles, but `simpa` runs the simplifier and
then `exact`. Nothing needed simplification. The linter
`linter.unnecessarySimpa` flags this pattern.

Failure classification: unnecessary assumptions *of automation*
(here: unnecessary `simpa`).

Diagnostic procedure:
1. `#check And.left` — already the goal.
2. If `exact h.left` works, `simpa` is not a repair.

Minimal repair: `exact h.left`.

Semantic faithfulness: projection of a conjunction, unchanged.

Robustness: `exact` does not depend on the simp set.
-/
theorem CaseC20.and_left {P Q : Prop} (h : P ∧ Q) : P :=
  h.left

/-! ### C21. Brittle incidental `simp` behavior -/

/--
Goal / mathematical intent: `n + 0 + 0 = n`.

Broken candidate:
```
example (n : ℕ) : n + 0 + 0 = n := by
  simp
```

This may compile because `add_zero` is a `[simp]` lemma. It is brittle:
if a local `simp` attribute, a changed import, or a `simp [-add_zero]`
elsewhere in a larger proof changes the set, the line stops working
or overshoots.

Failure classification: brittle proof depending on incidental simp
behavior.

Diagnostic procedure:
1. Identify the two rewrites: `add_zero` twice, or `Nat.add_zero`.
2. Record them with `simp only` or `rw`.

Minimal repair: `simp only [add_zero]`.

Semantic faithfulness: adding zero, unchanged.

Robustness: `simp only [add_zero]` still uses the simplifier but with
a closed lemma list. `rw [add_zero, add_zero]` is even more explicit.
-/
theorem CaseC21.add_zero_zero (n : ℕ) : n + 0 + 0 = n := by
  simp only [add_zero]

theorem CaseC21.add_zero_zero_rw (n : ℕ) : n + 0 + 0 = n := by
  rw [add_zero, add_zero]

/-! ### C22. `simp at` versus `simp_all` -/

/--
Goal / mathematical intent: from `h : n + 0 = m` conclude `n = m`.

Broken candidate:
```
example (n m : ℕ) (h : n + 0 = m) : n = m := by
  simp
```

Observed failure: `simp` without a location simplifies the *goal*.
The goal is already `n = m` and does not contain `+ 0`. The redex is
in `h`. `simp` leaves the goal unchanged.

Failure classification: simplifier cannot close goal (wrong location).

Diagnostic procedure:
1. Find the redex: it is in `h`, not in the target.
2. `simp only [add_zero] at h` updates `h` to `n = m`.
3. Then `exact h`. `simpa [add_zero] using h` is acceptable when the
   simplified hypothesis *is* the goal.
4. `simp_all` would simplify every hypothesis and the goal; here that
   is more search surface than needed.

Minimal repair: `simp only [add_zero] at h; exact h`.

Semantic faithfulness: same equality after reducing `+ 0`.

Robustness: location-targeted `simp` is the smallest effect.
-/
theorem CaseC22.simp_at_hypothesis (n m : ℕ) (h : n + 0 = m) : n = m := by
  simp only [add_zero] at h
  exact h
