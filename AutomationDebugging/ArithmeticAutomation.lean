/-
Copyright (c) 2026 lean4-automation-debugging contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Numeric and algebraic automation

Each tactic below has a problem class. Using it outside that class is
the typical failure. The repair is almost never "try a bigger tactic";
it is to identify the class and either switch procedure or supply a
missing hypothesis (nonzero, positivity, linearity).
-/

/-! ### C23. `norm_num` — closed numeric goals -/

/--
Natural problem class: equalities and inequalities on *closed* numeral
expressions (no free variables), including some casts and divisibility.

Success:
-/
theorem CaseC23.two_add_two : (2 : ℕ) + 2 = 4 := by
  norm_num

/--
Broken candidate:
```
example (n : ℕ) : n + 2 = 2 + n := by
  norm_num
```

Observed failure: `norm_num` does not solve identities in a free
variable. It reports that it could not close the goal.

Failure classification: arithmetic tactic used on unsupported goal.

Diagnostic procedure:
1. Ask whether every subterm is a closed numeral. Here `n` is free.
2. The class is commutativity, not numeric evaluation: `Nat.add_comm`
   or `ring` / `omega`.

Minimal repair: `exact Nat.add_comm n 2`.
-/
theorem CaseC23.add_comm_two (n : ℕ) : n + 2 = 2 + n :=
  Nat.add_comm n 2

/-! ### C24. `ring` and `ring_nf` — polynomial identities -/

/--
Natural problem class: equalities in commutative (semi)rings that hold
as polynomial identities.

Success:
-/
theorem CaseC24.sq_sub_sq (n m : ℤ) : n ^ 2 - m ^ 2 = (n + m) * (n - m) := by
  ring

/--
`ring_nf` rewrites a term into ring normal form without closing a
relation by itself. It is a normalization step.
-/
theorem CaseC24.ring_nf_example (n m : ℤ) :
    n + m + n = 2 * n + m := by
  ring_nf

/--
Broken candidate:
```
example (n m : ℝ) (h : n ≤ m) : n + 1 ≤ m + 1 := by
  ring
```

Observed failure: `ring` works on *equalities* of polynomials, not on
inequalities, and it does not consume `h`.

Failure classification: arithmetic tactic used on unsupported goal.

Diagnostic procedure:
1. Goal is an inequality, class of `linarith` / `omega`.
2. `#check add_le_add_right`.

Minimal repair: `exact add_le_add_right h 1` or `linarith`.
-/
theorem CaseC24.add_le_add_one {n m : ℝ} (h : n ≤ m) : n + 1 ≤ m + 1 := by
  linarith

/-! ### C25. `linarith` — linear inequalities in ordered rings -/

/--
Natural problem class: linear (in)equalities over `ℚ`/`ℝ`/`ℤ` with
hypotheses already in the context.

Success:
-/
theorem CaseC25.linear_real {a b c : ℝ} (h₁ : a ≤ b) (h₂ : b < c) : a < c + 1 := by
  linarith

/--
Broken candidate:
```
example {a b : ℝ} (h : a * a ≤ b * b) : |a| ≤ |b| := by
  linarith
```

Observed failure: the hypothesis is quadratic. `linarith` does not
expand products of variables. It fails to close the goal (and the
statement as written is also missing sign information for a naïve
linear reading).

Failure classification: arithmetic tactic used on unsupported goal
(nonlinear inequality).

Diagnostic procedure:
1. Count variable products. `a * a` is outside `linarith`.
2. Either use a dedicated lemma (`sq_le_sq`, `abs_le_abs`) or
   `nlinarith` *when* the nonlinear facts are in the supported fragment.

Minimal repair for a linear goal nearby: do not change the statement
to something `linarith` can prove. For a genuine linear neighbour:
-/
theorem CaseC25.linear_neighbour {a b : ℝ} (h : a ≤ b) : 2 * a ≤ 2 * b := by
  linarith

#check sq_le_sq

/-! ### C26. `nlinarith` — a nonlinear fragment -/

/--
Natural problem class: `linarith` plus some quadratic facts such as
`sq_nonneg`.

Success: `0 ≤ a * a` is `sq_nonneg`, which `nlinarith` knows.
-/
theorem CaseC26.sq_nonneg_add {a b : ℝ} : 0 ≤ a * a + b * b := by
  nlinarith

/--
Broken candidate:
```
example {a b : ℝ} : 0 ≤ a ^ 3 + b ^ 3 := by
  nlinarith
```

Observed failure: cubic forms are outside the fragment. The statement
is also false (`a = -1`). This is simultaneously an unsupported
tactic class *and* a semantic failure.

Failure classification: arithmetic tactic used on unsupported goal;
also syntactically attempted but semantically wrong if taken as a
theorem.

Diagnostic procedure:
1. Separate: is the statement true? No, not for all real `a b`.
2. Do not weaken to a different polynomial just to please `nlinarith`.
3. The intended true nearby statement is nonnegativity of squares.

Minimal repair: prove the true quadratic statement, not the false cubic.
-/
theorem CaseC26.sq_nonneg_pair {a b : ℝ} : 0 ≤ a ^ 2 + b ^ 2 := by
  nlinarith

/-! ### C27. `omega` — linear integer/natural arithmetic -/

/--
Natural problem class: linear goals in `ℕ`/`ℤ` (and `Fin`), including
many that `linarith` handles less natively on `ℕ`.

Success:
-/
theorem CaseC27.nat_pred {n : ℕ} (h : 3 ≤ n) : 1 ≤ n - 2 := by
  omega

/--
Broken candidate:
```
example {n : ℕ} : n * n ≥ n := by
  omega
```

Observed failure: `n * n` is nonlinear. `omega` rejects or fails.

Failure classification: arithmetic tactic used on unsupported goal.

Diagnostic procedure:
1. Product of two variable terms → not `omega`.
2. The true statement is `n ≤ n * n` on `ℕ`, proved by cases on `n`
   or `Nat.le_mul_of_pos_left` / `nlinarith` after a case split.

Minimal repair: case analysis on `n` (the nonlinear identity is true on `ℕ`), using
`Nat.le_mul_of_pos_right` in the successor case.
-/
theorem CaseC27.n_le_n_mul_n (n : ℕ) : n ≤ n * n := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n => exact Nat.le_mul_of_pos_right _ (Nat.succ_pos n)

/-! ### C28. Arithmetic tactic on a propositional goal -/

/--
Goal / mathematical intent: `P → P`.

Broken candidate:
```
example {P : Prop} : P → P := by
  omega
```

Observed failure: `omega` expects a numeric goal. A propositional
identity is the class of `intro; exact`.

Failure classification: arithmetic tactic used on unsupported goal.

Diagnostic procedure:
1. Read the target type: `Prop`, not `ℕ`/`ℤ`.
2. Switch mechanism: `intro h; exact h`.
-/
theorem CaseC28.imp_refl {P : Prop} : P → P :=
  fun h => h

/-! ### C29. Missing nonzero condition -/

/--
Goal / mathematical intent: `a / a = 1` in `ℝ`.

Broken candidate:
```
example {a : ℝ} : a / a = 1 := by
  simp [div_self]
```

Observed failure: `div_self` requires `a ≠ 0`. Without it the identity
is false at `a = 0` (`0 / 0 = 0` in Lean's field division). Automation
cannot invent the missing hypothesis.

Failure classification: missing nonzero condition.

Diagnostic procedure:
1. `#check div_self` — `a ≠ 0 → a / a = 1`.
2. The original *intent* is cancellation for nonzero `a`.
3. Adding `a ≠ 0` restores the intended theorem; changing `ℝ` to a
   group (where every element is invertible) would change the domain.

Minimal repair: take `h : a ≠ 0` and `exact div_self h`.

Semantic faithfulness: same division on `ℝ`; the nonzero hypothesis is
mathematically required, not a convenience for automation.
-/
theorem CaseC29.div_self_real {a : ℝ} (h : a ≠ 0) : a / a = 1 :=
  div_self h

#check div_self

/-! ### C30. Missing positivity condition -/

/--
Goal / mathematical intent: the inverse of a positive real is positive.

Broken candidate:
```
example {a : ℝ} (h : a ≠ 0) : 0 < a⁻¹ := by
  exact inv_pos.mpr h
```

Observed failure: `inv_pos` is `0 < a⁻¹ ↔ 0 < a`. The hypothesis
`a ≠ 0` does not imply `0 < a` (counterexample `a = -1`, where
`a⁻¹ = -1` is negative). Type mismatch: `0 < a` versus `a ≠ 0`.

Failure classification: missing positivity condition.

Diagnostic procedure:
1. `#check inv_pos` — biconditional with `0 < a`, not `a ≠ 0`.
2. The intended theorem is positivity, so the hypothesis must be
   `0 < a`. Replacing the conclusion by `a⁻¹ ≠ 0` would be a different
   theorem (`inv_ne_zero`).

Minimal repair: assume `0 < a`, apply `inv_pos.mpr`.

Semantic faithfulness: positivity of inversion, not mere invertibility.
-/
theorem CaseC30.inv_pos_of_pos {a : ℝ} (h : 0 < a) : 0 < a⁻¹ :=
  inv_pos.mpr h

#check inv_pos
#check inv_ne_zero
