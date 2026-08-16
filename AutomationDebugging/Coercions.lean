/-
Copyright (c) 2026 lean4-automation-debugging contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Ring

/-!
# Coercions, domains, and overloaded notation

Most "type mismatch" reports in arithmetic are really domain mistakes:
`ℕ` subtraction is truncated, `ℤ` subtraction is cancellative, and
`ℕ → ℝ` is a coercion that changes which lemmas match.
-/

/-! ### C36. Wrong domain (`ℕ` truncated subtraction vs `ℤ`) -/

/--
Goal / mathematical intent: cancellation `n - m + m = n`.

Broken candidate:
```
example (n m : ℕ) : n - m + m = n := by
  omega
```

Observed failure: the identity is false on `ℕ` when `m > n`
(truncated subtraction). `omega` cannot prove a false goal.
Switching the type to `ℤ` would prove a *different* statement about
a different operation.

Failure classification: wrong domain.

Diagnostic procedure:
1. Evaluate a counterexample: `n = 0`, `m = 1` gives `0 - 1 + 1 = 1 ≠ 0`.
2. The intended cancellative identity on `ℕ` is `m ≤ n → n - m + m = n`.
3. `#check Nat.sub_add_cancel`.
4. Reject the repair ` (n m : ℤ) : n - m + m = n ` unless the project
   actually meant integer subtraction.

Minimal repair: add the hypothesis `m ≤ n` and use `Nat.sub_add_cancel`.

Semantic faithfulness: remains a theorem about `ℕ` truncated
subtraction, with the necessary inequality. Domain is not changed to
`ℤ`.
-/
theorem CaseC36.sub_add_cancel {n m : ℕ} (h : m ≤ n) : n - m + m = n :=
  Nat.sub_add_cancel h

#check Nat.sub_add_cancel

/-! ### C37. Failed coercion (`ℕ` lemma on a `ℝ` term) -/

/--
Goal / mathematical intent: `(n : ℝ) * 1 = n`.

Broken candidate:
```
example (n : ℕ) : (n : ℝ) * 1 = n := by
  rw [Nat.mul_one]
```

Observed failure: `Nat.mul_one` expects a `ℕ` product. The product in
the goal is `ℝ`-multiplication after coercion. Rewrite match fails.

Failure classification: failed coercion.

Diagnostic procedure:
1. Hover / `#check` the goal: multiplication at `ℝ`.
2. `#check mul_one` — generic `MulOneClass` lemma.
3. Use the generic lemma, or rewrite before coercing.

Minimal repair: `rw [mul_one]`.
-/
theorem CaseC37.coe_mul_one (n : ℕ) : (n : ℝ) * 1 = n := by
  rw [mul_one]

/-! ### C38. Ambiguous coercion -/

/--
Goal / mathematical intent: `1 + 1 = 2` at `ℝ`, written with numerals
that could be `ℕ`, `ℤ`, or `ℝ`.

Broken candidate:
```
example : 1 + 1 = 2 := by
  exact Nat.add_left_eq_self.mp rfl
```

Observed failure: without an expected type, `1 + 1 = 2` elaborates as
`ℕ` (or becomes ambiguous in a polymorphic context). A `ℕ` lemma may
type-check against the elaborated `ℕ` goal while the *intent* was a
real identity. In a context with `[Add α] [One α]`, elaboration can
fail with "typeclass instance problem is stuck" or "ambiguous
overload".

Failure classification: ambiguous coercion / overloaded notation.

Diagnostic procedure:
1. Annotate the intended type: `(1 : ℝ) + 1 = 2`.
2. Then `norm_num` or `rfl` / `ring` at `ℝ`.

Minimal repair: ascribe `ℝ` and close with `norm_num`.

Semantic faithfulness: the reviewed theorem is the real identity, not
an accidental `ℕ` numeral lemma.
-/
theorem CaseC38.one_add_one_real : (1 : ℝ) + 1 = 2 := by
  norm_num

/-! ### C39. Overloaded notation / type ambiguity (`*` as `ℕ` vs `ℝ`) -/

/--
Goal / mathematical intent: distributivity of real multiplication
over addition, with a natural number in the term.

Broken candidate:
```
example (n : ℕ) (x : ℝ) : n * x + n * x = (n + n) * x := by
  rw [Nat.left_distrib]
```

Observed failure: `n * x` is not `ℕ`-multiplication. Lean coerces `n`
to `ℝ`, so the product is `ℝ`-multiplication. `Nat.left_distrib` does
not match. Alternatively, writing `n * x` without ascriptions can
leave a stuck metavariable for the multiplication instance.

Failure classification: overloaded notation / type ambiguity.

Diagnostic procedure:
1. Check the type of `n * x`: it should be `ℝ`.
2. `#check left_distrib` / `mul_add`.
3. Use the generic ring lemma `mul_add` / `add_mul`.

Minimal repair: `rw [← add_mul]` or `ring`.
-/
theorem CaseC39.two_nsmul_real (n : ℕ) (x : ℝ) :
    (n : ℝ) * x + n * x = (n + n) * x := by
  ring

#check add_mul
#check mul_add
