/-
Copyright (c) 2026 lean4-automation-debugging contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reviewer cases: semantic failures, under-specification, automation trade-offs

Compilation is not the acceptance criterion. This module records
proofs that Lean would accept for the *wrong* statement, statements
that are true but weaker than the intent, extra hypotheses that should
not be there, and a comparison of opaque automation with an explicit
proof of the same theorem.
-/

/-! ### C49. Syntactically attempted, semantically wrong statement -/

/-!
Goal / mathematical intent (false): every integer of the form
`n * n + n + 2` is even? More concretely, the classic false identity
`(n - m) + m = n` on `ℕ` without `m ≤ n` — already treated as a domain
error in C36. Here the false statement is algebraic:

`∀ a b : ℝ, a / b * b = a`.

Broken candidate:
```
example (a b : ℝ) : a / b * b = a := by
  ring
```

Observed failure: `ring` does not prove this, because it is false at
`b = 0`. A "successful" bad repair would be `ring` on the different
statement `a * b / b = a` still without `b ≠ 0`, or changing `ℝ` to a
group.

Failure classification: syntactically attempted but semantically wrong
statement.

Diagnostic procedure:
1. Counterexample: `a = 1`, `b = 0` gives `0 = 1` after Lean's
   `a / 0 = 0` convention? Check: `1 / 0 * 0 = 0 ≠ 1`.
2. The intended cancellation is `b ≠ 0 → a / b * b = a`.
3. `#check div_mul_cancel₀`.

Minimal repair: add `b ≠ 0`, use `div_mul_cancel₀`.

Semantic faithfulness: same real division; required nonzero hypothesis
added because the unrestricted statement is false. Domain stays `ℝ`.
-/
#check div_mul_cancel₀

theorem CaseC49.div_mul_cancel {a b : ℝ} (hb : b ≠ 0) : a / b * b = a :=
  div_mul_cancel₀ a hb

/-! ### C50. Proof compiles, statement is under-specified -/

/--
Goal / mathematical intent: `0` is the *unique* right identity of `ℕ`
addition.

Under-specified compiling statement:
`∃ z, ∀ n, n + z = n` — true, but does not mention uniqueness.
A proof of existence is not a proof of uniqueness.

Failure classification: proof compiles but statement is under-specified.

Diagnostic procedure:
1. Ask whether the intent was existence, uniqueness, or both.
2. `#check existsUnique_eq` / use `∃!`.
3. If uniqueness was intended, the statement must be `∃! z, ∀ n, n + z = n`.

Minimal repair: prove the unique-existence statement.

Semantic faithfulness: the `∃!` theorem is the intended one. The weak
`∃` form is kept as a named example of under-specification, not as a
substitute.
-/
theorem CaseC50.exists_right_identity : ∃ z : ℕ, ∀ n, n + z = n :=
  ⟨0, Nat.add_zero⟩

theorem CaseC50.existsUnique_right_identity :
    ∃! z : ℕ, ∀ n, n + z = n := by
  refine ⟨0, Nat.add_zero, ?_⟩
  intro z hz
  have := hz 0
  simp at this
  exact this

/-! ### C51. Unnecessary assumptions -/

/--
Goal / mathematical intent: `n + m = m + n`.

Broken candidate:
```
example (n m : ℕ) (h : n ≤ m) : n + m = m + n := Nat.add_comm n m
```

This compiles. The hypothesis `n ≤ m` is unused. Leaving it in the
statement changes the theorem: it is now a fact about ordered pairs,
not about all pairs. Callers must prove an inequality they do not
need.

Failure classification: unnecessary assumptions.

Diagnostic procedure:
1. Check whether `h` appears in the proof. It does not.
2. `#check Nat.add_comm` has no inequality binder.
3. Drop `h`.

Minimal repair: commutativity with no order hypothesis.

Semantic faithfulness: restored to the full domain `ℕ × ℕ`.
-/
theorem CaseC51.add_comm (n m : ℕ) : n + m = m + n :=
  Nat.add_comm n m

/-! ### C52. `grind` versus an explicit proof -/

/--
Goal / mathematical intent: `a + b + c = c + b + a` on `ℕ`.

Opaque automation:
```
example (a b c : ℕ) : a + b + c = c + b + a := by
  grind
```

`grind` is appropriate as a *diagnostic* closer for messy equalities
in a commutative monoid. For a three-term commute, it is opaque:
reviewers cannot see which lemmas fired, and a later `grind` failure
is harder to localize.

Failure classification: unnecessarily broad automation (successful).

Diagnostic procedure:
1. `grind` closes the goal in development.
2. Replace it with `ring` (problem class: polynomial / comm semiring
   identity) or an explicit `calc`.
3. Keep `grind` out of the reviewed proof unless the goal is in the
   fragment `grind` is designed for *and* an explicit proof is
   unreasonably long.

Minimal repair: `ring`, which is the named decision procedure for
this class.

Trade-off: `grind` maximizes closing power; `ring` is reviewable and
restricted to the correct class; `calc` is fully explicit.
-/
theorem CaseC52.add_comm_three (a b c : ℕ) : a + b + c = c + b + a := by
  ring

theorem CaseC52.add_comm_three_calc (a b c : ℕ) : a + b + c = c + b + a := by
  calc
    a + b + c = c + (a + b) := by rw [Nat.add_comm]
    _ = c + (b + a) := by rw [Nat.add_comm a b]
    _ = c + b + a := by rw [← Nat.add_assoc]

/-! ### C53. `aesop` versus an explicit proof -/

/--
Goal / mathematical intent: `P ∨ Q → Q ∨ P`.

Opaque automation: `aesop` typically succeeds by cases on `Or`.
The explicit proof is the reviewable artefact.

Trade-off: `aesop` is useful to *find* the case split. The recorded
proof should still show the two constructors.
-/
theorem CaseC53.or_comm {P Q : Prop} : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP => exact Or.inr hP
  | inr hQ => exact Or.inl hQ

/-! ### C54. Insufficient assumptions (cannot invent data) -/

/-!
Goal / mathematical intent: from `n ≤ m` conclude `n + k ≤ m`.

Broken candidate:
```
example (n m k : ℕ) (h : n ≤ m) : n + k ≤ m := by
  omega
```

Observed failure: false when `k > 0` and `n = m`. `omega` fails.
Adding `k = 0` would change the statement; dropping `k` would too.

Failure classification: insufficient assumptions.

Diagnostic procedure:
1. Counterexample: `n = m = 0`, `k = 1`.
2. The intended true theorem is `n ≤ m → n + k ≤ m + k`.
3. `#check Nat.add_le_add_right`.

Minimal repair: prove the translation-invariant form, which is the
intended inequality.

Semantic faithfulness: do not set `k = 0` merely to make `omega`
succeed.
-/
#check Nat.add_le_add_right

theorem CaseC54.add_le_add_right {n m k : ℕ} (h : n ≤ m) : n + k ≤ m + k :=
  Nat.add_le_add_right h k
