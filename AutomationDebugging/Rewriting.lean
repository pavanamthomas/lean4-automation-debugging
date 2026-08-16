/-
Copyright (c) 2026 lean4-automation-debugging contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Common

/-!
# Rewriting

Failures in this module are almost always *match* failures: the lemma
does not unify with a subterm of the goal, or it unifies in the wrong
direction. The diagnostic habit is: print the lemma with `#check`,
compare binders and implicit arguments, then rewrite a smaller
convertible subterm rather than the whole goal.
-/

/-! ### C09. Wrong rewrite direction -/

/--
Goal / mathematical intent: rewrite `n + 0` into `n` using `Nat.add_zero`.

Broken candidate:
```
example (n : ℕ) : n = n + 0 := by
  rw [Nat.add_zero]
```

Observed failure: `rw [Nat.add_zero]` looks for a subterm matching the
*left* side `n + 0`. The goal `n = n + 0` has `n + 0` on the right, so
the default direction does not match the occurrence we meant (and may
leave the goal unchanged or fail depending on occurrence selection).

More clearly the dual mistake:
```
example (n : ℕ) : n + 0 = n := by
  rw [← Nat.add_zero]
```
looks for `n` to replace by `n + 0`, which is the opposite of the intent.

Failure classification: failed rewrite match (wrong direction).

Diagnostic procedure:
1. `#check Nat.add_zero` — `∀ n, n + 0 = n`.
2. Identify which side of the goal is the *redex*.
3. Use `rw [Nat.add_zero]` to replace `n + 0` by `n`.
   Use `rw [← Nat.add_zero]` only to expand `n` into `n + 0`.

Minimal repair: rewrite in the direction that matches the redex.

Semantic faithfulness: same identity `n + 0 = n`.

Robustness: spelling the direction is cheaper than adding `simp`.
-/
theorem CaseC09.add_zero_right (n : ℕ) : n + 0 = n := by
  rw [Nat.add_zero]

theorem CaseC09.eq_add_zero (n : ℕ) : n = n + 0 := by
  rw [← Nat.add_zero n]

#check Nat.add_zero

/-! ### C10. Lemma does not syntactically match -/

/--
Goal / mathematical intent: commute `n + (m + 1)`.

Broken candidate:
```
example (n m : ℕ) : n + (m + 1) = (m + 1) + n := by
  rw [Nat.add_comm m n]
```

Observed failure: `Nat.add_comm m n` has type `m + n = n + m`, which does
not occur as a subterm. The subterm is `n + (m + 1)`, so the arguments
must be `n` and `m + 1`.

Failure classification: failed rewrite match (theorem does not
syntactically match).

Diagnostic procedure:
1. `#check Nat.add_comm` — `∀ a b, a + b = b + a`.
2. Zoom in on the exact subterm: `n + (m + 1)`.
3. Instantiate as `Nat.add_comm n (m + 1)`, or use uninstantiated
   `rw [Nat.add_comm]` and let unification pick the occurrence.

Minimal repair: `rw [Nat.add_comm n (m + 1)]`.

Semantic faithfulness: commutativity of addition, unchanged.

Robustness: instantiated `rw` is more stable than occurrence-index `rw [Nat.add_comm]`.
-/
theorem CaseC10.add_comm_succ (n m : ℕ) : n + (m + 1) = m + 1 + n := by
  rw [Nat.add_comm n (m + 1)]

#check Nat.add_comm

/-! ### C11. Coercion prevents a rewrite match -/

/--
Goal / mathematical intent: after coercing `n : ℕ` to `ℝ`, rewrite
`(n : ℝ) + 0`.

Broken candidate:
```
example (n : ℕ) : (n : ℝ) + 0 = n := by
  rw [Nat.add_zero]
```

Observed failure: `Nat.add_zero` rewrites a `ℕ`-addition. The goal
addition is `ℝ`-addition on a coerced `n`. Unification does not find
`n + 0` at type `ℕ`.

Failure classification: failed coercion (rewrite lemma at the wrong
type) / failed rewrite match.

Diagnostic procedure:
1. Check types: `(n : ℝ) + 0` has type `ℝ`.
2. `#check add_zero` at the generic `AddZeroClass` lemma, or
   `add_zero (n : ℝ)`.
3. Do not use a `ℕ` lemma on a `ℝ` term.

Minimal repair: `rw [add_zero]`.

Semantic faithfulness: the statement is an identity in `ℝ` after the
canonical coercion `ℕ → ℝ`. The repair does not change that coercion.

Robustness: generic algebraic lemmas survive type change; `Nat.*`
lemmas do not.
-/
theorem CaseC11.coe_add_zero (n : ℕ) : (n : ℝ) + 0 = n := by
  rw [add_zero]

#check add_zero
#check Nat.add_zero

/-! ### C12. Implicit argument mismatch on rewrite -/

/--
Goal / mathematical intent: rewrite with `mul_inv_cancel` at a real.

Broken candidate:
```
example {a : ℝ} (h : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [mul_inv_cancel]
```

Observed failure: `mul_inv_cancel` in a group (every element invertible)
has no `≠ 0` hypothesis. In `GroupWithZero` / fields the lemma needs
the nonzero proof as an explicit argument (often implicit in the
statement but not synthesizable from the goal alone). Lean reports
an unsolved metavariable or a rewrite that cannot find a match
because `h` was not supplied.

Failure classification: implicit argument mismatch.

Diagnostic procedure:
1. `#check @mul_inv_cancel` and `#check mul_inv_cancel₀` / `div_self`.
2. Inspect which arguments are implicit (`{}`) versus instance
   `[GroupWithZero]` versus explicit `(h : a ≠ 0)`.
3. Pass `h` explicitly: `rw [mul_inv_cancel₀ h]`.

Minimal repair: supply the nonzero proof to the field lemma.

Semantic faithfulness: still `a * a⁻¹ = 1` under `a ≠ 0` in `ℝ`.

Robustness: explicit `h` is reviewable; relying on implicit synthesis
from a `NeZero` instance is the next most robust option.
-/
theorem CaseC12.mul_inv_cancel_real {a : ℝ} (h : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [mul_inv_cancel₀ h]

#check mul_inv_cancel₀
#check @mul_inv_cancel₀

/-! ### C13. Multiple rewrites and local rewriting -/

/--
Goal / mathematical intent: from `a = b` and `c = d` conclude
`a + c = b + d` at `ℕ`, rewriting only in the goal.

Broken candidate:
```
example (a b c d : ℕ) (h₁ : a = b) (h₂ : c = d) : a + c = b + d := by
  rw [h₁, h₂] at *
```

Observed failure: `rw ... at *` rewrites hypotheses as well as the goal.
After rewriting `h₁` and `h₂` become `b = b` and `d = d`, which is
harmless here but destroys the original equalities if they are needed
later. This is a local-versus-global rewriting mistake.

Failure classification: simplifier / rewrite changes too much
(local versus global effect), applied to `rw`.

Diagnostic procedure:
1. Default `rw [h₁, h₂]` rewrites the goal only.
2. Use `rw [h₁] at h` only when that hypothesis is the intended target.
3. Avoid `at *` unless every location should change.

Minimal repair: `rw [h₁, h₂]` on the goal.

Semantic faithfulness: additivity of equality, unchanged.

Robustness: goal-only rewrite keeps hypotheses intact for later steps.
-/
theorem CaseC13.add_eq_add (a b c d : ℕ) (h₁ : a = b) (h₂ : c = d) :
    a + c = b + d := by
  rw [h₁, h₂]

/-! ### C14. `calc` for a chained equality -/

/--
Goal / mathematical intent: `(n + m) + k = k + (m + n)`.

Broken candidate:
```
example (n m k : ℕ) : n + m + k = k + (m + n) := by
  rw [Nat.add_comm n m, Nat.add_assoc]
```

Observed failure: after commuting `n + m`, the association and the
final commute of `k` still do not match in one shot; a rewrite sequence
without an intermediate display is hard to diagnose when it fails
mid-chain.

Failure classification: failed rewrite match (multi-step identity
presented as a single rewrite).

Diagnostic procedure:
1. Write the chain in `calc` so each step is a closed equality.
2. Check each justification with `#check`.

Minimal repair: a three-step `calc`.

Semantic faithfulness: commutativity and associativity of `ℕ` addition.

Robustness: `calc` is more reviewable than a long `rw` list; `abelf` /
`ring` would also close this but hide the steps.
-/
theorem CaseC14.add_reassoc (n m k : ℕ) : n + m + k = k + (m + n) := by
  calc
    n + m + k = m + n + k := by rw [Nat.add_comm n m]
    _ = k + (m + n) := by rw [Nat.add_comm]

/-! ### C15. Congruence -/

/--
Goal / mathematical intent: from `a = b` conclude `f a = f b`.

Broken candidate:
```
example {α β : Type} (f : α → β) (a b : α) (h : a = b) : f a = f b := by
  rw [h]
  -- alternatively, a mistaken `congr` without a function goal:
  -- congr
```

`rw [h]` actually succeeds here. The instructive failure is applying
`congr` to a goal that is not a function application with a leftover
function, or applying `congr` when `exact congrArg f h` is the lemma.

A realistic failure:
```
example {α : Type} (a b : α) (h : a = b) : a = b := by
  congr
```
`congr` reports that there is nothing to congruent-close; the goal is
already an equality of variables.

Failure classification: failed rewrite match / wrong mechanism
(`congr` used where `exact`/`rw` is enough, or where the function is
missing).

Diagnostic procedure:
1. If the goal is `f a = f b` and `a = b` is in context, `rw [h]` or
   `exact congrArg f h`.
2. `congr` is for *matching* two applications `f x₁ … = g y₁ …` and
   generating equality goals for mismatched arguments.
3. `#check congrArg`, `#check congrFun`.

Minimal repair: `exact congrArg f h`.

Semantic faithfulness: substitution of equals, unchanged.

Robustness: `congrArg` names the function; `congr` infers it and is
slightly more brittle under elaboration changes.
-/
theorem CaseC15.congrArg_apply {α β : Type} (f : α → β) {a b : α}
    (h : a = b) : f a = f b :=
  congrArg f h

#check congrArg
#check congrFun

/-! ### C16. Extensionality -/

/--
Goal / mathematical intent: two functions `ℕ → ℕ` that agree at every
point are equal.

Broken candidate:
```
example (f g : ℕ → ℕ) (h : ∀ n, f n = g n) : f = g := by
  rw [h]
```

Observed failure: `h` is a pointwise equality, not an equality of
functions. `rw [h]` looks for a subterm of type `∀ n, f n = g n` or
tries to treat `h` as an equality, and fails to match.

Failure classification: failed rewrite match (extensionality needed).

Diagnostic procedure:
1. Target type is `f = g` with `f g : ℕ → ℕ`.
2. `#check funext` — `(∀ x, f x = g x) → f = g`.
3. `ext n` is the tactic form; `exact funext h` is the term form.

Minimal repair: `exact funext h`.

Semantic faithfulness: function extensionality, unchanged.

Robustness: `funext` is the named lemma; `ext` is appropriate when
pointwise goals still need work.
-/
theorem CaseC16.funext_nat (f g : ℕ → ℕ) (h : ∀ n, f n = g n) : f = g :=
  funext h

#check funext
