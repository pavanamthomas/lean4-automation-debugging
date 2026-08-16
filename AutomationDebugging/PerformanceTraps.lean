/-
Copyright (c) 2026 lean4-automation-debugging contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Aesop
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Common

/-!
# Performance and automation traps

This file does **not** run pathological search. It records small,
reproducible cases where the *wrong width* of automation is the
defect, and replaces it with a decisive lemma or a restricted
configuration.

Build discipline used in this repository:

* Targeted module build: `lake build AutomationDebugging.PerformanceTraps`
* Full build: `lake build`
* Mathlib oleans come from `lake exe cache get` (already run after
  `lake update`). Downstream files should not force a mathlib rebuild.
* `exact?` / `aesop` / `grind` belong in diagnosis, not in a tight loop
  of "rebuild the world until search succeeds".
-/

/-! ### C47. Automation search explosion / excessive search -/

/-!
Goal / mathematical intent: `n ≤ n`.

Broken candidate:
```
example (n : ℕ) : n ≤ n := by
  aesop (config := { maxRuleApplications := 100000 })
```

Observed failure: the goal is `le_rfl`. Broad `aesop` (or `grind` with
a huge search limit) will usually still succeed, but it spends search
on a one-lemma goal. In larger contexts the same pattern becomes a
heartbeat timeout.

Failure classification: automation search explosion / excessive search.

Diagnostic procedure:
1. The target is reflexivity of `≤`.
2. `#check le_rfl`.
3. Do not raise `maxHeartbeats` to make search finish.

Minimal repair: `exact le_rfl`.

Semantic faithfulness: reflexivity, unchanged.

Robustness: a named lemma has constant cost.
-/
#check le_rfl

theorem CaseC47.le_refl (n : ℕ) : n ≤ n :=
  le_rfl

/-! ### C48. Unnecessarily broad automation; targeted vs full build -/

/--
Goal / mathematical intent: `P ∧ Q → Q ∧ P`.

Broken candidate:
```
example {P Q : Prop} : P ∧ Q → Q ∧ P := by
  aesop
```

This often succeeds, which is the trap: `aesop` searches a large rule
database for a two-constructor proof. The reviewable form is
`intro ⟨hP, hQ⟩; exact ⟨hQ, hP⟩`.

Failure classification: unnecessarily broad automation.

Diagnostic procedure:
1. Goal is swapping a pair of proofs.
2. `constructor` / `exact ⟨_, _⟩` is the mechanism.
3. Keep `aesop` as a search that *suggests* this term, then delete it.

Minimal repair: explicit introduction and pairing.

Build note: while developing this module, compile it alone:

```
lake build AutomationDebugging.PerformanceTraps
```

rather than `lake build` after every one-line tactic change. The full
build is the final gate, not the inner loop.

Cache note: `lake exe cache get` restores mathlib oleans. A targeted
module build should not recompile mathlib if the toolchain and
manifest are unchanged.
-/
theorem CaseC48.and_comm {P Q : Prop} : P ∧ Q → Q ∧ P := by
  intro h
  exact ⟨h.right, h.left⟩

/-- Restricted `aesop` as a documented alternative, not the default. -/
theorem CaseC48.and_comm_aesop_restricted {P Q : Prop} : P ∧ Q → Q ∧ P := by
  aesop
