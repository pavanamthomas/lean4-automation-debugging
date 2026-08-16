/-
Copyright (c) 2026 lean4-automation-debugging contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Common

/-!
# Goal-closing mechanisms

This module records the smallest goal-closing steps that sit underneath
automation. Each case states a mathematical intent, a defective attempt
(as a non-executable comment), the observed failure class, the diagnostic
steps that identify a repair, and a compiling proof that preserves the
original statement.

When to use which mechanism:

* `exact t` — `t` already has the goal type.
* `assumption` — some local hypothesis is definitionally the goal.
* `apply t` — `t` is an implication or forall whose conclusion unifies
  with the goal; remaining arguments become new goals.
* `refine t` — like `apply`/`exact`, but explicit holes `?_` become goals.
* `constructor` — the goal is an inductive type (typically `And`, `Iff`,
  `Exists`, a structure) and the default constructor is the right shape.
* `intro` — the goal is `∀` or `→`.
* `rcases` / `obtain` — destructure a hypothesis whose type is inductive
  (`And`, `Exists`, `Or`, a structure) while naming the pieces.
* `cases` — induction without an induction hypothesis; useful for
  empty types, `Or`, and `False`.
* `contradiction` — the local context contains `False`, or a pair `p` and
  `¬p`, or an impossible constructor equation.
-/

/-! ### C01. `exact` used on a related but different type -/

/--
Goal / mathematical intent: from `n = 0` conclude `n + 1 = 1`.

Broken candidate:
```
example (n : ℕ) (h : n = 0) : n + 1 = 1 := by
  exact h
```

Observed failure: type mismatch, `n = 0` versus `n + 1 = 1`.

Failure classification: type mismatch.

Diagnostic procedure:
1. Read the target: `n + 1 = 1`.
2. Read the context: `h : n = 0`.
3. `#check` the candidate term: `h` has type `n = 0`, not the goal.
4. The statement is an equality after substitution, not definitional
   equality of `h` with the goal. Rewrite (or `subst`) is the match.

Minimal repair: `rw [h]` (or `subst h`).

Semantic faithfulness: same domain `ℕ`, same hypothesis, same conclusion.

Robustness: `rw [h]` depends only on the equality `h`, not on a simp set.
-/
theorem CaseC01.succ_eq_one_of_eq_zero (n : ℕ) (h : n = 0) : n + 1 = 1 := by
  rw [h]

#check CaseC01.succ_eq_one_of_eq_zero

/-! ### C02. `assumption` when no hypothesis matches -/

/--
Goal / mathematical intent: from `n ≤ m` and `m ≤ k` conclude `n ≤ k`.

Broken candidate:
```
example (n m k : ℕ) (h₁ : n ≤ m) (h₂ : m ≤ k) : n ≤ k := by
  assumption
```

Observed failure: tactic `assumption` fails; neither `h₁` nor `h₂` is
definitionally `n ≤ k`.

Failure classification: insufficient assumptions *as a closing term*
(the assumptions are present but must be composed).

Diagnostic procedure:
1. Target is `n ≤ k`.
2. Local types are `n ≤ m` and `m ≤ k`.
3. `#check le_trans` (or `Nat.le_trans`): transitivity has the right shape.
4. `apply le_trans` produces two goals that `assumption` can close.

Minimal repair: `exact le_trans h₁ h₂`.

Semantic faithfulness: the transitivity statement is unchanged.

Robustness: naming `le_trans` is stable; `assumption` alone is the wrong
mechanism for a composite lemma.
-/
theorem CaseC02.le_trans_of_le (n m k : ℕ) (h₁ : n ≤ m) (h₂ : m ≤ k) : n ≤ k :=
  le_trans h₁ h₂

#check le_trans

/-! ### C03. `apply` versus `exact` on an implication -/

/--
Goal / mathematical intent: from `P → Q` and `P` conclude `Q`.

Broken candidate:
```
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  exact hPQ
```

Observed failure: type mismatch, `P → Q` versus `Q`.

Failure classification: type mismatch (implication not fully applied).

Diagnostic procedure:
1. Target is `Q`, not `P → Q`.
2. `hPQ` is a function. `apply hPQ` creates the remaining goal `P`.
3. That goal is `exact hP` (or `assumption`).

Minimal repair: `exact hPQ hP`, or `apply hPQ; exact hP`.

Semantic faithfulness: modus ponens, unchanged.

Robustness: `exact hPQ hP` is the smallest closed term; `apply` is
appropriate when later arguments still need proof.
-/
theorem CaseC03.modus_ponens {P Q : Prop} (hPQ : P → Q) (hP : P) : Q :=
  hPQ hP

/-! ### C04. `refine` with an explicit hole -/

/--
Goal / mathematical intent: pack two proofs into a conjunction.

Broken candidate:
```
example {P Q : Prop} (hP : P) (hQ : Q) : P ∧ Q := by
  refine ⟨hP⟩
```

Observed failure: type mismatch / wrong constructor arity; `And.intro`
expects two arguments.

Failure classification: structure field mismatch (constructor arity).

Diagnostic procedure:
1. `#print And` / `#check And.intro`: two fields, `left` and `right`.
2. `refine ⟨hP, ?_⟩` leaves exactly the unsolved `Q` goal.

Minimal repair: `refine ⟨hP, hQ⟩` or `constructor <;> assumption`.

Semantic faithfulness: same conjunction.

Robustness: `refine` is useful when one conjunct is immediate and the
other still needs a multi-step proof. Prefer a closed term when both
pieces are already in context.
-/
theorem CaseC04.and_intro {P Q : Prop} (hP : P) (hQ : Q) : P ∧ Q := by
  refine ⟨hP, ?_⟩
  exact hQ

#check And.intro

/-! ### C05. `constructor` for `Iff` -/

/--
Goal / mathematical intent: `n = 0 ↔ n + 1 = 1`.

Broken candidate:
```
example (n : ℕ) : n = 0 ↔ n + 1 = 1 := by
  constructor
  · intro h; exact h
```

Observed failure: type mismatch on the first direction (`n = 0` vs
`n + 1 = 1`). The second direction is also not definitional.

Failure classification: type mismatch inside a constructor-generated
subgoal.

Diagnostic procedure:
1. `constructor` on `↔` yields both directions; that shape is correct.
2. Each direction is an equality that needs `rw` or `omega`, not `exact`.

Minimal repair: prove each direction by rewriting or `omega`.

Semantic faithfulness: biconditional on `ℕ`, no extra hypotheses.

Robustness: `omega` closes both numeric sides here; an explicit `rw`
proof is more reviewable if the equalities become less linear.
-/
theorem CaseC05.eq_zero_iff_succ_eq_one (n : ℕ) : n = 0 ↔ n + 1 = 1 := by
  constructor
  · intro h
    rw [h]
  · intro h
    omega

/-! ### C06. `intro`, `rcases`, and `obtain` -/

/--
Goal / mathematical intent: from `∃ k, n = 2 * k` conclude `n ≠ 1`.

Broken candidate:
```
example (n : ℕ) (h : ∃ k, n = 2 * k) : n ≠ 1 := by
  intro hk
  exact absurd rfl hk
```

Observed failure: `intro` acts on the goal `n ≠ 1`, producing `n = 1 → False`.
It does **not** destructure `h`. The existential witness is never named,
so the arithmetic contradiction cannot be stated.

Failure classification: existential witness missing (misapplied `intro`).

Diagnostic procedure:
1. Distinguish goal-binders (`intro`) from hypothesis-destructuring
   (`rcases` / `obtain` / `cases`).
2. `obtain ⟨k, hk⟩ := h` names the witness.
3. Substitute and compare with `1 = 2 * k`, which `omega` refutes.

Minimal repair: `obtain` the witness, then contradict `n = 1`.

Semantic faithfulness: same existential hypothesis, same negation.

Robustness: `obtain` makes the witness visible for review; `aesop` can
hide that step.
-/
theorem CaseC06.even_ne_one (n : ℕ) (h : ∃ k, n = 2 * k) : n ≠ 1 := by
  obtain ⟨k, hk⟩ := h
  intro hn
  subst hn
  omega

/-! ### C07. `cases` versus `contradiction` -/

/--
Goal / mathematical intent: `False` from `n < 0` in `ℕ`.

Broken candidate:
```
example (n : ℕ) (h : n < 0) : False := by
  cases n
```

Observed failure: `cases n` splits into `0` and `succ`, but both subgoals
still carry a `< 0` hypothesis that is not automatically discharged.
The induction variable is the datum `n`, not the empty inequality.

Failure classification: incorrect induction variable (here: wrong
`cases` target). Also close to using an arithmetic fact as if it were
an inductive empty type.

Diagnostic procedure:
1. `#check Nat.not_lt_zero`: `∀ n, ¬ n < 0`.
2. The contradiction is the lemma applied to `h`, not a case-split on `n`.
3. `contradiction` also works once `Nat.not_lt_zero` is in the simp set,
   but `exact Nat.not_lt_zero n h` is the decisive lemma.

Minimal repair: apply `Nat.not_lt_zero`.

Semantic faithfulness: no change of domain; `n < 0` remains uninhabited
on `ℕ`.

Robustness: prefer the named lemma over a case-split that recreates it.
-/
theorem CaseC07.not_lt_zero (n : ℕ) (h : n < 0) : False :=
  Nat.not_lt_zero n h

#check Nat.not_lt_zero

/-- Same goal closed by `contradiction` after a `have` that surfaces `¬ n < 0`. -/
theorem CaseC07.not_lt_zero_contradiction (n : ℕ) (h : n < 0) : False := by
  have : ¬ n < 0 := Nat.not_lt_zero n
  contradiction

/-! ### C08. Existential goal with a missing witness -/

/--
Goal / mathematical intent: `∃ k, 2 * k = n` when `n` is even.

Broken candidate:
```
example (k n : ℕ) (h : n = 2 * k) : ∃ k, 2 * k = n := by
  constructor
```

Observed failure: `constructor` on `Exists` asks for a witness first.
Without supplying one, Lean does not guess `k`. Shadowing the binder
`k` against the context variable `k` also makes the intent unclear.

Failure classification: existential witness missing.

Diagnostic procedure:
1. The goal is `∃ k, 2 * k = n`. Write the witness explicitly.
2. `refine ⟨k, ?_⟩` or `exact ⟨k, h.symm⟩`.
3. Check that the witness type is `ℕ` and that `2 * k = n` follows from `h`.

Minimal repair: `exact ⟨k, h.symm⟩`.

Semantic faithfulness: same evenness predicate; witness is the given `k`.

Robustness: explicit witnesses survive refactor; `constructor` without a
term is under-specified.
-/
theorem CaseC08.exists_double (k n : ℕ) (h : n = 2 * k) : ∃ k, 2 * k = n :=
  ⟨k, h.symm⟩
