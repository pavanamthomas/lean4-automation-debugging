# Case index

Audited against compiling declarations in `AutomationDebugging/*.lean`.
Broken candidates are comments in those files, not executable code.

| Case | Failure class | Mathematical topic | Lean mechanism | Diagnostic tool | Repair strategy | Difficulty | Source file |
| --- | --- | --- | --- | --- | --- | --- | --- |
| C01 | Type mismatch | `n = 0 → n + 1 = 1` | `rw` vs `exact` | `#check` hypothesis type | Rewrite, do not `exact h` | Foundational | `GoalMechanics.lean` |
| C02 | Insufficient assumptions (as a closer) | Transitivity of `≤` | `exact le_trans` | `#check le_trans` | Compose the two inequalities | Foundational | `GoalMechanics.lean` |
| C03 | Type mismatch | Modus ponens | `exact` of a function | Target vs `P → Q` | Apply the implication | Foundational | `GoalMechanics.lean` |
| C04 | Structure field mismatch | Conjunction | `refine ⟨_, ?_⟩` | `#check And.intro` | Two constructor arguments | Foundational | `GoalMechanics.lean` |
| C05 | Type mismatch in subgoal | `n = 0 ↔ n + 1 = 1` | `constructor` | Split `Iff`, then `rw`/`omega` | Prove both directions | Foundational | `GoalMechanics.lean` |
| C06 | Existential witness missing | Even ⇒ `n ≠ 1` | `obtain`, `omega` | Distinguish `intro` vs `obtain` | Name the witness | Intermediate | `GoalMechanics.lean` |
| C07 | Incorrect induction variable | `¬ n < 0` on `ℕ` | `exact` / `contradiction` | `#check Nat.not_lt_zero` | Lemma, not `cases n` | Foundational | `GoalMechanics.lean` |
| C08 | Existential witness missing | Evenness as `∃` | `exact ⟨k, _⟩` | Goal is `Exists` | Supply `k` | Foundational | `GoalMechanics.lean` |
| C09 | Failed rewrite match (direction) | `n + 0 = n` | `rw` / `← rw` | `#check Nat.add_zero` | Match the redex side | Foundational | `Rewriting.lean` |
| C10 | Failed rewrite match (syntax) | Commute `n + (m+1)` | `rw [Nat.add_comm n _]` | `#check Nat.add_comm` | Instantiate arguments | Foundational | `Rewriting.lean` |
| C11 | Failed coercion | `(n : ℝ) + 0 = n` | `rw [add_zero]` | `#check add_zero` vs `Nat.add_zero` | Generic lemma | Intermediate | `Rewriting.lean` |
| C12 | Implicit argument mismatch | `a * a⁻¹ = 1` on `ℝ` | `rw [mul_inv_cancel₀ h]` | `#check @mul_inv_cancel₀` | Pass `a ≠ 0` | Intermediate | `Rewriting.lean` |
| C13 | Rewrite changes too much | Additivity of `=` | `rw` on the goal | Location of `rw` | Avoid `at *` | Foundational | `Rewriting.lean` |
| C14 | Failed rewrite match (chain) | Reassociate `+` | `calc` | One equality per step | Display the chain | Intermediate | `Rewriting.lean` |
| C15 | Wrong mechanism | Congruence | `congrArg` | `#check congrArg` | Named congruence | Intermediate | `Rewriting.lean` |
| C16 | Failed rewrite match | Function extensionality | `funext` | `#check funext` | Pointwise ⇒ function `=` | Intermediate | `Rewriting.lean` |
| C17 | Simplifier cannot close | Binomial square | `ring` | Problem class | Not `simp` | Intermediate | `Simplification.lean` |
| C18 | Simplifier changes too much | `succ` vs `+ 1` | `exact Nat.succ_eq_add_one` | `#check Nat.succ_eq_add_one` | Do not unfold `Nat.add` | Intermediate | `Simplification.lean` |
| C19 | Brittle incidental `simp` | `¬ (True ∧ False)` | `simp only` | `simp?` then record lemmas | Closed simp set | Foundational | `Simplification.lean` |
| C20 | Unnecessary `simpa` | `And.left` | `exact h.left` | Linter / `#check And.left` | Drop `simpa` | Foundational | `Simplification.lean` |
| C21 | Brittle incidental `simp` | `n + 0 + 0 = n` | `simp only [add_zero]` / `rw` | Identify `[simp]` lemmas | Record them | Intermediate | `Simplification.lean` |
| C22 | Simplifier cannot close (location) | Reduce hyp `n + 0 = m` | `simp only at h` | Redex is in `h` | `simp at`, not goal `simp` | Intermediate | `Simplification.lean` |
| C23 | Arithmetic on unsupported goal | Numerals vs free var | `norm_num` / `Nat.add_comm` | Closed term? | `norm_num` only on closed goals | Foundational | `ArithmeticAutomation.lean` |
| C24 | Arithmetic on unsupported goal | Polynomial `=` vs inequality | `ring` / `ring_nf` / `linarith` | Equality or inequality? | `ring` for `=`, `linarith` for `≤` | Intermediate | `ArithmeticAutomation.lean` |
| C25 | Arithmetic on unsupported goal | Linear vs quadratic | `linarith` | Count products | Stay linear; use `sq_le_sq` for squares | Intermediate | `ArithmeticAutomation.lean` |
| C26 | Unsupported fragment + false cubic | Squares vs cubes | `nlinarith` | Is the statement true? | Prove squares, not the false cubic | Advanced | `ArithmeticAutomation.lean` |
| C27 | Arithmetic on unsupported goal | `n ≤ n * n` | `omega` vs cases | Nonlinear `ℕ` | `Nat.le_mul_of_pos_right` | Intermediate | `ArithmeticAutomation.lean` |
| C28 | Arithmetic on unsupported goal | `P → P` | Identity function | Target is `Prop` | Not `omega` | Foundational | `ArithmeticAutomation.lean` |
| C29 | Missing nonzero | `a / a = 1` on `ℝ` | `div_self` | `#check div_self` | Add `a ≠ 0` | Intermediate | `ArithmeticAutomation.lean` |
| C30 | Missing positivity | `0 < a⁻¹` | `inv_pos.mpr` | `#check inv_pos` | Need `0 < a`, not `a ≠ 0` | Advanced | `ArithmeticAutomation.lean` |
| C31 | Unresolved theorem name | `ℕ` add commute | `Nat.add_comm` | `exact?` then `#check` / `#print` | Current name | Foundational | `Search.lean` |
| C32 | Deprecated / stale name | Digit length | `Nat.length_digits` | Deprecation warning | Replace `digits_len` | Intermediate | `Search.lean` |
| C33 | Theorem API changed | Parity and `n/2` | `Nat.bodd`, `Nat.div2` | Deprecation of `boddDiv2` | Split API | Intermediate | `Search.lean` |
| C34 | Wrong namespace | `ℕ` mul commute | `Nat.mul_comm` | `#check @mul_comm` | Right namespace / class | Foundational | `Search.lean` |
| C35 | Search left in the proof | Transitivity of `≤` | `le_trans` | `exact?` / `apply?` / `simp?` | Record the lemma | Intermediate | `Search.lean` |
| C36 | Wrong domain | Truncated subtraction | `Nat.sub_add_cancel` | Counterexample `m > n` | Add `m ≤ n`; keep `ℕ` | Intermediate | `Coercions.lean` |
| C37 | Failed coercion | `(n : ℝ) * 1 = n` | `rw [mul_one]` | Type of `*` | Generic lemma | Intermediate | `Coercions.lean` |
| C38 | Ambiguous coercion | `1 + 1 = 2` at `ℝ` | `norm_num` | Ascribe `(1 : ℝ)` | Annotate type | Intermediate | `Coercions.lean` |
| C39 | Overloaded notation | Distributivity `ℕ`/`ℝ` | `ring` | Type of `n * x` | Generic ring lemma | Advanced | `Coercions.lean` |
| C40 | Missing typeclass instance | Generic `add_comm` | `AddCommMagma` | `#check @add_comm` | Require commutativity | Intermediate | `Typeclasses.lean` |
| C41 | Stronger typeclass required | `a / a = 1` | `div_self` on `GroupWithZero` | `#check @div_self'` | Nonzero + `GroupWithZero` | Advanced | `Typeclasses.lean` |
| C42 | Structure field mismatch | Coordinate swap | structure fields | `#print Point` | Fields `x`,`y` not `fst`,`snd` | Intermediate | `Typeclasses.lean` |
| C43 | Induction hypothesis mismatch | `0 + n = n` | `induction`, `Nat.add_succ` | Print IH | Unfold successor in the goal | Intermediate | `InductionFailures.lean` |
| C44 | Incorrect induction variable | `n + m = m + n` | `induction n` | Which argument `add_succ` unfolds | Induct on `n` | Advanced | `InductionFailures.lean` |
| C45 | Wrong quantifier order | Bounded vs unbounded `ℕ` | `∃` witness `n` | Binder order | Prove `∀∃`, not false `∃∀` | Advanced | `InductionFailures.lean` |
| C46 | Implication reversed | `n = 0 → n ≤ 0` | `rw [h]` | `#check Nat.eq_zero_of_le_zero` | Do not use the converse | Intermediate | `InductionFailures.lean` |
| C47 | Automation search explosion | `n ≤ n` | `le_rfl` | `#check le_rfl` | Named lemma, not huge `aesop` | Foundational | `PerformanceTraps.lean` |
| C48 | Unnecessarily broad automation | `P ∧ Q → Q ∧ P` | `intro` / pairing vs `aesop` | Constructor shape | Explicit proof; targeted build | Advanced | `PerformanceTraps.lean` |
| C49 | Semantically wrong statement | `a / b * b = a` | `div_mul_cancel₀` | Counterexample `b = 0` | Add `b ≠ 0`; keep `ℝ` | Advanced | `ReviewerCases.lean` |
| C50 | Under-specified statement | Right identity of `+` | `∃!` | Existence vs uniqueness | Prove `∃!`, keep `∃` as the weak form | Advanced | `ReviewerCases.lean` |
| C51 | Unnecessary assumptions | `ℕ` add commute | `Nat.add_comm` | Unused binder | Drop the inequality | Foundational | `ReviewerCases.lean` |
| C52 | Opaque automation vs explicit | Three-term commute | `ring` / `calc` vs `grind` | Problem class | `ring` or `calc`, not `grind` | Advanced | `ReviewerCases.lean` |
| C53 | Opaque automation vs explicit | `Or` commute | `cases` | Constructors of `Or` | Explicit cases vs `aesop` | Foundational | `ReviewerCases.lean` |
| C54 | Insufficient assumptions | Translation of `≤` | `Nat.add_le_add_right` | Counterexample on `n + k ≤ m` | Prove `n + k ≤ m + k` | Advanced | `ReviewerCases.lean` |

## Counts

| Difficulty | Cases |
| --- | --- |
| Foundational | C01–C05, C07–C10, C13, C19, C20, C23, C28, C31, C34, C47, C51, C53 (19) |
| Intermediate | C06, C11, C12, C14–C18, C21, C22, C24, C25, C27, C29, C32, C33, C35–C38, C40, C42, C43, C46 (24) |
| Advanced | C26, C30, C39, C41, C44, C45, C48–C50, C52, C54 (11) |
| **Total** | **54** |

## Coverage by topic (non-exclusive)

| Topic | Cases |
| --- | --- |
| Type / coercion | C01, C03, C11, C36–C39 |
| Typeclass | C34, C40, C41 |
| Rewrite | C09–C16 |
| Simplification | C17–C22 |
| Arithmetic automation | C23–C30 |
| Search | C31–C35 |
| Induction / quantifiers | C43–C46 |
| Performance | C47, C48 |
| Semantic failure | C26, C45, C49, C50, C51, C54 |
