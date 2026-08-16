# Failure taxonomy

Each representative case exists as a compiling declaration in this
repository. Broken attempts are comments in the same file.

| Failure class | Typical Lean symptom | Likely cause | First diagnostic action | Common bad repair | Preferred repair | Representative case |
| --- | --- | --- | --- | --- | --- | --- |
| 1. Type mismatch | `type mismatch`, expected `T` got `S` | Term is related but not the goal | `#check` the term; compare with the target | `convert` / extra coercions that change meaning | Use a lemma or rewrite that produces `T` | C01 |
| 2. Wrong domain | Tactic fails on a “standard” identity | `ℕ` truncated ops vs `ℤ`/`ℝ` | Evaluate a counterexample at `0` | Change `ℕ` to `ℤ` | Keep the domain; add the missing inequality | C36 |
| 3. Failed coercion | Rewrite lemma does not match | Lemma is at `ℕ`, goal is coerced to `ℝ` | Hover types of `+` / `*` | `Nat.cast_id` noise | Generic algebraic lemma (`add_zero`, `mul_one`) | C11, C37 |
| 4. Implicit argument mismatch | Unsolved metavariable; rewrite fails | Nonzero proof not supplied | `#check @mul_inv_cancel₀` | Global `NeZero` instance | Pass `h : a ≠ 0` explicitly | C12 |
| 5. Missing typeclass instance | Failed to synthesize instance | Goal lemma needs `AddCommMagma`, context has `Add` | `#check @add_comm` | Fake `instance` | Add the class the theorem actually needs | C40 |
| 6. Wrong namespace | Unknown identifier or wrong lemma | `Nat.*` vs generic `mul_comm` | `#check Nat.mul_comm` and `@mul_comm` | Open a random namespace | Use the lemma in the right namespace | C34 |
| 7. Unresolved theorem name | Unknown identifier | Guessed English name | `exact?` then `#check` | Invent a similar identifier | Current mathlib name | C31 |
| 8. Deprecated / stale name | Deprecation warning | Alias scheduled for removal | Read the warning; `#check` replacement | Keep the alias | Current name (`Nat.length_digits`) | C32 |
| 9. Theorem API changed | Deprecated combined function | One function split into two | Read deprecation text | Wrap the old API | `Nat.bodd` and `Nat.div2` | C33 |
| 10. Failed rewrite match | `rw` fails to find a pattern | Wrong direction or arguments | `#check` lemma; identify the redex | `rw` at `*` | Instantiate / flip direction | C09, C10 |
| 11. Simplifier cannot close goal | `simp` leaves a goal | Wrong problem class or location | Is it a ring identity? Is the redex in a hyp? | More `simp` lemmas | `ring`, or `simp at h` | C17, C22 |
| 12. Simplifier changes too much | Later lemmas stop matching | Unfolded definitions | Identify library normal form | `simp [Nat.add]` | Named lemma (`Nat.succ_eq_add_one`) | C18 |
| 13. Arithmetic tactic on unsupported goal | `omega`/`ring`/`norm_num` fail | Nonlinear, inequality, free var, or `Prop` | Classify the goal | Raise heartbeats | Switch procedure or lemma | C23–C28 |
| 14. Insufficient assumptions | Goal is false or unprovable | Missing hypothesis that the *intent* has | Counterexample | Set a variable to `0` | Restore the intended hypothesis | C54 |
| 15. Unnecessary assumptions | Compiles with an unused binder | Extra `h` copied into the statement | Does `h` appear in the proof? | Leave it “for later” | Drop it | C51 |
| 16. Missing nonzero condition | `div_self` will not apply; false at `0` | Field cancellation needs `a ≠ 0` | `#check div_self` | Change to a group | Add `a ≠ 0` | C29, C49 |
| 17. Missing positivity condition | Type mismatch `0 < a` vs `a ≠ 0` | Inverse positivity is not invertibility | `#check inv_pos` | Prove `a⁻¹ ≠ 0` instead | Assume `0 < a` | C30 |
| 18. Wrong quantifier order | Witness chosen too early | `∃∀` vs `∀∃` | Write binders in order | Prove the swapped statement and relabel | Prove the intended quantifier prefix | C45 |
| 19. Implication reversed | Type mismatch on `→` | Used the converse lemma | `#check` both directions | `exact` the converse | Match implication direction | C46 |
| 20. Existential witness missing | `constructor` on `Exists` stuck | No witness term | `refine ⟨w, ?_⟩` | Let unification invent `w` | Supply `w` | C06, C08 |
| 21. Induction hypothesis mismatch | `rw [ih]` fails | IH is for `n`, goal is `n.succ` | Print IH; unfold successor in the goal | Induct again | `Nat.add_succ` then `ih` | C43 |
| 22. Incorrect induction variable | Cases on the wrong term | `cases n` vs lemma on the inequality | `#check` the empty-case lemma | More `cases` | Induct on the argument the lemmas unfold | C07, C44 |
| 23. Automation search explosion | Heartbeat timeout / slow `aesop` | Search on a one-lemma goal | `#check le_rfl` | Raise `maxHeartbeats` | Decisive lemma | C47 |
| 24. Brittle incidental `simp` | Later import breaks `simp` | Unrecorded simp set | `simp?` once | Keep bare `simp` | `simp only [...]` or `rw` | C19, C21 |
| 25. Ambiguous coercion | Stuck elaboration / accidental `ℕ` | Numerals without ascription | Ascribe `(1 : ℝ)` | Random `exact` of a `ℕ` lemma | Annotate the intended type | C38 |
| 26. Overloaded notation | `Nat.mul` vs `ℝ` mul | `n * x` with mixed types | Type of the product | Force `ℕ` lemmas | Generic `ring` / `add_mul` | C39 |
| 27. Structure field mismatch | Unknown field `fst` | `Prod` names on a custom structure | `#print` the structure | `cases` into the wrong type | Actual field names | C04, C42 |
| 28. Stronger typeclass required | Missing `Group` / `GroupWithZero` | `Div` is not cancellation | `#check @div_self'` vs `@div_self` | Add `[Group α]` for `ℕ` | Class that matches the algebra | C41 |
| 29. Semantically wrong statement | Tactic fails; or a “proof” of a false goal | Identity false at `0` | Counterexample | Change domain so it becomes true | Restore the true intended theorem | C49, C26 |
| 30. Under-specified statement | Compiles, misses uniqueness | `∃` proved, `∃!` intended | Ask what “the” object meant | Keep existence | Strengthen to `∃!` if that was the intent | C50 |
