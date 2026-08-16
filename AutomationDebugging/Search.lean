/-
Copyright (c) 2026 lean4-automation-debugging contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Common

/-!
# Theorem search and API navigation

Search protocol used throughout this repository:

1. SEARCH QUESTION — what type / statement is needed?
2. CANDIDATE API — a name from `exact?`, `apply?`, `simp?`, `#check`,
   or a grep through mathlib.
3. SIGNATURE CHECK — `#check` / `#print` the candidate.
4. WHY IT MATCHES — binders, domain, and conclusion.
5. FINAL USE — `exact`, `rw`, or `apply` of that lemma.

Search tactics (`exact?`, `apply?`, `simp?`) are diagnostic. Reviewed
proofs record the lemma they found.
-/

/-! ### C31. Unresolved theorem name -/

/-!
Goal / mathematical intent: commutativity of `ℕ` addition.

Broken candidate:
```
example (n m : ℕ) : n + m = m + n := Nat.add_commutative n m
```

Observed failure: unknown identifier `Nat.add_commutative`.

Failure classification: unresolved theorem name.

Diagnostic procedure:
SEARCH QUESTION: lemma of type `∀ n m : ℕ, n + m = m + n`.
CANDIDATE API: `exact?` suggests `Nat.add_comm`.
SIGNATURE CHECK:
-/
#check Nat.add_comm
#print Nat.add_comm

/-!
WHY IT MATCHES: binders `n m : ℕ`, conclusion `n + m = m + n`.
FINAL USE: `exact Nat.add_comm n m`.

Minimal repair: the current name `Nat.add_comm`, not a guessed
`add_commutative`.

Semantic faithfulness: commutativity on `ℕ`, unchanged.

Robustness: a named lemma is stable; a guessed English name is not.
-/
theorem CaseC31.add_comm (n m : ℕ) : n + m = m + n :=
  Nat.add_comm n m

/-! ### C32. Deprecated / stale theorem name -/

/-!
Goal / mathematical intent: the length of the base-`b` digits of a
nonzero `n` is `b.log n + 1`.

Broken candidate (still compiles with a deprecation warning):
```
example (b n : ℕ) (hb : 1 < b) (hn : n ≠ 0) :
    (b.digits n).length = b.log n + 1 :=
  Nat.digits_len b n hb hn
```

`Nat.digits_len` is a `@[deprecated]` alias of `Nat.length_digits`
(since 2026-03-18). Using it is a stale-name failure even when the
file still builds.

Failure classification: deprecated / stale theorem name.

Diagnostic procedure:
1. The compiler warning names the replacement `Nat.length_digits`.
2. `#check Nat.length_digits` confirms the signature.
3. Replace the alias.

SEARCH QUESTION: length of `Nat.digits b n`.
CANDIDATE API: `Nat.length_digits`.
SIGNATURE CHECK:
-/
#check Nat.length_digits

/-!
WHY IT MATCHES: it is the current name of the former `digits_len`.
FINAL USE: `Nat.length_digits`.

Semantic faithfulness: same digits lemma; only the identifier changes.

Robustness: current names survive the next deprecation sweep; aliases
are removed after a grace period.
-/
theorem CaseC32.length_digits (b n : ℕ) (hb : 1 < b) (hn : n ≠ 0) :
    (b.digits n).length = b.log n + 1 :=
  Nat.length_digits b n hb hn

/-! ### C33. Theorem API changed (renamed implementation) -/

/-!
Goal / mathematical intent: split a natural into parity and `n / 2`.

Broken candidate:
```
example (n : ℕ) : Bool × ℕ := Nat.boddDiv2 n
```

Observed failure: `Nat.boddDiv2` is deprecated (since 2026-03-22) with
the message to use `Nat.bodd` and `Nat.div2` instead. The *API shape*
changed: one combined function became two projections.

Failure classification: theorem API changed.

Diagnostic procedure:
SEARCH QUESTION: oddness of `n` and `⌊n / 2⌋`.
CANDIDATE API: `Nat.bodd`, `Nat.div2`.
SIGNATURE CHECK:
-/
#check Nat.bodd
#check Nat.div2

/-!
WHY IT MATCHES: `bodd n : Bool` and `div2 n = n / 2`.
FINAL USE: pair them explicitly.

Semantic faithfulness: same pair of data, current constructors.

Robustness: do not wrap the deprecated combined function.
-/
def CaseC33.bodd_div2 (n : ℕ) : Bool × ℕ :=
  (Nat.bodd n, Nat.div2 n)

theorem CaseC33.div2_eq (n : ℕ) : Nat.div2 n = n / 2 :=
  Nat.div2_val n

/-! ### C34. Wrong namespace -/

/-!
Goal / mathematical intent: commutativity of multiplication at a
generic commutative monoid, instantiated at `ℕ`.

Broken candidate:
```
example {α : Type} [Mul α] (a b : α) : a * b = b * a := mul_comm a b
```

Observed failure: `mul_comm` requires `CommMagma` / `CommMonoid`, not
bare `Mul`. Alternatively, writing `Add.add_comm` or `Monoid.mul_comm`
misses the lemma's actual namespace (`mul_comm` in the root / algebraic
hierarchy).

A second form of the same class: `Int.add_comm` vs `add_comm` after
opening the wrong namespace so that `add_comm` resolves to a `Nat`
lemma and then fails to apply to `ℤ`.

Failure classification: wrong namespace / missing typeclass instance.

Diagnostic procedure:
1. `#check @mul_comm` — `{α} [CommMagma α] (a b : α) : a * b = b * a`.
2. For `ℕ`, `Nat.mul_comm` is the specialized lemma; `mul_comm` also
   works because `ℕ` is a commutative monoid.
3. Do not search in `Add` for a multiplicative lemma.

SEARCH QUESTION: `∀ a b : ℕ, a * b = b * a`.
CANDIDATE API: `Nat.mul_comm` or `mul_comm`.
SIGNATURE CHECK:
-/
#check Nat.mul_comm
#check @mul_comm

theorem CaseC34.nat_mul_comm (a b : ℕ) : a * b = b * a :=
  Nat.mul_comm a b

/-! ### C35. `exact?` / `apply?` / `simp?` as search, not as the proof -/

/-!
Goal / mathematical intent: transitivity of `≤` on `ℕ`.

Broken candidate: leave `exact?` in the reviewed proof.
`exact?` re-runs a library search on every build. That is a
performance and robustness trap (see also PerformanceTraps.lean).

Diagnostic procedure (run interactively, then delete the search tactic):

SEARCH QUESTION: `n ≤ m → m ≤ k → n ≤ k`.
CANDIDATE API: `exact?` returns `le_trans` / `Nat.le_trans`.
SIGNATURE CHECK:
-/
#check Nat.le_trans
#check le_trans

/-!
WHY IT MATCHES: `le_trans` is `a ≤ b → b ≤ c → a ≤ c` on a preorder.
FINAL USE: `exact le_trans h₁ h₂`.

The compiling proof records the lemma. Comments below document what
the search tactics reported during development:

* `exact?` found `le_trans`.
* `apply?` found `le_trans` and left the two inequality goals.
* `simp?` did not close the goal (transitivity is not a simp identity
  here), which correctly signals a change of tool.

Semantic faithfulness: transitivity, unchanged.

Robustness: a recorded lemma does not depend on search ordering.
-/
theorem CaseC35.le_trans_nat (n m k : ℕ) (h₁ : n ≤ m) (h₂ : m ≤ k) : n ≤ k :=
  le_trans h₁ h₂
