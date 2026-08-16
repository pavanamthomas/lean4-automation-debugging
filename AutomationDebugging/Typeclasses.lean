/-
Copyright (c) 2026 lean4-automation-debugging contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Common

/-!
# Typeclasses and structures

A missing instance is not repaired by changing the theorem to a
weaker algebraic structure, nor by adding a `variable` that is not
justified by the intended domain.
-/

/-! ### C40. Missing typeclass instance -/

/-!
Goal / mathematical intent: commutativity of addition on a type that
only has `Add`.

Broken candidate:
```
example {α : Type} [Add α] (a b : α) : a + b = b + a := add_comm a b
```

Observed failure: `add_comm` requires `AddCommMagma` (or a stronger
commutative additive class). Lean reports a missing instance, not a
missing term of type `a + b = b + a`.

Failure classification: missing typeclass instance.

Diagnostic procedure:
1. `#check @add_comm` — inspect the instance binder.
2. Confirm that the intended domain really is commutative.
3. Add `[AddCommMagma α]` (or `[AddCommMonoid α]`, …) rather than
   synthesizing a fake instance.

Minimal repair: require `AddCommMagma`.

Semantic faithfulness: the theorem is commutativity, so the class
must include commutativity. Restricting to `ℕ` would also compile but
would change the intended generality.
-/
#check @add_comm

theorem CaseC40.add_comm_of_comm_magma {α : Type} [AddCommMagma α] (a b : α) :
    a + b = b + a :=
  add_comm a b

/-! ### C41. Theorem requires a stronger typeclass than is available -/

/-!
Goal / mathematical intent: `a / a = 1` on a type with only `Div`.

Broken candidate:
```
example {α : Type} [Div α] (a : α) : a / a = 1 := div_self' a
```

Observed failure: `div_self'` lives on a `Group` (division as
multiplication by inverse, every element invertible). A bare `Div`
has no such axiom. On `GroupWithZero` / `Field` one also needs
`a ≠ 0`. Lean reports a missing instance (`Group`, `One`, …).

Failure classification: theorem requires stronger typeclass than
available.

Diagnostic procedure:
1. `#check @div_self'` versus `#check @div_self`.
2. Choose the class that matches the intended algebra:
   groups (`div_self'`) vs fields (`div_self` + nonzero).
3. Do not add `[Group α]` if the intended type is `ℕ` or a monoid.

Minimal repair for a field: `[GroupWithZero α]` plus `a ≠ 0`.
-/
#check @div_self'
#check @div_self

theorem CaseC41.div_self_field {α : Type} [GroupWithZero α]
    (a : α) (h : a ≠ 0) : a / a = 1 :=
  div_self h

/-! ### C42. Structure field mismatch -/

/-- A tiny structure used to exhibit field-name mistakes. -/
structure CaseC42.Point where
  x : ℕ
  y : ℕ

/-!
Goal / mathematical intent: swap coordinates.

Broken candidate:
```
example (p : CaseC42.Point) : CaseC42.Point :=
  { fst := p.y, snd := p.x }
```

Observed failure: `Point` has fields `x` and `y`, not `fst` and `snd`
(`Prod` fields). Lean reports unknown field `fst`.

Failure classification: structure field mismatch.

Diagnostic procedure:
1. `#print CaseC42.Point` / `#check CaseC42.Point.x`.
2. Use the actual field names, or `cases p` and reconstruct.
3. Do not reuse `Prod` field names on a custom structure.

Minimal repair: `{ x := p.y, y := p.x }`.
-/
#print CaseC42.Point

def CaseC42.swap (p : CaseC42.Point) : CaseC42.Point :=
  { x := p.y, y := p.x }

theorem CaseC42.swap_x (p : CaseC42.Point) : (CaseC42.swap p).x = p.y :=
  rfl

theorem CaseC42.swap_involutive (p : CaseC42.Point) :
    CaseC42.swap (CaseC42.swap p) = p := by
  cases p
  rfl
