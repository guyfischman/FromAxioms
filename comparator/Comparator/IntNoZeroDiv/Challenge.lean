/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
CHALLENGE: the integers have no zero divisors, and negation passes through
multiplication.

Mathlib's vocabulary only. `mul_eq_zero` (`Mathlib/Algebra/GroupWithZero/Basic.lean`)
gives the first conjunct at `ℤ` through its `NoZeroDivisors` instance, and
`mul_neg` gives the second.

WHICH ROW, AND WHY THESE TWO STATEMENTS. The row is `zero and the negative
numbers`, whose `mathlib` field reads `Int (inductive)`. Mathlib's integers are
an inductive type with two constructors; the tower's `NumberTheory.Int` is a
ZFSet, built as differences of naturals and quotiented by the usual relation. The
carrier could hardly differ more, so what a pair can compare is the ARITHMETIC.

Both conjuncts are chosen to be THEOREMS about that arithmetic rather than laws
of the translation. `NumberTheory.intOfLean_add`, `_mul`, `_neg`, `_zero` and
`_one` are the tower's homomorphism laws for its own `Int → ZFSet` map, and
pairing one of THOSE would be pairing a translation against itself. Absence of
zero divisors is derived on the tower's side from `intMul_left_cancel`, and
`intMul_neg` from commutativity and `intNeg_mul`; neither is a homomorphism
law, so each side proves the statement by its own reasoning.

AND NO BRIDGE IS INVOLVED AT ALL, which is unusual for a `carrier: ZFSet` row.
`intOfLean` lives in `FromAxioms/NumberTheory/IntLean.lean` --- the TOWER's own
map from Lean's `Int`, not something `comparator/Comparator/Bridge/` supplies.
Lean's `Int` is core, so the tower can name it without reaching for Mathlib.
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Ring.Int.Defs

namespace Comparator.IntNoZeroDiv

/-- The challenge. Two facts about `ℤ`'s multiplication that are not laws of
any translation.

`Solution.lean` must close this using the `FromAxioms` tower. Nothing in this
file may be changed to make that easier. -/
def challenge : Prop :=
  (∀ a b : Int, a * b = 0 → a = 0 ∨ b = 0) ∧
  (∀ a b : Int, a * (-b) = -(a * b))

/-- `challenge` is Mathlib's, checked by discharging it from Mathlib. This says
nothing about the tower; `Solution.lean` does that. -/
theorem challenge_is_mathlibs : challenge :=
  ⟨fun _ _ h => mul_eq_zero.mp h, fun a b => mul_neg a b⟩

end Comparator.IntNoZeroDiv
