/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

import Mathlib.Algebra.Module.Defs

/-!
# The challenge: the two zero laws of a module, in Mathlib's words

`Module`, `•`, `+` and `CommRing` are Mathlib's. `zero_smul` and `smul_zero` are
not named in the statement, and neither is a class projection --- both are
theorems on mathlib's side, derived from the `Module` fields.

## Which statement, and why it is the right one to ask for

This is the row `module over a ring`, and the statement is chosen so the pair
is not circular. `Bridge/ModuleTransfer` discharges `IsModule`'s four scalar
clauses by mathlib's `smul_add`, `add_smul`, `MulAction.mul_smul` and
`one_smul`, which are its class fields, so none of those four can be the
challenge.

`0 • x = 0` and `c • 0 = 0` are on the other side of the line. Both are derived
on both sides: mathlib proves them from the fields, and the tower proves
`Algebra.zero_smul` and `Algebra.smul_vzero` from `IsModule` --- the first by
idempotence (`0 • x = 0 • x + 0 • x`, then cancel in the group), the second the
same argument run on the vector side.

## What the tower's predicate carries that the class does not

`Algebra.IsModule` is a `Prop` over eight explicit `ZFSet` arguments: the scalar
carrier, three ring operations, the vector carrier, vector addition, the vector
zero, and the action as a set function on `prod R V`. Three of its clauses say
the action is a function with that domain and range --- facts mathlib's `•` gets
from its type and never states.

## Both zeros, not one

`0 • x = 0` runs through the ring's zero and `c • 0 = 0` through the vector
group's, and those are two different encoded constants, `encode (0 : α)` and
`encode (0 : M)`. Asking for both forces the Solution through `RingTransfer`'s
carrier and the module bridge's own `vaddSet`, so neither half of the transport
can be passed over.
-/

namespace Comparator.ModuleQuotient

/-- The challenge. The two zero laws of a module.

`Solution.lean` must close this using the `FromAxioms` tower. Nothing in this
file may be changed to make that easier. -/
def challenge : Prop :=
  ∀ (α M : Type) [CommRing α] [AddCommGroup M] [Module α M] (c : α) (x : M),
      (0 : α) • x = 0 ∧ c • (0 : M) = 0

/-- The challenge is not vacuous, and Mathlib is the witness --- here by its
own derivation, which the Solution is forbidden to route through.

A `Prop` nobody has shown inhabited says nothing. -/
theorem challenge_is_mathlibs : challenge := by
  intro α M _ _ _ c x
  exact ⟨zero_smul α x, smul_zero c⟩

end Comparator.ModuleQuotient
