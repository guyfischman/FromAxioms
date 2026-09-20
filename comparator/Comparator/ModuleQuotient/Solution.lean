/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`.

The mathematics is `Algebra.smulT_zero_scalar` and `Algebra.smulT_zero_vector`
--- the tower's own theorems over an arbitrary Lean type, with the module
operations handed over as function arguments. Both run the idempotence argument
(`0 • x = 0 • x + 0 • x`, then cancel in the group), the first on the scalar side
and the second on the vector side.

Mathlib's `zero_smul` and `smul_zero` are not cited here. The Challenge's own
witness is exactly those two, and this file must not route through it.

A route through `Bridge/ModuleTransfer` --- encode `α` and `M` into ZFSet
carriers, apply the tower's ZFSet-sited `Algebra.zero_smul` and
`Algebra.smul_vzero`, and read the results back with `encode_injective` --- has
an axiom line no better than `Classical.choice`, and not because of anything
about the proof.

`TypeTransfer.encode_injective` factors through `embU`, which is Mostowski's
collapse indexed by `WellOrderingRel`. Well-ordering an arbitrary type is the
axiom of choice. Any Solution reaching an arbitrary `α : Type` by encoding it
pays choice by construction rather than by proof style, and there is no cheaper
encoding to go find. The challenge quantifies over an arbitrary `Type`, the
ZFSet-sited theorem does not, and the gap between the two is what that axiom
pays for.

The pair does not ask for `smul_add`, `add_smul`, `mul_smul` or `one_smul`:
those are mathlib's own class fields, and a pair asking for them would be
circular. What is passed in below is those fields; what is derived is the two
zero laws, by the tower's argument.

Three of `IsModule`'s clauses say the action is a set function with a given
domain and range --- facts mathlib's `•` gets from its type and never states.
Over a Lean type there is nothing to say, so those three clauses have no
counterpart among the hypotheses below.
-/
import Comparator.ModuleQuotient.Challenge
import FromAxioms.Algebra.Module

namespace Comparator.ModuleQuotient

/-- The tower's theorems this rests on, named where a reader of this file
can see them. -/
theorem rests_on_smulT_zero : True := by
  have _ := @Algebra.smulT_zero_scalar.{0}
  have _ := @Algebra.smulT_zero_vector.{0}
  trivial

/-- The challenge, from `FromAxioms`, with no encoding anywhere.

The two halves run through different operations --- the first through `α`'s zero
and its `add_smul`, the second through `M`'s zero and its `smul_add` --- exactly
as the Challenge's own note requires, and neither transports anything. -/
theorem solution : challenge := by
  intro α M _ _ _ c x
  refine ⟨?_, ?_⟩
  · -- the ring's zero, by idempotence in the scalar argument
    exact Algebra.smulT_zero_scalar
      (addM := fun a b => a + b) (zeroM := (0 : M)) (negM := fun a => -a)
      (smul := fun (a : α) (m : M) => a • m)
      (addA := fun a b => a + b) (zeroA := (0 : α))
      (fun a b d => add_assoc a b d) (fun a => add_zero a)
      (fun a => add_neg_cancel a)
      (fun d e y => add_smul d e y) (add_zero (0 : α)) x
  · -- and the vector group's, the same argument on the other side
    exact Algebra.smulT_zero_vector
      (addM := fun a b => a + b) (zeroM := (0 : M)) (negM := fun a => -a)
      (smul := fun (a : α) (m : M) => a • m)
      (fun a b d => add_assoc a b d) (fun a => add_zero a)
      (fun a => add_neg_cancel a)
      (fun d y z => smul_add d y z) c

#print axioms rests_on_smulT_zero
#print axioms solution

end Comparator.ModuleQuotient
