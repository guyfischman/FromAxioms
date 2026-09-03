/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The constructible hierarchy

`V` (Hierarchy.lean) sends each stage to its power set. `L` sends it to the
definable power set instead -- the subsets a first-order formula picks out
over that stage (DefinablePower.lean) -- and everything else is `V`'s
construction unchanged.

The route is forced, and the two obvious ones do not work. Iterating an
operation over a set's members needs the image of that set, which is
`replacement` and takes a `Definable` -- a map carrying a pre-set realisation.

- `memRec` is the general ∈-recursion and does not help: its step is handed a
  dependent `∀ y, y ∈ x → ZFSet`, which is not a `ZFSet → ZFSet` at all, so no
  image of it is formable.
- `V` is not stated over its operation. `PSet.V ⟨α, A⟩` is structural at the
  pre-set level with `powerset` written in, so `L` is not an instantiation of
  it either.

What makes `L` reachable is that the definable power set HAS the pre-set
realisation: it is a separation over a power set, both liftings, so the
composite is their composite and `Definable.spec` is `rfl`. With that, `L` is
`V`'s own shape -- structural recursion on the pre-set, then a congruence
lemma to lift -- and no replacement is needed at all, because the index type
does the work the image would have done.

This is a construction ABOUT the theory, not inside it. `definablePower`
is a Lean-level operation on sets, so `L` here is not a model construction
carried out in the object language, and no relative-consistency result follows
from it. What would be needed for that is a definability
predicate expressible in the ∈-language, which is a different object and is not
built.
-/

import FromAxioms.SetTheory.DefinablePower
import FromAxioms.SetTheory.Hierarchy

universe u

namespace PSet

/-- The hierarchy at the pre-set level: keep the index type, and send each
branch to the definable power set of its stage. `PSet.V`'s recursion with the
operation swapped. -/
def L (F : Nat → List ZFSet.{u} → ZFSet.{u}) (R : Nat → List ZFSet.{u} → Prop) :
    PSet.{u} → PSet.{u}
  | ⟨α, A⟩ => sUnion ⟨α, fun a => SetTheory.definablePowerFam F R (L F R (A a))⟩

/-- `L` respects `Equiv`, by the same induction that defines it. The stage-wise
step is `Definable.congr` on the operation, where the pre-set realisation pays
for itself a second time. -/
theorem L_congr {F : Nat → List ZFSet.{u} → ZFSet.{u}}
    {R : Nat → List ZFSet.{u} → Prop} :
    ∀ {x y : PSet.{u}}, Equiv x y → Equiv (L F R x) (L F R y)
  | ⟨_, A⟩, ⟨_, B⟩, h => by
    refine sUnion_congr ?_
    refine (equiv_iff_ext _ _).mpr fun w => ⟨?_, ?_⟩
    · rintro ⟨a, hw⟩
      obtain ⟨b, hb⟩ := h.left a
      exact ⟨b, hw.trans (SetTheory.definablePowerFam_congr (L_congr hb))⟩
    · rintro ⟨b, hw⟩
      obtain ⟨a, ha⟩ := h.right b
      exact ⟨a, hw.trans (SetTheory.definablePowerFam_congr (L_congr ha)).symm⟩

end PSet

namespace SetTheory

/-- The constructible hierarchy on sets. -/
def L (F : Nat → List ZFSet.{u} → ZFSet.{u}) (R : Nat → List ZFSet.{u} → Prop) :
    ZFSet.{u} → ZFSet.{u} :=
  Quotient.lift (fun p => mk (PSet.L F R p))
    (fun _ _ h => Quotient.sound (PSet.L_congr h))

#print axioms PSet.L_congr
#print axioms L
end SetTheory

namespace ZFSet
export SetTheory (L)
end ZFSet
