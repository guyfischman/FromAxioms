/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The von Neumann hierarchy.

    V x = ⋃ { 𝒫 (V y) | y ∈ x }

Read on ordinals this is the usual cumulative hierarchy; read on arbitrary sets
it is the same recursion with no well-ordering required, which is what makes it
available here.

Two things make it cheap. At the pre-set level the recursion is structural --
a pre-set is an index type together with a family, so the family of stages is
already indexed and the union of it is a pre-set with the same index type. No
well-foundedness, no replacement, nothing to assume. And the lift to `ZFSet` is
`Quotient.lift` over a congruence proof, as everywhere else.

The theorem worth having is `mem_V_succ`: every set appears at some stage. It
comes from `subset_V` by ∈-induction, and both are constructive -- the
well-foundedness that classical set theory assumes in order to build this
hierarchy was already a theorem here.
-/

import FromAxioms.NumberTheory.Natural

universe u

namespace PSet

/-- The hierarchy, by structural recursion: keep the index type, and send each
branch to the power set of its stage. -/
def V : PSet.{u} → PSet.{u}
  | ⟨α, A⟩ => sUnion ⟨α, fun a => powerset (V (A a))⟩

/-- `V` respects `Equiv`, by the same induction that defines it. -/
theorem V_congr : ∀ {x y : PSet.{u}}, Equiv x y → Equiv (V x) (V y)
  | ⟨α, A⟩, ⟨β, B⟩, h => by
    refine sUnion_congr ?_
    refine (equiv_iff_ext _ _).mpr fun w => ⟨?_, ?_⟩
    · rintro ⟨a, hw⟩
      obtain ⟨b, hb⟩ := h.left a
      exact ⟨b, hw.trans (powerset_congr (V_congr hb))⟩
    · rintro ⟨b, hw⟩
      obtain ⟨a, ha⟩ := h.right b
      exact ⟨a, hw.trans (powerset_congr (V_congr ha)).symm⟩

end PSet

open NumberTheory
namespace SetTheory

/-- The hierarchy on sets. -/
def V : ZFSet.{u} → ZFSet.{u} :=
  Quotient.lift (fun x => mk (PSet.V x)) (fun _ _ h => Quotient.sound (PSet.V_congr h))

#print axioms PSet.V_congr
end SetTheory

namespace ZFSet
export SetTheory (V)
end ZFSet
