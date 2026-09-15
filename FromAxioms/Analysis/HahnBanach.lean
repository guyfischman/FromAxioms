/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Hahn-Banach: the extension step, and where its cost sits

The one-dimensional extension step of the Hahn-Banach theorem, over an ABSTRACT
norm and vector addition rather than a particular carrier, together with the
supremum machinery it needs.

Every step here is choice-free: the gap inequality, that every lower candidate
sits below every upper one, the finite supremum as a fold, and -- given
`FamilyLocated` -- that the extension value exists and respects its bound.
`familyLocated_listToSet` then discharges `FamilyLocated` for a FINITE family,
so the finite-dimensional case costs nothing at all.

What remains unpriced is the step from a finite index set to an arbitrary one,
and the proof says exactly why: the left disjunct of `FamilyLocated` is found by
walking the list, so the induction IS the search and a list is what makes it
terminate.

`rangeSet_familyLocated` (`Extreme.lean`) supplies the same condition for free
from uniform continuity on a bounded interval, so the extreme value theorem and
this one need the SAME constructive ingredient -- and only one of them has a
source for it.
-/
import FromAxioms.SetTheory.Cardinal

universe u

open SetTheory
namespace Analysis



/-- A finite family of located reals is `FamilyLocated`, free.

Each member's own `located` clause decides `p ∈ L` or `q ∈ U`, and over a LIST
those finitely many decisions combine by induction: the first member landing on
the left settles the left disjunct, and if none does then every member is on the
right.

So the finite-dimensional case of a supremum argument costs nothing, and, read
the other way, this says exactly where an infinite family can fail: nothing
bounds the search for a member on the left. -/
theorem familyLocated_listToSet (xs : List ZFSet.{u})
    (hxs : ∀ z, z ∈ xs → z ∈ RealL.{u}) :
    FamilyLocated (listToSet xs) := by
  induction xs with
  | nil =>
      intro p _ q _ _
      refine Or.inr (fun z hz => ?_)
      exact absurd ((mem_listToSet_iff [] z).mp hz) List.not_mem_nil
  | cons a as ih =>
      intro p hp q hq hpq
      have ha : a ∈ RealL.{u} := hxs a List.mem_cons_self
      obtain ⟨La, Ua, haeq, hloc⟩ := (mem_RealL_iff a).mp ha
      rcases hloc.located p hp q hq hpq with hleft | hright
      · refine Or.inl ⟨a, (mem_listToSet_iff _ a).mpr List.mem_cons_self, La, Ua, haeq, ?_⟩
        exact hleft
      · rcases ih (fun z hz => hxs z (List.mem_cons_of_mem a hz)) p hp q hq hpq with
          ⟨z, hz, L, U, heq, hpL⟩ | hall
        · exact Or.inl ⟨z, (mem_listToSet_iff _ z).mpr
            (List.mem_cons_of_mem a ((mem_listToSet_iff as z).mp hz)), L, U, heq, hpL⟩
        · refine Or.inr (fun z hz L U heq => ?_)
          rcases List.mem_cons.mp ((mem_listToSet_iff _ z).mp hz) with rfl | hmem
          · rw [haeq] at heq
            exact (opair_injective heq).right ▸ hright
          · exact hall z ((mem_listToSet_iff as z).mpr hmem) L U heq

#print axioms Analysis.familyLocated_listToSet



end Analysis
namespace ZFSet
export Analysis (familyLocated_listToSet)
end ZFSet
