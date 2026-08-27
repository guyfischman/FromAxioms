/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The algebra of sets.

Binary union, intersection, difference and singletons, plus the standard laws
relating them. None of this needs new machinery: every operation is a few lines
from `sUnion`, `pair` and `sep`, which `ZFSet.lean` already provides.

    singleton x = insert x ∅          union x y = ⋃₀ {x, y}
    inter x y   = { w ∈ x | w ∈ y }   sdiff x y = { w ∈ x | w ∉ y }

Every proof below has the same shape: apply `ext`, rewrite membership on both
sides, and discharge the propositional core.
-/

import FromAxioms.SetTheory.PSet
import FromAxioms.SetTheory.ZFSet

universe u

open SetTheory
namespace Algebra

/-! ## Singletons -/

def singleton (x : ZFSet.{u}) : ZFSet.{u} := insert x empty

@[simp] theorem mem_singleton_iff (w x : ZFSet.{u}) : w ∈ singleton x ↔ w = x := by
  refine Iff.trans (mem_insert_iff w x empty) ?_
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (not_mem_empty w)
  · exact Or.inl

theorem mem_singleton_self (x : ZFSet.{u}) : x ∈ singleton x :=
  (mem_singleton_iff x x).mpr rfl

theorem singleton_injective {x y : ZFSet.{u}} (h : singleton x = singleton y) : x = y :=
  (mem_singleton_iff x y).mp (h ▸ mem_singleton_self x)

/-! ## Union, intersection, difference

Registered against Lean's `Union`/`Inter`/`SDiff` classes so the laws below can
be stated with `∪`, `∩` and `\` rather than as nested applications. -/

def union (x y : ZFSet.{u}) : ZFSet.{u} := sUnion (pair x y)

def inter (x y : ZFSet.{u}) : ZFSet.{u} := sep (fun w => w ∈ y) x

def sdiff (x y : ZFSet.{u}) : ZFSet.{u} := sep (fun w => w ∉ y) x

instance : Union ZFSet.{u} := ⟨union⟩
instance : Inter ZFSet.{u} := ⟨inter⟩
instance : SDiff ZFSet.{u} := ⟨sdiff⟩

@[simp] theorem mem_union_iff (w x y : ZFSet.{u}) : w ∈ x ∪ y ↔ w ∈ x ∨ w ∈ y := by
  refine Iff.trans (mem_sUnion_iff w (pair x y)) ?_
  constructor
  · rintro ⟨z, hz, hwz⟩
    rcases (mem_pair_iff z x y).mp hz with rfl | rfl
    · exact Or.inl hwz
    · exact Or.inr hwz
  · rintro (h | h)
    · exact ⟨x, (mem_pair_iff x x y).mpr (Or.inl rfl), h⟩
    · exact ⟨y, (mem_pair_iff y x y).mpr (Or.inr rfl), h⟩

@[simp] theorem mem_inter_iff (w x y : ZFSet.{u}) : w ∈ x ∩ y ↔ w ∈ x ∧ w ∈ y :=
  mem_sep_iff (fun w => w ∈ y) w x

@[simp] theorem mem_sdiff_iff (w x y : ZFSet.{u}) : w ∈ x \ y ↔ w ∈ x ∧ w ∉ y :=
  mem_sep_iff (fun w => w ∉ y) w x

/-! ## The laws

`ext` reduces each to a propositional identity, which `simp` then closes using
the membership lemmas above. -/


@[simp] theorem union_self (x : ZFSet.{u}) : x ∪ x = x :=
  ext _ _ fun z => by simp

@[simp] theorem union_empty (x : ZFSet.{u}) : x ∪ empty.{u} = x :=
  ext _ _ fun z => by simp

@[simp] theorem empty_union (x : ZFSet.{u}) : empty.{u} ∪ x = x :=
  ext _ _ fun z => by simp

@[simp] theorem inter_self (x : ZFSet.{u}) : x ∩ x = x :=
  ext _ _ fun z => by simp

@[simp] theorem inter_empty (x : ZFSet.{u}) : x ∩ empty.{u} = empty.{u} :=
  ext _ _ fun z => by simp

@[simp] theorem empty_inter (x : ZFSet.{u}) : empty.{u} ∩ x = empty.{u} :=
  ext _ _ fun z => by simp

/-! ### Absorption -/

@[simp] theorem union_inter_cancel (x y : ZFSet.{u}) : x ∪ x ∩ y = x :=
  ext _ _ fun w => by
    simp only [mem_union_iff, mem_inter_iff]
    exact ⟨fun h => h.elim id And.left, Or.inl⟩

@[simp] theorem inter_union_cancel (x y : ZFSet.{u}) : x ∩ (x ∪ y) = x :=
  ext _ _ fun w => by
    simp only [mem_union_iff, mem_inter_iff]
    exact ⟨And.left, fun h => ⟨h, Or.inl h⟩⟩

/-! ### Difference, and relative De Morgan

`ZFSet` has no complement -- there is no universal set -- so De Morgan appears
in its relative form, with `x \ ·` playing the part of negation. -/

@[simp] theorem sdiff_self (x : ZFSet.{u}) : x \ x = empty.{u} :=
  ext _ _ fun w => by simp

@[simp] theorem sdiff_empty (x : ZFSet.{u}) : x \ empty.{u} = x :=
  ext _ _ fun w => by simp

@[simp] theorem empty_sdiff (x : ZFSet.{u}) : empty.{u} \ x = empty.{u} :=
  ext _ _ fun w => by simp

/-! ### Difference against itself -/

/-- Removing `x` from anything already inside `x` leaves nothing. -/
@[simp] theorem sdiff_sdiff_left_self (x y : ZFSet.{u}) : (x \ y) \ x = empty.{u} :=
  ext _ _ fun w => by
    simp only [mem_sdiff_iff, not_mem_empty, iff_false]
    rintro ⟨⟨h, _⟩, h'⟩
    exact h' h

/-! ### Subset characterizations -/

@[simp] theorem empty_subset (x : ZFSet.{u}) : empty.{u} ⊆ x :=
  fun w hw => absurd hw (not_mem_empty w)

@[simp] theorem sUnion_singleton (x : ZFSet.{u}) : sUnion (singleton x) = x :=
  ext _ _ fun w => by
    simp only [mem_sUnion_iff, mem_singleton_iff]
    exact ⟨fun ⟨_, hz, hw⟩ => hz ▸ hw, fun hw => ⟨x, rfl, hw⟩⟩

/-! ## Audit -/

#print axioms mem_union_iff
#print axioms empty_subset
#print axioms sdiff_sdiff_left_self

end Algebra
#print axioms Algebra.empty_inter
#print axioms Algebra.empty_sdiff
#print axioms Algebra.inter_union_cancel
#print axioms Algebra.union_inter_cancel
namespace ZFSet
export Algebra (empty_inter empty_sdiff empty_subset empty_union inter inter_empty inter_self inter_union_cancel mem_inter_iff mem_sdiff_iff mem_singleton_iff mem_singleton_self mem_union_iff sUnion_singleton sdiff sdiff_empty sdiff_sdiff_left_self sdiff_self singleton singleton_injective union union_empty union_inter_cancel union_self)
end ZFSet
