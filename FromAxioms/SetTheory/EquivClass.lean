/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Equivalence classes and quotient sets.

The set-theoretic quotient, built without choice. The class of `a` is carved out
of `x` by separation, and the quotient is carved out of `𝒫 x` -- every class is
a subset of `x`, so the power set bounds the construction and Replacement is not
needed.

`cls_eq_cls_iff` states it: two classes are equal as sets exactly when their
representatives are related, so a quotient stands in for the relation.
-/

import FromAxioms.SetTheory.Relation

universe u

namespace SetTheory

structure IsEquivRel (r x : ZFSet.{u}) : Prop where
  refl : ∀ a, a ∈ x → opair a a ∈ r
  symm : ∀ a b, a ∈ x → b ∈ x → opair a b ∈ r → opair b a ∈ r
  trans : ∀ a b c, a ∈ x → b ∈ x → c ∈ x →
    opair a b ∈ r → opair b c ∈ r → opair a c ∈ r

def cls (r x a : ZFSet.{u}) : ZFSet.{u} := sep (fun b => opair a b ∈ r) x

@[simp] theorem mem_cls_iff (r x a b : ZFSet.{u}) :
    b ∈ cls r x a ↔ b ∈ x ∧ opair a b ∈ r :=
  mem_sep_iff _ b x

theorem cls_subset (r x a : ZFSet.{u}) : cls r x a ⊆ x :=
  fun _ hb => ((mem_cls_iff r x a _).mp hb).left

theorem mem_cls_self {r x a : ZFSet.{u}} (h : IsEquivRel r x) (ha : a ∈ x) :
    a ∈ cls r x a :=
  (mem_cls_iff r x a a).mpr ⟨ha, h.refl a ha⟩

theorem cls_eq_cls_iff {r x a b : ZFSet.{u}} (h : IsEquivRel r x)
    (ha : a ∈ x) (hb : b ∈ x) : cls r x a = cls r x b ↔ opair a b ∈ r := by
  constructor
  · intro he
    exact ((mem_cls_iff r x a b).mp (he ▸ mem_cls_self h hb)).right
  · intro hab
    refine ext _ _ fun c => ?_
    refine Iff.trans (mem_cls_iff r x a c) (Iff.trans ?_ (mem_cls_iff r x b c).symm)
    constructor
    · rintro ⟨hc, hac⟩
      exact ⟨hc, h.trans b a c hb ha hc (h.symm a b ha hb hab) hac⟩
    · rintro ⟨hc, hbc⟩
      exact ⟨hc, h.trans a b c ha hb hc hab hbc⟩

def quotientSet (r x : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun c => ∃ a, a ∈ x ∧ c = cls r x a) (powerset x)

@[simp] theorem cls_empty (r a : ZFSet.{u}) : cls r empty.{u} a = empty.{u} :=
  ext _ _ fun b => ⟨fun hb => absurd ((mem_sep_iff _ _ _).mp hb).left
    (not_mem_empty b), fun hb => absurd hb (not_mem_empty b)⟩

/-- Quotienting nothing gives nothing -- not the one-element set the powerset in
the definition might suggest, because a class needs a representative. -/
@[simp] theorem quotientSet_empty (r : ZFSet.{u}) :
    quotientSet r empty.{u} = empty.{u} := by
  refine ext _ _ fun c => ⟨fun hc => ?_, fun hc => absurd hc (not_mem_empty c)⟩
  obtain ⟨a, ha, -⟩ := ((mem_sep_iff _ _ _).mp hc).right
  exact absurd ha (not_mem_empty a)

theorem mem_quotientSet_iff (r x c : ZFSet.{u}) :
    c ∈ quotientSet r x ↔ ∃ a, a ∈ x ∧ c = cls r x a := by
  refine Iff.trans (mem_sep_iff _ c _) ⟨And.right, ?_⟩
  rintro ⟨a, ha, rfl⟩
  exact ⟨(mem_powerset_iff _ x).mpr (cls_subset r x a), a, ha, rfl⟩

theorem cls_mem_quotientSet {r x a : ZFSet.{u}} (ha : a ∈ x) :
    cls r x a ∈ quotientSet r x :=
  (mem_quotientSet_iff r x _).mpr ⟨a, ha, rfl⟩

/-- The class map, as a set of pairs: it sends each member to its class. -/
def clsMap (r G : ZFSet.{u}) : ZFSet.{u} :=
  graphOn G (quotientSet r G) (cls r G)

theorem app_clsMap {r G a : ZFSet.{u}} (ha : a ∈ G) :
    app (clsMap r G) a = cls r G a :=
  app_graphOn (fun _ hm => cls_mem_quotientSet hm) ha

#print axioms cls_eq_cls_iff
#print axioms mem_quotientSet_iff
#print axioms app_clsMap
end SetTheory

namespace ZFSet
export SetTheory (IsEquivRel app_clsMap cls clsMap cls_empty cls_eq_cls_iff cls_mem_quotientSet cls_subset mem_cls_iff mem_cls_self mem_quotientSet_iff quotientSet quotientSet_empty)
end ZFSet
