/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Ordered pairs and products.

Sets are unordered, so an ordered pair has to be encoded. Kuratowski's encoding
is `⟨a, b⟩ = {{a}, {a, b}}`: the first coordinate is distinguished by appearing
in both members.

Everything here rests on `opair_injective`, which is what makes the encoding an
encoding at all. The cartesian product then carves out of
`𝒫(𝒫(x ∪ y))` -- the smallest set-theoretic universe large enough to hold every
`⟨a, b⟩` with `a ∈ x` and `b ∈ y`.
-/

import FromAxioms.Algebra.Algebra

universe u

open Algebra
namespace SetTheory

/-! ## Unordered pairs, refined -/

@[simp] theorem pair_self (a : ZFSet.{u}) : pair a a = singleton a :=
  ext _ _ fun w => by simp [mem_pair_iff, mem_singleton_iff]

theorem pair_comm (a b : ZFSet.{u}) : pair a b = pair b a :=
  ext _ _ fun w => by simp [mem_pair_iff, Or.comm]

theorem pair_eq_singleton_iff (a b c : ZFSet.{u}) :
    pair a b = singleton c ↔ a = c ∧ b = c := by
  constructor
  · intro h
    have ha : a ∈ singleton c := h ▸ (mem_pair_iff a a b).mpr (Or.inl rfl)
    have hb : b ∈ singleton c := h ▸ (mem_pair_iff b a b).mpr (Or.inr rfl)
    exact ⟨(mem_singleton_iff a c).mp ha, (mem_singleton_iff b c).mp hb⟩
  · rintro ⟨rfl, rfl⟩
    exact pair_self _

theorem pair_eq_pair_iff (a b c d : ZFSet.{u}) :
    pair a b = pair c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha := (mem_pair_iff a c d).mp (h ▸ (mem_pair_iff a a b).mpr (Or.inl rfl))
    have hb := (mem_pair_iff b c d).mp (h ▸ (mem_pair_iff b a b).mpr (Or.inr rfl))
    have hc := (mem_pair_iff c a b).mp (h ▸ (mem_pair_iff c c d).mpr (Or.inl rfl))
    have hd := (mem_pair_iff d a b).mp (h ▸ (mem_pair_iff d c d).mpr (Or.inr rfl))
    rcases ha with rfl | rfl
    · rcases hb with rfl | rfl
      · rcases hd with rfl | rfl <;> simp_all
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases hb with rfl | rfl
      · exact Or.inr ⟨rfl, rfl⟩
      · rcases hc with rfl | rfl <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact pair_comm _ _

/-! ## Ordered pairs -/

/-- The ordered pair from sets, in Kuratowski's encoding. -/
def opair (a b : ZFSet.{u}) : ZFSet.{u} := pair (singleton a) (pair a b)

@[simp] theorem mem_opair_iff (w a b : ZFSet.{u}) :
    w ∈ opair a b ↔ w = singleton a ∨ w = pair a b :=
  mem_pair_iff w (singleton a) (pair a b)

/-- The encoding is faithful: `⟨a, b⟩` determines both coordinates. -/
theorem opair_injective {a b c d : ZFSet.{u}} (h : opair a b = opair c d) :
    a = c ∧ b = d := by
  rcases (pair_eq_pair_iff _ _ _ _).mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · -- {a} = {c} and {a,b} = {c,d}
    have hac : a = c := singleton_injective h₁
    subst hac
    rcases (pair_eq_pair_iff a b a d).mp h₂ with ⟨_, hbd⟩ | ⟨had, hba⟩
    · exact ⟨rfl, hbd⟩
    · subst hba; subst had; exact ⟨rfl, rfl⟩
  · -- {a} = {c,d} and {a,b} = {c}
    obtain ⟨hca, hda⟩ := (pair_eq_singleton_iff c d a).mp h₁.symm
    obtain ⟨_, hba⟩ := (pair_eq_singleton_iff a b c).mp h₂
    subst hca; subst hda; subst hba
    exact ⟨rfl, rfl⟩

@[simp] theorem opair_eq_opair_iff (a b c d : ZFSet.{u}) :
    opair a b = opair c d ↔ a = c ∧ b = d :=
  ⟨opair_injective, fun ⟨hc, hd⟩ => by rw [hc, hd]⟩

/-! ## The cartesian product

`⟨a, b⟩` has `{a}` and `{a, b}` as members, both subsets of `x ∪ y`, so the pair
itself lies in `𝒫(𝒫(x ∪ y))`. Separation cuts the product out of that. -/

/-- The cartesian product: coordinates, as a set of ordered pairs. -/
def prod (x y : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ a, a ∈ x ∧ ∃ b, b ∈ y ∧ p = opair a b)
    (powerset (powerset (x ∪ y)))

theorem opair_mem_powerset {a b x y : ZFSet.{u}} (ha : a ∈ x) (hb : b ∈ y) :
    opair a b ∈ powerset (powerset (x ∪ y)) := by
  refine (mem_powerset_iff _ _).mpr fun w hw => ?_
  refine (mem_powerset_iff _ _).mpr fun v hv => ?_
  rcases (mem_opair_iff w a b).mp hw with rfl | rfl
  · rw [(mem_singleton_iff v a).mp hv]
    exact (mem_union_iff a x y).mpr (Or.inl ha)
  · rcases (mem_pair_iff v a b).mp hv with rfl | rfl
    · exact (mem_union_iff v x y).mpr (Or.inl ha)
    · exact (mem_union_iff v x y).mpr (Or.inr hb)

theorem mem_prod_iff (p x y : ZFSet.{u}) :
    p ∈ prod x y ↔ ∃ a, a ∈ x ∧ ∃ b, b ∈ y ∧ p = opair a b := by
  refine Iff.trans (mem_sep_iff _ p _) ?_
  constructor
  · exact And.right
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨opair_mem_powerset ha hb, a, ha, b, hb, rfl⟩

theorem opair_mem_prod {a b x y : ZFSet.{u}} (ha : a ∈ x) (hb : b ∈ y) :
    opair a b ∈ prod x y :=
  (mem_prod_iff _ x y).mpr ⟨a, ha, b, hb, rfl⟩

theorem mem_prod_left {a b x y : ZFSet.{u}} (h : opair a b ∈ prod x y) : a ∈ x := by
  obtain ⟨a', ha', b', hb', he⟩ := (mem_prod_iff _ x y).mp h
  obtain ⟨rfl, rfl⟩ := opair_injective he
  exact ha'

theorem mem_prod_right {a b x y : ZFSet.{u}} (h : opair a b ∈ prod x y) : b ∈ y := by
  obtain ⟨a', ha', b', hb', he⟩ := (mem_prod_iff _ x y).mp h
  obtain ⟨rfl, rfl⟩ := opair_injective he
  exact hb'

@[simp] theorem prod_empty (x : ZFSet.{u}) : prod x empty.{u} = empty.{u} :=
  ext _ _ fun w => by
    simp only [mem_prod_iff, not_mem_empty, iff_false]
    rintro ⟨_, _, _, hb, _⟩
    exact hb

@[simp] theorem empty_prod (y : ZFSet.{u}) : prod empty.{u} y = empty.{u} :=
  ext _ _ fun w => by
    simp only [mem_prod_iff, not_mem_empty, iff_false]
    rintro ⟨_, ha, _⟩
    exact ha

/-! ## Projections

The coordinates of a pair, extracted the way `app` extracts a value: separate
out the ones that work, note that there is exactly one, and take `⋃` of the
resulting singleton. No choice: the object is provably unique, and `⋃` of a
singleton is a definable operation.

The separation is over `⋃p`, which for `⟨a,b⟩ = {{a},{a,b}}` is `{a,b}`. -/

theorem fst_mem_sUnion (a b : ZFSet.{u}) : a ∈ sUnion (opair a b) :=
  (mem_sUnion_iff a _).mpr ⟨singleton a, (mem_opair_iff _ a b).mpr (Or.inl rfl),
    mem_singleton_self a⟩

theorem snd_mem_sUnion (a b : ZFSet.{u}) : b ∈ sUnion (opair a b) :=
  (mem_sUnion_iff b _).mpr ⟨pair a b, (mem_opair_iff _ a b).mpr (Or.inr rfl),
    (mem_pair_iff b a b).mpr (Or.inr rfl)⟩

def fst (p : ZFSet.{u}) : ZFSet.{u} :=
  sUnion (sep (fun a => ∃ b, p = opair a b) (sUnion p))

def snd (p : ZFSet.{u}) : ZFSet.{u} :=
  sUnion (sep (fun b => ∃ a, p = opair a b) (sUnion p))

@[simp] theorem fst_opair (a b : ZFSet.{u}) : fst (opair a b) = a := by
  have hsep : sep (fun x => ∃ y, opair a b = opair x y) (sUnion (opair a b))
      = singleton a := by
    refine ext _ _ fun x => ?_
    refine Iff.trans (mem_sep_iff _ _ _) (Iff.trans ?_ (mem_singleton_iff x a).symm)
    constructor
    · rintro ⟨-, y, he⟩
      exact (opair_injective he).left.symm
    · rintro rfl
      exact ⟨fst_mem_sUnion x b, b, rfl⟩
  rw [fst, hsep, sUnion_singleton]

@[simp] theorem snd_opair (a b : ZFSet.{u}) : snd (opair a b) = b := by
  have hsep : sep (fun y => ∃ x, opair a b = opair x y) (sUnion (opair a b))
      = singleton b := by
    refine ext _ _ fun y => ?_
    refine Iff.trans (mem_sep_iff _ _ _) (Iff.trans ?_ (mem_singleton_iff y b).symm)
    constructor
    · rintro ⟨-, x, he⟩
      exact (opair_injective he).right.symm
    · rintro rfl
      exact ⟨snd_mem_sUnion a y, a, rfl⟩
  rw [snd, hsep, sUnion_singleton]

#print axioms opair_injective
#print axioms fst_opair
#print axioms snd_opair
#print axioms mem_prod_iff

/-! ## The tagged union

Two sets side by side, each member carrying which side it came from. The tags
are `empty` and `singleton empty`; nothing about them matters except that they
differ, which `tag_ne` proves from `not_mem_empty`.

The point of tagging rather than taking `x ∪ y` is that the halves stay
separable WITHOUT deciding membership: a map out of the union can be assembled
as a union of two graphs on disjoint domains, where the alternative -- a case
split on which side a member came from -- would be a case split on an equality
of sets and is not available. -/

#print axioms opair_mem_prod

/-- Membership in a relation cut out of `prod X X`. A relation on pairs
is a subset of `prod X X` carved by a condition on the four coordinates;
deciding membership means unfolding the separation, splitting the outer pair
and then both inner ones, and rebuilding the product membership on the way
back.

Written out once here rather than once per relation. The integer and rational relations each state their
membership in one line by applying it, as does the fraction relation on the
analysis track.
-/
theorem mem_pairRel_iff {X a b c d : ZFSet.{u}}
    {P : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}
    (hab : opair a b ∈ X) (hcd : opair c d ∈ X) :
    opair (opair a b) (opair c d) ∈
      sep (fun p => ∃ w x y z, p = opair (opair w x) (opair y z) ∧ P w x y z)
        (prod X X) ↔ P a b c d := by
  refine Iff.trans (mem_sep_iff _ _ _) ⟨?_, ?_⟩
  · rintro ⟨_, a', b', c', d', he, h⟩
    obtain ⟨h₁, h₂⟩ := opair_injective he
    obtain ⟨rfl, rfl⟩ := opair_injective h₁
    obtain ⟨rfl, rfl⟩ := opair_injective h₂
    exact h
  · intro h
    exact ⟨opair_mem_prod hab hcd, a, b, c, d, rfl, h⟩

#print axioms mem_pairRel_iff


end SetTheory

namespace ZFSet
export SetTheory (empty_prod fst fst_mem_sUnion fst_opair mem_opair_iff mem_pairRel_iff mem_prod_iff mem_prod_left mem_prod_right opair opair_eq_opair_iff opair_injective opair_mem_powerset opair_mem_prod pair_comm pair_eq_pair_iff pair_eq_singleton_iff pair_self prod prod_empty snd snd_mem_sUnion snd_opair)
end ZFSet
