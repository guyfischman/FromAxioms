/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Toward Sylow: transporting an order through a quotient.

`ClassEquation.lean` gives the p-group centre; `Cyclic.lean` gives orders and
the divisibility of exponents. Cauchy's theorem needs both, so this file sits
above both rather than pulling either under the other.
-/

import FromAxioms.NumberTheory.Prime
import FromAxioms.SetTheory.Cardinal

universe u

open NumberTheory SetTheory
namespace Algebra

/-! ## Bipartite graphs, as a relation on a product

No new object: a bipartite graph is a subset of `prod A B`, and the
neighbourhood of a set is a `sep` over `B`. Everything Hall needs about
finiteness and enumeration is already in `Cardinal.lean` and
`DisjointCount.lean`. -/

/-- The neighbourhood of `S` across the relation `R`. -/
def nbhd (R B S : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun b => ∃ a, a ∈ S ∧ opair a b ∈ R) B

theorem mem_nbhd_iff (R B S b : ZFSet.{u}) :
    b ∈ nbhd R B S ↔ b ∈ B ∧ ∃ a, a ∈ S ∧ opair a b ∈ R :=
  mem_sep_iff _ _ _

/-- Hall's condition: every set of boys knows at least as many girls.

Stated with the two counts SUPPLIED rather than existentially, so the condition
says nothing about finiteness and carries no decision -- the caller produces the
counts from whatever finiteness it has. -/
def HallCondition (R A B : ZFSet.{u}) : Prop :=
  ∀ S, S ⊆ A → ∀ s t : Nat,
    Equinumerous S (ofNat.{u} s) → Equinumerous (nbhd R B S) (ofNat.{u} t) →
      s ≤ t

/-- A matching: an injective function from `A` into `B` whose graph lies
inside `R`. -/
def IsMatching (M R A B : ZFSet.{u}) : Prop :=
  M ⊆ R ∧ IsInjection M A B

/-- Two injections with disjoint domains and disjoint codomains union to an
injection.

`Cardinal.lean` has the COUNT version (`equinumerous_union_disjoint`) and not
this one. Hall's theorem needs it to glue the two halves of the critical-set
split, where the codomains are disjoint by construction. -/
theorem isInjection_union {f g x y z w : ZFSet.{u}}
    (hf : IsInjection f x z) (hg : IsInjection g y w)
    (hdx : ∀ a, a ∈ x → a ∉ y) (hdz : ∀ b, b ∈ z → b ∉ w) :
    IsInjection (f ∪ g) (x ∪ y) (z ∪ w) := by
  obtain ⟨hffun, hfdom, hfran, hfinj⟩ := hf
  obtain ⟨hgfun, hgdom, hgran, hginj⟩ := hg
  -- `isFunction_union` is already in `Relation.lean`; it wants the
  -- disjointness as a statement about PAIRS, which the domains supply
  have hfun : IsFunction (f ∪ g) :=
    isFunction_union hffun hgfun (fun a b c hb hc =>
      hdx a (hfdom ▸ (mem_domain_iff a f).mpr ⟨b, hb⟩)
        (hgdom ▸ (mem_domain_iff a g).mpr ⟨c, hc⟩))
  -- the union agrees with each side on that side's domain
  have hvalf : ∀ c, c ∈ x → app (f ∪ g) c = app f c := by
    intro c hc
    obtain ⟨d, hd⟩ := (mem_domain_iff c f).mp (hfdom ▸ hc)
    rw [app_eq hffun hd]
    exact app_eq hfun ((mem_union_iff _ _ _).mpr (Or.inl hd))
  have hvalg : ∀ c, c ∈ y → app (f ∪ g) c = app g c := by
    intro c hc
    obtain ⟨d, hd⟩ := (mem_domain_iff c g).mp (hgdom ▸ hc)
    rw [app_eq hgfun hd]
    exact app_eq hfun ((mem_union_iff _ _ _).mpr (Or.inr hd))
  refine ⟨hfun, ?_, ?_, ?_⟩
  · refine ext _ _ (fun a => ⟨fun ha => ?_, fun ha => ?_⟩)
    · obtain ⟨b, hb⟩ := (mem_domain_iff a _).mp ha
      rcases (mem_union_iff _ _ _).mp hb with h | h
      · exact (mem_union_iff _ _ _).mpr
          (Or.inl (hfdom ▸ (mem_domain_iff a f).mpr ⟨b, h⟩))
      · exact (mem_union_iff _ _ _).mpr
          (Or.inr (hgdom ▸ (mem_domain_iff a g).mpr ⟨b, h⟩))
    · rcases (mem_union_iff _ _ _).mp ha with h | h
      · obtain ⟨b, hb⟩ := (mem_domain_iff a f).mp (hfdom ▸ h)
        exact (mem_domain_iff a _).mpr ⟨b, (mem_union_iff _ _ _).mpr (Or.inl hb)⟩
      · obtain ⟨b, hb⟩ := (mem_domain_iff a g).mp (hgdom ▸ h)
        exact (mem_domain_iff a _).mpr ⟨b, (mem_union_iff _ _ _).mpr (Or.inr hb)⟩
  · intro b hb
    obtain ⟨a, ha⟩ := (mem_range_iff b _).mp hb
    rcases (mem_union_iff _ _ _).mp ha with h | h
    · exact (mem_union_iff _ _ _).mpr
        (Or.inl (hfran _ ((mem_range_iff b f).mpr ⟨a, h⟩)))
    · exact (mem_union_iff _ _ _).mpr
        (Or.inr (hgran _ ((mem_range_iff b g).mpr ⟨a, h⟩)))
  · -- a shared value would have to cross the disjoint codomains
    intro a ha b hb he
    rcases (mem_union_iff _ _ _).mp ha with h1 | h1 <;>
      rcases (mem_union_iff _ _ _).mp hb with h2 | h2
    · rw [hvalf a h1, hvalf b h2] at he
      exact hfinj a h1 b h2 he
    · exfalso
      rw [hvalf a h1, hvalg b h2] at he
      refine hdz (app f a) (hfran _ ?_) (he ▸ hgran _ ?_)
      · obtain ⟨d, hd⟩ := (mem_domain_iff a f).mp (hfdom ▸ h1)
        exact (mem_range_iff _ f).mpr ⟨a, (app_eq hffun hd) ▸ hd⟩
      · obtain ⟨d, hd⟩ := (mem_domain_iff b g).mp (hgdom ▸ h2)
        exact (mem_range_iff _ g).mpr ⟨b, (app_eq hgfun hd) ▸ hd⟩
    · exfalso
      rw [hvalg a h1, hvalf b h2] at he
      refine hdz (app f b) (hfran _ ?_) (he ▸ hgran _ ?_)
      · obtain ⟨d, hd⟩ := (mem_domain_iff b f).mp (hfdom ▸ h2)
        exact (mem_range_iff _ f).mpr ⟨b, (app_eq hffun hd) ▸ hd⟩
      · obtain ⟨d, hd⟩ := (mem_domain_iff a g).mp (hgdom ▸ h1)
        exact (mem_range_iff _ g).mpr ⟨a, (app_eq hgfun hd) ▸ hd⟩
    · rw [hvalg a h1, hvalg b h2] at he
      exact hginj a h1 b h2 he

#print axioms isInjection_union
#print axioms nbhd
#print axioms mem_nbhd_iff
#print axioms HallCondition
#print axioms IsMatching
end Algebra

namespace ZFSet
export Algebra (HallCondition IsMatching isInjection_union mem_nbhd_iff nbhd)
end ZFSet
