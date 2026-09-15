/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# What the classical audit lines actually establish.

`#print axioms` is an upper bound. It reports the axioms a proof used, never
the ones a theorem needs, and the gap is concrete here: two proofs of the
same walk, one paying `Classical.choice` and one not.

The lower bound has to be argued the other way round -- by deriving a known
non-constructive principle from the theorem, in a proof that is itself
choice-free. Then the audit line on the reversal certifies that the classical
content is real and not an artefact of how the proof was written.

The witness both reversals use is the cut of a proposition:

    propCut p = { q ∈ ℚ | q < 0 ∨ (p ∧ q < 1) }

which is `0` when `p` fails and `1` when it holds, without deciding which. Any
principle strong enough to place it relative to a rational strictly between `0`
and `1` therefore decides `p`.
-/

import FromAxioms.Analysis.Located

universe u

open Analysis NumberTheory SetTheory
namespace Constructive

/-- Excluded middle, stated inside this development so it can be a conclusion. -/
def EM : Prop := ∀ p : Prop, p ∨ ¬ p

/-- The family `{0} ∪ {1 | p}`: inhabited and bounded above however `p` turns
out, with supremum `0` or `1` accordingly. -/
private def propFamily (p : Prop) : ZFSet.{u} :=
  sep (fun c => c = realZero.{u} ∨ (p ∧ c = ratCut ratOne.{u})) Real.{u}

private theorem mem_propFamily_iff (p : Prop) (c : ZFSet.{u}) :
    c ∈ propFamily.{u} p ↔
      c ∈ Real.{u} ∧ (c = realZero.{u} ∨ (p ∧ c = ratCut ratOne.{u})) :=
  mem_sep_iff _ c _

/-- The trade-off, made precise. Completeness on the located encoding would
have to produce a located supremum, and that decides `p` for the two-element
family `{0} ∪ {1 | p}`. So the two encodings cannot both be free: one-sided cuts
buy completeness and lose the additive group, located pairs buy the
group and lose completeness. -/
theorem em_of_sup_located
    (h : ∀ S : ZFSet.{u}, S ⊆ Real.{u} → (∃ c, c ∈ S) →
      (∃ b, b ∈ Real.{u} ∧ ∀ c, c ∈ S → realLe c b) →
      (∀ c, c ∈ S → Located c) → Located (sUnion S)) : EM := by
  intro p
  obtain ⟨t, htQ, h0t, ht1⟩ := rat_dense ratZero_mem_Rat ratOne_mem_Rat ratZero_lt_one
  have hzeroLoc : Located realZero.{u} :=
    located_of_isLocated (isLocated_ratCut ratZero_mem_Rat)
  have honeLoc : Located (ratCut ratOne.{u}) :=
    located_of_isLocated (isLocated_ratCut ratOne_mem_Rat)
  have hzero_sub_one : realLe realZero.{u} (ratCut ratOne.{u}) := by
    intro q hq
    obtain ⟨hqQ, hq0⟩ := (mem_ratCut_iff ratZero.{u} q).mp hq
    exact (mem_ratCut_iff ratOne.{u} q).mpr
      ⟨hqQ, ratLt_trans hqQ ratZero_mem_Rat ratOne_mem_Rat hq0 ratZero_lt_one⟩
  have hmemS := mem_propFamily_iff p
  have hloc := h (propFamily.{u} p) (fun c hc => ((hmemS c).mp hc).left)
    ⟨realZero.{u}, (hmemS _).mpr ⟨realZero_mem_Real, Or.inl rfl⟩⟩
    ⟨ratCut ratOne.{u}, ratCut_mem_Real ratOne_mem_Rat, fun c hc => by
      rcases ((hmemS c).mp hc).right with rfl | ⟨-, rfl⟩
      · exact hzero_sub_one
      · exact realLe_refl _⟩
    (fun c hc => by
      rcases ((hmemS c).mp hc).right with rfl | ⟨-, rfl⟩
      · exact hzeroLoc
      · exact honeLoc)
  obtain ⟨q, hq, s, hsQ, hs, hlt⟩ := hloc t htQ h0t
  obtain ⟨c, hc, hqc⟩ := (mem_sUnion_iff q (propFamily.{u} p)).mp hq
  have hqQ : q ∈ NumberTheory.Rat.{u} := ((mem_Real_iff c).mp ((hmemS c).mp hc).left).subset q hqc
  rcases ratLt_trichotomy ratZero_mem_Rat hqQ with h0q | h0q | h0q
  · -- `q` is positive, so the rung it came from cannot be `0`
    rcases ((hmemS c).mp hc).right with rfl | ⟨hp, -⟩
    · exact absurd (ratLt_trans ratZero_mem_Rat hqQ ratZero_mem_Rat h0q
        ((mem_ratCut_iff ratZero.{u} q).mp hqc).right) ratLt_irrefl
    · exact Or.inl hp
  · rcases ((hmemS c).mp hc).right with rfl | ⟨hp, -⟩
    · exact absurd (h0q ▸ ((mem_ratCut_iff ratZero.{u} q).mp hqc).right) ratLt_irrefl
    · exact Or.inl hp
  · -- `s` is below `1`, so if `p` held it would be in the union
    refine Or.inr fun hp => hs ?_
    have hqt : ratLe (ratAdd q t) t := by
      have hstep := (ratAdd_le_add_right_iff htQ hqQ ratZero_mem_Rat).mpr h0q.left
      rwa [ratZero_add htQ] at hstep
    have hs1 : ratLt s ratOne.{u} := ratLt_trans hsQ htQ ratOne_mem_Rat
      (ratLt_of_lt_of_le hsQ (ratAdd_mem_Rat hqQ htQ) htQ hlt hqt) ht1
    exact (mem_sUnion_iff s (propFamily.{u} p)).mpr ⟨ratCut ratOne.{u},
      (hmemS _).mpr ⟨ratCut_mem_Real ratOne_mem_Rat, Or.inr ⟨hp, rfl⟩⟩,
      (mem_ratCut_iff ratOne.{u} s).mpr ⟨hsQ, hs1⟩⟩


/-- Weak excluded middle, the target for `sdiff_inter`, which is de Morgan's
third law and strictly weaker than `EM`. -/
def WEM : Prop := ∀ p : Prop, ¬ p ∨ ¬ ¬ p

/-- `EM` gives `WEM`, which the prose has asserted since the two names appeared
and nothing proved. The lattice check wants a witness for every edge, and this
is the edge that had none. -/
theorem wem_of_em (hem : EM) : WEM := fun p =>
  (hem p).elim (fun hp => Or.inr fun hnp => hnp hp) Or.inl

/-- Regularity as a statement about sets, named as a Prop so the registry can
reverse to it --- the `Zermelo-Fraenkel set theory` row's landmark.

Every non-empty set has a member disjoint from it. `regularity_of_em` concluded
it inline, so the row's two ends were not one identifier; naming it makes them
one. -/
def Regularity : Prop :=
  ∀ x : ZFSet.{u}, x ≠ empty.{u} →
    ∃ y : ZFSet.{u}, y ∈ x ∧ ∀ z : ZFSet.{u}, z ∈ y → z ∉ x

/-! ## The other direction

`statement → EM` is a lower bound. These are the matching upper bounds, in the
same currency: `EM → statement`, with nothing beyond the quotient. The pair
pins each result to exactly excluded middle, which the build alone cannot say
-- Lean's `Classical.em` is derived from `Classical.choice` and reports only the
latter, so a Phase 2 audit line cannot tell the two apart.

`realMul` is absent because it is a definition by cases, and defining data by
cases needs the decision as data (`Decidable`), which `EM` -- a `Prop`-valued
disjunction -- cannot supply. Proving by cases needs `em`; defining by cases
needs choice. That is why `realNonneg_or` appears here and `realMul` does not.
-/

theorem dne_of_em (h : EM) {p : Prop} (hnn : ¬ ¬ p) : p :=
  (h p).elim id fun hn => absurd hn hnn

theorem regularity_of_em (h : EM) (x : ZFSet.{u}) (hx : x ≠ empty.{u}) :
    ∃ y : ZFSet.{u}, y ∈ x ∧ ∀ z : ZFSet.{u}, z ∈ y → z ∉ x := by
  refine dne_of_em h fun hc => ?_
  have key : ∀ y : ZFSet.{u}, y ∉ x :=
    inductionOn (motive := fun y => y ∉ x) fun y ih hy => hc ⟨y, hy, ih⟩
  exact hx (ext x empty.{u} fun z =>
    ⟨fun hz => absurd hz (key z), fun hz => absurd hz (not_mem_empty z)⟩)

/-! ## Defining by cases

The same measurement as `Logic/Reverse.lean`'s `decider_of_em`, in the phase
where the results that need it live. Defining data by cases and proving by
cases are different claims, and one audit line cannot separate them: Lean's
`Classical.em` is derived from `Classical.choice`, so both report the same
axiom. A result that only proves by cases takes `EM` as a binder; one that
defines data cannot, and takes a `Decidable` parameter instead. -/

/-- A decision as data. -/
inductive Decider (p : Prop) : Type where
  | isTrue : p → Decider p
  | isFalse : ¬ p → Decider p

/-- Data decides, so it proves. Axiom-free. -/
theorem em_of_decider (d : ∀ q : Prop, Decider q) : EM :=
  fun p => (d p).rec (fun hp => Or.inl hp) (fun hn => Or.inr hn)

/-! ## Audit

Both reversals are choice-free. -/
/-- Excluded middle makes every family of reals located.

The converse of `em_of_familyLocated` (`Calibrate.lean`), which turns that
lemma's one-way price into an equivalence --- stated there, where both
directions are in scope, as `familyLocated_all_iff_em`.

ONLY THE EXISTENTIAL NEEDS DECIDING, and that is the whole content. `EM` picks
between "some member's lower cut holds `p`" and its negation; in the negative
branch each member's own `IsLocated.located` field supplies `q ∈ U` for free,
its left disjunct refuted by the negation just assumed. So family locatedness
costs one decision about a single proposition, not a decision per member:
membership in `RealL` already carries pointwise locatedness, and what the
family form adds is only that the choice be made uniformly. -/
theorem familyLocated_of_em (hem : EM) {S : ZFSet.{u}} (hS : S ⊆ RealL.{u}) :
    FamilyLocated S := by
  intro p hp0 q hq hpq
  rcases hem (∃ z, z ∈ S ∧ ∃ L U, z = opair L U ∧ p ∈ L) with hex | hnex
  · exact Or.inl hex
  · refine Or.inr (fun z hz L U heq => ?_)
    obtain ⟨L', U', heq', hloc⟩ := (mem_RealL_iff z).mp (hS z hz)
    obtain ⟨rfl, rfl⟩ := opair_injective (heq.symm.trans heq')
    rcases hloc.located p hp0 q hq hpq with hp | hqU
    · exact absurd ⟨z, hz, L, U, heq, hp⟩ hnex
    · exact hqU


#print axioms EM
#print axioms em_of_sup_located
#print axioms regularity_of_em
#print axioms Regularity
#print axioms em_of_decider

#print axioms familyLocated_of_em

#print axioms mem_propFamily_iff
#print axioms wem_of_em
#print axioms dne_of_em
end Constructive

namespace ZFSet
export Constructive (Decider EM Regularity WEM dne_of_em em_of_decider em_of_sup_located familyLocated_of_em regularity_of_em wem_of_em)
end ZFSet
