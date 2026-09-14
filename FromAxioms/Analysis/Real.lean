/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The reals.

A real is a Dedekind cut of ℚ: a set of rationals that is non-empty, proper,
downward closed, and has no greatest element. `Real` is carved out of `𝒫 ℚ` by
separation, so nothing here needs replacement -- the same bounding move that
placed the quotient set inside a power set.

The order is `⊆`, which makes reflexivity and transitivity trivial and
antisymmetry extensionality. Completeness is then literally a union: `⋃ S` is a
cut whenever `S` is a non-empty family of cuts with an upper bound, and
`subset_sUnion` and `sUnion_subset` say it is the least one.

Classical logic USED TO enter at exactly two places, and both were the same
step: deciding a comparison that no witness has been produced for.
`realLe_of_witness` -- a rational in `x` but not in `y` forces `y ⊆ x` -- is
constructive, and it is the whole mathematical content of linearity; the retired
`realLe_total` paid `em` only to decide that such a rational exists.
Multiplication was the same story one level up: the four sign cases are each
constructive, and choosing between them is not. On ℚ the corresponding
trichotomy was free, because equality of rationals reduces to equality of
naturals.

NEITHER PLACE IS IN THIS FILE ANY MORE. The comparisons are stated in
`Constructive/` with `EM` as a binder and reversed back to it, so each is priced
exactly rather than merely bounded; the sign decision is a `Decidable` parameter
of `realMulOf`. Nothing here depends on `Classical.choice`.

Addition, negation and multiplication on the non-negative cone are all
choice-free. `x + (-x) = 0` is not: it needs locatedness, which a one-sided cut
does not carry.
-/

import FromAxioms.NumberTheory.Rational

universe u

open NumberTheory SetTheory
namespace Analysis

/-- The four conditions defining a Dedekind cut. -/
structure IsCut (c : ZFSet.{u}) : Prop where
  subset : c ⊆ NumberTheory.Rat.{u}
  nonempty : ∃ q, q ∈ c
  proper : ∃ q, q ∈ NumberTheory.Rat.{u} ∧ q ∉ c
  down : ∀ q, q ∈ c → ∀ p, p ∈ NumberTheory.Rat.{u} → ratLt p q → p ∈ c
  no_greatest : ∀ q, q ∈ c → ∃ p, p ∈ c ∧ ratLt q p

/-- The real numbers, defined by Dedekind cuts. -/
def Real : ZFSet.{u} := sep IsCut.{u} (powerset NumberTheory.Rat.{u})

theorem mem_Real_iff (c : ZFSet.{u}) : c ∈ Real.{u} ↔ IsCut c :=
  Iff.trans (mem_sep_iff _ _ _)
    ⟨fun h => h.right, fun h => ⟨(mem_powerset_iff _ _).mpr h.subset, h⟩⟩

/-! ## ℚ inside ℝ -/

/-- The cut of a rational: everything strictly below it. -/
def ratCut (q : ZFSet.{u}) : ZFSet.{u} := sep (fun p => ratLt p q) NumberTheory.Rat.{u}

theorem mem_ratCut_iff (q p : ZFSet.{u}) : p ∈ ratCut q ↔ p ∈ NumberTheory.Rat.{u} ∧ ratLt p q :=
  mem_sep_iff _ _ _

/-- The cut below a NON-rational is empty, because `ratLe` names `ratOf` on
its right side and nothing is `≤ empty`. `ratCut` is total, so this says what it
returns off the rationals rather than leaving it unspecified --- and with
`NumberTheory.ratUpper_empty` it pins both halves of `realLOf empty`. -/
theorem ratCut_empty : ratCut empty.{u} = empty.{u} := by
  refine ext _ _ (fun z => ⟨fun hz => ?_, fun hz => absurd hz (not_mem_empty _)⟩)
  exact absurd ((mem_ratCut_iff _ z).mp hz).right.left
    NumberTheory.not_ratLe_empty_right

theorem ratCut_mem_Real {q : ZFSet.{u}} (hq : q ∈ NumberTheory.Rat.{u}) : ratCut q ∈ Real.{u} := by
  refine (mem_Real_iff _).mpr ⟨fun p hp => ((mem_ratCut_iff q p).mp hp).left, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, hs, hlt⟩ := rat_no_least hq
    exact ⟨s, (mem_ratCut_iff q s).mpr ⟨hs, hlt⟩⟩
  · exact ⟨q, hq, fun h => ratLt_irrefl ((mem_ratCut_iff q q).mp h).right⟩
  · intro r hr p hp hlt
    obtain ⟨hrQ, hrq⟩ := (mem_ratCut_iff q r).mp hr
    exact (mem_ratCut_iff q p).mpr ⟨hp, ratLt_trans hp hrQ hq hlt hrq⟩
  · intro r hr
    obtain ⟨hrQ, hrq⟩ := (mem_ratCut_iff q r).mp hr
    obtain ⟨t, ht, h₁, h₂⟩ := rat_dense hrQ hq hrq
    exact ⟨t, (mem_ratCut_iff q t).mpr ⟨ht, h₂⟩, h₁⟩

/-! ## Order -/

def realLe (x y : ZFSet.{u}) : Prop := x ⊆ y

theorem realLe_refl (x : ZFSet.{u}) : realLe x x := fun _ h => h

/-- A member of a cut is strictly below any rational that is not a member. -/
theorem ratLt_of_mem_of_not_mem {c q p : ZFSet.{u}} (hc : IsCut c) (hq : q ∈ c)
    (hp : p ∈ NumberTheory.Rat.{u}) (hpc : p ∉ c) : ratLt q p := by
  have hqQ : q ∈ NumberTheory.Rat.{u} := hc.subset q hq
  have hne : q ≠ p := fun he => hpc (he ▸ hq)
  rcases ratLe_total hqQ hp with h | h
  · exact ⟨h, hne⟩
  · exact absurd (hc.down q hq p hp ⟨h, fun he => hne he.symm⟩) hpc

/-! ## Addition

`x + y` is the set of sums, `{q + r | q ∈ x, r ∈ y}`. Each cut condition
transfers directly except properness, which needs the observation below: a
rational inside a cut is strictly below every rational outside it. That is the
same fact `realLe_of_witness` turns on, and it is constructive. -/

def realAdd (x y : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ q, q ∈ x ∧ ∃ r, r ∈ y ∧ p = ratAdd q r) NumberTheory.Rat.{u}

theorem mem_realAdd_iff (x y p : ZFSet.{u}) :
    p ∈ realAdd x y ↔ p ∈ NumberTheory.Rat.{u} ∧ ∃ q, q ∈ x ∧ ∃ r, r ∈ y ∧ p = ratAdd q r :=
  mem_sep_iff _ p _

theorem realAdd_mem_Real {x y : ZFSet.{u}} (hx : x ∈ Real.{u}) (hy : y ∈ Real.{u}) :
    realAdd x y ∈ Real.{u} := by
  have cx := (mem_Real_iff x).mp hx
  have cy := (mem_Real_iff y).mp hy
  refine (mem_Real_iff _).mpr ⟨fun p hp => ((mem_realAdd_iff x y p).mp hp).left, ?_, ?_, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := cx.nonempty
    obtain ⟨r, hr⟩ := cy.nonempty
    exact ⟨ratAdd q r, (mem_realAdd_iff x y _).mpr
      ⟨ratAdd_mem_Rat (cx.subset q hq) (cy.subset r hr), q, hq, r, hr, rfl⟩⟩
  · obtain ⟨q₀, hq₀Q, hq₀⟩ := cx.proper
    obtain ⟨r₀, hr₀Q, hr₀⟩ := cy.proper
    refine ⟨ratAdd q₀ r₀, ratAdd_mem_Rat hq₀Q hr₀Q, fun hmem => ?_⟩
    obtain ⟨-, q, hq, r, hr, he⟩ := (mem_realAdd_iff x y _).mp hmem
    exact ratLt_irrefl (he ▸ ratAdd_lt_add (cx.subset q hq) hq₀Q (cy.subset r hr) hr₀Q
      (ratLt_of_mem_of_not_mem cx hq hq₀Q hq₀) (ratLt_of_mem_of_not_mem cy hr hr₀Q hr₀))
  · rintro p hp p' hp'Q hlt
    obtain ⟨hpQ, q, hq, r, hr, rfl⟩ := (mem_realAdd_iff x y p).mp hp
    have hqQ := cx.subset q hq
    have hrQ := cy.subset r hr
    -- shift the first summand down by exactly `p' - p`
    have hd := ratAdd_mem_Rat hp'Q (ratNeg_mem_Rat hpQ)
    refine (mem_realAdd_iff x y p').mpr ⟨hp'Q, ratAdd q (ratAdd p' (ratNeg (ratAdd q r))), ?_,
      r, hr, ?_⟩
    · refine cx.down q hq _ (ratAdd_mem_Rat hqQ hd) ?_
      have h0 : ratLt (ratAdd p' (ratNeg (ratAdd q r))) ratZero.{u} := by
        have := (ratAdd_lt_add_left_iff (ratNeg_mem_Rat hpQ) hp'Q hpQ).mpr hlt
        rwa [ratAdd_comm (ratNeg_mem_Rat hpQ) hp'Q,
             ratAdd_comm (ratNeg_mem_Rat hpQ) hpQ, ratAdd_neg hpQ] at this
      have := (ratAdd_lt_add_left_iff hqQ hd ratZero_mem_Rat).mpr h0
      rwa [ratAdd_zero hqQ] at this
    · rw [ratAdd_comm hqQ hd, ratAdd_assoc hd hqQ hrQ, ratAdd_comm hd hpQ,
          ratAdd_sub_cancel hp'Q hpQ]
  · rintro p hp
    obtain ⟨hpQ, q, hq, r, hr, rfl⟩ := (mem_realAdd_iff x y p).mp hp
    obtain ⟨q', hq', hlt⟩ := cx.no_greatest q hq
    have hqQ := cx.subset q hq
    have hq'Q := cx.subset q' hq'
    have hrQ := cy.subset r hr
    refine ⟨ratAdd q' r, (mem_realAdd_iff x y _).mpr
      ⟨ratAdd_mem_Rat hq'Q hrQ, q', hq', r, hr, rfl⟩, ?_⟩
    rw [ratAdd_comm hqQ hrQ, ratAdd_comm hq'Q hrQ]
    exact (ratAdd_lt_add_left_iff hrQ hqQ hq'Q).mpr hlt

theorem realAdd_comm {x y : ZFSet.{u}} (hx : x ∈ Real.{u}) (hy : y ∈ Real.{u}) :
    realAdd x y = realAdd y x := by
  have cx := (mem_Real_iff x).mp hx
  have cy := (mem_Real_iff y).mp hy
  refine ext _ _ fun p => ?_
  refine Iff.trans (mem_realAdd_iff x y p) (Iff.trans ?_ (mem_realAdd_iff y x p).symm)
  constructor
  · rintro ⟨hpQ, q, hq, r, hr, rfl⟩
    exact ⟨hpQ, r, hr, q, hq, ratAdd_comm (cx.subset q hq) (cy.subset r hr)⟩
  · rintro ⟨hpQ, r, hr, q, hq, rfl⟩
    exact ⟨hpQ, q, hq, r, hr, ratAdd_comm (cy.subset r hr) (cx.subset q hq)⟩

/-- Zero. -/
def realZero : ZFSet.{u} := ratCut ratZero.{u}

theorem realZero_mem_Real : realZero.{u} ∈ Real.{u} := ratCut_mem_Real ratZero_mem_Rat

/-- `x + 0 = x`. The inclusion that needs work is `⊇`: a member of `x` has to be
written as a sum, and the summand above it is exactly what `no_greatest`
provides. -/
theorem realAdd_zero {x : ZFSet.{u}} (hx : x ∈ Real.{u}) :
    realAdd x realZero.{u} = x := by
  have cx := (mem_Real_iff x).mp hx
  refine ext _ _ fun p => ⟨?_, ?_⟩
  · intro hp
    obtain ⟨hpQ, q, hq, r, hr, rfl⟩ := (mem_realAdd_iff _ _ p).mp hp
    obtain ⟨hrQ, hrlt⟩ := (mem_ratCut_iff ratZero.{u} r).mp hr
    have hqQ := cx.subset q hq
    refine cx.down q hq _ hpQ ?_
    have hstep := (ratAdd_lt_add_left_iff hqQ hrQ ratZero_mem_Rat).mpr hrlt
    rwa [ratAdd_zero hqQ] at hstep
  · intro hp
    have hpQ := cx.subset p hp
    obtain ⟨q, hq, hlt⟩ := cx.no_greatest p hp
    have hqQ := cx.subset q hq
    have hnq := ratNeg_mem_Rat hqQ
    refine (mem_realAdd_iff _ _ p).mpr ⟨hpQ, q, hq, ratAdd p (ratNeg q), ?_, ?_⟩
    · refine (mem_ratCut_iff ratZero.{u} _).mpr ⟨ratAdd_mem_Rat hpQ hnq, ?_⟩
      have hstep := (ratAdd_lt_add_left_iff hnq hpQ hqQ).mpr hlt
      rwa [ratAdd_comm hnq hpQ, ratAdd_comm hnq hqQ, ratAdd_neg hqQ] at hstep
    · exact (ratAdd_sub_cancel hpQ hqQ).symm

/-! ## Negation

`-x` is `{p | p < -q for some q outside x}`. Quantifying over the complement
is what makes the result a cut: taking `{-q | q ∉ x}` directly would have a
greatest element whenever `x` has a least upper bound in ℚ. -/

def realNeg (x : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ q, q ∈ NumberTheory.Rat.{u} ∧ q ∉ x ∧ ratLt p (ratNeg q)) NumberTheory.Rat.{u}

/-! No ladder walk is needed here. `located_of_adjacent` takes the adjacency
step as the hypothesis `adj`, so it is choice-free, and
`Constructive.cut_located_of_em` discharges that hypothesis from an `EM`
binder. -/

/-- For every `ε > 0`, a member and a non-member within `ε` of each other. This
is the data a one-sided cut does not carry. -/
def Located (x : ZFSet.{u}) : Prop :=
  ∀ ε, ε ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} ε →
    ∃ q, q ∈ x ∧ ∃ s, s ∈ NumberTheory.Rat.{u} ∧ s ∉ x ∧ ratLt s (ratAdd q ε)

/-! ## Multiplication on the non-negative cone

`{q·r}` is only the right set of products when both factors are non-negative,
so multiplication is given on the cone first. Extending it to all of ℝ is a
different matter: the textbook definition splits on the sign of each factor, and
deciding the sign of a real is the same comparison `Constructive.realLe_total_of_em`
prices at excluded middle. Nothing below uses it, because `realNonneg` is a
hypothesis here rather than something to be decided. -/

def realNonneg (x : ZFSet.{u}) : Prop := realLe realZero.{u} x


/-- A rational outside a non-negative cut is itself non-negative. -/
theorem ratZero_le_of_not_mem {x q : ZFSet.{u}} (hx0 : realNonneg x) (hq : q ∈ NumberTheory.Rat.{u})
    (hqx : q ∉ x) : ratLe ratZero.{u} q := by
  rcases ratLe_total ratZero_mem_Rat hq with h | h
  · exact h
  · rcases rat_eq_or_ne hq ratZero_mem_Rat with rfl | hne
    · exact ratLe_refl hq
    · exact absurd (hx0 q ((mem_ratCut_iff ratZero.{u} q).mpr ⟨hq, h, hne⟩)) hqx

def realMulNonneg (x y : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ratLt p ratZero.{u} ∨ ∃ q, q ∈ x ∧ ∃ r, r ∈ y ∧
        ratLe ratZero.{u} q ∧ ratLe ratZero.{u} r ∧ ratLt p (ratMul q r)) NumberTheory.Rat.{u}

theorem mem_realMulNonneg_iff (x y p : ZFSet.{u}) :
    p ∈ realMulNonneg x y ↔ p ∈ NumberTheory.Rat.{u} ∧ (ratLt p ratZero.{u} ∨ ∃ q, q ∈ x ∧ ∃ r, r ∈ y ∧
      ratLe ratZero.{u} q ∧ ratLe ratZero.{u} r ∧ ratLt p (ratMul q r)) :=
  mem_sep_iff _ p _

theorem realMulNonneg_mem_Real {x y : ZFSet.{u}} (hx : x ∈ Real.{u}) (hy : y ∈ Real.{u})
    (hx0 : realNonneg x) (hy0 : realNonneg y) : realMulNonneg x y ∈ Real.{u} := by
  have cx := (mem_Real_iff x).mp hx
  have cy := (mem_Real_iff y).mp hy
  refine (mem_Real_iff _).mpr
    ⟨fun p hp => ((mem_realMulNonneg_iff x y p).mp hp).left, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, hsQ, hslt⟩ := rat_no_least ratZero_mem_Rat
    exact ⟨s, (mem_realMulNonneg_iff x y s).mpr ⟨hsQ, Or.inl hslt⟩⟩
  · obtain ⟨q₀, hq₀Q, hq₀⟩ := cx.proper
    obtain ⟨r₀, hr₀Q, hr₀⟩ := cy.proper
    have hq₀0 := ratZero_le_of_not_mem hx0 hq₀Q hq₀
    have hr₀0 := ratZero_le_of_not_mem hy0 hr₀Q hr₀
    refine ⟨ratMul q₀ r₀, ratMul_mem_Rat hq₀Q hr₀Q, fun hmem => ?_⟩
    rcases ((mem_realMulNonneg_iff x y _).mp hmem).right with hlt | ⟨q, hq, r, hr, _, hr0, hlt⟩
    · exact not_ratLt_of_ratLe ratZero_mem_Rat (ratMul_mem_Rat hq₀Q hr₀Q)
        (ratZero_le_mul hq₀Q hr₀Q hq₀0 hr₀0) hlt
    · have hqQ := cx.subset q hq
      have hrQ := cy.subset r hr
      have h₁ : ratLe (ratMul q r) (ratMul q₀ r) :=
        ratMul_le_mul_right hqQ hq₀Q hrQ (ratLt_of_mem_of_not_mem cx hq hq₀Q hq₀).left hr0
      have h₂ : ratLe (ratMul q₀ r) (ratMul q₀ r₀) := by
        rw [ratMul_comm hq₀Q hrQ, ratMul_comm hq₀Q hr₀Q]
        exact ratMul_le_mul_right hrQ hr₀Q hq₀Q
          (ratLt_of_mem_of_not_mem cy hr hr₀Q hr₀).left hq₀0
      exact not_ratLt_of_ratLe (ratMul_mem_Rat hqQ hrQ) (ratMul_mem_Rat hq₀Q hr₀Q)
        (ratLe_trans (ratMul_mem_Rat hqQ hrQ) (ratMul_mem_Rat hq₀Q hrQ)
          (ratMul_mem_Rat hq₀Q hr₀Q) h₁ h₂) hlt
  · rintro p hp p' hp'Q hlt
    obtain ⟨hpQ, hcase⟩ := (mem_realMulNonneg_iff x y p).mp hp
    refine (mem_realMulNonneg_iff x y p').mpr ⟨hp'Q, ?_⟩
    rcases hcase with h | ⟨q, hq, r, hr, hq0, hr0, h⟩
    · exact Or.inl (ratLt_trans hp'Q hpQ ratZero_mem_Rat hlt h)
    · exact Or.inr ⟨q, hq, r, hr, hq0, hr0,
        ratLt_trans hp'Q hpQ (ratMul_mem_Rat (cx.subset q hq) (cy.subset r hr)) hlt h⟩
  · rintro p hp
    obtain ⟨hpQ, hcase⟩ := (mem_realMulNonneg_iff x y p).mp hp
    rcases hcase with h | ⟨q, hq, r, hr, hq0, hr0, h⟩
    · obtain ⟨t, htQ, h₁, h₂⟩ := rat_dense hpQ ratZero_mem_Rat h
      exact ⟨t, (mem_realMulNonneg_iff x y t).mpr ⟨htQ, Or.inl h₂⟩, h₁⟩
    · obtain ⟨t, htQ, h₁, h₂⟩ :=
        rat_dense hpQ (ratMul_mem_Rat (cx.subset q hq) (cy.subset r hr)) h
      exact ⟨t, (mem_realMulNonneg_iff x y t).mpr
        ⟨htQ, Or.inr ⟨q, hq, r, hr, hq0, hr0, h₂⟩⟩, h₁⟩

#print axioms ratCut_empty
#print axioms ratCut_mem_Real
#print axioms Real
#print axioms IsCut
#print axioms realAdd_mem_Real
#print axioms realAdd_zero
#print axioms realMulNonneg_mem_Real
#print axioms mem_Real_iff
#print axioms mem_ratCut_iff
#print axioms realLe_refl
#print axioms ratLt_of_mem_of_not_mem
#print axioms mem_realAdd_iff
#print axioms realAdd_comm
#print axioms realZero_mem_Real
#print axioms ratZero_le_of_not_mem
#print axioms mem_realMulNonneg_iff
end Analysis

namespace ZFSet
export Analysis (ratCut_empty IsCut Located Real mem_Real_iff mem_ratCut_iff mem_realAdd_iff mem_realMulNonneg_iff ratCut ratCut_mem_Real ratLt_of_mem_of_not_mem ratZero_le_of_not_mem realAdd realAdd_comm realAdd_mem_Real realAdd_zero realLe realLe_refl realMulNonneg realMulNonneg_mem_Real realNeg realNonneg realZero realZero_mem_Real)
end ZFSet
