/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# What it costs to decide that a real is zero

`DecidableVanishing R zero` is the hypothesis every degree argument in
`PolyRing.lean` carries: that a coefficient can be told apart from zero. Over a
finite ring it is free, and over `ℚ` it is arithmetic. Over `ℝ` it is not, and
this file measures it.

The measurement is a transport. `Ternary.lean` walks a binary sequence down the
thirds and lands on nested intervals; `Nested.lean` turns those into a located
pair, which is a member of `RealL`; and `toCut` is injective on `RealL`, so the
located real is zero exactly when its lower cut is. That last equivalence is
`Omniscience.lean`'s `TernaryZeroDecidable`, which is `WLPO`.

So the bridge the reduction needed is `toCut_injective`, and the chain is

    DecidableVanishing RealL realLZero  →  TernaryZeroDecidable  →  WLPO

The converse holds on the walk-built family -- `ternary_vanishing_of_wlpo` --
so `WLPO` is exactly the price there. For an arbitrary located real it is a
lower bound only, and the gap is the familiar one: `located` returns a
disjunction, and turning one into a bit is defining data by cases.
-/

import FromAxioms.NumberTheory.Prime
import FromAxioms.SetTheory.Uncountable

set_option autoImplicit false

universe u

open Analysis NumberTheory SetTheory
namespace Constructive

/-- The ternary walk, as a located real rather than a bare cut. -/
def ternaryReal (α : Nat → Bool) : ZFSet.{u} :=
  opair (nestLower (tlowSeq.{u} (boolDigit α))) (nestUpper (thighSeq.{u} (boolDigit α)))

theorem ternaryReal_mem (α : Nat → Bool) : ternaryReal.{u} α ∈ RealL.{u} :=
  (mem_RealL_iff _).mpr ⟨_, _, rfl, isLocated_nest (isNested_ternary (boolDigit_le_one α))⟩


/-- The walk never goes below zero: every rational above it is above one of
the walk's upper endpoints, and those are positive. -/
theorem ternaryReal_nonneg (α : Nat → Bool) :
    realLLe realLZero.{u} (ternaryReal.{u} α) := by
  rintro ⟨p, hpU, hp0⟩
  rw [ternaryReal, snd_opair] at hpU
  rw [realLZero, realLOf, fst_opair] at hp0
  obtain ⟨hpQ, hpneg⟩ := (mem_ratCut_iff _ p).mp hp0
  obtain ⟨-, m, hm, hlt⟩ := (mem_nestUpper_iff _ p).mp hpU
  obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
  rw [app_thighSeq, thigh] at hlt
  have hpos : ratLt ratZero.{u} (ratNat.{u} (tnum (boolDigit α) i + 1) (pow3 i)) := by
    rw [ratZero_eq_ratNat, ratNat_lt_iff (by omega) (pow3_pos i)]
    omega
  exact ratLt_irrefl (ratLt_trans ratZero_mem_Rat hpQ ratZero_mem_Rat
    (ratLt_trans ratZero_mem_Rat (ratNat_mem_Rat (pow3_pos i)) hpQ hpos hlt) hpneg)

/-- And it lands in `[0,1]`, with the upper end ATTAINED. The lower cut
holds nothing above `1`, because every approximant is `tnum c n / 3^n` and
`tnum_lt_pow3` keeps that strictly below one. The companion to
`ternaryReal_nonneg`, and what lets a product be compared against a single
factor.

THE BOUND IS TIGHT AND THE STRICT FORM IS FALSE. `tnum c (n+1)` is
`3 * tnum c n + 2 * c n`, which DOUBLES each digit, so the walk is the Cantor
embedding whose supremum is exactly `1` --- attained at the all-true sequence.
A caller needing `<` must constrain the SEQUENCE rather than sharpen this
proof; `ternaryReal_lt_one_of_head_false` does it with a single digit. -/
theorem ternaryReal_le_one (a : Nat → Bool) :
    realLLe (ternaryReal.{u} a) realLOne.{u} := by
  rintro ⟨p, hpU, hplow⟩
  rw [realLOne, realLOf, snd_opair] at hpU
  rw [ternaryReal, fst_opair] at hplow
  obtain ⟨hpQ, hp1⟩ := (mem_sep_iff _ _ _).mp hpU
  obtain ⟨-, m, hm, hlt⟩ := (mem_nestLower_iff _ p).mp hplow
  obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
  rw [app_tlowSeq, tlow] at hlt
  have hb := tnum_lt_pow3 (boolDigit_le_one a) i
  have hlt1 : ratLt.{u} (ratNat.{u} (tnum (boolDigit a) i) (pow3 i)) ratOne.{u} := by
    -- `intOfNat 1` and `intOne` are the same term
    have : ratOne.{u} = ratNat.{u} 1 1 := rfl
    rw [this, ratNat_lt_iff (pow3_pos i) (by omega)]
    omega
  exact ratLt_irrefl (ratLt_trans (ratNat_mem_Rat (pow3_pos i)) ratOne_mem_Rat
    (ratNat_mem_Rat (pow3_pos i)) hlt1 (ratLt_trans ratOne_mem_Rat hpQ
      (ratNat_mem_Rat (pow3_pos i)) hp1 hlt))

/-- A walk whose first digit is `false` is STRICTLY below one.

`ternaryReal_le_one` cannot be sharpened as it stands, because its bound is
attained, so the strictness has to be bought from the SEQUENCE. One digit pays
for it: with `a 0 = false` the walk is confined to the first third, and `1/2` is
then a rational lying in its upper cut and under one, which is exactly the
witness `realLLt` asks for.

THE INDEX IS ONE, NOT ZERO, and that is the whole content. `thigh` at zero is
`1` itself and says nothing; at one it is `(2 * d_0 + 1)/3`, which the
hypothesis pins at `1/3`. -/
theorem ternaryReal_lt_one_of_head_false {a : Nat → Bool} (h : a 0 = false) :
    realLLt (ternaryReal.{u} a) realLOne.{u} := by
  have hd : boolDigit a 0 = 0 := by rw [boolDigit, h]; decide
  have ht : tnum (boolDigit a) 1 = 0 := by
    show 3 * 0 + 2 * boolDigit a 0 = 0
    rw [hd]
  have hp3 : pow3 1 = 3 := rfl
  refine ⟨ratNat.{u} 1 2, ?_, ?_⟩
  · rw [ternaryReal, snd_opair]
    refine (mem_nestUpper_iff _ _).mpr ⟨ratNat_mem_Rat (by omega), ofNat.{u} 1,
      ofNat_mem_omega 1, ?_⟩
    rw [app_thighSeq, thigh, ht, hp3]
    exact (ratNat_lt_iff (by omega) (by omega)).mpr (by omega)
  · rw [realLOne, realLOf, fst_opair]
    refine (mem_ratCut_iff _ _).mpr ⟨ratNat_mem_Rat (by omega), ?_⟩
    have hone : ratOne.{u} = ratNat.{u} 1 1 := rfl
    rw [hone]
    exact (ratNat_lt_iff (by omega) (by omega)).mpr (by omega)

#print axioms Constructive.ternaryReal_lt_one_of_head_false

end Constructive

#print axioms Constructive.ternaryReal_mem
#print axioms Constructive.ternaryReal_nonneg
#print axioms Constructive.ternaryReal_le_one
namespace ZFSet
export Constructive (ternaryReal ternaryReal_le_one ternaryReal_mem ternaryReal_nonneg)
end ZFSet
