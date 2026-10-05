/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Calibrating the readouts

The hypothesis inventory (`tools/hypotheses.json`) carries, for each assumed
principle or readout, the lattice principle it is worth. This file holds the
witnesses that cross file boundaries: the readouts are defined where their
consumers live (`Deriv.lean`), the principles where the lattice lives
(`Omniscience.lean`, through `Vanishing.lean`), and no other file imports
both sides.

The pattern of every entry: the reverse direction -- readout implies
principle -- is a theorem, because reading the data yields the disjunction.
The forward direction is `n/a`, not `open`: a readout is `Type`-level data,
and no `Prop`-level principle constructs data. A readout
hypothesis is therefore strictly sharper than its principle, so
the consumers keep the readout form.

That last claim is false for a readout whose bit is a `ZFSet`, and
`Analysis.SignReadout` is one. `condP P A B` is a total `ZFSet` term for any
`Prop` `P` -- separation does not ask whether `P` is decided -- so a readout
carrying a set-valued bit is not on the far side of the wall at all. What its
fields cost is three `Prop` obligations, and a `Prop`-level decision discharges
them: `Constructive.signReadout_of_decidableRealLLe` builds the whole structure
from `WEM`.

So the `n/a` is a fact about the bit's sort and not about readouts. Where the
bit is a `Bool` or a `Nat`-valued modulus the wall is real and countable choice
is the price -- `Analysis.nonempty_uniformOn_of_countableNatChoice` pays
exactly that, and its conclusion is `Nonempty` for exactly this reason. Both
halves appear in `exactIVT01_of_wem_of_countableNatChoice` below, so it takes
two principles rather than one.
-/

import FromAxioms.Analysis.Complete
import FromAxioms.NumberTheory.Halving

set_option autoImplicit false

universe u

open Analysis Constructive NumberTheory SetTheory Topology

namespace Analysis

end Analysis

namespace Metamath

/-- A decider for every predicate is refutable, so `HalveDecider` cannot be
calibrated the way the readouts are. Take `P a b` to be `a = 0 ∧ b = 1`: it
holds at the starting interval, and whichever way `decided` goes, `keepsL` or
`keepsR` asserts it of a halved interval, where the midpoint would have to be
an endpoint.

A readout is data about an object and can be demanded of every object. A
decider carries a promise about `P`, so demanding one for every `P` demands the
promise of predicates that cannot keep it, and its calibration is relative to a
`P`. -/
theorem not_halveDecider_forall :
    (∀ P : ZFSet.{u} → ZFSet.{u} → Prop, HalveDecider P) → False := by
  intro h
  have hm0 := lt_ratMid ratZero_mem_Rat ratOne_mem_Rat ratZero_lt_one
  have hm1 := ratMid_lt ratZero_mem_Rat ratOne_mem_Rat ratZero_lt_one
  have hP : (fun a b => a = ratZero.{u} ∧ b = ratOne.{u}) ratZero.{u} ratOne.{u} :=
    ⟨rfl, rfl⟩
  rcases (h (fun a b => a = ratZero.{u} ∧ b = ratOne.{u})).decided
      ratZero.{u} ratOne.{u} ratZero_mem_Rat ratOne_mem_Rat with hgo | hgo
  · have hstep := (h (fun a b => a = ratZero.{u} ∧ b = ratOne.{u})).keepsL
      ratZero.{u} ratOne.{u} ratZero_mem_Rat ratOne_mem_Rat
      (ratLe_refl ratZero_mem_Rat) ratZero_lt_one (ratLe_refl ratOne_mem_Rat)
      hP hgo
    rw [hstep.right] at hm1
    exact ratLt_irrefl hm1
  · have hstep := (h (fun a b => a = ratZero.{u} ∧ b = ratOne.{u})).keepsR
      ratZero.{u} ratOne.{u} ratZero_mem_Rat ratOne_mem_Rat
      (ratLe_refl ratZero_mem_Rat) ratZero_lt_one (ratLe_refl ratOne_mem_Rat)
      hP hgo
    rw [hstep.left] at hm0
    exact ratLt_irrefl hm0

/-- Exact IVT on the unit interval: every uniformly continuous function
strictly straddling zero has a root. -/
def ExactIVT01 : Prop :=
  ∀ G : ZFSet.{u} → ZFSet.{u},
    (∀ x, x ∈ realLIcc ratZero.{u} ratOne.{u} → G x ∈ RealL.{u}) →
    UniformlyContinuousOn G ratZero.{u} ratOne.{u} →
    realLLt (G (realLOf ratZero.{u})) realLZero.{u} →
    realLLt realLZero.{u} (G (realLOf ratOne.{u})) →
    ∃ c, And (c ∈ realLIcc ratZero.{u} ratOne.{u}) (G c = realLZero.{u})

/-- The read: an attainment equation for the clamped gadget decides the
sign of the unclamped real, by cotransitivity at `4/9 < 5/9` and the two
exclusions. -/
theorem signDisjunction_read {z c : ZFSet.{u}} (hz : z ∈ RealL.{u})
    (hcR : c ∈ RealL.{u})
    (heq : mvGadget (realLClamp z) c = realLMul (realLOf (ratInv
      (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))) (realLClamp z)) :
    Or (realLLe z realLZero.{u}) (realLLe realLZero.{u} z) := by
  have hLm := realLClamp_mem hz
  obtain ⟨hblo, hbhi⟩ := realLClamp_bracket (z := z)
  have hinv9pos := ratInv_pos ratNine_mem ratZero_lt_nine.{u}
  have hinv9Q := ratInv_mem_Rat ratNine_mem ratNine_ne_zero.{u}
  have h45 : ratLt ratFour.{u} ratFive.{u} := by
    have hstep := (ratAdd_lt_add_right_iff ratFour_mem ratZero_mem_Rat
      ratOne_mem_Rat).mpr ratZero_lt_one
    rwa [ratZero_add ratFour_mem] at hstep
  have hpq : ratLt (ratMul ratFour.{u} (ratInv ratNine.{u}))
      (ratMul ratFive.{u} (ratInv ratNine.{u})) :=
    ratMul_lt_mul_right ratFour_mem ratFive_mem hinv9Q
      (fun he => hinv9pos.right he.symm) hinv9pos.left h45
  have hpqR : realLLt
      (realLOf (ratMul ratFour.{u} (ratInv ratNine.{u})))
      (realLOf (ratMul ratFive.{u} (ratInv ratNine.{u}))) :=
    (realLOf_lt_realLOf (ratMul_mem_Rat ratFour_mem hinv9Q)
      (ratMul_mem_Rat ratFive_mem hinv9Q)).mpr hpq
  rcases realLLt_cotrans (realLOf_mem (ratMul_mem_Rat ratFour_mem hinv9Q))
    (realLOf_mem (ratMul_mem_Rat ratFive_mem hinv9Q)) hcR hpqR with h4c | hc5
  · exact Or.inl ((realLClamp_nonpos_iff hz).mp
      (fun hLpos => mvGadget_exclusion_pos hLm hcR hLpos hbhi h4c heq))
  · exact Or.inr ((realLClamp_nonneg_iff hz).mp
      (fun hLneg => mvGadget_exclusion_neg hLm hcR hLneg hblo hc5 heq))

/-- The clamped mean sits strictly inside `(-1, 1)`. -/
theorem clamp_third_strict {z : ZFSet.{u}} (hz : z ∈ RealL.{u}) :
    And (realLLt (realLOf (ratNeg ratOne.{u}))
      (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u})))) (realLClamp z)))
      (realLLt (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u})))) (realLClamp z))
        (realLOf ratOne.{u})) := by
  have hLm := realLClamp_mem hz
  obtain ⟨hblo, hbhi⟩ := realLClamp_bracket (z := z)
  have h3Q := ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
  have h3R := realLOf_mem h3Q
  have h2Q := ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat
  have hinv3Q := ratInv_three_mem_Rat.{u}
  have hinv3R := realLOf_mem hinv3Q
  have hu := realLMul_mem hinv3R hLm
  have hinv3_pos : realLLt realLZero.{u} (realLOf (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))) :=
    (realLOf_lt_realLOf ratZero_mem_Rat hinv3Q).mpr
      (ratInv_pos h3Q ratZero_lt_three.{u})
  -- `1/3 < 1`, and its negation flipped
  have h13 : ratLt ratOne.{u} (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})) := by
    have h12 : ratLt ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}) := by
      have hstep := (ratAdd_lt_add_left_iff ratOne_mem_Rat ratZero_mem_Rat
        ratOne_mem_Rat).mpr ratZero_lt_one
      rwa [ratAdd_zero ratOne_mem_Rat] at hstep
    have h23 := (ratAdd_lt_add_left_iff ratOne_mem_Rat ratOne_mem_Rat
      h2Q).mpr h12
    exact ratLt_trans ratOne_mem_Rat (ratAdd_mem_Rat ratOne_mem_Rat
      ratOne_mem_Rat) h3Q h12 h23
  have hinv3_lt_1 : ratLt (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u}))) ratOne.{u} := by
    have hstep := ratMul_lt_mul_right ratOne_mem_Rat h3Q hinv3Q
      (fun he => (ratInv_pos h3Q ratZero_lt_three.{u}).right he.symm)
      (ratInv_pos h3Q ratZero_lt_three.{u}).left h13
    rwa [ratOne_mul hinv3Q, ratMul_inv h3Q ratThree_ne_zero.{u}] at hstep
  -- `u ≤ 1/3` and `-1/3 ≤ u`, from the clamp bracket
  have hu_le : realLLe (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))) (realLClamp z))
      (realLOf (ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))) := by
    have hstep := realLMul_le_right hLm realLOne_mem hinv3R hbhi
      (realLLe_of_lt realLZero_mem hinv3R hinv3_pos)
    rw [realLMul_comm hLm hinv3R, realLMul_comm realLOne_mem hinv3R,
      realLMul_one hinv3R] at hstep
    exact hstep
  have hng_le_u : realLLe (realLOf (ratNeg (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))))
      (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u})))) (realLClamp z)) := by
    have hstep := realLMul_le_right (realLNeg_mem realLOne_mem) hLm
      hinv3R hblo (realLLe_of_lt realLZero_mem hinv3R hinv3_pos)
    rw [realLMul_comm (realLNeg_mem realLOne_mem) hinv3R,
      realLMul_comm hLm hinv3R,
      realLMul_neg hinv3R realLOne_mem, realLMul_one hinv3R,
      realLOf_neg hinv3Q] at hstep
    exact hstep
  -- strict endpoint comparisons: `-1 < u < 1`
  have hu_lt_1 : realLLt (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))) (realLClamp z))
      (realLOf ratOne.{u}) :=
    realLLt_of_le_of_lt hu hinv3R (realLOf_mem ratOne_mem_Rat) hu_le
      ((realLOf_lt_realLOf hinv3Q ratOne_mem_Rat).mpr hinv3_lt_1)
  have hn1_lt_u : realLLt (realLOf (ratNeg ratOne.{u}))
      (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u})))) (realLClamp z)) := by
    refine realLLt_of_lt_of_le (realLOf_mem (ratNeg_mem_Rat ratOne_mem_Rat))
      (realLOf_mem (ratNeg_mem_Rat hinv3Q)) hu ?_ hng_le_u
    exact (realLOf_lt_realLOf (ratNeg_mem_Rat ratOne_mem_Rat)
      (ratNeg_mem_Rat hinv3Q)).mpr
      ((ratNeg_lt_neg_iff ratOne_mem_Rat hinv3Q).mpr hinv3_lt_1)
  exact ⟨hn1_lt_u, hu_lt_1⟩

/-- Exact zero-crossing yields the sign disjunction. The gadget shifted
by its own mean crosses zero -- strictly negative at `0`, strictly positive
at `1` -- and an exact root is the attainment equation. This closes
`IVT.lean`'s calibration: the approximate theorem is free, the exact one
costs `LLPO`. -/
theorem signDisjunction_of_exact_ivt
    (hivt : ExactIVT01.{u}) :
    SignDisjunction.{u} := by
  intro z hz
  have hLm := realLClamp_mem hz
  obtain ⟨hblo, hbhi⟩ := realLClamp_bracket (z := z)
  obtain ⟨hn1_lt_u, hu_lt_1⟩ := clamp_third_strict.{u} hz
  have hinv3R := realLOf_mem ratInv_three_mem_Rat.{u}
  have hu := realLMul_mem hinv3R hLm
  obtain ⟨c, hcIcc, hroot⟩ := hivt
    (fun t => realLAdd (mvGadget (realLClamp z) t)
      (realLNeg (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u})))) (realLClamp z))))
    (fun x hx => realLAdd_mem
      (mvGadget_mem hLm ((mem_realLIcc_iff _ _ x).mp hx).left)
      (realLNeg_mem hu))
    (uniformlyContinuousOn_add
      (fun x hx => mvGadget_mem hLm ((mem_realLIcc_iff _ _ x).mp hx).left)
      (fun _ _ => realLNeg_mem hu)
      (mvGadget_uc hLm) (uniformlyContinuousOn_const (realLNeg_mem hu)))
    (by
      show realLLt (realLAdd (mvGadget (realLClamp z) (realLOf ratZero.{u}))
        (realLNeg (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
          (ratAdd ratOne.{u} ratOne.{u})))) (realLClamp z)))) realLZero.{u}
      rw [mvGadget_at_zero hLm hblo]
      have hstep := realLLt_add_right
        (realLOf_mem (ratNeg_mem_Rat ratOne_mem_Rat)) hu
        (realLNeg_mem hu) hn1_lt_u
      rwa [realLAdd_neg hu] at hstep)
    (by
      show realLLt realLZero.{u}
        (realLAdd (mvGadget (realLClamp z) (realLOf ratOne.{u}))
          (realLNeg (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
            (ratAdd ratOne.{u} ratOne.{u})))) (realLClamp z))))
      rw [mvGadget_at_one hLm hbhi]
      have hstep := realLLt_add_right hu (realLOf_mem ratOne_mem_Rat)
        (realLNeg_mem hu) hu_lt_1
      rwa [realLAdd_neg hu] at hstep)
  have hcR := ((mem_realLIcc_iff _ _ c).mp hcIcc).left
  have heq : mvGadget (realLClamp z) c
      = realLMul (realLOf (ratInv (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u})))) (realLClamp z) := by
    have hstep : realLAdd (realLAdd (mvGadget (realLClamp z) c)
        (realLNeg (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
          (ratAdd ratOne.{u} ratOne.{u})))) (realLClamp z))))
        (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
          (ratAdd ratOne.{u} ratOne.{u})))) (realLClamp z))
        = realLAdd realLZero.{u}
          (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
            (ratAdd ratOne.{u} ratOne.{u})))) (realLClamp z)) :=
      congrArg (fun w => realLAdd w (realLMul (realLOf (ratInv
        (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))))
        (realLClamp z))) hroot
    rw [realLSub_add_cancel (mvGadget_mem hLm hcR) hu,
      realLAdd_comm realLZero_mem hu, realLAdd_zero hu] at hstep
    exact hstep
  exact signDisjunction_read hz hcR heq


/-- The located opens are the order topology.

The clause that makes `MaxAttainmentTop` a statement about this tree rather
than about an abstract carrier: `realLOpens` was defined by rational brackets,
`IsOrderTopology` by rays and order intervals, and they agree.

The rational endpoints do the work twice. `realLOpens`'s docstring gives the
first reason --- a basis whose endpoints are decidable keeps the opens from
inheriting the reals' undecidable order. The second shows up in the last
clause, which asks for a closed order interval inside `U` while the bracket
supplies an open one. Tightening the bracket once on each side closes the gap,
and `exists_rat_between` is exactly that tightening --- it is `realLLt`'s own
definition (a shared rational) read back as density, so no decision is made
about either endpoint. -/
theorem isOrderTopology_realLOpens :
    IsOrderTopology realLOpens.{u} RealL.{u} realLLtRel.{u} := by
  refine ⟨isTopology_realLOpens, ?_, ?_, ?_⟩
  · -- the ray above `a` is open
    intro a ha
    refine (mem_realLOpens_iff _).mpr ⟨fun w hw => ((mem_sep_iff _ _ _).mp hw).left,
      fun x hx => ?_⟩
    obtain ⟨hxR, hax⟩ := (mem_sep_iff _ _ _).mp hx
    have hlt : realLLt a x := (opair_mem_realLLtRel_iff ha hxR).mp hax
    obtain ⟨p, hpQ, hap, hpx⟩ := exists_rat_between ha hxR hlt
    obtain ⟨_, r, _, hrQ, _, hxr, _⟩ :=
      exists_rat_bracket hxR ratOne_mem_Rat ratZero_lt_one
    refine ⟨p, hpQ, r, hrQ, hpx, hxr, fun w hw => ?_⟩
    obtain ⟨hwR, hpw, _⟩ := (mem_realLIoo_iff p r w).mp hw
    exact (mem_sep_iff _ _ _).mpr ⟨hwR,
      (opair_mem_realLLtRel_iff ha hwR).mpr
        (realLLt_trans ha (realLOf_mem hpQ) hwR hap hpw)⟩
  · -- the ray below `b` is open
    intro b hb
    refine (mem_realLOpens_iff _).mpr ⟨fun w hw => ((mem_sep_iff _ _ _).mp hw).left,
      fun x hx => ?_⟩
    obtain ⟨hxR, hxb⟩ := (mem_sep_iff _ _ _).mp hx
    have hlt : realLLt x b := (opair_mem_realLLtRel_iff hxR hb).mp hxb
    obtain ⟨q, hqQ, hxq, hqb⟩ := exists_rat_between hxR hb hlt
    obtain ⟨l, _, hlQ, _, hlx, _, _⟩ :=
      exists_rat_bracket hxR ratOne_mem_Rat ratZero_lt_one
    refine ⟨l, hlQ, q, hqQ, hlx, hxq, fun w hw => ?_⟩
    obtain ⟨hwR, _, hwq⟩ := (mem_realLIoo_iff l q w).mp hw
    exact (mem_sep_iff _ _ _).mpr ⟨hwR,
      (opair_mem_realLLtRel_iff hwR hb).mpr
        (realLLt_trans hwR (realLOf_mem hqQ) hb hwq hqb)⟩
  · -- every open contains an order interval around each of its points
    intro U hU x hx
    obtain ⟨p, hpQ, q, hqQ, hpx, hxq, hsub⟩ := ((mem_realLOpens_iff U).mp hU).right x hx
    have hxR : x ∈ RealL.{u} := ((mem_realLOpens_iff U).mp hU).left x hx
    -- Tighten once on each side. The bracket gives an open interval inside `U`;
    -- the clause wants a closed one, so the endpoints have to move strictly in.
    obtain ⟨a, haQ, hpa, hax⟩ := exists_rat_between (realLOf_mem hpQ) hxR hpx
    obtain ⟨b, hbQ, hxb, hbq⟩ := exists_rat_between hxR (realLOf_mem hqQ) hxq
    refine ⟨realLOf a, realLOf b, Or.inl ⟨realLOf_mem haQ,
        (opair_mem_realLLtRel_iff (realLOf_mem haQ) hxR).mpr hax⟩,
      Or.inl ⟨realLOf_mem hbQ,
        (opair_mem_realLLtRel_iff hxR (realLOf_mem hbQ)).mpr hxb⟩,
      fun w hw => ?_⟩
    obtain ⟨hwR, hlo, hhi⟩ := (mem_sep_iff _ _ _).mp hw
    refine hsub w ((mem_realLIoo_iff p q w).mpr ⟨hwR, ?_, ?_⟩)
    · rcases hlo with haw | haw
      · exact realLLt_trans (realLOf_mem hpQ) (realLOf_mem haQ) hwR hpa
          ((opair_mem_realLLtRel_iff (realLOf_mem haQ) hwR).mp haw)
      · exact haw ▸ hpa
    · rcases hhi with hwb | hwb
      · exact realLLt_trans hwR (realLOf_mem hbQ) (realLOf_mem hqQ)
          ((opair_mem_realLLtRel_iff hwR (realLOf_mem hbQ)).mp hwb) hbq
      · exact hwb ▸ hbq

/-- Exact IVT on the unit interval, stated topologically. The same
predicate as `ExactIVT01` with its continuity hypothesis given as membership in
the located order topology rather than as a modulus. -/
def ExactIVT01Top : Prop :=
  ∀ G : ZFSet.{u} → ZFSet.{u},
    (∀ x, x ∈ realLIcc ratZero.{u} ratOne.{u} → G x ∈ RealL.{u}) →
    IsContinuous (graphOn (realLIcc ratZero.{u} ratOne.{u}) RealL.{u} G)
      (realLIcc ratZero.{u} ratOne.{u}) RealL.{u}
      (subspaceOpens realLOpens.{u} (realLIcc ratZero.{u} ratOne.{u}))
      realLOpens.{u} →
    realLLt (G (realLOf ratZero.{u})) realLZero.{u} →
    realLLt realLZero.{u} (G (realLOf ratOne.{u})) →
    ∃ c, And (c ∈ realLIcc ratZero.{u} ratOne.{u}) (G c = realLZero.{u})

/-- `ExactIVT01Top` implies `ExactIVT01`. -/
theorem exactIVT01_of_top (h : ExactIVT01Top.{u}) : ExactIVT01.{u} :=
  fun G hmaps hUC hlo hhi =>
    h G hmaps (isContinuous_of_uniformlyContinuousOn ratZero_mem_Rat
      ratOne_mem_Rat ratZero_lt_one hmaps hUC) hlo hhi

/-- `LLPO` with binary dependent choice recovers the sign disjunction --
the converse of `llpo_of_signDisjunction`, and the choice layer is what it
turns on: reading a real's sign from sequence-`LLPO` means extracting digit
streams from the per-scale located disjunctions, which is exactly what
`BinaryDC` does. Two zero-anchored streams -- `d` from `located(0, 1/(n+1))`
and `e` from `located(-1/(n+1), 0)` -- cannot both register a strict claim
(`0 ∈ L` and `0 ∈ U` give `z < z`), so `LLPO` picks a side, and each side
closes by an Archimedean contradiction. -/
theorem signDisjunction_of_llpo_binaryDC (hllpo : LLPO)
    (hdc : BinaryDC) : SignDisjunction.{u} := by
  intro z hz
  obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff z).mp hz
  obtain ⟨c, hc1, hcspec⟩ := hdc (fun _ _ => ratZero.{u} ∈ L)
    (fun _ n => invWidth (ofNat.{u} n) ∈ U)
    (fun _ n => hloc.located ratZero.{u} ratZero_mem_Rat _
      (invWidth_mem_Rat (ofNat_mem_omega.{u} n))
      (invWidth_pos (ofNat_mem_omega.{u} n)))
  obtain ⟨e, he1, hespec⟩ := hdc
    (fun _ n => ratNeg (invWidth (ofNat.{u} n)) ∈ L)
    (fun _ _ => ratZero.{u} ∈ U)
    (fun _ n => hloc.located _
      (ratNeg_mem_Rat (invWidth_mem_Rat (ofNat_mem_omega.{u} n)))
      ratZero.{u} ratZero_mem_Rat
      (by
        have hstep := (ratNeg_lt_neg_iff
          (invWidth_mem_Rat (ofNat_mem_omega.{u} n)) ratZero_mem_Rat).mpr
          (invWidth_pos (ofNat_mem_omega.{u} n))
        rwa [ratNeg_zero] at hstep))
  have hdisj : ¬ ((∃ n, (fun n => if c n = 0 then true else false) n = true)
      ∧ (∃ n, (fun n => if e n = 1 then true else false) n = true)) := by
    rintro ⟨⟨n₁, hn₁⟩, ⟨n₂, hn₂⟩⟩
    have hn₁' : (if c n₁ = 0 then true else false) = true := hn₁
    have hn₂' : (if e n₂ = 1 then true else false) = true := hn₂
    have h0L : ratZero.{u} ∈ L := by
      have hc0 : c n₁ = 0 := by
        rcases Nat.decEq (c n₁) 0 with h | h
        · rw [if_neg h] at hn₁'
          exact Bool.noConfusion hn₁'
        · exact h
      rcases hcspec n₁ with ⟨_, hA⟩ | ⟨h1, _⟩
      · exact hA
      · exact absurd h1 (by omega)
    have h0U : ratZero.{u} ∈ U := by
      have he1' : e n₂ = 1 := by
        rcases Nat.decEq (e n₂) 1 with h | h
        · rw [if_neg h] at hn₂'
          exact Bool.noConfusion hn₂'
        · exact h
      rcases hespec n₂ with ⟨h0, _⟩ | ⟨_, hB⟩
      · exact absurd h0 (by omega)
      · exact hB
    exact ratLt_irrefl (hloc.ordered ratZero.{u} h0L ratZero.{u} h0U)
  rcases hllpo (fun n => if c n = 0 then true else false)
    (fun n => if e n = 1 then true else false) hdisj with hα | hβ
  · -- every digit of `d` is `1`: `z` is below every scale, so `z ≤ 0`
    refine Or.inl ?_
    rintro ⟨p, hpU0, hpL⟩
    rw [realLZero, realLOf, snd_opair] at hpU0
    obtain ⟨hpQ, hp0⟩ := (mem_sep_iff _ _ _).mp hpU0
    rw [fst_opair] at hpL
    obtain ⟨N, hNw, hNp⟩ := exists_invWidth_lt hpQ hp0
    obtain ⟨j, rfl⟩ := (mem_omega_iff N).mp hNw
    have hcj : c j = 1 := by
      have hne : ¬ c j = 0 := by
        intro h0
        have := hα j
        rw [if_pos h0] at this
        exact Bool.noConfusion this
      have := hc1 j
      omega
    have hjU : invWidth (ofNat.{u} j) ∈ U := by
      rcases hcspec j with ⟨h0, _⟩ | ⟨_, hB⟩
      · exact absurd h0 (by omega)
      · exact hB
    exact ratLt_irrefl (ratLt_trans hpQ
      (invWidth_mem_Rat (ofNat_mem_omega.{u} j)) hpQ
      (hloc.ordered p hpL _ hjU) hNp)
  · -- every digit of `e` is `0`: `z` is above every scale, so `0 ≤ z`
    refine Or.inr ?_
    rintro ⟨p, hpU, hpL0⟩
    rw [realLZero, realLOf, fst_opair] at hpL0
    obtain ⟨hpQ, hp0⟩ := (mem_ratCut_iff _ p).mp hpL0
    rw [snd_opair] at hpU
    have hnp0 : ratLt ratZero.{u} (ratNeg p) := by
      have hstep := (ratNeg_lt_neg_iff ratZero_mem_Rat hpQ).mpr hp0
      rwa [ratNeg_zero] at hstep
    obtain ⟨N, hNw, hNp⟩ := exists_invWidth_lt (ratNeg_mem_Rat hpQ) hnp0
    obtain ⟨j, rfl⟩ := (mem_omega_iff N).mp hNw
    have hej : e j = 0 := by
      have hne : ¬ e j = 1 := by
        intro h1
        have := hβ j
        rw [if_pos h1] at this
        exact Bool.noConfusion this
      have := he1 j
      omega
    have hjL : ratNeg (invWidth (ofNat.{u} j)) ∈ L := by
      rcases hespec j with ⟨_, hA⟩ | ⟨h1, _⟩
      · exact hA
      · exact absurd h1 (by omega)
    have hplt : ratLt p (ratNeg (invWidth (ofNat.{u} j))) := by
      have hstep := (ratNeg_lt_neg_iff (ratNeg_mem_Rat hpQ)
        (invWidth_mem_Rat (ofNat_mem_omega.{u} j))).mpr hNp
      rwa [ratNeg_ratNeg hpQ] at hstep
    exact ratLt_irrefl (ratLt_trans hpQ
      (ratNeg_mem_Rat (invWidth_mem_Rat (ofNat_mem_omega.{u} j))) hpQ hplt
      (hloc.ordered _ hjL p hpU))

/-- The payload the bisection carries, named so that the instance of
`BinaryDCOn` this file actually uses can be written down.

A hypothesis about `halveS P` needs a `P`.

An `abbrev` rather than a `def` -- `halve_limit_of_binaryDCOnAt` unifies its
`P` against this, and a `def` makes that unification the caller's problem. -/
abbrev straddleSignP (G : ZFSet.{u} → ZFSet.{u}) (a b : ZFSet.{u}) : Prop :=
  And (realLLe (G (realLOf a)) realLZero.{u})
      (realLLe realLZero.{u} (G (realLOf b)))

set_option maxHeartbeats 1000000 in
/-- The exact IVT from a bisection limit, and no principle at all.

This is the funnel the seven bisection theorems pass through, and this form
says what they actually spend. Darboux, Rolle, Taylor, the extreme value
theorem, the exact IVT, the mean value theorem and the mean value theorem for
integrals each spend `SignDisjunction + BinaryDCOn`, while the reversal
recovers only the first summand. Both
summands are consumed here, and both are consumed producing one object: a
halving limit for the straddle payload. Everything after that object -- nesting
the endpoints, and pinning `G c` to zero by uniform continuity -- is a theorem of
the ambient axioms, which is what this signature makes visible.

So what these theorems need is `HasHalveLimit (straddleSignP G)`, not two
principles. The two corollaries below reach it two ways, and neither is a
special case of the other: `SignDisjunction` supplies the step and the chain
principle supplies the iteration, while a `HalveDecider` supplies both at once.
-/
theorem attainment_of_halveLimit_le {G : ZFSet.{u} → ZFSet.{u}}
    (hlim : HasHalveLimit (straddleSignP G))
    (hGm : ∀ x, x ∈ realLIcc ratZero.{u} ratOne.{u} → G x ∈ RealL.{u})
    (hGuc : UniformlyContinuousOn G ratZero.{u} ratOne.{u}) :
    ∃ c, And (c ∈ realLIcc ratZero.{u} ratOne.{u}) (G c = realLZero.{u}) := by
  obtain ⟨c, hcIcc, hstage⟩ := hlim
  have hcR := ((mem_realLIcc_iff _ _ c).mp hcIcc).left
  refine ⟨c, hcIcc, ?_⟩
  refine realLLe_antisymm (hGm _ hcIcc) realLZero_mem ?_ ?_
  · -- `G c ≤ 0`: within every scale of a left endpoint whose value is `≤ 0`
    refine realLLe_zero_of_forall_invWidth (hGm _ hcIcc) ?_
    intro n
    obtain ⟨m, hm⟩ := hGuc n
    have hiQ := invWidth_mem_Rat (ofNat_mem_omega.{u} m)
    have hnQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
    obtain ⟨a, b, haQ, hbQ, h0a, hab, hb1, hpay, hwd, hac, hcb⟩ := hstage m
    have ha1 : ratLe a ratOne.{u} :=
      ratLe_trans haQ hbQ ratOne_mem_Rat hab.left hb1
    have haIcc : realLOf a ∈ realLIcc ratZero.{u} ratOne.{u} :=
      realLOf_mem_realLIcc ratZero_mem_Rat ratOne_mem_Rat haQ h0a ha1
    have hcIcc' : c ∈ realLIcc a b :=
      (mem_realLIcc_iff _ _ c).mpr ⟨hcR, hac, hcb⟩
    have hclose : Close c (realLOf a) (realLOf (invWidth (ofNat.{u} m))) :=
      withinOf_mono (realLAdd_mem hcR (realLNeg_mem (realLOf_mem haQ)))
        (ratAdd_mem_Rat hbQ (ratNeg_mem_Rat haQ)) hiQ hwd
        (withinOf_diam haQ hbQ hcIcc' (left_mem_realLIcc haQ hbQ hab.left))
    have hGclose := hm (invWidth (ofNat.{u} m)) c (realLOf a) hiQ
      (invWidth_pos (ofNat_mem_omega.{u} m)) (ratLe_refl hiQ)
      hcIcc haIcc hclose
    have hshift := le_add_radius_of_close (hGm _ hcIcc) (hGm _ haIcc)
      (realLOf_mem hnQ) hGclose
    refine realLLe_trans (hGm _ hcIcc)
      (realLAdd_mem (hGm _ haIcc) (realLOf_mem hnQ))
      (realLOf_mem hnQ) hshift ?_
    have hadd := realLLe_add_right (hGm _ haIcc) realLZero_mem
      (realLOf_mem hnQ) hpay.left
    rwa [realLAdd_comm realLZero_mem (realLOf_mem hnQ),
      realLAdd_zero (realLOf_mem hnQ)] at hadd
  · -- `0 ≤ G c`: above every negated scale, via the right endpoint
    refine zero_le_of_forall_neg_invWidth (hGm _ hcIcc) ?_
    intro n
    obtain ⟨m, hm⟩ := hGuc n
    have hiQ := invWidth_mem_Rat (ofNat_mem_omega.{u} m)
    have hnQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
    obtain ⟨a, b, haQ, hbQ, h0a, hab, hb1, hpay, hwd, hac, hcb⟩ := hstage m
    have h0b : ratLe ratZero.{u} b :=
      ratLe_trans ratZero_mem_Rat haQ hbQ h0a hab.left
    have hbIcc : realLOf b ∈ realLIcc ratZero.{u} ratOne.{u} :=
      realLOf_mem_realLIcc ratZero_mem_Rat ratOne_mem_Rat hbQ h0b hb1
    have hcIcc' : c ∈ realLIcc a b :=
      (mem_realLIcc_iff _ _ c).mpr ⟨hcR, hac, hcb⟩
    have hclose : Close (realLOf b) c (realLOf (invWidth (ofNat.{u} m))) :=
      withinOf_mono (realLAdd_mem (realLOf_mem hbQ) (realLNeg_mem hcR))
        (ratAdd_mem_Rat hbQ (ratNeg_mem_Rat haQ)) hiQ hwd
        (withinOf_diam haQ hbQ (right_mem_realLIcc haQ hbQ hab.left) hcIcc')
    have hGclose := hm (invWidth (ofNat.{u} m)) (realLOf b) c hiQ
      (invWidth_pos (ofNat_mem_omega.{u} m)) (ratLe_refl hiQ)
      hbIcc hcIcc hclose
    have hGble := le_add_radius_of_close (hGm _ hbIcc) (hGm _ hcIcc)
      (realLOf_mem hnQ) hGclose
    rw [← realLOf_neg hnQ]
    exact realLLe_neg_of_le_add (hGm _ hcIcc) (realLOf_mem hnQ)
      (realLLe_trans realLZero_mem (hGm _ hbIcc)
        (realLAdd_mem (hGm _ hcIcc) (realLOf_mem hnQ)) hpay.right hGble)

/-! ### The ceiling, at one node

It is bounded on both sides by principles already named:

    Constructive.SignDisjunction  ≤  NonnegDecision  ≤  Constructive.WEM
                                     NonnegDecision  ≤  DecidableRealLLt
                                     NonnegDecision  ≤  Constructive.ZeroOrApart
                                     NonnegDecision  ≤  Constructive.EqOrApart

The gap to the floor is one double negation. Unfolding `realLLe`, whose
definition is a negation, the two ends of the bracket read

    SignDisjunction    ¬ (0 < z)  ∨  ¬ (z < 0)
    NonnegDecision     ¬ (z < 0)  ∨  ¬ ¬ (z < 0)

so what remains is whether the theorem can stabilise its own sign disjunction.

Why the midpoint is clamped. `HalveDecider.decided` is quantified over all
rational pairs, with only `a, b ∈ Rat` in hand --- no `0 ≤ a` and no `b ≤ 1`.
`WEM` did not care, taking any `Prop`; a principle restricted to `z ∈ RealL`
does, because `G` is only known to take real values on `[0,1]`. So `goLeft`
tests `G` at `max 0 (min m 1)`, which lies in `[0,1]` for every rational `m`
and equals `m` at every stage the recursion actually reaches (`ratMid_facts`
supplies the two bounds there). `ratMin` and `ratMax` decide a comparison of
rationals, which is free. -/

/-- The chain principle at one carrier, plus the sign disjunction for the
step. The halving machine's payload is the pair of endpoint signs; the sign
disjunction at the midpoint keeps one half's pair intact; the chain iterates.

Why the instance is the statement. A reversal to the quantified form would have
to conclude a chain in an arbitrary set, `powerset RealL` included, from
theorems that conclude only about `RealL`. Here the carrier is
`halveS (straddleSignP G)` -- coded pairs of rationals carrying `G`'s two
endpoint signs, which is those theorems' own subject.

Not claimed: that the instance is cheaper. `binaryDCOnAt_of_binaryDCOn` fixes the
direction and nothing here derives the quantified form back, so this is an upper
bound moving down, not a separation. -/
theorem attainment_of_signDisjunction_binaryDCOnAt_le (hsd : SignDisjunction.{u})
    {G : ZFSet.{u} → ZFSet.{u}}
    (hbdc : BinaryDCOnAt.{u}
      (halveS (straddleSignP G)) (halveR (straddleSignP G)))
    (hGm : ∀ x, x ∈ realLIcc ratZero.{u} ratOne.{u} → G x ∈ RealL.{u})
    (hGuc : UniformlyContinuousOn G ratZero.{u} ratOne.{u})
    (hG0 : realLLe (G (realLOf ratZero.{u})) realLZero.{u})
    (hG1 : realLLe realLZero.{u} (G (realLOf ratOne.{u}))) :
    ∃ c, And (c ∈ realLIcc ratZero.{u} ratOne.{u}) (G c = realLZero.{u}) := by
  have hGm' : ∀ q, q ∈ NumberTheory.Rat.{u} → ratLe ratZero.{u} q →
      ratLe q ratOne.{u} → G (realLOf q) ∈ RealL.{u} := fun q hq h0 h1 =>
    hGm _ (realLOf_mem_realLIcc ratZero_mem_Rat ratOne_mem_Rat hq h0 h1)
  have hstep : ∀ a b, a ∈ NumberTheory.Rat.{u} → b ∈ NumberTheory.Rat.{u} → ratLe ratZero.{u} a →
      ratLt a b → ratLe b ratOne.{u} →
      straddleSignP G a b →
      straddleSignP G a (ratMid a b) ∨ straddleSignP G (ratMid a b) b := by
    intro a b ha hb h0a hab hb1 hpay
    obtain ⟨hmQ, ham, hmb, h0m, hm1⟩ := ratMid_facts ha hb h0a hab hb1
    rcases hsd (G (realLOf (ratMid a b))) (hGm' _ hmQ h0m hm1) with hle | hge
    · exact Or.inr ⟨hle, hpay.right⟩
    · exact Or.inl ⟨hpay.left, hge⟩
  exact attainment_of_halveLimit_le
    (halve_limit_of_binaryDCOnAt hbdc hstep ⟨hG0, hG1⟩) hGm hGuc

/-- A uniformly continuous `G` on `[0, 1]` with `G 0 ≤ 0 ≤ G 1` has a zero, from
`SignDisjunction` and `BinaryDCOn`. -/
theorem attainment_of_signDisjunction_binaryDCOn_le (hsd : SignDisjunction.{u})
    (hbdc : BinaryDCOn.{u}) {G : ZFSet.{u} → ZFSet.{u}}
    (hGm : ∀ x, x ∈ realLIcc ratZero.{u} ratOne.{u} → G x ∈ RealL.{u})
    (hGuc : UniformlyContinuousOn G ratZero.{u} ratOne.{u})
    (hG0 : realLLe (G (realLOf ratZero.{u})) realLZero.{u})
    (hG1 : realLLe realLZero.{u} (G (realLOf ratOne.{u}))) :
    ∃ c, And (c ∈ realLIcc ratZero.{u} ratOne.{u}) (G c = realLZero.{u}) :=
  attainment_of_signDisjunction_binaryDCOnAt_le hsd
    (binaryDCOnAt_of_binaryDCOn hbdc
      (fun _ hp => ((mem_sep_iff _ _ _).mp hp).left))
    hGm hGuc hG0 hG1

/-! ### The same bound with the chain removed -/

/-- The sign disjunction with dependent choice recovers the exact IVT --
the strict hypotheses weaken into the non-strict core. -/
theorem attainment_of_signDisjunction_binaryDCOn (hsd : SignDisjunction.{u})
    (hbdc : BinaryDCOn.{u}) : ExactIVT01.{u} :=
  fun _ hGm hGuc hG0 hG1 =>
    attainment_of_signDisjunction_binaryDCOn_le hsd hbdc hGm hGuc
      (realLLe_of_lt (hGm _ (left_mem_realLIcc ratZero_mem_Rat
        ratOne_mem_Rat ratZero_lt_one.left)) realLZero_mem hG0)
      (realLLe_of_lt realLZero_mem (hGm _ (right_mem_realLIcc
        ratZero_mem_Rat ratOne_mem_Rat ratZero_lt_one.left)) hG1)

/-- The sandwich closes: `LLPO` with both choice layers recovers the
exact IVT, so `ExactIVT01` sits between `LLPO`, which is choice-free, and
`LLPO + BinaryDC + DC`. The gap is exactly the two choice layers, and whether
either is removable is the model-dependent question the record leaves open. -/
theorem exactIVT_of_llpo_binaryDC_binaryDCOn (hllpo : LLPO) (hbdc : BinaryDC)
    (hbdcon : BinaryDCOn.{u}) : ExactIVT01.{u} :=
  attainment_of_signDisjunction_binaryDCOn
    (signDisjunction_of_llpo_binaryDC hllpo hbdc) hbdcon

#print axioms Metamath.not_halveDecider_forall
#print axioms Metamath.signDisjunction_read
#print axioms Metamath.clamp_third_strict
#print axioms Metamath.signDisjunction_of_exact_ivt
#print axioms Metamath.exactIVT01_of_top
#print axioms Metamath.isOrderTopology_realLOpens
#print axioms Metamath.signDisjunction_of_llpo_binaryDC
#print axioms Metamath.attainment_of_signDisjunction_binaryDCOn
#print axioms Metamath.exactIVT_of_llpo_binaryDC_binaryDCOn
#print axioms Metamath.attainment_of_signDisjunction_binaryDCOn_le
#print axioms Metamath.attainment_of_signDisjunction_binaryDCOnAt_le
#print axioms Metamath.straddleSignP
/-! ## Local nonzeroness, as data

A `Prop` saying a good point exists in each interval cannot supply one, and
extracting a function from it for every interval at once is countable choice.
Booij's corresponding hypothesis is lifts to locators, likewise structure.
`LocalNonzeroData` decides nothing about `G` at a point the caller names, so it
is not a sign readout. -/

/-- Local nonzeroness as data, with the contraction Booij's middle third
gives. `pt` names, in each interval, a rational where `G` is apart from zero. -/
structure LocalNonzeroData (G : ZFSet.{u} → ZFSet.{u}) where
  pt : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}
  ratio : ZFSet.{u}
  ratio_mem : ratio ∈ NumberTheory.Rat.{u}
  ratio_pos : ratLt ratZero.{u} ratio
  ratio_lt_one : ratLt ratio ratOne.{u}
  pt_mem : ∀ a b, a ∈ NumberTheory.Rat.{u} → b ∈ NumberTheory.Rat.{u} →
    pt a b ∈ NumberTheory.Rat.{u}
  pt_between : ∀ a b, a ∈ NumberTheory.Rat.{u} → b ∈ NumberTheory.Rat.{u} →
    ratLt a b → And (ratLt a (pt a b)) (ratLt (pt a b) b)
  pt_apart : ∀ a b, a ∈ NumberTheory.Rat.{u} → b ∈ NumberTheory.Rat.{u} →
    ratLt a b → realLApart realLZero.{u} (G (realLOf (pt a b)))
  pt_maps : ∀ a b, a ∈ NumberTheory.Rat.{u} → b ∈ NumberTheory.Rat.{u} →
    G (realLOf (pt a b)) ∈ RealL.{u}
  pt_shrinkL : ∀ a b, a ∈ NumberTheory.Rat.{u} → b ∈ NumberTheory.Rat.{u} →
    ratLt a b →
    ratLe (ratAdd (pt a b) (ratNeg a)) (ratMul ratio (ratAdd b (ratNeg a)))
  pt_shrinkR : ∀ a b, a ∈ NumberTheory.Rat.{u} → b ∈ NumberTheory.Rat.{u} →
    ratLt a b →
    ratLe (ratAdd b (ratNeg (pt a b))) (ratMul ratio (ratAdd b (ratNeg a)))


/-- `√2` as a member of `RealL`, named once. -/
def sqrtTwoR : ZFSet.{u} :=
  opair NumberTheory.sqrtTwo.{u} (nestUpper NumberTheory.sqHighSeq.{u})

end Metamath
#print axioms Metamath.ExactIVT01
#print axioms Metamath.ExactIVT01Top
namespace ZFSet
export Metamath (ExactIVT01 ExactIVT01Top LocalNonzeroData attainment_of_signDisjunction_binaryDCOn attainment_of_signDisjunction_binaryDCOnAt_le attainment_of_signDisjunction_binaryDCOn_le clamp_third_strict exactIVT01_of_top exactIVT_of_llpo_binaryDC_binaryDCOn isOrderTopology_realLOpens not_halveDecider_forall signDisjunction_of_exact_ivt signDisjunction_of_llpo_binaryDC signDisjunction_read sqrtTwoR straddleSignP)
end ZFSet
