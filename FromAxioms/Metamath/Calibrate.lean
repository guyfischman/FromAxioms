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

THAT LAST CLAIM IS FALSE FOR A READOUT WHOSE BIT IS A `ZFSet`, and
`Analysis.SignReadout` is one. `condP P A B` is a total `ZFSet` term for ANY
`Prop` `P` -- separation does not ask whether `P` is decided -- so a readout
carrying a set-valued bit is not on the far side of the wall at all. What its
fields cost is three `Prop` obligations, and a `Prop`-level decision discharges
them: `Constructive.signReadout_of_decidableRealLLe` builds the whole structure
from `WEM`.

SO THE `n/a` IS A FACT ABOUT THE BIT'S SORT AND NOT ABOUT READOUTS. Where the
bit is a `Bool` or a `Nat`-valued modulus the wall is real and countable choice
is the price -- `Analysis.nonempty_uniformOn_of_countableNatChoice` pays
exactly that, and its conclusion is `Nonempty` for exactly this reason. Both
halves appear in `exactIVT01_of_wem_of_countableNatChoice` below, so it takes
two principles rather than one.
-/

import FromAxioms.Analysis.Complex
import FromAxioms.Analysis.Deriv
import FromAxioms.Analysis.Weier
import FromAxioms.Constructive.ContentLocated
import FromAxioms.NumberTheory.Halving

set_option autoImplicit false

universe u

open Analysis Constructive NumberTheory SetTheory

namespace Analysis

end Analysis

namespace Metamath

/-- Exact IVT on the unit interval: every uniformly continuous function
strictly straddling zero has a root. -/
def ExactIVT01 : Prop :=
  ∀ G : ZFSet.{u} → ZFSet.{u},
    (∀ x, x ∈ realLIcc ratZero.{u} ratOne.{u} → G x ∈ RealL.{u}) →
    UniformlyContinuousOn G ratZero.{u} ratOne.{u} →
    realLLt (G (realLOf ratZero.{u})) realLZero.{u} →
    realLLt realLZero.{u} (G (realLOf ratOne.{u})) →
    ∃ c, And (c ∈ realLIcc ratZero.{u} ratOne.{u}) (G c = realLZero.{u})

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
`BinaryDCOn` this file actually uses can be WRITTEN DOWN.

It was a lambda inside the proof below until now, so the seven rows' debt could
only ever be stated in the quantified form: a hypothesis about `halveS P` needs
a `P`.

An `abbrev` rather than a `def` -- `halve_limit_of_binaryDCOnAt` unifies its
`P` against this, and a `def` makes that unification the caller's problem. -/
abbrev straddleSignP (G : ZFSet.{u} → ZFSet.{u}) (a b : ZFSet.{u}) : Prop :=
  And (realLLe (G (realLOf a)) realLZero.{u})
      (realLLe realLZero.{u} (G (realLOf b)))

set_option maxHeartbeats 1000000 in
/-- The exact IVT from a bisection LIMIT, and no principle at all.

THIS IS THE FUNNEL THE SEVEN BISECTION THEOREMS PASS THROUGH, and this form
says what they actually spend. Darboux, Rolle, Taylor, the extreme value
theorem, the exact IVT, the mean value theorem and the mean value theorem for
integrals each spend `SignDisjunction + BinaryDCOn`, while the reversal
recovers only the first summand. Both
summands are consumed HERE, and both are consumed producing ONE object: a
halving limit for the straddle payload. Everything after that object -- nesting
the endpoints, and pinning `G c` to zero by uniform continuity -- is a theorem of
the ambient axioms, which is what this signature makes visible.

SO THE ROWS' DEBT IS `HasHalveLimit (straddleSignP G)`, not two principles. The
two corollaries below reach it two ways, and neither is a special case of the
other: `SignDisjunction` supplies the STEP and the chain principle supplies the
ITERATION, while a `HalveDecider` supplies both at once. -/
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

/-! ### AND THE CEILING COMES DOWN AGAIN, TO ONE NODE IN THE ROW'S OWN VOCABULARY

IT IS BOUNDED ON BOTH SIDES BY NODES ALREADY NAMED HERE, so it is worth a
name rather than an inline binder:

    Constructive.SignDisjunction  ≤  NonnegDecision  ≤  Constructive.WEM
                                     NonnegDecision  ≤  DecidableRealLLt
                                     NonnegDecision  ≤  Constructive.ZeroOrApart
                                     NonnegDecision  ≤  Constructive.EqOrApart

AND THE GAP TO THE FLOOR IS NOW ONE DOUBLE NEGATION, WRITTEN OUT. Unfolding
`realLLe`, whose definition is a NEGATION, the two ends of the bracket read

    SignDisjunction    ¬ (0 < z)  ∨  ¬ (z < 0)
    NonnegDecision     ¬ (z < 0)  ∨  ¬ ¬ (z < 0)

so what the row still owes is exactly whether the landmark can STABILISE its own
sign disjunction. That is a sharper question than *is some chain principle
reversible*, and it is asked in one vocabulary rather than in two.

WHY THE MIDPOINT IS CLAMPED, AND IT IS NOT DECORATION. `HalveDecider.decided`
is quantified over ALL rational pairs, with only `a, b ∈ Rat` in hand --- no
`0 ≤ a` and no `b ≤ 1`. `WEM` did not care, taking any `Prop`; a principle
restricted to `z ∈ RealL` does, because `G` is only known to take real values on
`[0,1]`. So `goLeft` tests `G` at `max 0 (min m 1)`, which lies in `[0,1]` for
every rational `m` and EQUALS `m` at every stage the recursion actually reaches
(`ratMid_facts` supplies the two bounds there). `ratMin` and `ratMax` decide a
comparison of RATIONALS, which is free. -/

/-- The chain principle AT ONE CARRIER, plus the sign disjunction for the
step. The halving machine's payload is the pair of endpoint signs; the sign
disjunction at the midpoint keeps one half's pair intact; the chain iterates.

WHY THE INSTANCE IS THE STATEMENT AND THE QUANTIFIED FORM WAS NOT. Those rows'
reversal target read `<landmark> -> BinaryDCOn`: a chain in an ARBITRARY set,
`powerset RealL` included, derived from landmarks that conclude only about
`RealL`. Here the carrier is `halveS (straddleSignP G)` -- coded pairs of
RATIONALS carrying `G`'s two endpoint signs, which is the landmarks' own
subject. The target shrinks to a statement about the very object the landmark
speaks of.

NOT CLAIMED: that the instance is CHEAPER. `binaryDCOnAt_of_binaryDCOn` fixes the
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

/-- The same from the quantified principle, kept with its signature intact
because seventeen theorems and seven registry rows cite it. The whole difference
is `binaryDCOnAt_of_binaryDCOn`, and its subset side condition is discharged by
`halveR` being a `sep` of `prod (halveS _) (halveS _)`.

SO THE PROOF NO LONGER USES `BinaryDCOn` AT ALL -- it uses one instance of it,
and this line takes the instance. So a reader asking what these theorems spend
finds the answer in a signature rather than in a proof body. -/
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

/-! ### The same bound with the CHAIN removed -/

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

#print axioms Metamath.signDisjunction_of_llpo_binaryDC
#print axioms Metamath.attainment_of_signDisjunction_binaryDCOn
#print axioms Metamath.exactIVT_of_llpo_binaryDC_binaryDCOn
#print axioms Metamath.attainment_of_signDisjunction_binaryDCOn_le
#print axioms Metamath.attainment_of_signDisjunction_binaryDCOnAt_le
#print axioms Metamath.straddleSignP
end Metamath
#print axioms Metamath.ExactIVT01
namespace ZFSet
export Metamath (ExactIVT01 attainment_of_signDisjunction_binaryDCOn attainment_of_signDisjunction_binaryDCOnAt_le attainment_of_signDisjunction_binaryDCOn_le exactIVT_of_llpo_binaryDC_binaryDCOn signDisjunction_of_llpo_binaryDC straddleSignP)
end ZFSet
