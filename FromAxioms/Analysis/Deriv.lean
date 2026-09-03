/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The derivative, in the located reals

Bounds first. Every estimate in differential calculus is of the shape "this real
is within that rational of zero", and the located encoding makes the rational
side the cheap side: `WithinOf z (realLOf c)` says exactly that `c` is missing
from the lower half of `z` and `-c` from the upper half, which is two membership
facts rather than an order chase. The algebra of such bounds -- monotone in the
bound, additive, and multiplicative -- is what the rest of the file is written
in.

The multiplicative one is the only hard one, and it is where locatedness is
spent. A product `x·y` has, for its lower half, the rationals below all four
corners of some bracket; `mulLower_tight` says the bracket may be taken as
narrow as asked, and the margin that makes "as narrow as asked" enough comes
from the lower half being open -- a rational in it always has a larger one in
it, and that gap is the `η` the box estimate has to fit inside.
-/

import FromAxioms.Analysis.IVT

universe u

open NumberTheory SetTheory
namespace Analysis

/-! ## Bounds by a rational

`WithinOf z (realLOf c)` is the workhorse. Read through `realLOf_lt_iff_mem_lower`
and `lt_realLOf_iff_mem_upper` it is a statement about two rationals not being in
two sets, which is the form every proof below consumes it in. -/

/-- A bound may always be weakened. -/
theorem withinOf_mono {x c d : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hc : c ∈ NumberTheory.Rat.{u})
    (hd : d ∈ NumberTheory.Rat.{u}) (hcd : ratLe c d) (h : WithinOf x (realLOf c)) :
    WithinOf x (realLOf d) := by
  have hnc := ratNeg_mem_Rat hc
  have hnd := ratNeg_mem_Rat hd
  refine ⟨?_, ?_⟩
  · rw [realLOf_neg hd]
    refine realLLe_trans (realLOf_mem hnd) (realLOf_mem hnc) hx ?_ ?_
    · exact (realLOf_le_realLOf hnd hnc).mpr ((ratNeg_le_neg_iff hd hc).mpr hcd)
    · have := h.left
      rwa [realLOf_neg hc] at this
  · exact realLLe_trans hx (realLOf_mem hc) (realLOf_mem hd) h.right
      ((realLOf_le_realLOf hc hd).mpr hcd)

/-! ## The derivative -/

/-- Every located real has a rational bound, and it is read off a bracket
rather than chosen: locatedness hands over `lo < x < hi`, and any rational above
both `hi` and `-lo` will do. -/
theorem exists_rat_bound {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    ∃ K, K ∈ NumberTheory.Rat.{u} ∧ ratLe ratZero.{u} K ∧ WithinOf x (realLOf K) := by
  obtain ⟨lo, hi, hloQ, hhiQ, hlt1, hlt2, -⟩ :=
    exists_rat_bracket hx ratOne_mem_Rat ratZero_lt_one
  obtain ⟨k, hkQ, hkhi, hklo⟩ := exists_gt_two hhiQ (ratNeg_mem_Rat hloQ)
  obtain ⟨K, hKQ, hKk, hK0⟩ := exists_gt_two hkQ ratZero_mem_Rat
  have hhiK : ratLt hi K := ratLt_trans hhiQ hkQ hKQ hkhi hKk
  have hloK : ratLt (ratNeg lo) K := ratLt_trans (ratNeg_mem_Rat hloQ) hkQ hKQ hklo hKk
  refine ⟨K, hKQ, hK0.left, ?_, ?_⟩
  · rw [realLOf_neg hKQ]
    refine realLLe_of_lt (realLOf_mem (ratNeg_mem_Rat hKQ)) hx
      (realLLt_trans (realLOf_mem (ratNeg_mem_Rat hKQ)) (realLOf_mem hloQ) hx ?_ hlt1)
    refine (realLOf_lt_realLOf (ratNeg_mem_Rat hKQ) hloQ).mpr ?_
    have := (ratNeg_lt_neg_iff hKQ (ratNeg_mem_Rat hloQ)).mpr hloK
    rwa [ratNeg_ratNeg hloQ] at this
  · exact realLLe_of_lt hx (realLOf_mem hKQ)
      (realLLt_trans hx (realLOf_mem hhiQ) (realLOf_mem hKQ) hlt2
        ((realLOf_lt_realLOf hhiQ hKQ).mpr hhiK))

/-! ### Recovering a factorisation

The readout alone settles the algebra. `caraSlope` is the difference quotient
where the readout says apart and `L` where it says zero, `realLInvApart` supplies
the reciprocal without deciding a sign, and the factorisation and
the value at `a` both fall out with no principle beyond the readout. What it does
not settle is continuity at `a`, which is the whole remaining content of the
converse and is queued as its own item. -/

/-- Deciding whether a real vanishes, as data rather than as a disjunction. -/
structure VanishReadout : Type (u + 1) where
  bit : ZFSet.{u} → ZFSet.{u}
  mem_two : ∀ z, z ∈ RealL.{u} → bit z ∈ ofNat.{u} 2
  zero : ∀ z, z ∈ RealL.{u} → bit z = empty.{u} → z = realLZero.{u}
  apart : ∀ z, z ∈ RealL.{u} → bit z = ofNat.{u} 1 → realLApart realLZero.{u} z

/-- Uniform continuity on `[p, q]`, with the modulus quantified per scale. -/
def UniformlyContinuousOn (H : ZFSet.{u} → ZFSet.{u}) (p q : ZFSet.{u}) : Prop :=
  ∀ n : Nat, ∃ m : Nat, ∀ w x y, w ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} w →
    ratLe w (invWidth (ofNat.{u} m)) → x ∈ realLIcc p q → y ∈ realLIcc p q →
    Close x y (realLOf w) → Close (H x) (H y) (realLOf (invWidth (ofNat.{u} n)))

/-! ## Upgrading a weak order to a strict one

`realLLe u v` is a negation and carries no witness, so nothing follows from it
about how far apart `u` and `v` are. What is available is a dichotomy at a
margin: either they are within `δ`, or they are apart by more than any `e`
below `δ`. Cotransitivity supplies it, and the known direction of the order is
what makes the second alternative one-sided rather than an apartness.

Every argument replacing two reals by nearby rationals needs this first,
because a rational strictly between `u` and `v` exists only once `u < v` is
strict. -/

/-- A rational between the endpoints names a point of the interval. -/
theorem realLOf_mem_realLIcc {p q x : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (hx : x ∈ NumberTheory.Rat.{u}) (hpx : ratLe p x) (hxq : ratLe x q) :
    realLOf x ∈ realLIcc p q :=
  (mem_realLIcc_iff p q _).mpr ⟨realLOf_mem hx, (realLOf_le_realLOf hp hx).mpr hpx,
    (realLOf_le_realLOf hx hq).mpr hxq⟩

/-! ### Uniform continuity along a Lipschitz reparameterisation

Hadamard's factorisation integrates `F'` along the segment from `a` to `x`, so
what has to be uniformly continuous is `F'` composed with an affine map. The
composition is the general fact and the affine case is an instance of it: a map
that moves points by at most `K` times the step turns a modulus for `H` into a
modulus for `H ∘ G`, by asking for the step `K` times smaller. -/

/-- The diameter bound. The difference of two points of `[p, q]` is within
`q - p`, with no sign decided: each side of the bracket is the sum of the two
one-sided estimates. -/
theorem withinOf_diam {p q z y : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (hz : z ∈ realLIcc p q) (hy : y ∈ realLIcc p q) :
    WithinOf (realLAdd z (realLNeg y)) (realLOf (ratAdd q (ratNeg p))) := by
  obtain ⟨hzR, hpz, hzq⟩ := (mem_realLIcc_iff p q z).mp hz
  obtain ⟨hyR, hpy, hyq⟩ := (mem_realLIcc_iff p q y).mp hy
  have hnp := ratNeg_mem_Rat hp
  have hnq := ratNeg_mem_Rat hq
  have hQ := ratAdd_mem_Rat hq hnp
  constructor
  · have h := realLLe_add (realLOf_mem hp) hzR (realLNeg_mem (realLOf_mem hq))
      (realLNeg_mem hyR) hpz (realLNeg_le_neg hyR (realLOf_mem hq) hyq)
    have hid : realLNeg (realLOf (ratAdd q (ratNeg p)))
        = realLAdd (realLOf p) (realLNeg (realLOf q)) := by
      rw [realLOf_neg hQ, ratNeg_add hq hnp, ratNeg_ratNeg hp,
        ratAdd_comm hnq hp, realLOf_add hp hnq, realLOf_neg hq]
    rw [hid]
    exact h
  · have h := realLLe_add hzR (realLOf_mem hq) (realLNeg_mem hyR)
      (realLNeg_mem (realLOf_mem hp)) hzq (realLNeg_le_neg (realLOf_mem hp) hyR hpy)
    rw [realLOf_add hq hnp, ← realLOf_neg hp]
    exact h

#print axioms withinOf_mono
#print axioms exists_rat_bound
#print axioms realLOf_mem_realLIcc
#print axioms withinOf_diam
end Analysis

namespace ZFSet
export Analysis (UniformlyContinuousOn VanishReadout exists_rat_bound realLOf_mem_realLIcc withinOf_diam withinOf_mono)
end ZFSet
