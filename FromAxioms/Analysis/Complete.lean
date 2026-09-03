/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Cauchy completeness for the located reals

Every limit downstream of the derivative -- the integral, power series, the
transcendental functions -- is a limit of a sequence of reals, and the
development had no way to name one. `Nested.lean`'s intervals and
`Cauchy.lean`'s `limLower` are both stated for rational sequences, and
bracketing a real sequence by rationals to reach them needs a sequence of
brackets, which is countable choice.

So the limit is built here, directly, as a located pair: the rationals
eventually strictly below the sequence against those eventually strictly above.
The shape is `limLower`'s; what differs is that the comparison is `realLLt`
rather than `ratLt`, and that the margin keeping "strictly" honest is a scale
rather than an arbitrary rational.

The sequence is a Lean-level `Nat → ZFSet`, which is how `realPartial` and
`natSeq` already present sequences, so nothing is chosen to index it. The
modulus is an existential per scale.
-/

import FromAxioms.Analysis.Ternary
import FromAxioms.NumberTheory.Prime

universe u

open NumberTheory SetTheory
namespace Analysis

/-! ## The Cauchy condition, and the two halves of the limit -/

/-- A sequence of reals with a modulus: past `m`, any two terms are within the
scale asked for. The modulus is an existential per scale, and every use of it
below is inside a proof. -/
def IsCauchyReal (x : Nat → ZFSet.{u}) : Prop :=
  ∀ n : Nat, ∃ m : Nat, ∀ j k : Nat, m ≤ j → m ≤ k →
    WithinOf (realLAdd (x j) (realLNeg (x k))) (invScale.{u} n)

/-! ## Convergence -/

/-- The sequence eventually stays within every scale of `L`. -/
def TendsToL (x : Nat → ZFSet.{u}) (L : ZFSet.{u}) : Prop :=
  ∀ n : Nat, ∃ m : Nat, ∀ k : Nat, m ≤ k →
    WithinOf (realLAdd (x k) (realLNeg L)) (invScale.{u} n)

/-! ## The constant

The one integral that can be computed rather than approximated, which turns the
fundamental theorem into a Taylor statement: subtracting the constant `F' a`
from the integrand replaces the increment by the increment past the tangent,
which is the order-one remainder. -/

/-- Below every scale is below zero: the Archimedean closer. This is the
method of exhaustion in its modern form -- Archimedes exhausts a quantity by
showing it is smaller than every member of a shrinking family, and concludes it
is zero rather than merely small. -/
theorem realLLe_zero_of_forall_invWidth {x : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (h : ∀ n : Nat, realLLe x (realLOf (invWidth (ofNat.{u} n)))) :
    realLLe x realLZero.{u} := by
  rintro ⟨p, hpU0, hpL⟩
  rw [realLZero, realLOf, snd_opair] at hpU0
  obtain ⟨hpQ, hp0⟩ := (mem_sep_iff _ _ _).mp hpU0
  obtain ⟨N, hNw, hNp⟩ := exists_invWidth_lt hpQ hp0
  obtain ⟨j, rfl⟩ := (mem_omega_iff N).mp hNw
  have hxlt : realLLt (realLOf p) x :=
    (realLOf_lt_iff_mem_lower hx hpQ).mpr hpL
  have hchain := realLLt_of_lt_of_le (realLOf_mem hpQ) hx
    (invScale_mem.{u} j) hxlt (h j)
  exact ratLt_irrefl (ratLt_trans hpQ
    (invWidth_mem_Rat (ofNat_mem_omega.{u} j)) hpQ
    ((realLOf_lt_realLOf hpQ
      (invWidth_mem_Rat (ofNat_mem_omega.{u} j))).mp hchain) hNp)

/-- Above every negated scale is above zero: the mirror closer. -/
theorem zero_le_of_forall_neg_invWidth {x : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (h : ∀ n : Nat, realLLe (realLOf (ratNeg (invWidth (ofNat.{u} n)))) x) :
    realLLe realLZero.{u} x := by
  rintro ⟨p, hpU, hpL0⟩
  rw [realLZero, realLOf, fst_opair] at hpL0
  obtain ⟨hpQ, hp0⟩ := (mem_ratCut_iff _ p).mp hpL0
  have hnp0 : ratLt ratZero.{u} (ratNeg p) := by
    have hstep := (ratNeg_lt_neg_iff ratZero_mem_Rat hpQ).mpr hp0
    rwa [ratNeg_zero] at hstep
  obtain ⟨N, hNw, hNp⟩ := exists_invWidth_lt (ratNeg_mem_Rat hpQ) hnp0
  obtain ⟨j, rfl⟩ := (mem_omega_iff N).mp hNw
  have hxlt : realLLt x (realLOf p) :=
    (lt_realLOf_iff_mem_upper hx hpQ).mpr hpU
  have hchain := realLLt_of_le_of_lt
    (realLOf_mem (ratNeg_mem_Rat (invWidth_mem_Rat (ofNat_mem_omega.{u} j))))
    hx (realLOf_mem hpQ) (h j) hxlt
  have hplt : ratLt p (ratNeg (invWidth (ofNat.{u} j))) := by
    have hstep := (ratNeg_lt_neg_iff (ratNeg_mem_Rat hpQ)
      (invWidth_mem_Rat (ofNat_mem_omega.{u} j))).mpr hNp
    rwa [ratNeg_ratNeg hpQ] at hstep
  exact ratLt_irrefl (ratLt_trans
    (ratNeg_mem_Rat (invWidth_mem_Rat (ofNat_mem_omega.{u} j))) hpQ
    (ratNeg_mem_Rat (invWidth_mem_Rat (ofNat_mem_omega.{u} j)))
    ((realLOf_lt_realLOf (ratNeg_mem_Rat
      (invWidth_mem_Rat (ofNat_mem_omega.{u} j))) hpQ).mp hchain) hplt)

#print axioms Analysis.realLLe_zero_of_forall_invWidth
#print axioms Analysis.zero_le_of_forall_neg_invWidth
end Analysis
namespace ZFSet
export Analysis (IsCauchyReal TendsToL realLLe_zero_of_forall_invWidth zero_le_of_forall_neg_invWidth)
end ZFSet
