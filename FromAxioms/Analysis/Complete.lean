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

import FromAxioms.Analysis.Deriv

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

/-- A real that is at most `invWidth n` for every `n` is at most zero. -/
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

/-- A real that is at least `-invWidth n` for every `n` is at least zero. -/
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

/-! ## The mean value gadget

The median `f_L(t) = max(3t-2, min(L, 3t-1))` clamps `L` into the moving
window `[3t-2, 3t-1]`. Its mean over `[0,1]` is exactly `L/3`, and where
that mean can be attained is controlled by `L`'s sign -- the two facts the
exact mean value theorem's reversal reads off. -/

/-- The gadget: `L` clamped into the moving window. -/
def mvGadget (L t : ZFSet.{u}) : ZFSet.{u} :=
  realLMax
    (realLAdd (realLMul (realLOf (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u}))) t)
      (realLOf (ratNeg (ratAdd ratOne.{u} ratOne.{u}))))
    (realLMin L
      (realLAdd (realLMul (realLOf (ratAdd ratOne.{u}
          (ratAdd ratOne.{u} ratOne.{u}))) t)
        (realLOf (ratNeg ratOne.{u}))))

theorem mvGadget_mem {L t : ZFSet.{u}} (hL : L ∈ RealL.{u})
    (ht : t ∈ RealL.{u}) : mvGadget L t ∈ RealL.{u} :=
  realLMax_mem
    (realLAdd_mem (realLMul_mem (realLOf_mem (ratAdd_mem_Rat ratOne_mem_Rat
        (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat))) ht)
      (realLOf_mem (ratNeg_mem_Rat (ratAdd_mem_Rat ratOne_mem_Rat
        ratOne_mem_Rat))))
    (realLMin_mem hL
      (realLAdd_mem (realLMul_mem (realLOf_mem (ratAdd_mem_Rat ratOne_mem_Rat
          (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat))) ht)
        (realLOf_mem (ratNeg_mem_Rat ratOne_mem_Rat))))

/-- The gadget is uniformly continuous: a median of two affine maps. -/
theorem mvGadget_uc {L p q : ZFSet.{u}} (hL : L ∈ RealL.{u}) :
    UniformlyContinuousOn (mvGadget L) p q := by
  have h3Q := ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
  have h3R := realLOf_mem h3Q
  have h30 := ratZero_le_three.{u}
  have hAff : ∀ c : ZFSet.{u}, c ∈ NumberTheory.Rat.{u} → UniformlyContinuousOn
      (fun t => realLAdd (realLMul (realLOf (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u}))) t) (realLOf c)) p q := by
    intro c hc
    refine uniformlyContinuousOn_of_hasDerivOn
      (F' := fun _ => realLOf (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u})))
      (fun x hx => realLAdd_mem (realLMul_mem h3R
        ((mem_realLIcc_iff p q x).mp hx).left) (realLOf_mem hc))
      (fun _ _ => h3R)
      (hasDerivOn_affine h3R (realLOf_mem hc)) h3Q h30 ?_
    exact fun _ _ => withinOf_self h3Q h30
  exact uniformlyContinuousOn_median hL
    (fun x hx => realLAdd_mem (realLMul_mem h3R
      ((mem_realLIcc_iff p q x).mp hx).left)
      (realLOf_mem (ratNeg_mem_Rat (ratAdd_mem_Rat ratOne_mem_Rat
        ratOne_mem_Rat))))
    (fun x hx => realLAdd_mem (realLMul_mem h3R
      ((mem_realLIcc_iff p q x).mp hx).left)
      (realLOf_mem (ratNeg_mem_Rat ratOne_mem_Rat)))
    (hAff _ (ratNeg_mem_Rat (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)))
    (hAff _ (ratNeg_mem_Rat ratOne_mem_Rat))

/-- `1/3 + (1/3 + 1/3) = 1`: a real is three thirds of itself. -/
theorem ratInv_three_triple : ratAdd (ratInv (ratAdd ratOne.{u}
    (ratAdd ratOne.{u} ratOne.{u})))
    (ratAdd (ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))
      (ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))))
    = ratOne.{u} := by
  have h3Q := ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
  have h3ne : ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})
      ≠ ratZero.{u} := fun he => ratZero_lt_three.{u}.right he.symm
  have hinv3Q := ratInv_mem_Rat h3Q h3ne
  have hexp : ratMul (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))
      (ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))
      = ratAdd (ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))
        (ratAdd (ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))
          (ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))) := by
    rw [ratAdd_mul ratOne_mem_Rat
        (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat) hinv3Q,
      ratAdd_mul ratOne_mem_Rat ratOne_mem_Rat hinv3Q,
      ratOne_mul hinv3Q]
  rw [← hexp, ratMul_inv h3Q h3ne]

/-- A real is three thirds of itself: `L = L/3 + (L/3 + L/3)`. -/
theorem realL_three_thirds {L : ZFSet.{u}} (hL : L ∈ RealL.{u}) :
    L = realLAdd (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u})))) L)
      (realLAdd (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
          (ratAdd ratOne.{u} ratOne.{u})))) L)
        (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
          (ratAdd ratOne.{u} ratOne.{u})))) L)) := by
  have h3Q := ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
  have hinv3Q := ratInv_mem_Rat h3Q
    (fun he => ratZero_lt_three.{u}.right he.symm)
  have hinv3R := realLOf_mem hinv3Q
  have h1L : L = realLMul (realLOf (ratAdd (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))
      (ratAdd (ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))
        (ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))))) L := by
    rw [ratInv_three_triple]
    show L = realLMul realLOne.{u} L
    rw [realLMul_comm realLOne_mem hL, realLMul_one hL]
  refine h1L.trans ?_
  rw [realLOf_add hinv3Q (ratAdd_mem_Rat hinv3Q hinv3Q),
    realLOf_add hinv3Q hinv3Q,
    realLAdd_mul hinv3R (realLAdd_mem hinv3R hinv3R) hL,
    realLAdd_mul hinv3R hinv3R hL]

/-! ## The read-off window

The attainment point is read against the rationals `4/9 < 5/9`. What the two
thresholds buy: at `c > 4/9` the window's top `3c-1` clears `1/3`, the most
the clamped mean can be; at `c < 5/9` the window's bottom `3c-2` stays under
`-1/3`, the least it can be. -/

def ratFour : ZFSet.{u} :=
  ratAdd (ratAdd ratOne.{u} ratOne.{u}) (ratAdd ratOne.{u} ratOne.{u})

def ratFive : ZFSet.{u} := ratAdd ratOne.{u} ratFour.{u}

def ratNine : ZFSet.{u} :=
  ratMul (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))
    (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))

theorem ratFour_mem : ratFour.{u} ∈ NumberTheory.Rat.{u} :=
  ratAdd_mem_Rat (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)

theorem ratFive_mem : ratFive.{u} ∈ NumberTheory.Rat.{u} :=
  ratAdd_mem_Rat ratOne_mem_Rat ratFour_mem

theorem ratNine_mem : ratNine.{u} ∈ NumberTheory.Rat.{u} :=
  ratMul_mem_Rat (ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat))
    (ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat))

theorem ratZero_lt_nine : ratLt ratZero.{u} ratNine.{u} := by
  have h3Q := ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
  have hstep := ratMul_lt_mul_right ratZero_mem_Rat h3Q h3Q
    (fun he => ratZero_lt_three.{u}.right he.symm)
    ratZero_lt_three.{u}.left ratZero_lt_three.{u}
  rwa [ratZero_mul h3Q] at hstep

theorem ratNine_ne_zero : ratNine.{u} ≠ ratZero.{u} :=
  NumberTheory.ratNe_zero_of_pos ratZero_lt_nine.{u}

theorem ratInv_nine_mem_Rat : ratInv ratNine.{u} ∈ NumberTheory.Rat.{u} :=
  ratInv_mem_Rat ratNine_mem ratNine_ne_zero.{u}

theorem ratInv_three_mem_Rat :
    ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})) ∈ NumberTheory.Rat.{u} :=
  ratInv_mem_Rat (ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)) ratThree_ne_zero.{u}

/-- `3·(1/9) = 1/3`: the nine-instance of inverse cancellation. -/
theorem ratThree_mul_inv_nine :
    ratMul (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))
      (ratInv ratNine.{u})
    = ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})) := by
  have h3Q := ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
  have h3ne := ratThree_ne_zero.{u}
  have hinv9Q := ratInv_nine_mem_Rat.{u}
  have hinv3Q := ratInv_three_mem_Rat.{u}
  have hxQ := ratMul_mem_Rat h3Q hinv9Q
  have h3x : ratMul (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))
      (ratMul (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))
        (ratInv ratNine.{u})) = ratOne.{u} := by
    rw [← ratMul_assoc h3Q h3Q hinv9Q]
    show ratMul ratNine.{u} (ratInv ratNine.{u}) = ratOne.{u}
    exact ratMul_inv ratNine_mem ratNine_ne_zero.{u}
  have hchain : ratMul (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))
      (ratMul (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))
        (ratMul (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))
          (ratInv ratNine.{u})))
      = ratMul (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))
        (ratInv ratNine.{u}) := by
    rw [← ratMul_assoc hinv3Q h3Q hxQ, ratMul_comm hinv3Q h3Q,
      ratMul_inv h3Q h3ne, ratOne_mul hxQ]
  rw [h3x, ratMul_one hinv3Q] at hchain
  exact hchain.symm

/-- `3·(4/9) = 1 + 1/3`: at the lower threshold, the window top clears the
mean's ceiling. -/
theorem ratThree_mul_four_ninths :
    ratMul (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))
      (ratMul ratFour.{u} (ratInv ratNine.{u}))
    = ratAdd ratOne.{u}
        (ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))) := by
  have h3Q := ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
  have h3ne := ratThree_ne_zero.{u}
  have hinv9Q := ratInv_nine_mem_Rat.{u}
  have hinv3Q := ratInv_three_mem_Rat.{u}
  have hfour : ratFour.{u} = ratAdd (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})) ratOne.{u} := by
    show ratAdd (ratAdd ratOne.{u} ratOne.{u}) (ratAdd ratOne.{u} ratOne.{u})
      = _
    rw [ratAdd_assoc ratOne_mem_Rat ratOne_mem_Rat
        (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat),
      ratAdd_assoc ratOne_mem_Rat (ratAdd_mem_Rat ratOne_mem_Rat
        ratOne_mem_Rat) ratOne_mem_Rat,
      ← ratAdd_assoc ratOne_mem_Rat ratOne_mem_Rat ratOne_mem_Rat]
  rw [← ratMul_assoc h3Q ratFour_mem hinv9Q, ratMul_comm h3Q ratFour_mem,
    ratMul_assoc ratFour_mem h3Q hinv9Q, ratThree_mul_inv_nine,
    hfour, ratAdd_mul h3Q ratOne_mem_Rat hinv3Q,
    ratMul_inv h3Q h3ne, ratOne_mul hinv3Q]

/-- `3·(5/9) = 2 - 1/3`: at the upper threshold, the window bottom stays
under the mean's floor. -/
theorem ratThree_mul_five_ninths :
    ratMul (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))
      (ratMul ratFive.{u} (ratInv ratNine.{u}))
    = ratAdd (ratAdd ratOne.{u} ratOne.{u})
        (ratNeg (ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))) := by
  have h3Q := ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
  have h3ne := ratThree_ne_zero.{u}
  have hinv9Q := ratInv_nine_mem_Rat.{u}
  have hinv3Q := ratInv_three_mem_Rat.{u}
  have h31 := ratThree_add_neg_one.{u}
  have hfive : ratAdd (ratAdd (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u}))
      (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))
      (ratNeg ratOne.{u}) = ratFive.{u} := by
    rw [ratAdd_assoc h3Q h3Q (ratNeg_mem_Rat ratOne_mem_Rat), h31,
      ratAdd_assoc ratOne_mem_Rat
        (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
        (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)]
    rfl
  rw [← ratMul_assoc h3Q ratFive_mem hinv9Q, ratMul_comm h3Q ratFive_mem,
    ratMul_assoc ratFive_mem h3Q hinv9Q, ratThree_mul_inv_nine,
    ← hfive,
    ratAdd_mul (ratAdd_mem_Rat h3Q h3Q) (ratNeg_mem_Rat ratOne_mem_Rat)
      hinv3Q,
    ratAdd_mul h3Q h3Q hinv3Q, ratMul_inv h3Q h3ne,
    ratMul_comm (ratNeg_mem_Rat ratOne_mem_Rat) hinv3Q,
    ratMul_neg hinv3Q ratOne_mem_Rat, ratMul_one hinv3Q]

/-- If `0 < L ≤ 1` and `4/9 < c`, then `mvGadget L c ≠ L / 3`. -/
theorem mvGadget_exclusion_pos {L c : ZFSet.{u}} (hL : L ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (hL0 : realLLt realLZero.{u} L)
    (hL1 : realLLe L realLOne.{u})
    (hc49 : realLLt (realLOf (ratMul ratFour.{u} (ratInv ratNine.{u}))) c)
    (heq : mvGadget L c = realLMul (realLOf (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))) L) : False := by
  have h3Q := ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
  have h3R := realLOf_mem h3Q
  have hinv3Q := ratInv_three_mem_Rat.{u}
  have hinv3R := realLOf_mem hinv3Q
  have hu := realLMul_mem hinv3R hL
  have hpQ := ratMul_mem_Rat ratFour_mem
    (ratInv_mem_Rat ratNine_mem ratNine_ne_zero.{u})
  have hpR := realLOf_mem hpQ
  have hBm := realLAdd_mem (realLMul_mem h3R hc)
    (realLOf_mem (ratNeg_mem_Rat ratOne_mem_Rat))
  -- `u < L`: the clamp exceeds its own third
  have hinv3_pos : realLLt realLZero.{u} (realLOf (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))) :=
    (realLOf_lt_realLOf ratZero_mem_Rat hinv3Q).mpr
      (ratInv_pos h3Q ratZero_lt_three.{u})
  have hu_pos : realLLt realLZero.{u} (realLMul (realLOf (ratInv
      (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))) L) :=
    realLMul_pos hinv3R hL hinv3_pos hL0
  have huu_pos : realLLt realLZero.{u} (realLAdd (realLMul (realLOf (ratInv
      (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))) L)
      (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u})))) L)) := by
    have hstep := realLLt_add_right realLZero_mem hu hu hu_pos
    rw [realLAdd_comm realLZero_mem hu, realLAdd_zero hu] at hstep
    exact realLLt_trans realLZero_mem hu (realLAdd_mem hu hu) hu_pos hstep
  have hu_lt_L : realLLt (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))) L) L := by
    have hstep := realLLt_add_right realLZero_mem (realLAdd_mem hu hu)
      hu huu_pos
    rw [realLAdd_comm realLZero_mem hu, realLAdd_zero hu,
      realLAdd_comm (realLAdd_mem hu hu) hu] at hstep
    rwa [← realL_three_thirds.{u} hL] at hstep
  -- `u ≤ 1/3`
  have hu_le : realLLe (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))) L)
      (realLOf (ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))) := by
    have hstep := realLMul_le_right hL realLOne_mem hinv3R hL1
      (realLLe_of_lt realLZero_mem hinv3R hinv3_pos)
    rw [realLMul_comm hL hinv3R, realLMul_comm realLOne_mem hinv3R,
      realLMul_one hinv3R] at hstep
    exact hstep
  -- `1/3 < 3c - 1`
  have hB_gt : realLLt (realLOf (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u}))))
      (realLAdd (realLMul (realLOf (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u}))) c)
        (realLOf (ratNeg ratOne.{u}))) := by
    have hmul := realLMul_lt_right hpR hc h3R hc49
      ((realLOf_lt_realLOf ratZero_mem_Rat h3Q).mpr ratZero_lt_three.{u})
    rw [realLMul_comm hpR h3R, realLMul_comm hc h3R,
      ← realLOf_mul h3Q hpQ, ratThree_mul_four_ninths] at hmul
    have hshift := realLLt_add_right
      (realLOf_mem (ratAdd_mem_Rat ratOne_mem_Rat hinv3Q))
      (realLMul_mem h3R hc)
      (realLOf_mem (ratNeg_mem_Rat ratOne_mem_Rat)) hmul
    rw [← realLOf_add (ratAdd_mem_Rat ratOne_mem_Rat hinv3Q)
        (ratNeg_mem_Rat ratOne_mem_Rat)] at hshift
    have hrat : ratAdd (ratAdd ratOne.{u} (ratInv (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u})))) (ratNeg ratOne.{u})
        = ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})) := by
      rw [ratAdd_comm ratOne_mem_Rat hinv3Q,
        ratAdd_assoc hinv3Q ratOne_mem_Rat (ratNeg_mem_Rat ratOne_mem_Rat),
        ratAdd_neg ratOne_mem_Rat, ratAdd_zero hinv3Q]
    rwa [hrat] at hshift
  -- assemble: the mean sits strictly below the gadget it should equal
  have hu_lt_B := realLLt_of_le_of_lt hu hinv3R hBm hu_le hB_gt
  have hmin := realLLt_min hL hBm hu_lt_L hu_lt_B
  have hle : realLLe (realLMin L (realLAdd (realLMul (realLOf
      (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))) c)
      (realLOf (ratNeg ratOne.{u})))) (mvGadget L c) :=
    realLLe_max_right (realLMin_mem hL hBm)
  have hfinal := realLLt_of_lt_of_le hu (realLMin_mem hL hBm)
    (mvGadget_mem hL hc) hmin hle
  rw [heq] at hfinal
  exact realLLt_irrefl hu hfinal

/-- If `-1 ≤ L < 0` and `c < 5/9`, then `mvGadget L c ≠ L / 3`. -/
theorem mvGadget_exclusion_neg {L c : ZFSet.{u}} (hL : L ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (hL0 : realLLt L realLZero.{u})
    (hlo : realLLe (realLNeg realLOne.{u}) L)
    (hc59 : realLLt c (realLOf (ratMul ratFive.{u} (ratInv ratNine.{u}))))
    (heq : mvGadget L c = realLMul (realLOf (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))) L) : False := by
  have h3Q := ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
  have h3R := realLOf_mem h3Q
  have h2Q := ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat
  have hinv3Q := ratInv_three_mem_Rat.{u}
  have hinv3R := realLOf_mem hinv3Q
  have hu := realLMul_mem hinv3R hL
  have hqQ := ratMul_mem_Rat ratFive_mem
    (ratInv_mem_Rat ratNine_mem ratNine_ne_zero.{u})
  have hqR := realLOf_mem hqQ
  have hAm := realLAdd_mem (realLMul_mem h3R hc)
    (realLOf_mem (ratNeg_mem_Rat h2Q))
  have hinv3_pos : realLLt realLZero.{u} (realLOf (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))) :=
    (realLOf_lt_realLOf ratZero_mem_Rat hinv3Q).mpr
      (ratInv_pos h3Q ratZero_lt_three.{u})
  -- `u < 0`, hence `L < u`
  have hu_neg : realLLt (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))) L) realLZero.{u} := by
    have hnL : realLLt realLZero.{u} (realLNeg L) := by
      have hstep := realLNeg_lt_neg hL realLZero_mem hL0
      rwa [realLNeg_zero] at hstep
    have hpos := realLMul_pos hinv3R (realLNeg_mem hL) hinv3_pos hnL
    rw [realLMul_neg hinv3R hL] at hpos
    have hstep := realLNeg_lt_neg realLZero_mem (realLNeg_mem hu) hpos
    rwa [realLNeg_realLNeg hu, realLNeg_zero] at hstep
  have huu_neg : realLLt (realLAdd (realLMul (realLOf (ratInv
      (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))) L)
      (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u})))) L)) realLZero.{u} := by
    have hstep := realLLt_add_right hu realLZero_mem hu hu_neg
    rw [realLAdd_comm realLZero_mem hu, realLAdd_zero hu] at hstep
    exact realLLt_trans (realLAdd_mem hu hu) hu realLZero_mem hstep hu_neg
  have hL_lt_u : realLLt L (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))) L) := by
    have hstep := realLLt_add_right (realLAdd_mem hu hu) realLZero_mem
      hu huu_neg
    rw [realLAdd_comm realLZero_mem hu, realLAdd_zero hu,
      realLAdd_comm (realLAdd_mem hu hu) hu] at hstep
    rwa [← realL_three_thirds.{u} hL] at hstep
  -- `-1/3 ≤ u`
  have hng_le_u : realLLe (realLOf (ratNeg (ratInv (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u})))))
      (realLMul (realLOf (ratInv (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u})))) L) := by
    have hstep := realLMul_le_right (realLNeg_mem realLOne_mem) hL
      hinv3R hlo (realLLe_of_lt realLZero_mem hinv3R hinv3_pos)
    rw [realLMul_comm (realLNeg_mem realLOne_mem) hinv3R,
      realLMul_comm hL hinv3R,
      realLMul_neg hinv3R realLOne_mem, realLMul_one hinv3R,
      realLOf_neg hinv3Q] at hstep
    exact hstep
  -- `3c - 2 < -1/3`
  have hA_lt : realLLt (realLAdd (realLMul (realLOf (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u}))) c)
      (realLOf (ratNeg (ratAdd ratOne.{u} ratOne.{u}))))
      (realLOf (ratNeg (ratInv (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u}))))) := by
    have hmul := realLMul_lt_right hc hqR h3R hc59
      ((realLOf_lt_realLOf ratZero_mem_Rat h3Q).mpr ratZero_lt_three.{u})
    rw [realLMul_comm hc h3R, realLMul_comm hqR h3R,
      ← realLOf_mul h3Q hqQ, ratThree_mul_five_ninths] at hmul
    have hshift := realLLt_add_right (realLMul_mem h3R hc)
      (realLOf_mem (ratAdd_mem_Rat h2Q (ratNeg_mem_Rat hinv3Q)))
      (realLOf_mem (ratNeg_mem_Rat h2Q)) hmul
    rw [← realLOf_add (ratAdd_mem_Rat h2Q (ratNeg_mem_Rat hinv3Q))
        (ratNeg_mem_Rat h2Q)] at hshift
    have hrat : ratAdd (ratAdd (ratAdd ratOne.{u} ratOne.{u})
        (ratNeg (ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u})))))
        (ratNeg (ratAdd ratOne.{u} ratOne.{u}))
        = ratNeg (ratInv (ratAdd ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}))) := by
      rw [ratAdd_comm h2Q (ratNeg_mem_Rat hinv3Q),
        ratAdd_assoc (ratNeg_mem_Rat hinv3Q) h2Q (ratNeg_mem_Rat h2Q),
        ratAdd_neg h2Q, ratAdd_zero (ratNeg_mem_Rat hinv3Q)]
    rwa [hrat] at hshift
  -- assemble: the gadget sits strictly below the mean it should equal
  have hA_lt_u := realLLt_of_lt_of_le hAm
    (realLOf_mem (ratNeg_mem_Rat hinv3Q)) hu hA_lt hng_le_u
  have hmax := realLMax_lt hAm hL hA_lt_u hL_lt_u
  have hle2 : realLLe (mvGadget L c)
      (realLMax (realLAdd (realLMul (realLOf (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u}))) c)
        (realLOf (ratNeg (ratAdd ratOne.{u} ratOne.{u})))) L) := by
    refine realLMax_le (realLLe_max_left hAm) ?_
    exact realLLe_trans
      (realLMin_mem hL (realLAdd_mem (realLMul_mem h3R hc)
        (realLOf_mem (ratNeg_mem_Rat ratOne_mem_Rat)))) hL
      (realLMax_mem hAm hL) (realLMin_le_left hL) (realLLe_max_right hL)
  have hfinal := realLLt_of_le_of_lt (mvGadget_mem hL hc)
    (realLMax_mem hAm hL) hu hle2 hmax
  rw [heq] at hfinal
  exact realLLt_irrefl hu hfinal

/-- `mvGadget L 0 = -1` when `-1 ≤ L`. -/
theorem mvGadget_at_zero {L : ZFSet.{u}} (hL : L ∈ RealL.{u})
    (hlo : realLLe (realLNeg realLOne.{u}) L) :
    mvGadget L (realLOf ratZero.{u}) = realLOf (ratNeg ratOne.{u}) := by
  have h3Q := ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
  have h2Q := ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat
  have hn1R := realLOf_mem (ratNeg_mem_Rat ratOne_mem_Rat)
  have hn2R := realLOf_mem (ratNeg_mem_Rat h2Q)
  have hzero : ∀ cq : ZFSet.{u}, cq ∈ NumberTheory.Rat.{u} →
      realLAdd (realLMul (realLOf (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u}))) (realLOf ratZero.{u}))
        (realLOf cq) = realLOf cq := by
    intro cq hcq
    rw [← realLOf_mul h3Q ratZero_mem_Rat, ratMul_zero h3Q]
    show realLAdd realLZero.{u} (realLOf cq) = realLOf cq
    rw [realLAdd_comm realLZero_mem (realLOf_mem hcq),
      realLAdd_zero (realLOf_mem hcq)]
  show realLMax
      (realLAdd (realLMul (realLOf (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u}))) (realLOf ratZero.{u}))
        (realLOf (ratNeg (ratAdd ratOne.{u} ratOne.{u}))))
      (realLMin L (realLAdd (realLMul (realLOf (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u}))) (realLOf ratZero.{u}))
        (realLOf (ratNeg ratOne.{u})))) = realLOf (ratNeg ratOne.{u})
  rw [hzero _ (ratNeg_mem_Rat h2Q), hzero _ (ratNeg_mem_Rat ratOne_mem_Rat)]
  have hloOf : realLLe (realLOf (ratNeg ratOne.{u})) L := by
    have hstep := hlo
    rwa [show realLNeg realLOne.{u} = realLOf (ratNeg ratOne.{u}) from
      realLOf_neg ratOne_mem_Rat] at hstep
  have hminEq : realLMin L (realLOf (ratNeg ratOne.{u}))
      = realLOf (ratNeg ratOne.{u}) :=
    realLLe_antisymm (realLMin_mem hL hn1R) hn1R
      (realLMin_le_right hn1R) (le_realLMin hloOf (realLLe_refl hn1R))
  rw [hminEq]
  have hn21 : realLLe (realLOf (ratNeg (ratAdd ratOne.{u} ratOne.{u})))
      (realLOf (ratNeg ratOne.{u})) := by
    refine (realLOf_le_realLOf (ratNeg_mem_Rat h2Q)
      (ratNeg_mem_Rat ratOne_mem_Rat)).mpr ?_
    have h12 : ratLt ratOne.{u} (ratAdd ratOne.{u} ratOne.{u}) := by
      have hstep := (ratAdd_lt_add_left_iff ratOne_mem_Rat ratZero_mem_Rat
        ratOne_mem_Rat).mpr ratZero_lt_one
      rwa [ratAdd_zero ratOne_mem_Rat] at hstep
    exact ((ratNeg_lt_neg_iff h2Q ratOne_mem_Rat).mpr h12).left
  exact realLLe_antisymm (realLMax_mem hn2R hn1R) hn1R
    (realLMax_le hn21 (realLLe_refl hn1R)) (realLLe_max_right hn1R)

/-- `mvGadget L 1 = 1` when `L ≤ 1`. -/
theorem mvGadget_at_one {L : ZFSet.{u}} (hL : L ∈ RealL.{u})
    (hhi : realLLe L realLOne.{u}) :
    mvGadget L (realLOf ratOne.{u}) = realLOf ratOne.{u} := by
  have h3Q := ratAdd_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
  have h2Q := ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat
  have h1R := realLOf_mem ratOne_mem_Rat
  have h2R := realLOf_mem h2Q
  have hA1 : realLAdd (realLMul (realLOf (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u}))) (realLOf ratOne.{u}))
      (realLOf (ratNeg (ratAdd ratOne.{u} ratOne.{u})))
      = realLOf ratOne.{u} := by
    rw [← realLOf_mul h3Q ratOne_mem_Rat, ratMul_one h3Q,
      ← realLOf_add h3Q (ratNeg_mem_Rat h2Q), ratThree_add_neg_two]
  have hB2 : realLAdd (realLMul (realLOf (ratAdd ratOne.{u}
      (ratAdd ratOne.{u} ratOne.{u}))) (realLOf ratOne.{u}))
      (realLOf (ratNeg ratOne.{u}))
      = realLOf (ratAdd ratOne.{u} ratOne.{u}) := by
    rw [← realLOf_mul h3Q ratOne_mem_Rat, ratMul_one h3Q,
      ← realLOf_add h3Q (ratNeg_mem_Rat ratOne_mem_Rat)]
    have h31 := ratThree_add_neg_one.{u}
    rw [h31]
  show realLMax
      (realLAdd (realLMul (realLOf (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u}))) (realLOf ratOne.{u}))
        (realLOf (ratNeg (ratAdd ratOne.{u} ratOne.{u}))))
      (realLMin L (realLAdd (realLMul (realLOf (ratAdd ratOne.{u}
        (ratAdd ratOne.{u} ratOne.{u}))) (realLOf ratOne.{u}))
        (realLOf (ratNeg ratOne.{u})))) = realLOf ratOne.{u}
  rw [hA1, hB2]
  refine realLLe_antisymm (realLMax_mem h1R (realLMin_mem hL h2R)) h1R
    (realLMax_le (realLLe_refl h1R) ?_) (realLLe_max_left h1R)
  exact realLLe_trans (realLMin_mem hL h2R) hL h1R
    (realLMin_le_left hL) hhi

#print axioms Analysis.mvGadget_mem
#print axioms Analysis.mvGadget_uc
#print axioms Analysis.ratInv_three_triple
#print axioms Analysis.realL_three_thirds
#print axioms Analysis.ratZero_lt_nine
#print axioms Analysis.ratNine_ne_zero
#print axioms Analysis.ratInv_nine_mem_Rat
#print axioms Analysis.ratInv_three_mem_Rat
#print axioms Analysis.ratThree_mul_inv_nine
#print axioms Analysis.ratThree_mul_four_ninths
#print axioms Analysis.ratThree_mul_five_ninths
#print axioms Analysis.mvGadget_exclusion_pos
#print axioms Analysis.mvGadget_exclusion_neg
#print axioms Analysis.mvGadget_at_zero
#print axioms Analysis.mvGadget_at_one
#print axioms Analysis.realLLe_zero_of_forall_invWidth
#print axioms Analysis.zero_le_of_forall_neg_invWidth
#print axioms ratFour_mem
#print axioms ratFive_mem
#print axioms ratNine_mem
end Analysis
namespace ZFSet
export Analysis (IsCauchyReal TendsToL mvGadget mvGadget_at_one mvGadget_at_zero mvGadget_exclusion_neg mvGadget_exclusion_pos mvGadget_mem mvGadget_uc ratFive ratFive_mem ratFour ratFour_mem ratInv_nine_mem_Rat ratInv_three_mem_Rat ratInv_three_triple ratNine ratNine_mem ratNine_ne_zero ratThree_mul_five_ninths ratThree_mul_four_ninths ratThree_mul_inv_nine ratZero_lt_nine realLLe_zero_of_forall_invWidth realL_three_thirds zero_le_of_forall_neg_invWidth)
end ZFSet
