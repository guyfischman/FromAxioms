/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
MATRIX PRODUCTS AND POWERS, ACROSS THE TRANSPORT.

The last carrier rung under Cayley-Hamilton. `cayleyHamilton_matSet` states the
theorem as a fold over `k` of `A^k · charPoly_k`, so the powers have to cross.

    tower     matMulOn add mul zero A B n i k
                = foldF add zero (fun j => A i j · B j k) n
    mathlib   (M * N) i k = ∑ j, M i j * N j k        (`Matrix.mul_apply`)

The same shape as the determinant's convolution: mathlib sums over `Fin n`, the
tower folds over `0 .. n-1`, and `Fin.sum_univ_eq_sum_range` plus `SumFold`
carry one to the other. `matPow` then follows by induction on the exponent,
with `matPow … 0 = idMat` against `M ^ 0 = 1`.

THE SIZE IS FIXED THROUGHOUT, so `matPow` recurses on the exponent and takes
`n` as a parameter: `matMulOn` needs the size as its fold bound and cannot take
it from the recursion. The transported statement inherits that shape rather
than fighting it.
-/
import Comparator.Bridge.MatrixTransfer
import Comparator.Bridge.SumFold
import Mathlib.Data.Matrix.Mul

open SetTheory NumberTheory Algebra Comparator.TypeTransfer Comparator.RingTransfer
open Comparator.MatrixTransfer Comparator.SumFold
open scoped Classical

namespace Comparator.MatMulTransfer

variable {α : Type} [CommRing α] {m : Nat}

/-- The transported product is the product of the transports, on the
square. -/
theorem matMulOn_encMat (M N : Matrix (Fin m) (Fin m) α) {i k : Nat}
    (hi : i < m) (hk : k < m) :
    matMulOn (opSet (α := α) (· + ·)) (opSet (α := α) (· * ·)) (encode (0 : α))
        (encMat M) (encMat N) m i k
      = encMat (M * N) i k := by
  have hterm : (fun j => opAt (opSet (α := α) (· * ·))
        (encMat M i j) (encMat N j k))
      = fun j => encode (if h : j < m then M ⟨i, hi⟩ ⟨j, h⟩ * N ⟨j, h⟩ ⟨k, hk⟩
                         else 0 * 0) := by
    funext j
    by_cases h : j < m
    · rw [encMat_apply_lt M hi h, encMat_apply_lt N h hk, opAt_opSet, dif_pos h]
    · rw [encMat, encMat, dif_neg (fun hc => h hc.2), dif_neg (fun hc => h hc.1),
        opAt_opSet, dif_neg h]
  show foldF (opSet (α := α) (· + ·)) (encode (0 : α))
      (fun j => opAt (opSet (α := α) (· * ·)) (encMat M i j) (encMat N j k)) m = _
  rw [hterm, ← encode_sum_eq_foldF, encMat_apply_lt (M * N) hi hk,
    Matrix.mul_apply]
  refine congrArg encode ?_
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => if h : j < m then M ⟨i, hi⟩ ⟨j, h⟩ * N ⟨j, h⟩ ⟨k, hk⟩ else 0 * 0) m]
  exact Finset.sum_congr rfl (fun j _ => by rw [dif_pos j.isLt])

/-- And the powers, by induction on the exponent. -/
theorem matPow_encMat (M : Matrix (Fin m) (Fin m) α) :
    ∀ (k : Nat) {i j : Nat}, i < m → j < m →
      matPow (opSet (α := α) (· + ·)) (opSet (α := α) (· * ·)) (encode (0 : α))
          (encode (1 : α)) m (encMat M) k i j
        = encMat (M ^ k) i j
  | 0, i, j, hi, hj => by
    show idMat (encode (0 : α)) (encode (1 : α)) i j = _
    rw [idMat, encMat_apply_lt (M ^ 0) hi hj, pow_zero]
    by_cases h : i = j
    · -- The two `Fin`s must be one TERM before `one_apply_eq` applies.
      have hji : (⟨j, hj⟩ : Fin m) = ⟨i, hi⟩ := Fin.ext h.symm
      rw [if_pos h, hji, Matrix.one_apply_eq]
    · rw [if_neg h, Matrix.one_apply_ne (fun hc => h (congrArg Fin.val hc))]
  | k + 1, i, j, hi, hj => by
    -- The inductive hypothesis holds ON THE SQUARE only, so the two entry
    -- functions are not equal --- `matMulOn_congr_left` is what makes the
    -- square enough, exactly as `detN_congr_lt` did for the determinant.
    show matMulOn (opSet (α := α) (· + ·)) (opSet (α := α) (· * ·)) (encode (0 : α))
        (matPow _ _ _ _ m (encMat M) k) (encMat M) m i j = _
    rw [matMulOn_congr_left (A' := encMat (M ^ k)) hi
        (fun l hl => matPow_encMat M k hi hl),
      matMulOn_encMat (M ^ k) M hi hj, pow_succ]

#print axioms matMulOn_encMat
#print axioms matPow_encMat

end Comparator.MatMulTransfer
