/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
THE DETERMINANT BRIDGE WITHOUT AN ENCODING --- `detT` against `Matrix.det`, over
the same Lean type.

`DetTransfer.detN_encMat` reaches `Matrix.det` from the tower's `detN` by
putting `α` into a `ZFSet` first, and that step --- `TypeTransfer.encode_injective`
--- costs `Classical.choice`. The tower does not: `detN_mul` and `detT_mul` are
both `[propext, Quot.sound]`. So the published pair's axiom line has carried a
cost that is the BRIDGE's rather than the mathematics', which is what
`Comparator/Audit.lean`'s `surcharge` reports.

`Algebra.detT` is the re-sited Laplace determinant: the same recursion with the
entry type a PARAMETER and the ring operations as function arguments. This file
matches it against `Matrix.det` directly, and the proof is `detN_encMat`'s with
the encode/decode removed --- lemma for lemma:

    detN_encMat                     here
    ---------------------------     ------------------------
    matMinor_encMat                 matMinorT_submatrix
    ringSign_encode                 sign_eq_neg_one_pow
    SumFold.foldF_eq_encode_sum     sumUptoT_eq_sum_range
    detN_congr_lt                   detT_congr_lt   (cited unchanged)

WHAT THIS DOES NOT DO. It does not make a Solution choice-free.
`Matrix.det_fin_zero` --- the statement that the empty determinant is `1` ---
itself prints `Classical.choice`, as do `Matrix.det_succ_row_zero`,
`Fin.sum_univ_eq_sum_range` and `Finset.sum_range_succ`. Any theorem stated
ABOUT `Matrix.det` carries it, whatever the tower under it costs. What this
file removes is the SURCHARGE: the choice a pair pays over and above what
mathlib's own statement of the same theorem already costs.
-/
import Comparator.Bridge.MatrixTransfer
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Algebra

namespace Comparator.DetSited

variable {α : Type} [CommRing α]

/-- The tower's bounded sum is mathlib's range sum. -/
theorem sumUptoT_eq_sum_range (f : Nat → α) :
    ∀ n : Nat, sumUptoT (· + ·) (0 : α) f n = ∑ j ∈ Finset.range n, f j
  | 0 => by rw [Finset.range_zero, Finset.sum_empty]; rfl
  | n + 1 => by
    rw [sumUptoT_succ, Finset.sum_range_succ, sumUptoT_eq_sum_range f n]

/-- The tower's parity sign is `(-1) ^ j`. Permutation parity is never
transported: both sides are read off `j % 2`. -/
theorem sign_eq_neg_one_pow (j : Nat) (t : α) :
    (if j % 2 = 0 then t else -t) = (-1) ^ j * t := by
  rcases Nat.eq_zero_or_pos (j % 2) with h | h
  · rw [if_pos h, Even.neg_one_pow ⟨j / 2, by omega⟩, _root_.one_mul]
  · rw [if_neg (by omega), Odd.neg_one_pow ⟨j / 2, by omega⟩, neg_one_mul]

omit [CommRing α] in
/-- The tower's minor is mathlib's submatrix ON THE SQUARE.

`Fin.succAbove j k` IS `if k < j then k else k + 1`, which is `matMinorT`'s
reindexing, so the recursions line up with no bookkeeping step. They differ OFF
the square, so the caller needs `detT_congr_lt` and not an equation of entry
functions.

THE RING IS NOT USED HERE AND THE LINTER SAID SO. This lemma is index
arithmetic: it moves between `matMinorT`'s `if k < j then k else k + 1` and
`Fin.succAbove`, and touches no operation on `α`. That is also why it is the one
declaration in this file printing `[propext, Quot.sound]` --- everything else
touches Mathlib's `Finset.sum` or parity API, which carries `Classical.choice`.

The `omit` goes ABOVE the docstring, not between it and the `theorem`: a
docstring must attach directly to the declaration, so `omit … in` there is
`unexpected token 'omit'`. Same placement rule as `set_option … in`. -/
theorem matMinorT_submatrix {m : Nat} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) α)
    (E : Nat → Nat → α)
    (hE : ∀ i j, ∀ hi : i < m + 1, ∀ hj : j < m + 1, E i j = M ⟨i, hi⟩ ⟨j, hj⟩)
    (j : Fin (m + 1)) (i k : Nat) (hi : i < m) (hk : k < m) :
    matMinorT E j.val i k
      = (M.submatrix Fin.succ j.succAbove) ⟨i, hi⟩ ⟨k, hk⟩ := by
  have hidx : (if k < j.val then k else k + 1) = (j.succAbove ⟨k, hk⟩).val := by
    rw [Fin.succAbove]
    by_cases h : (⟨k, hk⟩ : Fin m).castSucc < j
    · rw [if_pos h, if_pos (show k < j.val from h)]; rfl
    · rw [if_neg h, if_neg (show ¬ k < j.val from h)]; rfl
  show E (i + 1) (if k < j.val then k else k + 1) = _
  rw [hidx, hE (i + 1) (j.succAbove ⟨k, hk⟩).val (by omega)
    (j.succAbove ⟨k, hk⟩).isLt]
  rfl

/-- THE TWO DETERMINANTS AGREE, WITH NO ENCODING.

`E` agrees with `M` on the square and is arbitrary off it, which is the shape a
caller has: `detT` reads a `Nat`-indexed function and `Matrix.det` a
`Fin`-indexed one. -/
theorem detT_eq_det : ∀ (m : Nat) (M : Matrix (Fin m) (Fin m) α)
    (E : Nat → Nat → α),
    (∀ i j, ∀ hi : i < m, ∀ hj : j < m, E i j = M ⟨i, hi⟩ ⟨j, hj⟩) →
    detT (· + ·) (· * ·) (fun x => -x) (0 : α) 1 E m = M.det
  | 0, M, E, _ => by rw [Matrix.det_fin_zero]; rfl
  | n + 1, M, E, hE => by
    set g : Nat → α := fun j =>
      if h : j < n + 1 then
        (-1) ^ j * M 0 ⟨j, h⟩ * (M.submatrix Fin.succ (Fin.succAbove ⟨j, h⟩)).det
      else 0 with hg
    have hdet : M.det = ∑ j ∈ Finset.range (n + 1), g j := by
      rw [Matrix.det_succ_row_zero, ← Fin.sum_univ_eq_sum_range g (n + 1)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hg]
      simp only [dif_pos j.isLt, Fin.eta]
    rw [detT_succ, hdet, ← sumUptoT_eq_sum_range g (n + 1)]
    refine sumUptoT_congr_lt (· + ·) (0 : α) _ _ (n + 1) (fun j hj => ?_)
    show (if j % 2 = 0 then _ else -_) = g j
    rw [sign_eq_neg_one_pow, hg]
    simp only [dif_pos hj]
    -- THE TARGET FUNCTION HAS TO BE NAMED. `detT_congr_lt`'s second matrix is
    -- implicit, and a `Fin`-indexed right-hand side leaves it a metavariable the
    -- unifier cannot solve -- the error reads as a mismatch on the minor and is
    -- a missing `F`.
    set F : Nat → Nat → α := fun i k =>
      if hi : i < n then
        if hk : k < n then
          (M.submatrix Fin.succ (Fin.succAbove ⟨j, hj⟩)) ⟨i, hi⟩ ⟨k, hk⟩
        else 0
      else 0 with hF
    rw [hE 0 j (Nat.succ_pos n) hj,
      detT_congr_lt (· + ·) (· * ·) (fun x => -x) (0 : α) 1 (F := F) n
        (fun i k hi hk => by
          rw [matMinorT_submatrix M E hE ⟨j, hj⟩ i k hi hk, hF]
          simp only [dif_pos hi, dif_pos hk]),
      detT_eq_det n (M.submatrix Fin.succ (Fin.succAbove ⟨j, hj⟩)) F
        (fun i k hi hk => by rw [hF]; simp only [dif_pos hi, dif_pos hk]),
      _root_.mul_assoc]
    congr 2

/-- The tower's matrix product is mathlib's, ON THE SQUARE.

`matMulOnT` is a bounded fold over the shared index; `Matrix.mul_apply` is a
`Fin` sum. Same summand, and `Fin.sum_univ_eq_sum_range` moves between the two
index types. -/
theorem matMulOnT_mul {m : Nat} (M N : Matrix (Fin m) (Fin m) α)
    (A B : Nat → Nat → α)
    (hA : ∀ i j, ∀ hi : i < m, ∀ hj : j < m, A i j = M ⟨i, hi⟩ ⟨j, hj⟩)
    (hB : ∀ i j, ∀ hi : i < m, ∀ hj : j < m, B i j = N ⟨i, hi⟩ ⟨j, hj⟩)
    (i k : Nat) (hi : i < m) (hk : k < m) :
    matMulOnT (· + ·) (· * ·) (0 : α) A B m i k = (M * N) ⟨i, hi⟩ ⟨k, hk⟩ := by
  set g : Nat → α := fun j =>
    if h : j < m then M ⟨i, hi⟩ ⟨j, h⟩ * N ⟨j, h⟩ ⟨k, hk⟩ else 0 with hg
  -- THE `Fin` SUM HAS TO BE MOVED IN ITS OWN `have`, not inside the goal's
  -- rewrite chain: `Matrix.mul_apply` leaves `∑ j : Fin m, …` on the RIGHT, and
  -- `← Fin.sum_univ_eq_sum_range` looks for a RANGE sum, so the pattern is
  -- reported missing against a goal that visibly contains the sum. Same shape
  -- as `hdet` below.
  have hsum : (M * N) ⟨i, hi⟩ ⟨k, hk⟩ = ∑ j ∈ Finset.range m, g j := by
    rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range g m]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hg]
    simp only [dif_pos j.isLt, Fin.eta]
  show sumUptoT (· + ·) (0 : α) (fun j => A i j * B j k) m = _
  rw [hsum, ← sumUptoT_eq_sum_range g m]
  refine sumUptoT_congr_lt (· + ·) (0 : α) _ _ m (fun j hj => ?_)
  rw [hA i j hi hj, hB j k hj hk, hg]
  simp only [dif_pos hj]

#print axioms sumUptoT_eq_sum_range
#print axioms sign_eq_neg_one_pow
#print axioms matMinorT_submatrix
#print axioms matMulOnT_mul
#print axioms detT_eq_det

end Comparator.DetSited
