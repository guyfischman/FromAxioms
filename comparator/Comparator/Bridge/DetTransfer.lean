/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
THE TWO DETERMINANTS AGREE, and that is the theorem here; the rest is a change
of carrier.

They are NOT the same definition:

    tower     `detN` (`PolyRing.lean:10307`) --- Laplace along row 0, with the
              sign as `Nat` PARITY: `if j % 2 = 0 then t else -t`
    mathlib   `Matrix.det` --- the signed sum over PERMUTATIONS, with the sign
              as `Equiv.Perm.sign`

Reconstructing permutation parity in a constructive setting would be a serious
piece of work. It is not needed: mathlib proves its OWN Laplace expansion,
`Matrix.det_succ_row_zero`, so the two meet by induction on the size and the
permutation sign never has to be transported.

THE MINORS ALREADY MATCH. The tower's `matMinor E j = fun i k => E (i+1) (if k < j
then k else k+1)` and mathlib's `A.submatrix Fin.succ j.succAbove` are the same
reindexing, because `Fin.succAbove j k` IS `if k < j then k else k+1`. So the
recursions line up term by term and the induction has no bookkeeping step.

TWO LEMMAS THIS TREE ALREADY HAD, and finding them is most of why this is short:
`detN_congr_lt` (`PolyRing.lean:13301`) says a determinant reads only the
entries inside its own square --- needed because `matMinor (encMat M) j` and
`encMat (M.submatrix ...)` agree on the square and differ on the junk outside
it --- and `SumFold.encode_sum_eq_foldF` turns mathlib's `Finset` sum into the
tower's fold.
-/
import Comparator.Bridge.MatrixTransfer
import Comparator.Bridge.SumFold
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open SetTheory NumberTheory Algebra Comparator.TypeTransfer Comparator.RingTransfer
open Comparator.MatrixTransfer Comparator.SumFold
open scoped Classical

namespace Comparator.DetTransfer

variable {α : Type} [CommRing α]

/-- The tower's minor of a transported matrix agrees, ON ITS OWN SQUARE, with
the transport of mathlib's submatrix. They differ off it, so `detN_congr_lt`
rather than an equation of entry functions. -/
theorem matMinor_encMat {m : Nat} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) α)
    (j : Fin (m + 1)) (i k : Nat) (hi : i < m) (hk : k < m) :
    matMinor (encMat M) j.val i k
      = encMat (M.submatrix Fin.succ j.succAbove) i k := by
  -- The two reindexings agree as NATURALS first; everything else is `encMat`'s
  -- computation rule at the corresponding `Fin`s.
  have hidx : (if k < j.val then k else k + 1) = (j.succAbove ⟨k, hk⟩).val := by
    rw [Fin.succAbove]
    by_cases h : (⟨k, hk⟩ : Fin m).castSucc < j
    · rw [if_pos h, if_pos (show k < j.val from h)]
      rfl
    · rw [if_neg h, if_neg (show ¬ k < j.val from h)]
      rfl
  show encMat M (i + 1) (if k < j.val then k else k + 1) = _
  rw [hidx,
    show i + 1 = ((⟨i, hi⟩ : Fin m).succ : Fin (m + 1)).val from rfl,
    encMat_apply M ((⟨i, hi⟩ : Fin m).succ) (j.succAbove ⟨k, hk⟩)]
  -- The remaining side is closed by `encMat`'s rule read BACKWARDS: rewriting
  -- `i` to `(⟨i, hi⟩ : Fin m).val` fails its motive, since `hi` mentions `i`.
  exact (encMat_apply (M.submatrix Fin.succ j.succAbove) ⟨i, hi⟩ ⟨k, hk⟩).symm

/-- The encoded negation is the encoding of the negation. `ringNeg` is THE
additive inverse, so uniqueness settles it: `encode a + encode (-a)` is
`encode 0` by `opAt_opSet`, and `ringNeg_eq_of_add_zero` reads off the rest. -/
theorem ringNeg_encode (a : α) :
    ringNeg (encodeSet α) (opSet (α := α) (· + ·)) (encode (0 : α)) (encode a)
      = encode (-a) :=
  ringNeg_eq_of_add_zero isRing_transported (encode_mem a) (encode_mem (-a))
    (by rw [opAt_opSet, add_neg_cancel])

/-- The sign the tower forms --- `Nat` parity --- against the sign mathlib
forms, `(-1) ^ j`. They agree, and neither side has to know about permutation
parity for that. -/
theorem ringSign_encode (j : Nat) (a : α) :
    ringSign (encodeSet α) (opSet (α := α) (· + ·)) (encode (0 : α)) j (encode a)
      = encode ((-1) ^ j * a) := by
  rw [ringSign]
  rcases Nat.eq_zero_or_pos (j % 2) with h | h
  · rw [if_pos h, Even.neg_one_pow ⟨j / 2, by omega⟩, _root_.one_mul]
  · rw [if_neg (by omega), ringNeg_encode,
      Odd.neg_one_pow ⟨j / 2, by omega⟩, neg_one_mul]

/-- THE TWO DETERMINANTS AGREE. Induction on the size: mathlib's
`det_succ_row_zero` is its own Laplace expansion along row 0, which is how
`detN` is defined, so the step is term-by-term. `detN_congr_lt` handles the junk
outside the square, `matMinor_encMat` matches the minors, and `SumFold` turns
mathlib's `Finset` sum into the tower's fold. -/
theorem detN_encMat : ∀ (m : Nat) (M : Matrix (Fin m) (Fin m) α),
    detN (encodeSet α) (opSet (α := α) (· + ·)) (opSet (α := α) (· * ·))
        (encode (0 : α)) (encode (1 : α)) (encMat M) m
      = encode M.det
  | 0, M => by rw [Matrix.det_fin_zero]; rfl
  | n + 1, M => by
    -- The summand as a `Nat`-indexed function, so `Fin.sum_univ_eq_sum_range`
    -- applies. The junk branch is never read: the sum is over `range (n+1)`.
    set g : Nat → α := fun j =>
      if h : j < n + 1 then
        (-1) ^ j * M 0 ⟨j, h⟩ * (M.submatrix Fin.succ (Fin.succAbove ⟨j, h⟩)).det
      else 0 with hg
    have hdet : M.det = ∑ j ∈ Finset.range (n + 1), g j := by
      rw [Matrix.det_succ_row_zero, ← Fin.sum_univ_eq_sum_range g (n + 1)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hg]
      simp only [dif_pos j.isLt, Fin.eta]
    rw [detN_succ, hdet, ← foldF_eq_encode_sum g (n + 1)]
    refine foldF_congr (n + 1) (fun j hj => ?_)
    rw [detTerm_eq, hg]
    simp only [dif_pos hj]
    -- Inner first, sign last: `ringSign_encode` only fires once its argument is
    -- literally an `encode`.
    rw [encMat_apply_lt M (Nat.succ_pos n) hj,
      detN_congr_lt n (fun i k hi hk => matMinor_encMat M ⟨j, hj⟩ i k hi hk),
      detN_encMat n (M.submatrix Fin.succ (Fin.succAbove ⟨j, hj⟩)),
      opAt_opSet, ringSign_encode, _root_.mul_assoc]
    -- `(0 : Fin (n+1))` against the `⟨0, _⟩` the Nat-indexed rule produced.
    congr 2

#print axioms matMinor_encMat
#print axioms ringNeg_encode
#print axioms ringSign_encode
#print axioms detN_encMat

end Comparator.DetTransfer
