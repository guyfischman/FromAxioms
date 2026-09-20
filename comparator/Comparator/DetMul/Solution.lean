/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`, without citing mathlib's
proof of it, and without an encoding.

The mathematics is `Algebra.detT_mul` --- the determinant's multiplicativity
stated over an arbitrary Lean type, with the ring operations as function
arguments and the entries in `α` itself. Its proof goes through `expandSumT` and
`leibSumT_eq_detT`, the Leibniz sum re-sited; `detT` is the Laplace recursion,
and Laplace does not multiply term by term.

What changed, and why. The previous version of this file transported `α`
into a `ZFSet` with `TypeTransfer.encode_injective` and applied the `ZFSet`
theorem `detN_mul`. That worked and cost `Classical.choice`, which the tower
does not: `detN_mul` and `detT_mul` are both `[propext, Quot.sound]`. Six bridge
modules are gone with it --- `TypeTransfer`, `RingTransfer`, `MatrixTransfer`,
`MatMulTransfer`, `DetTransfer` and `SumFold` --- replaced by one,
`Bridge.DetSited`, which matches `detT` against `Matrix.det` over the same type.

The axiom line does not improve, and it cannot. Measured against the pinned
checkout by two tracks independently: `Matrix.det` itself is
`[propext, Quot.sound, Classical.choice]`, as are `Matrix.det_mul`,
`Matrix.det_succ_row_zero`, `Matrix.det_fin_zero` and `Finset.sum_range_succ`.
The choice is in the challenge's vocabulary, so no Solution about `Matrix.det`
can print `[propext, Quot.sound]` by any route. Anyone reading this file's
`#print axioms` for a claim about the tower's floor is reading the wrong number;
`Comparator/Audit.lean`'s `surcharge` is the right one, and with mathlib's own
cost in its baseline this pair reports no surcharge.

What the re-siting buys is therefore smaller than a clean line and still real:
six fewer modules between a reader and the proof, and a genuinely clean line for
any future pair whose mathlib-side vocabulary is choice-free, where the encoding
would otherwise have been the only thing spending it.

The one step that is not a rewrite is still `detT_congr_lt`. `matMulOnT_mul`
matches the tower's product with `(M * N)` only on the square --- off it both
are junk and need not agree --- and `detT` reads only entries below the size, so
the bounded congruence is what carries the swap.

The empty matrix is a separate case, as before and for the same reason:
`detT_mul` carries `0 < n` and mathlib's holds at every size. At `m = 0` both
determinants are `1` and the identity is `1 = 1 * 1`.
-/
import Comparator.DetMul.Challenge
import Comparator.Bridge.DetSited

open Algebra Comparator.DetSited

namespace Comparator.DetMul

variable {α : Type} [CommRing α]

/-- A `Fin`-indexed matrix read as the `Nat`-indexed function `detT` wants,
with junk off the square. -/
private def natMat {m : Nat} (M : Matrix (Fin m) (Fin m) α) : Nat → Nat → α :=
  fun i j => if hi : i < m then if hj : j < m then M ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0

private theorem natMat_apply {m : Nat} (M : Matrix (Fin m) (Fin m) α)
    (i j : Nat) (hi : i < m) (hj : j < m) : natMat M i j = M ⟨i, hi⟩ ⟨j, hj⟩ := by
  unfold natMat
  simp only [dif_pos hi, dif_pos hj]

/-- The challenge, from `FromAxioms`. -/
theorem solution : challenge := by
  intro R _ m M N
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Matrix.det_fin_zero, Matrix.det_fin_zero, Matrix.det_fin_zero,
      _root_.one_mul]
  -- all three determinants into the tower's spelling
  rw [← detT_eq_det m M (natMat M) (natMat_apply M),
    ← detT_eq_det m N (natMat N) (natMat_apply N),
    ← detT_eq_det m (M * N) (natMat (M * N)) (natMat_apply (M * N)),
    -- the product agrees with the tower's fold on the square only
    detT_congr_lt (· + ·) (· * ·) (fun x => -x) (0 : R) 1
      (F := matMulOnT (· + ·) (· * ·) (0 : R) (natMat M) (natMat N) m) m
      (fun i k hi hk => by
        rw [natMat_apply (M * N) i k hi hk,
          matMulOnT_mul M N (natMat M) (natMat N)
            (natMat_apply M) (natMat_apply N) i k hi hk])]
  -- and the tower's theorem, whose every hypothesis is a ring identity
  exact detT_mul (· + ·) (· * ·) (fun x => -x) (0 : R) 1
    (fun p q r => by ring) (fun p q => by ring) (fun q => by ring)
    (fun q => by ring) (fun q => by ring) (fun p => by ring) (fun p => by ring)
    (fun p q r => by ring) (fun p q r => by ring) (fun p => by ring)
    (fun p => by ring) (fun p q => by ring) (by ring) (fun q => by ring)
    (fun p q => by ring) (fun p q r => by ring) (fun p q => by ring)
    (natMat M) (natMat N) hm

#print axioms solution

end Comparator.DetMul
