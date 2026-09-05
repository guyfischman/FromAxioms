/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
A MATHLIB MATRIX, AS THE TOWER'S ENTRY FUNCTION OVER THE ENCODED CARRIER.

The bottom rung for the 1858 row, Cayley-Hamilton. The two libraries hold a
matrix differently and the difference is smaller than it looks:

    mathlib   Matrix (Fin m) (Fin m) α, a bundled function on Fin
    tower     A : Nat → Nat → ZFSet, an ENTRY FUNCTION, with the size carried
              separately as the `n` every theorem takes

`cayleyHamilton_matSet` (`CharPoly.lean:7565`) is stated for exactly such an
entry function with `∀ i j, A i j ∈ R`, so the transport is `encode` at each
entry and a junk value off the square. The junk is never read: every theorem
above quantifies indices below `n`.

WHAT THE ROW WILL NEED ABOVE THIS, measured rather than guessed:

  * `detN` (`PolyRing.lean:10307`) is LAPLACE ALONG ROW 0 with a `Nat`-parity
    sign; `Matrix.det` is the signed sum over permutations. Those are not the
    same definition --- but mathlib proves `Matrix.det_succ_row_zero`, which IS
    Laplace along row 0, so the two meet by induction on the size rather than by
    reconstructing permutation parity. That is the real content of this row.
  * `charMat` is `X·I - A` over `R[X]` and mathlib's `charmatrix` is the same
    object, so once `detN` and `det` agree the characteristic polynomials do.
  * `PolyTransfer` and `RingTransfer` already carry `R[X]` and `R`.

So the row is a determinant identity plus four transports, and the determinant
identity is a theorem rather than a change of carrier. This file is the first
transport.
-/
import Comparator.Bridge.RingTransfer
import Mathlib.Data.Matrix.Basic

open SetTheory NumberTheory Algebra Comparator.TypeTransfer Comparator.RingTransfer
open scoped Classical

namespace Comparator.MatrixTransfer

variable {α : Type} [CommRing α] {m : Nat}

/-- A mathlib matrix as an entry function.

NAMED `encMat` AND NOT `matOf`: the tower already has `Algebra.matOf`
(`LinAlg.lean:1183`), and this file opens `Algebra`, so the obvious name
resolves to that one and `rw` reports the tower's constant where the reader
expects this definition. The clash is silent at the definition site and only
surfaces at the first rewrite.

Off the square the value is
`encode 0`, which no theorem above reads: every index is quantified below the
size. -/
noncomputable def encMat (M : Matrix (Fin m) (Fin m) α) : Nat → Nat → ZFSet.{0} :=
  fun i j =>
    if h : i < m ∧ j < m then encode (M ⟨i, h.1⟩ ⟨j, h.2⟩) else encode (0 : α)

/-- THE COMPUTATION RULE, on the square. -/
theorem encMat_apply (M : Matrix (Fin m) (Fin m) α) (i j : Fin m) :
    encMat M i.val j.val = encode (M i j) := by
  rw [encMat, dif_pos ⟨i.isLt, j.isLt⟩]

/-- The same rule with `Nat` indices, which is the form every caller wants:
the tower indexes matrices by `Nat` throughout, so a `Fin`-stated rule never
matches syntactically --- `encMat M ↑0 ↑⟨j, hj⟩` and `encMat M 0 j` are the same
term and `rw` sees two. -/
theorem encMat_apply_lt (M : Matrix (Fin m) (Fin m) α) {i j : Nat}
    (hi : i < m) (hj : j < m) :
    encMat M i j = encode (M ⟨i, hi⟩ ⟨j, hj⟩) := by
  rw [encMat, dif_pos ⟨hi, hj⟩]

/-- Every entry lands in the encoded carrier, junk included --- which is the
hypothesis `cayleyHamilton_matSet` takes, and it holds unconditionally rather
than only on the square. -/
theorem encMat_mem (M : Matrix (Fin m) (Fin m) α) :
    ∀ i j : Nat, encMat M i j ∈ encodeSet α := by
  intro i j
  rw [encMat]
  split
  · exact encode_mem _
  · exact encode_mem _

/-- The transport is injective on the square, so a conclusion about the
transported matrix is a conclusion about the original. -/
theorem encMat_injective {M N : Matrix (Fin m) (Fin m) α}
    (h : ∀ i j : Fin m, encMat M i.val j.val = encMat N i.val j.val) : M = N := by
  ext i j
  have := h i j
  rw [encMat_apply, encMat_apply] at this
  exact encode_injective this

#print axioms encMat_apply
#print axioms encMat_mem
#print axioms encMat_injective

end Comparator.MatrixTransfer
