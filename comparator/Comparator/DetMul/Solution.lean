/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`, without citing mathlib's
proof of it.

THE MATHEMATICS IS `Algebra.detN_mul` (`PolyRing.lean:16432`), over an
arbitrary `IsRing` with entries in the carrier and matrices of any positive
size. Its proof goes through `expandSum` and `leibSum_eq_detN` --- the Leibniz
sum --- so the tower has multiplicativity at all: `detN` itself is the Laplace
recursion, and Laplace does not multiply term by term.

THE CARRIER IS ALREADY BUILT. Every rung below is reused unchanged:

    TypeTransfer     `α` as a ZFSet carrier, with `encode` injective
    RingTransfer     the transported operations, and `isRing_transported`
    MatrixTransfer   a `Matrix (Fin m) (Fin m) α` as an entry function
    MatMulTransfer   `matMulOn_encMat` --- the transported product
    DetTransfer      `detN_encMat` --- `detN` = `Matrix.det`

So this Solution is an assembly and contains no new mathematics, which is
exactly what a comparator pair should cost once the transfer exists. THAT IS THE
MEASUREMENT THIS PAIR MAKES: the Cayley-Hamilton carrier was ten rungs, and the
second row over the same carrier is one theorem long.

THE ONE STEP THAT IS NOT A REWRITE is `detN_congr_lt`. `matMulOn_encMat` matches
the transported product with `encMat (M * N)` ONLY ON THE SQUARE --- off it,
both are junk and need not agree --- and `detN` reads only entries below the
size, so the bounded congruence is what carries the swap. The unbounded form
would not apply.

THE EMPTY MATRIX IS A SEPARATE CASE, as it is on the Cayley-Hamilton pair and
for the same reason: `detN_mul` carries `0 < n` and mathlib's holds at every
size. At `m = 0` both determinants are `1` by `Matrix.det_fin_zero` and the
identity is `1 = 1 * 1`. The tower is not being asked for something it lacks.

THE AXIOM PRINT NAMES `Classical.choice` AND IT IS THE ENCODING'S, NOT THE
MATHEMATICS'. Checked step by step rather than assumed
(`.agent/chains/probe-detmul-axiom-source.lean`):

    Algebra.detN_mul                  [propext, Quot.sound]
    Algebra.detN_congr_lt             [propext, Quot.sound]
    TypeTransfer.encode_injective     [propext, Classical.choice, Quot.sound]
    RingTransfer.isRing_transported   [propext, Classical.choice, Quot.sound]
    DetTransfer.detN_encMat           [propext, Classical.choice, Quot.sound]
    challenge_is_mathlibs             [propext, Classical.choice, Quot.sound]

Both tower theorems are at the floor; choice appears first at
`encode_injective` --- putting an arbitrary `Type` into a ZFSet --- and
propagates from there through every bridge. MATHLIB'S OWN PROOF of the same
statement carries it too, which is the comparison that settles what the
Solution's line can mean.

THE PRINT ALONE DOES NOT SAY WHERE THE CHOICE COMES FROM. Here the encoding is
its whole source.
-/
import Comparator.DetMul.Challenge
import Comparator.Bridge.DetTransfer
import Comparator.Bridge.MatMulTransfer

open SetTheory NumberTheory Algebra
open Comparator.TypeTransfer Comparator.RingTransfer Comparator.MatrixTransfer
open Comparator.MatMulTransfer Comparator.DetTransfer

namespace Comparator.DetMul

/-- The challenge, from `FromAxioms`. -/
theorem solution : challenge := by
  intro R _ m M N
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Matrix.det_fin_zero, Matrix.det_fin_zero, Matrix.det_fin_zero,
      _root_.one_mul]
  refine encode_injective ?_
  -- The product's determinant, transported.
  rw [← detN_encMat (α := R) m (M * N)]
  -- `matMulOn_encMat` agrees with `encMat (M * N)` on the square only, so the
  -- swap needs the BOUNDED congruence.
  rw [← detN_congr_lt (R := encodeSet R) (add := opSet (α := R) (· + ·))
      (mul := opSet (α := R) (· * ·)) (zero := encode (0 : R))
      (one := encode (1 : R)) m
      (fun i k hi hk => matMulOn_encMat M N hi hk)]
  -- The tower's theorem, then the two factors back through the same bridge.
  rw [detN_mul isRing_transported (encMat_mem M) (encMat_mem N) hm,
    detN_encMat (α := R) m M, detN_encMat (α := R) m N, opAt_opSet]

#print axioms solution

end Comparator.DetMul
