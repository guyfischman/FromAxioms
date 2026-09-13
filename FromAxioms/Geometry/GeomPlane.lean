/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The coordinate plane over the located reals.

A point is an ordered pair of located reals and the squared distance between
two points is the sum of the squared coordinate differences. Squared, because
the distance itself is a square root and every statement Euclid makes about
distances -- equal, congruent, on a circle -- is an equation between squares.
Keeping it squared means the equilateral triangle below needs no root of the
distance at all.

The one identity everything here rests on is `two_square`, the
Brahmagupta--Fibonacci identity `(px - qy)² + (py + qx)² = (p² + q²)(x² + y²)`.
It is multiplicativity of the complex modulus written without complex numbers,
and it turns a rotation into an algebraic manipulation.

`sqDist_apex_left` and `sqDist_apex_right` are Euclid I.1. Euclid builds the
apex by intersecting two circles, which is a continuity principle and does not
follow from the ordered-field axioms; here the apex is named, by a formula in
the coordinates of the two given points and `√3`. No principle is used, and the
statement needs no hypothesis: for coincident points the triangle degenerates to
a point and the three squared distances are still equal.

`sqDist_meet_left` and `sqDist_meet_right` are the general circle-circle
intersection, which is free for the same reason and needs two hypotheses that
Euclid I.1 does not: the centres apart, because the construction divides by
twice their squared distance, and the overlap condition, which makes the one
root real.
-/

import FromAxioms.Analysis.IVT
import FromAxioms.Geometry.GeomSqrt
import FromAxioms.SetTheory.LeastSearch

universe u

open Analysis SetTheory
namespace Geometry

/-! ## Ring rearrangements

Two expansions, which with `realLMul_shuffle_pair` reduce a squared sum of
products to a canonical shape. -/


theorem sq_diff {u v : ZFSet.{u}} (hu : u ∈ RealL.{u}) (hv : v ∈ RealL.{u}) :
    realLMul (realLAdd u (realLNeg v)) (realLAdd u (realLNeg v))
      = realLAdd (realLAdd (realLMul u u) (realLMul v v))
          (realLNeg (realLAdd (realLMul u v) (realLMul u v))) := by
  have hnv := realLNeg_mem hv
  have huv := realLMul_mem hu hv
  rw [sq_sum hu hnv, realLMul_neg_neg hv hv, realLMul_neg hu hv,
    ← realLNeg_realLAdd huv huv]

/-! ## Points, and the squared distance -/

/-- The squared distance. The distance itself is `realLSqrt` of this; every
statement below is an equation between squares, so the root is never taken. -/
def sqDist (P Q : ZFSet.{u}) : ZFSet.{u} :=
  realLAdd
    (realLMul (realLAdd (fst P) (realLNeg (fst Q)))
      (realLAdd (fst P) (realLNeg (fst Q))))
    (realLMul (realLAdd (snd P) (realLNeg (snd Q)))
      (realLAdd (snd P) (realLNeg (snd Q))))

theorem sqDist_opair (x y x' y' : ZFSet.{u}) :
    sqDist (opair x y) (opair x' y')
      = realLAdd (realLMul (realLAdd x (realLNeg x')) (realLAdd x (realLNeg x')))
          (realLMul (realLAdd y (realLNeg y')) (realLAdd y (realLNeg y'))) := by
  rw [sqDist, fst_opair, fst_opair, snd_opair, snd_opair]

#print axioms sq_diff
end Geometry

#print axioms Geometry.sqDist_opair
#print axioms Geometry.sqDist
namespace ZFSet
export Geometry (sqDist sqDist_opair sq_diff)
end ZFSet
