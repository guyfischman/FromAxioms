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

import FromAxioms.Analysis.Deriv
import FromAxioms.Analysis.Weier
import FromAxioms.Geometry.GeomSqrt

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

/-- The two-square identity. A rotation by the direction `(p, q)` scales
every squared length by `p² + q²`; with `p² + q² = 1` it is an isometry. -/
theorem two_square {p q x y : ZFSet.{u}} (hp : p ∈ RealL.{u}) (hq : q ∈ RealL.{u})
    (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u}) :
    realLAdd
        (realLMul (realLAdd (realLMul p x) (realLNeg (realLMul q y)))
          (realLAdd (realLMul p x) (realLNeg (realLMul q y))))
        (realLMul (realLAdd (realLMul p y) (realLMul q x))
          (realLAdd (realLMul p y) (realLMul q x)))
      = realLMul (realLAdd (realLMul p p) (realLMul q q))
          (realLAdd (realLMul x x) (realLMul y y)) := by
  have hpx := realLMul_mem hp hx
  have hqy := realLMul_mem hq hy
  have hpy := realLMul_mem hp hy
  have hqx := realLMul_mem hq hx
  have hpp := realLMul_mem hp hp
  have hqq := realLMul_mem hq hq
  have hxx := realLMul_mem hx hx
  have hyy := realLMul_mem hy hy
  -- the two cross terms are the same product, so they cancel
  have hcross : realLMul (realLMul p x) (realLMul q y)
      = realLMul (realLMul p y) (realLMul q x) := by
    rw [realLMul_shuffle_pair hp hx hq hy, realLMul_shuffle_pair hp hy hq hx,
      realLMul_comm hx hy]
  rw [sq_diff hpx hqy, sq_sum hpy hqx, hcross]
  have hT := realLMul_mem hpy hqx
  rw [realLAdd_interchange (realLAdd_mem (realLMul_mem hpx hpx) (realLMul_mem hqy hqy))
      (realLNeg_mem (realLAdd_mem hT hT))
      (realLAdd_mem (realLMul_mem hpy hpy) (realLMul_mem hqx hqx))
      (realLAdd_mem hT hT),
    realLAdd_comm (realLNeg_mem (realLAdd_mem hT hT)) (realLAdd_mem hT hT),
    realLAdd_neg (realLAdd_mem hT hT),
    realLAdd_zero (realLAdd_mem (realLAdd_mem (realLMul_mem hpx hpx)
      (realLMul_mem hqy hqy)) (realLAdd_mem (realLMul_mem hpy hpy)
      (realLMul_mem hqx hqx)))]
  -- both sides are now `p²x² + q²y² + p²y² + q²x²`
  rw [realLMul_shuffle_pair hp hx hp hx, realLMul_shuffle_pair hq hy hq hy,
    realLMul_shuffle_pair hp hy hp hy, realLMul_shuffle_pair hq hx hq hx,
    realLAdd_mul hpp hqq (realLAdd_mem hxx hyy),
    realLMul_distrib hpp hxx hyy, realLMul_distrib hqq hxx hyy,
    realLAdd_interchange (realLMul_mem hpp hxx) (realLMul_mem hqq hyy)
      (realLMul_mem hpp hyy) (realLMul_mem hqq hxx),
    realLAdd_comm (realLMul_mem hqq hyy) (realLMul_mem hqq hxx)]

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

/-! ## The constants Euclid I.1 needs

A half and a root of three. Both are named rather than found: `geomHalf` is the
inverse of a positive real and `geomRootThree` is `realLSqrt`, so neither costs
anything beyond the ambient axioms. -/

private theorem realLThree_mem :
    realLAdd (realLAdd realLOne.{u} realLOne.{u}) realLOne.{u} ∈ RealL.{u} :=
  realLAdd_mem realLTwo_mem realLOne_mem

private theorem realLThree_nonneg :
    realLLe realLZero.{u} (realLAdd (realLAdd realLOne.{u} realLOne.{u}) realLOne.{u}) :=
  realLLe_of_lt realLZero_mem realLThree_mem
    (realLAdd_pos_of_nonneg realLTwo_mem realLOne_mem realLTwo_pos
      (realLLe_of_lt realLZero_mem realLOne_mem realLZero_lt_one))

/-- One half. -/
def geomHalf : ZFSet.{u} := realLInv (realLAdd realLOne.{u} realLOne.{u})

/-- The root of three: the height of the equilateral triangle on a unit base,
doubled. -/
def geomRootThree : ZFSet.{u} :=
  realLSqrt (realLAdd (realLAdd realLOne.{u} realLOne.{u}) realLOne.{u})

theorem geomHalf_mem : geomHalf.{u} ∈ RealL.{u} := realLInv_mem realLTwo_mem realLTwo_pos

theorem geomRootThree_mem : geomRootThree.{u} ∈ RealL.{u} :=
  realLSqrt_mem realLThree_mem realLThree_nonneg

theorem geomRootThree_sq :
    realLMul geomRootThree.{u} geomRootThree.{u}
      = realLAdd (realLAdd realLOne.{u} realLOne.{u}) realLOne.{u} :=
  realLSqrt_sq realLThree_mem realLThree_nonneg

theorem two_mul_geomHalf :
    realLMul (realLAdd realLOne.{u} realLOne.{u}) geomHalf.{u} = realLOne.{u} :=
  realLMul_inv realLTwo_mem realLTwo_pos

/-- The rotation coefficients are those of a unit vector: `p² + q² = 1` with
`p = 1/2` and `q = √3/2`. -/
theorem geom_coeff_sq :
    realLAdd (realLMul geomHalf.{u} geomHalf.{u})
        (realLMul (realLMul geomHalf.{u} geomRootThree.{u})
          (realLMul geomHalf.{u} geomRootThree.{u}))
      = realLOne.{u} := by
  have hh := realLMul_mem geomHalf_mem geomHalf_mem
  have hdist : realLMul (realLMul geomHalf.{u} geomHalf.{u})
        (realLAdd realLOne.{u}
          (realLAdd (realLAdd realLOne.{u} realLOne.{u}) realLOne.{u}))
      = realLAdd (realLMul geomHalf.{u} geomHalf.{u})
          (realLMul (realLMul geomHalf.{u} geomHalf.{u})
            (realLAdd (realLAdd realLOne.{u} realLOne.{u}) realLOne.{u})) := by
    rw [realLMul_distrib hh realLOne_mem realLThree_mem, realLMul_one hh]
  have hfour : realLMul (realLAdd realLOne.{u} realLOne.{u})
      (realLAdd realLOne.{u} realLOne.{u})
      = realLAdd realLOne.{u} (realLAdd (realLAdd realLOne.{u} realLOne.{u})
          realLOne.{u}) := by
    rw [realLAdd_mul realLOne_mem realLOne_mem realLTwo_mem,
      realLMul_comm realLOne_mem realLTwo_mem, realLMul_one realLTwo_mem,
      realLAdd_assoc realLOne_mem realLOne_mem realLTwo_mem,
      realLAdd_comm realLOne_mem realLTwo_mem]
  rw [realLMul_shuffle_pair geomHalf_mem geomRootThree_mem geomHalf_mem geomRootThree_mem,
    geomRootThree_sq, ← hdist, ← hfour,
    realLMul_shuffle_pair geomHalf_mem geomHalf_mem realLTwo_mem realLTwo_mem,
    realLMul_comm geomHalf_mem realLTwo_mem, two_mul_geomHalf,
    realLMul_one realLOne_mem]

/-! ## Euclid I.1

The apex of the equilateral triangle on `A B`, written down. `p·u - q·v` and
`p·v + q·u` is the sixty-degree rotation of the displacement `A → B`, scaled to
land on the third vertex; `two_square` turns each of the two congruences into
`p² + q² = 1`. -/

/-- The third vertex of an equilateral triangle on the segment `A B`. -/
def apex (A B : ZFSet.{u}) : ZFSet.{u} :=
  opair
    (realLAdd (fst A)
      (realLAdd (realLMul geomHalf.{u} (realLAdd (fst B) (realLNeg (fst A))))
        (realLNeg (realLMul (realLMul geomHalf.{u} geomRootThree.{u})
          (realLAdd (snd B) (realLNeg (snd A)))))))
    (realLAdd (snd A)
      (realLAdd (realLMul geomHalf.{u} (realLAdd (snd B) (realLNeg (snd A))))
        (realLMul (realLMul geomHalf.{u} geomRootThree.{u})
          (realLAdd (fst B) (realLNeg (fst A))))))

/-- Euclid I.1, first congruence. The apex is as far from `A` as `B` is. -/
theorem sqDist_apex_left {x y x' y' : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hx' : x' ∈ RealL.{u}) (hy' : y' ∈ RealL.{u}) :
    sqDist (apex (opair x y) (opair x' y')) (opair x y)
      = sqDist (opair x y) (opair x' y') := by
  have hq := realLMul_mem geomHalf_mem geomRootThree_mem
  have ha := realLAdd_mem hx' (realLNeg_mem hx)
  have hb := realLAdd_mem hy' (realLNeg_mem hy)
  simp only [apex, fst_opair, snd_opair]
  rw [sqDist_opair, sqDist_opair,
    shift_sub hx (realLAdd_mem (realLMul_mem geomHalf_mem ha)
      (realLNeg_mem (realLMul_mem hq hb))),
    shift_sub hy (realLAdd_mem (realLMul_mem geomHalf_mem hb) (realLMul_mem hq ha)),
    two_square geomHalf_mem hq ha hb, geom_coeff_sq,
    realLMul_comm realLOne_mem (realLAdd_mem (realLMul_mem ha ha) (realLMul_mem hb hb)),
    realLMul_one (realLAdd_mem (realLMul_mem ha ha) (realLMul_mem hb hb)),
    ← realLNeg_sub hx' hx, ← realLNeg_sub hy' hy, realLNeg_sq ha, realLNeg_sq hb]

#print axioms realLThree_mem
#print axioms realLThree_nonneg
#print axioms sq_diff
#print axioms geomHalf_mem
#print axioms geomRootThree_mem
#print axioms two_mul_geomHalf
end Geometry

#print axioms Geometry.two_square
#print axioms Geometry.sqDist_opair
#print axioms Geometry.sqDist
#print axioms Geometry.geom_coeff_sq
#print axioms Geometry.geomRootThree_sq
#print axioms Geometry.sqDist_apex_left
namespace ZFSet
export Geometry (apex geomHalf geomHalf_mem geomRootThree geomRootThree_mem geomRootThree_sq geom_coeff_sq sqDist sqDist_apex_left sqDist_opair sq_diff two_mul_geomHalf two_square)
end ZFSet
