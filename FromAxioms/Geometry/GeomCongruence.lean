/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Hilbert's congruence group.

Segments are congruent when their squared distances are equal, which makes
`SegCong` an equivalence relation for free and makes the additive axioms
statements about `sqDist` alone.

Angles are the hard case: a congruence of angles is naturally a ratio, and a
ratio needs the lengths themselves rather than their squares. The way through
is the one that makes the rest of the geometry free -- keep everything squared
-- and the identity that lets it work is polarisation:

    |u - v|² = |u|² + |v|² - 2·(u · v)

so that a congruence of angles between sides already known congruent is
exactly an equality of dot products, with no root and no ratio. That is enough
for SAS, which is the axiom the group exists to support.
-/

import FromAxioms.Analysis.Complex
import FromAxioms.Geometry.GeomPlane
import FromAxioms.SetTheory.Uncountable

universe u

open Analysis SetTheory
namespace Geometry

/-- The dot product of two displacement vectors, in coordinates. -/
def dotP (ux uy vx vy : ZFSet.{u}) : ZFSet.{u} :=
  realLAdd (realLMul ux vx) (realLMul uy vy)

/-- The squared length of a displacement. -/
def sqNorm (ux uy : ZFSet.{u}) : ZFSet.{u} :=
  realLAdd (realLMul ux ux) (realLMul uy uy)

theorem sqNorm_mem {ux uy : ZFSet.{u}} (hux : ux ∈ RealL.{u})
    (huy : uy ∈ RealL.{u}) : sqNorm ux uy ∈ RealL.{u} :=
  realLAdd_mem (realLMul_mem hux hux) (realLMul_mem huy huy)

/-- Polarisation. `|u - v|² = (|u|² + |v|²) - 2·(u · v)`, and it is the
whole of the congruence group: it turns an angle into a dot product without
taking a root or forming a ratio. -/
theorem sqNorm_sub {ux uy vx vy : ZFSet.{u}} (hux : ux ∈ RealL.{u})
    (huy : uy ∈ RealL.{u}) (hvx : vx ∈ RealL.{u}) (hvy : vy ∈ RealL.{u}) :
    sqNorm (realLAdd ux (realLNeg vx)) (realLAdd uy (realLNeg vy))
      = realLAdd (realLAdd (sqNorm ux uy) (sqNorm vx vy))
          (realLNeg (realLAdd (dotP ux uy vx vy) (dotP ux uy vx vy))) := by
  have hxx := realLMul_mem hux hux
  have hyy := realLMul_mem huy huy
  have hvxx := realLMul_mem hvx hvx
  have hvyy := realLMul_mem hvy hvy
  have hxv := realLMul_mem hux hvx
  have hyv := realLMul_mem huy hvy
  simp only [sqNorm, dotP]
  rw [sq_diff hux hvx, sq_diff huy hvy,
    realLAdd_interchange (realLAdd_mem hxx hvxx)
      (realLNeg_mem (realLAdd_mem hxv hxv)) (realLAdd_mem hyy hvyy)
      (realLNeg_mem (realLAdd_mem hyv hyv)),
    ← realLNeg_realLAdd (realLAdd_mem hxv hxv) (realLAdd_mem hyv hyv),
    realLAdd_interchange hxx hvxx hyy hvyy,
    realLAdd_interchange hxv hxv hyv hyv]

/-! ## Transferring a segment onto a ray

The first statement in this track that needs a square root of a quantity
varying with the input and a reciprocal in the same breath. Both are now
available and neither costs anything, so III.1 is free -- but it is worth
noting that Euclid I.1 needed neither, so that one came out free
before any of this machinery existed. -/

/-- Squared distance is the squared norm of the displacement. Written once
here because every point-level statement below needs it. -/
theorem sqDist_eq_sqNorm {xA yA xB yB : ZFSet.{u}} (hxA : xA ∈ RealL.{u})
    (hyA : yA ∈ RealL.{u}) (hxB : xB ∈ RealL.{u}) (hyB : yB ∈ RealL.{u}) :
    sqDist (opair xA yA) (opair xB yB)
      = sqNorm (realLAdd xB (realLNeg xA)) (realLAdd yB (realLNeg yA)) := by
  rw [sqDist_opair, ← realLNeg_sub hxB hxA, ← realLNeg_sub hyB hyA,
    realLMul_neg_neg (realLAdd_mem hxB (realLNeg_mem hxA))
      (realLAdd_mem hxB (realLNeg_mem hxA)),
    realLMul_neg_neg (realLAdd_mem hyB (realLNeg_mem hyA))
      (realLAdd_mem hyB (realLNeg_mem hyA))]
  rfl

/-- Squared distance does not care which end you measure from. -/
theorem sqDist_comm {x y x' y' : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hx' : x' ∈ RealL.{u}) (hy' : y' ∈ RealL.{u}) :
    sqDist (opair x y) (opair x' y') = sqDist (opair x' y') (opair x y) := by
  rw [sqDist_opair, sqDist_opair, ← realLNeg_sub hx' hx, ← realLNeg_sub hy' hy,
    realLMul_neg_neg (realLAdd_mem hx' (realLNeg_mem hx))
      (realLAdd_mem hx' (realLNeg_mem hx)),
    realLMul_neg_neg (realLAdd_mem hy' (realLNeg_mem hy))
      (realLAdd_mem hy' (realLNeg_mem hy))]

/-! ## Pythagoras

Stated for the cost rather than the theorem. The right angle arrives as
`dotP = 0` -- a hypothesis, not a decision -- so polarisation does the whole
work and nothing is spent: `|u - v|² = |u|² + |v|² - 2(u·v)` with the last term
gone. That is the same shape as every other free result here, and the point of
recording it is that the classical landmark a reader looks for costs exactly
nothing. -/

/-- The Pythagorean theorem, on displacements. -/
theorem pythagoras {ux uy vx vy : ZFSet.{u}} (hux : ux ∈ RealL.{u})
    (huy : uy ∈ RealL.{u}) (hvx : vx ∈ RealL.{u}) (hvy : vy ∈ RealL.{u})
    (hperp : dotP ux uy vx vy = realLZero.{u}) :
    sqNorm (realLAdd ux (realLNeg vx)) (realLAdd uy (realLNeg vy))
      = realLAdd (sqNorm ux uy) (sqNorm vx vy) := by
  rw [sqNorm_sub hux huy hvx hvy, hperp, realLAdd_zero realLZero_mem,
    realLNeg_zero, realLAdd_zero (realLAdd_mem (sqNorm_mem hux huy)
      (sqNorm_mem hvx hvy))]

/-- Pythagoras, on points: with the right angle at `C`, the square on the
hypotenuse is the sum of the squares on the legs. The perpendicularity is
supplied, which is what Euclid does too -- I.47 assumes the right angle rather
than deciding it. -/
theorem pythagoras_points {xA yA xB yB xC yC : ZFSet.{u}} (hxA : xA ∈ RealL.{u})
    (hyA : yA ∈ RealL.{u}) (hxB : xB ∈ RealL.{u}) (hyB : yB ∈ RealL.{u})
    (hxC : xC ∈ RealL.{u}) (hyC : yC ∈ RealL.{u})
    (hperp : dotP (realLAdd xA (realLNeg xC)) (realLAdd yA (realLNeg yC))
      (realLAdd xB (realLNeg xC)) (realLAdd yB (realLNeg yC)) = realLZero.{u}) :
    sqDist (opair xA yA) (opair xB yB)
      = realLAdd (sqDist (opair xC yC) (opair xA yA))
          (sqDist (opair xC yC) (opair xB yB)) := by
  have hAC := realLAdd_mem hxA (realLNeg_mem hxC)
  have hAC' := realLAdd_mem hyA (realLNeg_mem hyC)
  have hBC := realLAdd_mem hxB (realLNeg_mem hxC)
  have hBC' := realLAdd_mem hyB (realLNeg_mem hyC)
  rw [sqDist_comm hxA hyA hxB hyB, sqDist_eq_sqNorm hxB hyB hxA hyA,
    sqDist_eq_sqNorm hxC hyC hxA hyA, sqDist_eq_sqNorm hxC hyC hxB hyB,
    ← pythagoras hAC hAC' hBC hBC' hperp, disp_sub hxC hxB hxA,
    disp_sub hyC hyB hyA]

#print axioms Geometry.sqNorm_sub
#print axioms Geometry.sqDist_eq_sqNorm
#print axioms Geometry.pythagoras
#print axioms Geometry.pythagoras_points
#print axioms sqNorm_mem
#print axioms sqDist_comm
end Geometry

namespace ZFSet
export Geometry (dotP pythagoras pythagoras_points sqDist_comm sqDist_eq_sqNorm sqNorm sqNorm_mem sqNorm_sub)
end ZFSet
