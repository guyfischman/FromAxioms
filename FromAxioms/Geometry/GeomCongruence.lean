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

universe u

open Analysis
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

#print axioms Geometry.sqNorm_sub
#print axioms Geometry.pythagoras
#print axioms sqNorm_mem
end Geometry

namespace ZFSet
export Geometry (dotP pythagoras sqNorm sqNorm_mem sqNorm_sub)
end ZFSet
