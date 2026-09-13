/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Distinct, versus apart.

Euclid I.1 in `GeomPlane.lean` needs no principle. One enters at the step from
two points being distinct -- `¬ (A = B)`, a negation, which decides nothing
-- to their displacement being apart from zero, which is positive data and is
what says the line through them is a line rather than the whole plane.
-/

import FromAxioms.SetTheory.Uncountable

universe u

open Analysis SetTheory
namespace Geometry


/-! ## Lines -/

/-- `P` satisfies `a·x + b·y = c`. -/
def OnLine (a b c P : ZFSet.{u}) : Prop :=
  realLAdd (realLMul a (fst P)) (realLMul b (snd P)) = c

/-! ## Where two lines cross

Solving the pair needs the determinant inverted, so it needs `a·b' - a'·b`
apart from zero. Read as `¬ (det = 0)` instead, the same statement costs
`NeApartZero` and so `MP`. -/

/-- `a·b' - a'·b`. -/
def det (a b a' b' : ZFSet.{u}) : ZFSet.{u} :=
  realLAdd (realLMul a b') (realLNeg (realLMul a' b))

/-! ## Parallelism, read three ways

* negative -- they have no common point;
* equational -- the determinant of the coefficient pairs is zero;
* disjunctive -- they are parallel or they meet.

The first two are cheap and the third is where a decision hides. -/

/-- The equational reading: the coefficient pairs are proportional. -/
def ParallelDet (a b a' b' : ZFSet.{u}) : Prop :=
  det a b a' b' = realLZero.{u}

/-! ## Hilbert's fourth group

Playfair's form: through a point off a line there is exactly one parallel. With
parallelism read equationally it is two lines of algebra, and both halves are
free -- the constant is computed from the point rather than chosen, and two
lines with one direction through one point have equal constants because both
constants are that same computation. -/

/-- Playfair, uniqueness: free. Two lines of one direction through one point
have the same constant, because each constant is the value of that direction
at that point. This is the whole of the uniqueness half at fixed direction; the
step from "parallel to `l`" to "of `l`'s direction" is `ParallelDet` unfolded
plus a division. -/
theorem playfair_unique {a b c₁ c₂ P : ZFSet.{u}}
    (h₁ : OnLine a b c₁ P) (h₂ : OnLine a b c₂ P) : c₁ = c₂ := by
  rw [OnLine] at h₁ h₂
  rw [← h₁, ← h₂]

end Geometry

#print axioms Geometry.playfair_unique
namespace ZFSet
export Geometry (OnLine ParallelDet det playfair_unique)
end ZFSet
