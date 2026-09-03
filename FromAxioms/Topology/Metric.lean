/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Balls, open sets and density on the located reals

The layer Baire needs, and which `Located.lean` stops just short of: it builds
`RealL` with an order, an apartness, arithmetic and located suprema, and nothing
above that.

Built over `RealL` distances rather than over an abstract metric space. The
point is a theorem about the reals this development actually has, not a general
topology -- and an abstract metric would need a distance into `RealL` anyway,
so the abstraction would buy nothing here and cost a layer.

A ball is written as a two-sided inequality, `c - r < x < c + r`, rather than
through an absolute value. When this file was written no `realLAbs` existed
and a case split on the sign seemed the price of one; `Deriv.lean` has since
defined it case-free as `max(x, -x)`. The two-sided form remains -- it is
the same set, and rewriting a working vocabulary buys nothing.

Density is stated as "meets every ball", not through a closure operator: a
closure needs limit points, and limit points on located reals need the located
suprema machinery for no gain. Meeting every ball is what the Baire argument
uses.
-/

import FromAxioms.Analysis.Cauchy

universe u

open Algebra Analysis SetTheory
namespace Topology

/-! ## Balls -/

/-- The open ball, as the two-sided inequality. -/
def realLBall (c r : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun x => realLLt (realLAdd c (realLNeg r)) x ∧ realLLt x (realLAdd c r))
    RealL.{u}

/-! ## Dense and open, with their witnesses

Stated with the witnesses as data, the walk's step is a function and no
choice is needed anywhere. This is the locator pattern, and the same trade
`SideReadout` makes: the disjunction -- here the existential -- is available
already, and what is missing is the function that picks.
-/

/-- Openness and density, with the two witnesses supplied rather than
asserted. `centre` gives the point density promises; `radius` gives the ball
openness promises around it. -/
structure DenseOpenWitness (S : ZFSet.{u}) : Type (u + 1) where
  subset : S ⊆ RealL.{u}
  centre : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}
  radius : ZFSet.{u} → ZFSet.{u}
  centre_mem : ∀ c r, c ∈ RealL.{u} → r ∈ RealL.{u} →
    realLLt realLZero.{u} r → centre c r ∈ S
  centre_ball : ∀ c r, c ∈ RealL.{u} → r ∈ RealL.{u} →
    realLLt realLZero.{u} r → centre c r ∈ realLBall c r
  radius_mem : ∀ x, x ∈ S → radius x ∈ RealL.{u}
  radius_pos : ∀ x, x ∈ S → realLLt realLZero.{u} (radius x)
  radius_sub : ∀ x, x ∈ S → realLBall x (radius x) ⊆ S

/-! ## Rational intervals

`IsNested` in `Nested.lean` is stated over rational sequences, so a recursion
that produces balls with real centres and radii cannot feed it directly. Every
point of an open set sits in a rational interval inside it, and the witnesses
come straight from the order bridge -- `realLLt (x - r) x` is a rational
strictly between them.
-/

/-- The open interval with rational endpoints. -/
def realLIoo (p q : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun x => realLLt (realLOf p) x ∧ realLLt x (realLOf q)) RealL.{u}

end Topology

#print axioms Topology.DenseOpenWitness
namespace ZFSet
export Topology (DenseOpenWitness realLBall realLIoo)
end ZFSet
