/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

import FromAxioms.Algebra.Module
import FromAxioms.NumberTheory.Halving

/-!
# The inner product space, and completeness in finite dimension

Both places a principle could have entered are definitions, not theorems.
`IsInnerProduct` takes a `nonneg` set rather than a positive cone, because
`IsPosCone`'s `total` clause is priced at `NeApartZero` and an inner product
never decides a sign. `IsHilbertSpaceL` is stated over `RealL` rather than an
arbitrary complete ordered field, because a general scale is available only
through that same cone while `invScale` needs no division in the ring.

    generality in the SCALARS is free; generality in the SCALE costs a principle

With those two choices every result here is `[propext, Quot.sound]`, including
convergence in norm.
-/

open Algebra NumberTheory SetTheory
namespace Analysis

universe u

/-- An inner product on a module, with positivity carried by a `nonneg` set
and no totality clause. `IsPosCone`'s `total` is priced at `NeApartZero`
(`Ordered.lean`), and nothing an inner product needs decides a sign -- so
inheriting it would charge this theory for a definition rather than for its
mathematics. -/
structure IsInnerProduct (R add mul zero one V vadd vzero smul form nonneg : ZFSet.{u}) :
    Prop where
  module : IsModule R add mul zero one V vadd vzero smul
  maps : ∀ u, u ∈ V → ∀ v, v ∈ V → opAt form u v ∈ R
  symm : ∀ u, u ∈ V → ∀ v, v ∈ V → opAt form u v = opAt form v u
  add_left : ∀ u, u ∈ V → ∀ u', u' ∈ V → ∀ v, v ∈ V →
    opAt form (opAt vadd u u') v = opAt add (opAt form u v) (opAt form u' v)
  smul_left : ∀ c, c ∈ R → ∀ u, u ∈ V → ∀ v, v ∈ V →
    opAt form (opAt smul c u) v = opAt mul c (opAt form u v)
  nonneg_zero : zero ∈ nonneg
  self_nonneg : ∀ u, u ∈ V → opAt form u u ∈ nonneg


/-- An inner product is additive in its right argument. -/
theorem innerProduct_add_right
    {R add mul zero one V vadd vzero smul form nonneg : ZFSet.{u}}
    (hI : IsInnerProduct R add mul zero one V vadd vzero smul form nonneg)
    {u v v' : ZFSet.{u}} (hu : u ∈ V) (hv : v ∈ V) (hv' : v' ∈ V) :
    opAt form u (opAt vadd v v')
      = opAt add (opAt form u v) (opAt form u v') := by
  have hvv' : opAt vadd v v' ∈ V := vaddAt_mem hI.module hv hv'
  rw [hI.symm _ hu _ hvv', hI.add_left _ hv _ hv' _ hu,
    hI.symm _ hv _ hu, hI.symm _ hv' _ hu]

/-- `<x + y, x + y> = (<x, x> + <x, y>) + (<x, y> + <y, y>)` in any inner
product space. -/
theorem innerProduct_add_self
    {R add mul zero one V vadd vzero smul form nonneg : ZFSet.{u}}
    (hI : IsInnerProduct R add mul zero one V vadd vzero smul form nonneg)
    {x y : ZFSet.{u}} (hx : x ∈ V) (hy : y ∈ V) :
    opAt form (opAt vadd x y) (opAt vadd x y)
      = opAt add (opAt add (opAt form x x) (opAt form x y))
          (opAt add (opAt form x y) (opAt form y y)) := by
  have hxy : opAt vadd x y ∈ V := vaddAt_mem hI.module hx hy
  rw [hI.add_left _ hx _ hy _ hxy,
    innerProduct_add_right hI hx hx hy, innerProduct_add_right hI hy hx hy,
    hI.symm _ hy _ hx]

#print axioms Analysis.innerProduct_add_right
#print axioms Analysis.innerProduct_add_self
#print axioms IsInnerProduct
/-!
### The expansion over a Lean type

`innerProduct_add_self` above is over `IsInnerProduct`, whose every argument is a
`ZFSet`. Over a type the proof needs two equations, `add_left` and `symm`, and
the memberships vanish, so `IsInnerFormT` carries those two clauses and no
more. `R` is a bare type with a binary `add`, not even associative.

These print `does not depend on any axioms`.
-/

/-- An inner-product-like form over Lean types: symmetric, and additive on
the left. Two clauses, because two clauses are what the expansion consumes. -/
structure IsInnerFormT {V : Type u} {R : Type v}
    (vadd : V → V → V) (add : R → R → R) (form : V → V → R) : Prop where
  symm : ∀ u w, form u w = form w u
  add_left : ∀ u u' w, form (vadd u u') w = add (form u w) (form u' w)

/-- A version of `innerProduct_add_right` over a Lean type. -/
theorem isInnerFormT_add_right {V : Type u} {R : Type v}
    {vadd : V → V → V} {add : R → R → R} {form : V → V → R}
    (hI : IsInnerFormT vadd add form) (x y y' : V) :
    form x (vadd y y') = add (form x y) (form x y') := by
  rw [hI.symm x (vadd y y'), hI.add_left y y' x, hI.symm y x, hI.symm y' x]

/-- `<x + y, x + y> = (<x, x> + <x, y>) + (<x, y> + <y, y>)` over a Lean type.
Here `add` is a bare binary operation, so the middle terms are not collected. -/
theorem isInnerFormT_add_self {V : Type u} {R : Type v}
    {vadd : V → V → V} {add : R → R → R} {form : V → V → R}
    (hI : IsInnerFormT vadd add form) (x y : V) :
    form (vadd x y) (vadd x y)
      = add (add (form x x) (form x y)) (add (form x y) (form y y)) := by
  rw [hI.add_left x y (vadd x y),
    isInnerFormT_add_right hI x x y, isInnerFormT_add_right hI y x y,
    hI.symm y x]

#print axioms IsInnerFormT
#print axioms isInnerFormT_add_right
#print axioms isInnerFormT_add_self
end Analysis


namespace ZFSet
export Analysis (IsInnerFormT IsInnerProduct innerProduct_add_right innerProduct_add_self isInnerFormT_add_right isInnerFormT_add_self)
end ZFSet
