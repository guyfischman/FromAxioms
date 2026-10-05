/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Field extensions.

A ring homomorphism, and the one construction that produces extensions:
`K[x]/(g)` for an irreducible `g`, with `K` sitting inside it as the classes of
the constant polynomials. That embedding is what lets a polynomial be carried
into the larger field, where `g` acquires a root.
-/

import FromAxioms.Algebra.PolyRing

universe u

open Algebra NumberTheory
namespace SetTheory


/-- `x² - c`, over any commutative ring. -/
def sqrtPoly (R add zero one c : ZFSet.{u}) : ZFSet.{u} :=
  polyOfList R zero [ringNeg R add zero c, zero, one]

#print axioms sqrtPoly
end SetTheory
namespace ZFSet
export SetTheory (sqrtPoly)
end ZFSet
