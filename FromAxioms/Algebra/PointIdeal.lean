/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The ideal of a point on a plane curve

The divisor-to-ideal-class correspondence needs the ideal of `R[x][y]` whose
members vanish at a point. It needs no new construction: it is the KERNEL of
evaluation, and evaluation is a ring homomorphism twice over.

`evalPoint` at the outer layer carries `R[x][y]` to `R[x]`; `evalPoint` at the
inner layer carries `R[x]` to `R`; `isRingHom_comp` composes them and
`isIdeal_ker` makes the kernel an ideal.
-/

import FromAxioms.Analysis.Cauchy

universe u

open Analysis
namespace Algebra


/-- `1` is not `0` over the located reals. -/
theorem realLOne_ne_zero : realLOne.{u} ≠ realLZero.{u} := by
  intro h
  exact realLApart_irrefl realLZero_mem.{u} (h ▸ realLApart_zero_one.{u})

end Algebra
#print axioms Algebra.realLOne_ne_zero
namespace ZFSet
export Algebra (realLOne_ne_zero)
end ZFSet
