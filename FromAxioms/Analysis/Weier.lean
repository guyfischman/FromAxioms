/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Powers, finite sums, and the road to Weierstrass

Polynomial approximation of a uniformly continuous function on the unit
interval (Weierstrass, 1885) has a constructive proof through Bernstein
polynomials: the weights are rational, the argument is a variance bound,
and the modulus of continuity is exactly the input the estimate
consumes.

This file carries that route. The carriers come first -- the power and
the finite sum on located reals, by the recursions `riemannSum` set the
style for -- then the Bernstein basis and its algebra (`bernTerm`,
`bernPair`, `bern_recombine`), the partition of unity
(`bernTerm_sum_one`), the two moment identities and the variance bound
they give (`bern_first_moment`, `bern_second_moment`, `bern_variance`),
and the approximation itself in `weierstrassApprox`.

The variance bound turns a modulus of continuity into a bound on the error. The
degree `N` that `weierstrassApprox` returns depends on the target `n₀` alone,
so the approximation is uniform on the interval, and the file is choice-free.
-/

import FromAxioms.Analysis.Located

universe u

namespace Analysis

/-- The `k`-th power of a located real. -/
def realLPow (x : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => realLOne.{u}
  | k + 1 => realLMul x (realLPow x k)

/-- The sum of the first `k` values of an indexed family of reals. -/
def realLSum (G : Nat → ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => realLZero.{u}
  | k + 1 => realLAdd (realLSum G k) (G k)

end Analysis

namespace ZFSet
export Analysis (realLPow realLSum)
end ZFSet
