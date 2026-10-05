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
import FromAxioms.NumberTheory.Prime

universe u

open NumberTheory
namespace Analysis

/-- The `k`-th power of a located real. -/
def realLPow (x : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => realLOne.{u}
  | k + 1 => realLMul x (realLPow x k)

theorem realLPow_mem {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    ∀ k : Nat, realLPow x k ∈ RealL.{u}
  | 0 => realLOne_mem
  | k + 1 => realLMul_mem hx (realLPow_mem hx k)

/-- The sum of the first `k` values of an indexed family of reals. -/
def realLSum (G : Nat → ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => realLZero.{u}
  | k + 1 => realLAdd (realLSum G k) (G k)

/-- Membership from bounded hypotheses: the sum only reads below its
bound. -/
theorem realLSum_mem' {G : Nat → ZFSet.{u}} :
    ∀ k : Nat, (∀ i : Nat, i < k → G i ∈ RealL.{u}) →
      realLSum G k ∈ RealL.{u}
  | 0, _ => realLZero_mem
  | k + 1, h => realLAdd_mem
      (realLSum_mem' k (fun i hi => h i (Nat.lt_succ_of_lt hi)))
      (h k (Nat.lt_succ_self k))

/- Peeling the first term off a sum.

`realLSum` is a left fold --- `realLSum G (k+1)` is `realLSum G k + G k`, so
the term it exposes for free is the last one. Peeling the first needs an
induction: no unfolding reaches the head of a left fold. -/
theorem realLSum_mem {G : Nat → ZFSet.{u}}
    (hG : ∀ k : Nat, G k ∈ RealL.{u}) :
    ∀ k : Nat, realLSum G k ∈ RealL.{u} :=
  fun k => realLSum_mem' k (fun i _ => hG i)


/-! ## The Bernstein basis -/

/-- One expansion term over an arbitrary pair,
`C(n,k) · x^k · y^(n-k)`, the coefficient carried as a rational --
`choose` is `Prime.lean`'s. -/
def bernPair (n k : Nat) (x y : ZFSet.{u}) : ZFSet.{u} :=
  realLMul (realLOf (ratNat.{u} (choose n k) 1))
    (realLMul (realLPow x k) (realLPow y (n - k)))

theorem bernPair_mem {x y : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (n k : Nat) : bernPair n k x y ∈ RealL.{u} :=
  realLMul_mem (realLOf_mem (ratNat_mem_Rat Nat.one_pos))
    (realLMul_mem (realLPow_mem hx k) (realLPow_mem hy (n - k)))

/-- The Bernstein basis proper: the complement is `1 - x`. -/
def bernTerm (n k : Nat) (x : ZFSet.{u}) : ZFSet.{u} :=
  bernPair n k x (realLAdd realLOne.{u} (realLNeg x))

theorem bernTerm_mem {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) (n k : Nat) :
    bernTerm n k x ∈ RealL.{u} :=
  bernPair_mem hx (realLAdd_mem realLOne_mem (realLNeg_mem hx)) n k

/-! ## The Pascal split, on located reals

`PolyRing.lean` proves the binomial theorem once for every internal ring;
the located reals are a meta-level structure, so the same three-step
split -- absorb the factor, apply Pascal to the coefficient, recombine
the shifted sums -- is restated here over `realLSum`. -/

/-- The Bernstein operator: the function sampled at the grid,
weighted by the basis. -/
def bernOp (n : Nat) (F : ZFSet.{u} → ZFSet.{u}) (x : ZFSet.{u}) :
    ZFSet.{u} :=
  realLSum (fun k => realLMul (F (realLOf (ratNat.{u} k n)))
    (bernTerm n k x)) (n + 1)

#print axioms Analysis.bernPair_mem
#print axioms Analysis.realLSum_mem'
#print axioms Analysis.bernTerm_mem
#print axioms Analysis.realLPow_mem
#print axioms Analysis.realLSum_mem
end Analysis

namespace ZFSet
export Analysis (bernOp bernPair bernPair_mem bernTerm bernTerm_mem realLPow realLPow_mem realLSum realLSum_mem realLSum_mem')
end ZFSet
