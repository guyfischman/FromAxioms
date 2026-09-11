/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`.

This file imports Mathlib because the challenge is stated over `ℝ` and `ℚ` and
cannot be mentioned without them. It does not cite `Nat.Prime.irrational_sqrt`
or anything downstream of it. The arithmetic comes from one declaration of this
tower,

    NumberTheory.prime_sq_irrational :
      IsPrime n → ∀ a b : Nat, a * a = n * (b * b) → b = 0

and Mathlib supplies only the plumbing between that and `Real.sqrt`.

Our statement is over Lean's `Nat`, with no reals and no subtraction, so no
transfer of a number system is needed here. The only bridge is between two
spellings of primality over the same `Nat`, and it is shared with every other
`carrier: nat` pair in `Comparator.Bridge.NatPrime`.
-/
import Comparator.IrrationalSqrtPrime.Challenge
import Comparator.Bridge.NatPrime
import FromAxioms

namespace Comparator.IrrationalSqrtPrime

open NumberTheory

/-- The challenge, discharged.

A rational equal to `√p` squares to `p`; a rational whose square is a natural
number has denominator 1; so `p` would be a perfect square, and
`prime_sq_irrational` at `b = 1` says it is not. -/
theorem solution : challenge := by
  intro p hp
  have key : ∀ a b : Nat, a * a = p * (b * b) → b = 0 :=
    prime_sq_irrational (isPrime_of_prime hp)
  rintro ⟨q, hq⟩
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hsq : ((q ^ 2 : ℚ) : ℝ) = ((p : ℚ) : ℝ) := by
    push_cast
    rw [hq, Real.sq_sqrt hp0]
  have hq2 : q ^ 2 = (p : ℚ) := by exact_mod_cast hsq
  have hden : q.den = 1 := by
    have : (q ^ 2).den = 1 := by rw [hq2]; simp
    have hd : q.den ^ 2 = 1 := by rw [← Rat.den_pow]; exact this
    nlinarith [q.den_pos, hd]
  have hnum : q.num ^ 2 = (p : ℤ) := by
    have hc : ((q.num : ℚ)) = q := by
      rw [← Rat.num_div_den q, hden]; simp
    -- In `ℚ` first, then cast down: the goal is over `ℤ`, so `hc` does not
    -- rewrite in it.
    have hqq : ((q.num : ℚ)) ^ 2 = (p : ℚ) := by rw [hc, hq2]
    exact_mod_cast hqq
  have habs : q.num.natAbs * q.num.natAbs = p * (1 * 1) := by
    have := congrArg Int.natAbs hnum
    simpa [Int.natAbs_mul, pow_two] using this
  exact absurd (key q.num.natAbs 1 habs) one_ne_zero

end Comparator.IrrationalSqrtPrime
