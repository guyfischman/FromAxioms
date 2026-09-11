/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# √2.

The oldest result this development reaches: there is a real whose square is
`2`, and no rational has that square.

Two halves, and they lean on each other.

`sq_two_irrational` is the Nat-level statement -- `p² = 2q²` forces `q = 0` --
by descent: `p²` even makes `p` even, halving gives a smaller pair, and strong
induction closes it. No axioms, and the arithmetic stays in `Nat`.

The real is then built by bisection. The interval `[kₙ/2ⁿ, (kₙ+1)/2ⁿ]` is
halved by asking whether `(2kₙ+1)² < 2·(2ⁿ⁺¹)²` -- a comparison of naturals,
which is decidable data rather than a `Prop` disjunction, so the sequence is
definable without any axiom. This is the same reason `Ternary.lean` is
choice-free, arrived at from the other direction: there the decision was pushed
into arithmetic, here it was arithmetic to begin with.

The invariant is `kₙ² < 2·4ⁿ < (kₙ+1)²`, and keeping it is exactly where
irrationality is needed: the middle point could a priori equal `2·4ⁿ`, and
`sq_two_irrational` is what rules that out.
-/

import FromAxioms.NumberTheory.Prime

universe u

namespace NumberTheory

/-! ## The Nat-level theorem -/

/-- `(2m)² = 4m²`, and its odd companion. Without `ring`, the two identities the
descent needs are proved once and reused. -/
private theorem four_sq (m : Nat) : (2 * m) * (2 * m) = 4 * (m * m) := by
  rw [Nat.mul_assoc, ← Nat.mul_assoc m 2 m, Nat.mul_comm m 2, Nat.mul_assoc,
    ← Nat.mul_assoc]

/-- The irrationality of √2, as the prime case at `2`.

`prime_sq_irrational` runs the descent for an arbitrary prime modulus, and the
only thing this row adds is `isPrime_two`. The descent WAS written out here once,
with a private `odd_sq` and `even_of_sq_even` supplying `2 ∣ p² → 2 ∣ p` by
expanding `(2r+1)²`; the general lemma gets that step from `prime_divides_sq` and
needs no expansion, so the specialised proof and both helpers came out together.

The two case of `prime_sq_irrational`, whose type quantifies over `n` under
`IsPrime n` and so is a different statement from this one. -/
theorem sq_two_irrational : ∀ p q : Nat, p * p = 2 * (q * q) → q = 0 :=
  prime_sq_irrational isPrime_two

/-! ## The bisection -/

def pow2 : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * pow2 n

theorem succ_le_pow2 : ∀ n : Nat, n + 1 ≤ pow2 n
  | 0 => by simp [pow2]
  | n + 1 => by
    have := succ_le_pow2 n
    simp only [pow2]
    omega

#print axioms sq_two_irrational
#print axioms four_sq
#print axioms succ_le_pow2
end NumberTheory

namespace ZFSet
export NumberTheory (pow2 sq_two_irrational succ_le_pow2)
end ZFSet
