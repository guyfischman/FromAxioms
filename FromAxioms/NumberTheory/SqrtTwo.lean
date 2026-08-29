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

import FromAxioms.SetTheory.ZFSet

universe u

namespace NumberTheory

/-! ## The Nat-level theorem -/

/-- `(2m)² = 4m²`, and its odd companion. Without `ring`, the two identities the
descent needs are proved once and reused. -/
private theorem four_sq (m : Nat) : (2 * m) * (2 * m) = 4 * (m * m) := by
  rw [Nat.mul_assoc, ← Nat.mul_assoc m 2 m, Nat.mul_comm m 2, Nat.mul_assoc,
    ← Nat.mul_assoc]

private theorem odd_sq (r : Nat) : (2 * r + 1) * (2 * r + 1) = 4 * (r * r) + 4 * r + 1 := by
  rw [Nat.add_mul, Nat.mul_add, four_sq]
  omega

private theorem even_of_sq_even {p : Nat} (h : p * p % 2 = 0) : p % 2 = 0 := by
  rcases (by omega : p % 2 = 0 ∨ p % 2 = 1) with h0 | h1
  · exact h0
  · exfalso
    obtain ⟨r, rfl⟩ : ∃ r, p = 2 * r + 1 := ⟨p / 2, by omega⟩
    rw [odd_sq] at h
    omega

/-- The irrationality of √2, by descent: a solution forces a smaller
one. -/
theorem sq_two_irrational : ∀ p q : Nat, p * p = 2 * (q * q) → q = 0 := by
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
    intro q hpq
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · rfl
    · exfalso
      -- `p` is even, so `p = 2r` and `q² = 2r²`
      have hpe : p % 2 = 0 := even_of_sq_even (by omega)
      have hp : p = 2 * (p / 2) := by omega
      have hr : q * q = 2 * ((p / 2) * (p / 2)) := by
        have h4 : (2 * (p / 2)) * (2 * (p / 2)) = 2 * (q * q) := by rw [← hp]; exact hpq
        rw [four_sq] at h4
        omega
      -- and `q < p`, so the induction hypothesis applies to the smaller pair
      have hqp : q < p := by
        rcases Nat.lt_or_ge q p with h | h
        · exact h
        · exfalso
          have h2 : p * p ≤ q * q := Nat.mul_le_mul h h
          have h3 : 0 < q * q := Nat.mul_pos hq hq
          omega
      exact absurd (ih q hqp (p / 2) hr) (by omega)

#print axioms sq_two_irrational
end NumberTheory

namespace ZFSet
export NumberTheory (sq_two_irrational)
end ZFSet
