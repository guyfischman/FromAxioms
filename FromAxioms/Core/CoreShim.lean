/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Core lemmas that are classical, redone.

Lean core is not uniformly constructive. The lemmas reproved here are not
scattered at random: each is a general statement whose special case at a
decidable type is constructive. Core pays an axiom for the generality; a
development that lives inside decidable arithmetic does not have to.
-/

namespace Core

/-- `Nat.mul_lt_mul_right` without the axiom. -/
theorem mul_lt_mul_right' {m n k : Nat} (hk : 0 < k) (h : m < n) : m * k < n * k := by
  have hstep : (m + 1) * k ≤ n * k := Nat.mul_le_mul_right k (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hstep
  omega

/-- `Nat.pow_lt_pow_right` without the axiom. -/
theorem pow_lt_pow_right' {b j k : Nat} (hb : 1 < b) (hjk : j < k) : b ^ j < b ^ k := by
  have hpos : 0 < b ^ j := Nat.pos_pow_of_pos (by omega)
  have hsplit : b ^ k = b ^ j * b ^ (k - j) := by
    rw [← Nat.pow_add]
    exact congrArg _ (by omega)
  have hge : b ^ 1 ≤ b ^ (k - j) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.pow_one] at hge
  have hstep : b ^ j * 2 ≤ b ^ j * b ^ (k - j) := Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## Audit

All three at `[propext]` or better -- which is the whole point of the file. -/

/-- A base above one makes the exponent recoverable from the power. -/
theorem pow_right_injective {b j k : Nat} (hb : 1 < b) (h : b ^ j = b ^ k) : j = k := by
  rcases Nat.lt_trichotomy j k with hlt | he | hgt
  · exact absurd h (by have := pow_lt_pow_right' hb hlt; omega)
  · exact he
  · exact absurd h (by have := pow_lt_pow_right' hb hgt; omega)

#print axioms mul_lt_mul_right'
/-- The split from `n <= m`, by deciding `n < m`. -/
theorem eq_or_lt_of_le' {n m : Nat} (h : n ≤ m) : n = m ∨ n < m :=
  if hlt : n < m then Or.inr hlt
  else Or.inl (Nat.le_antisymm h (Nat.ge_of_not_lt hlt))

#print axioms eq_or_lt_of_le'
#print axioms pow_lt_pow_right'
#print axioms pow_right_injective


end Core

namespace ZFSet
export Core (eq_or_lt_of_le' mul_lt_mul_right' pow_lt_pow_right' pow_right_injective)
end ZFSet
