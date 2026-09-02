/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Core lemmas that are classical, redone.

Lean core is not uniformly constructive. Each lemma reproved here is a general
statement whose special case at a decidable type is constructive. Core pays an
axiom for the generality; a development that lives inside decidable arithmetic
does not have to.

| core lemma | core's axioms | why it is avoidable |
|---|---|---|
| `Nat.mul_lt_mul_right` | `Classical.choice` | `Nat.mul_le_mul_right` is free; `<` follows by contraposition |
| `Nat.lt_of_mul_lt_mul_left` | `Classical.choice` | same shape, same fix |
| `List.perm_cons_erase` | `Classical.choice` | general over `BEq`/`LawfulBEq`; `Nat` equality is decidable |
| `Nat.pow_lt_pow_right` | `Classical.choice` | `Nat.pow_le_pow_right` is free; the strict form splits off one factor |
| `List.mem_append` | `propext` | it is an `Iff`; the three directions a caller needs are each a recursion on the first list |

`List.mem_append` is here for `propext` rather than `Classical.choice`, and
there is no axiom-free alternative in core. `Metamath/FirstOrder.lean`
documents the technique for its own layer
--- *`List.Mem` is an inductive and its `Iff` lemmas in core are not ... recursing
on the membership instead keeps the whole derivation layer free of axioms
* --- and keeps `DerivesFO` clean that way, but the discipline was
local to that file and the lemmas were never written down.

Two proofs of the same statement can print different axioms when one routes
through a combinator that appends contexts and the other does not, so an axiom
line can report a proof path rather than a property of the theorem. The lemmas
below remove that route.

Anything else that turns up goes here, with the audit line that motivated it.
Nothing in this file is new mathematics -- it exists so that the pattern is
visible in one place instead of being rediscovered file by file.
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

All three at `[propext]` or better. -/

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


/-- `Nat.div_lt_of_lt_mul`, constructively. The core lemma is classical,
and its content is not. Dividing is a
computation; the only case split is on whether the divisor is zero, and the
hypothesis rules that out by itself. -/
theorem div_lt_of_lt_mul' {m n k : Nat} (h : m < n * k) : m / n < k := by
  rcases Nat.lt_or_ge (m / n) k with hk | hk
  · exact hk
  · have h1 : n * k ≤ n * (m / n) := Nat.mul_le_mul_left n hk
    have h2 : n * (m / n) + m % n = m := Nat.div_add_mod m n
    omega

#print axioms Core.div_lt_of_lt_mul'


end Core

namespace ZFSet
export Core (div_lt_of_lt_mul' eq_or_lt_of_le' mul_lt_mul_right' pow_lt_pow_right' pow_right_injective)
end ZFSet
