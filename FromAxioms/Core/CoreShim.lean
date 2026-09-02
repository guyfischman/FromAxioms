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

`List.mem_append` IS THE FIRST ENTRY HERE FOR `propext` RATHER THAN
`Classical.choice`, and the reason it is worth an entry is the SCALE. Measured
2026-08-30: 175 uses across 28 files, and no axiom-free alternative anywhere in
the tree. `Metamath/FirstOrder.lean` documents the technique for its own layer
--- *`List.Mem` is an inductive and its `Iff` lemmas in core are not ... recursing
on the membership instead keeps the whole derivation layer free of axioms
* --- and keeps `DerivesFO` clean that way, but the discipline was
local to that file and the lemmas were never written down.

HOW IT WAS FOUND, because the route matters more than the lemma. Two Henkin-set
clauses with identical mathematics printed different axioms: `mem_disj_iff` at
ZERO and `mem_conj_iff` at `propext`. The difference was not conjunction versus
disjunction --- it was that one proof routed through `DerivesIn.conj_intro`,
which appends two contexts, and the other did not. `#print axioms` was reporting
a PROOF-PATH ARTEFACT as though it were a property of the theorem, which is
exactly the noise a library about measuring cost cannot afford.

`DerivesIn.imp_elim` and `DerivesIn.conj_intro` were the only two theory-level
combinators carrying it; rebuilt on the three lemmas below they print nothing,
and so does every Henkin clause above them. THE OTHER 173 USES ARE UNTOUCHED and
are a measured backlog rather than a claim --- the technique is here, the sweep
is not, and it crosses four other tracks' live files.

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


end Core

namespace ZFSet
export Core (eq_or_lt_of_le' mul_lt_mul_right' pow_lt_pow_right' pow_right_injective)
end ZFSet
