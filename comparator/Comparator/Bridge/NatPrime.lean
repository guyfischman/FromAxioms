/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
BRIDGE: primality, Mathlib's spelling against ours.

Both are predicates on Lean's `Nat`, so this is a restatement and not a transfer
of a number system. Every pair whose row has `carrier: nat` needs it, in one
direction or the other.

    Nat.Prime p                 Mathlib's
    NumberTheory.IsPrime p      `2 ≤ p ∧ ∀ d, 2 ≤ d → Divides d p → d = p`
    NumberTheory.Divides d n    `∃ k, n = d * k`

The two differ in which divisors they quantify over: Mathlib rules on every
divisor and allows `1`, ours rules only on divisors that are at least `2`. They
meet because a divisor of a number `≥ 2` is `0`, `1`, or `≥ 2`, and `0` is
excluded by the bound.
-/
import Mathlib.Data.Nat.Prime.Basic
import FromAxioms

open NumberTheory

/-- Mathlib's primality implies ours. -/
theorem isPrime_of_prime {p : ℕ} (hp : Nat.Prime p) : IsPrime p := by
  refine ⟨hp.two_le, fun d hd hdvd => ?_⟩
  obtain ⟨k, hk⟩ := hdvd
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp d ⟨k, hk⟩) with h1 | hs
  · omega
  · exact hs

/-- Ours implies Mathlib's. A divisor `m` of `p` is `0`, `1`, or at least `2`;
`0` would force `p = 0` against `2 ≤ p`, `1` is allowed outright, and our clause
sends the rest to `p`. -/
theorem prime_of_isPrime {p : ℕ} (hp : IsPrime p) : Nat.Prime p := by
  obtain ⟨h2, hd⟩ := hp
  -- `Nat.prime_def` from the pinned checkout, `Data/Nat/Prime/Defs.lean:94`:
  --   `Prime p ↔ 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p`
  refine Nat.prime_def.mpr ⟨h2, fun m hm => ?_⟩
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · -- `m < 2`, so `m` is 0 or 1. `interval_cases` is NOT available here:
    -- `Mathlib.Tactic.IntervalCases` is not imported by `Prime/Basic`, and the
    -- build reports it as `unknown tactic`. `Nat.eq_zero_or_pos` plus `omega`
    -- needs no extra import.
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact absurd (Nat.zero_dvd.mp hm) (by omega)
    · exact Or.inl (by omega)
  · obtain ⟨k, hk⟩ := hm
    exact Or.inr (hd m hge ⟨k, hk⟩)

/-- The two spellings agree. -/
theorem isPrime_iff_prime {p : ℕ} : IsPrime p ↔ Nat.Prime p :=
  ⟨prime_of_isPrime, isPrime_of_prime⟩
