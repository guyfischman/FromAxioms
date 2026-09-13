/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
CHALLENGE: Euclid's theorem on the infinitude of primes.

Mathlib's vocabulary only. `Mathlib/Data/Nat/Prime/Infinite.lean:29`, inside
`namespace Nat`, so the bare `Prime` there is `Nat.Prime`:

    theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ Prime p
-/
import Mathlib.Data.Nat.Prime.Infinite

namespace Comparator.InfinitudePrimes

/-- Mathlib's theorem as a closed proposition. -/
def challenge : Prop :=
  ∀ n : ℕ, ∃ p, n ≤ p ∧ Nat.Prime p

/-- `challenge` is Mathlib's theorem, checked by discharging it from Mathlib.
This says nothing about the tower; `Solution.lean` does that. -/
theorem challenge_is_mathlibs : challenge :=
  Nat.exists_infinite_primes

end Comparator.InfinitudePrimes
