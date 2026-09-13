/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`.

`NumberTheory.exists_prime_ge (n : Nat) : ∃ p, IsPrime p ∧ n ≤ p` is the whole
of it. Both sides quantify over Lean's `Nat`, so nothing is transferred; the only
step is `Comparator.Bridge.NatPrime`, which sends our primality to Mathlib's.

Mathlib's `Nat.exists_infinite_primes` is not cited.
-/
import Comparator.InfinitudePrimes.Challenge
import Comparator.Bridge.NatPrime
import FromAxioms

namespace Comparator.InfinitudePrimes

open NumberTheory

theorem solution : challenge := by
  intro n
  obtain ⟨p, hp, hle⟩ := exists_prime_ge n
  exact ⟨p, hle, prime_of_isPrime hp⟩

end Comparator.InfinitudePrimes
