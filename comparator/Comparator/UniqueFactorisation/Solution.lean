/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`.

    NumberTheory.factorization_perm : ∀ l₁ l₂ : List Nat,
      (∀ p ∈ l₁, IsPrime p) → (∀ p ∈ l₂, IsPrime p) →
      prodList l₁ = prodList l₂ → l₁.Perm l₂

OURS IS THE SYMMETRIC FORM AND THE STRONGER OF THE TWO. mathlib's statement is
relative to the canonical `primeFactorsList n`; ours mentions no canonical list
at all, so mathlib's is the instance at `l₂ := primeFactorsList n`. Nothing has
to be transferred --- both sides are over Lean's `Nat`.

TWO BRIDGING STEPS.

  * `prodList` versus `List.prod`: the same fold under two names, bridged by
    `prodList_eq_prod`, which takes no axioms.
  * THE ZERO CASE. `primeFactorsList 0` is empty, so `prod_primeFactorsList`
    carries a positivity hypothesis. It is discharged rather than assumed:
    `l.prod = 0` puts `0` in `l`, and `0` is not prime.

`Nat.primeFactorsList_unique` is not cited.
-/
import Comparator.UniqueFactorisation.Challenge
import Comparator.Bridge.NatPrime
import FromAxioms

namespace Comparator.UniqueFactorisation

/-- Our `prodList` is mathlib's `List.prod`. Both fold `1` and `*` down the
list; the recursions agree step by step. -/
theorem prodList_eq_prod : ∀ l : List Nat, NumberTheory.prodList l = l.prod
  | [] => rfl
  | p :: t => by
    show p * NumberTheory.prodList t = (p :: t).prod
    rw [prodList_eq_prod t, List.prod_cons]

theorem solution : challenge := by
  intro n l h₁ h₂
  refine NumberTheory.factorization_perm l n.primeFactorsList
    (fun p hp => isPrime_of_prime (h₂ p hp))
    (fun p hp => isPrime_of_prime (Nat.prime_of_mem_primeFactorsList hp)) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `List.prod_eq_zero_iff` gives `0 ∈ l` directly, and `0` is not prime
    exact absurd (h₂ 0 (List.prod_eq_zero_iff.mp h₁)) Nat.not_prime_zero
  · rw [prodList_eq_prod, prodList_eq_prod, h₁,
      Nat.prod_primeFactorsList (by omega)]

end Comparator.UniqueFactorisation
