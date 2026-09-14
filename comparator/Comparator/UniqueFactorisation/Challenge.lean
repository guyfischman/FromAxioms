/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
CHALLENGE: uniqueness of the prime factorisation.

Mathlib's vocabulary only. `Mathlib/Data/Nat/Factors.lean:173` at the pin:

    theorem Nat.primeFactorsList_unique {n : ℕ} {l : List ℕ}
        (h₁ : prod l = n) (h₂ : ∀ p ∈ l, Prime p) : l ~ primeFactorsList n

Mathlib's `Nat.factors` family is now `primeFactorsList`; the only
`theorem factors_unique` in the checkout is `UniqueFactorizationMonoid`'s, over
a general monoid.

MATHLIB'S STATEMENT IS RELATIVE TO A CANONICAL LIST. Ours is symmetric --- any
two prime lists with equal products are permutations --- so mathlib's is the
specialisation at `primeFactorsList n`, and that is the direction the solution
takes.
-/
import Mathlib.Data.Nat.Factors

namespace Comparator.UniqueFactorisation

/-- Mathlib's theorem as a closed proposition. -/
def challenge : Prop :=
  ∀ (n : ℕ) (l : List ℕ), l.prod = n → (∀ p ∈ l, Nat.Prime p) →
    l.Perm n.primeFactorsList

/-- `challenge` is Mathlib's theorem, checked by discharging it from Mathlib. -/
theorem challenge_is_mathlibs : challenge :=
  fun _ _ h₁ h₂ => Nat.primeFactorsList_unique h₁ h₂

end Comparator.UniqueFactorisation
