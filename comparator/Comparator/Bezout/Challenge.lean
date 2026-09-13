/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
CHALLENGE: Bezout's identity.

Mathlib's vocabulary only. `Mathlib/Data/Int/GCD.lean:126`:

    theorem Nat.gcd_eq_gcd_ab : (gcd x y : ℤ) = x * gcdA x y + y * gcdB x y

MATHLIB NAMES ITS WITNESSES AND THIS CHALLENGE DOES NOT, which is a real
difference and is stated rather than papered over. `gcdA` and `gcdB` are computed
by the extended Euclidean algorithm; the challenge asks only that coefficients
EXIST. `challenge_is_mathlibs` below closes that gap in the direction that
matters here --- mathlib's named witnesses inhabit the existential --- so the
challenge is a consequence of mathlib's theorem and not a weakening dressed up as
one. The row's `at_parity` records that mathlib additionally provides the
witnesses as computable functions.
-/
import Mathlib.Data.Int.GCD

namespace Comparator.Bezout

/-- Bezout's identity as a closed proposition, over Lean's own `Nat` and `Int`
--- the same objects on both sides, with nothing transferred. -/
def challenge : Prop :=
  ∀ x y : ℕ, ∃ u v : ℤ, (Nat.gcd x y : ℤ) = (x : ℤ) * u + (y : ℤ) * v

/-- `challenge` follows from Mathlib's theorem, with `gcdA` and `gcdB` as the
witnesses. This says nothing about the tower; `Solution.lean` does that. -/
theorem challenge_is_mathlibs : challenge :=
  fun x y => ⟨Nat.gcdA x y, Nat.gcdB x y, Nat.gcd_eq_gcd_ab x y⟩

end Comparator.Bezout
