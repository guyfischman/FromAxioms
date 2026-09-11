/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
CHALLENGE: the irrationality of the square root of a prime.

Mathlib's vocabulary only. This file imports Mathlib and nothing else, so the
statement below is not ours. `Mathlib/RingTheory/Real/Irrational.lean:131`:

    theorem Nat.Prime.irrational_sqrt {p : ℕ} (hp : Nat.Prime p) : Irrational (√p)

with, at line 31 of the same file,

    def Irrational (x : ℝ) := x ∉ Set.range ((↑) : ℚ → ℝ)
-/
import Mathlib.RingTheory.Real.Irrational

namespace Comparator.IrrationalSqrtPrime

/-- Mathlib's theorem as a closed proposition, at Mathlib's generality: every
prime, not 2 alone. -/
def challenge : Prop :=
  ∀ p : ℕ, Nat.Prime p → Irrational (Real.sqrt (p : ℝ))

/-- `challenge` is Mathlib's theorem and not a lookalike, checked by discharging
it from Mathlib. This says nothing about the tower; `Solution.lean` does that. -/
theorem challenge_is_mathlibs : challenge :=
  fun _ hp => hp.irrational_sqrt

end Comparator.IrrationalSqrtPrime
