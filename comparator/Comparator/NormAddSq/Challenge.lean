/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
CHALLENGE: expanding the square of a norm in a real inner product space.

Mathlib's vocabulary only. `Mathlib/Analysis/InnerProductSpace/Basic.lean:390`,
under the section variables at lines 349-350:

    variable {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace R F]

    theorem norm_add_sq_real (x y : F) :
      ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_R + ‖y‖ ^ 2

`⟪x, y⟫_R` is `inner R x y`, from the scoped notation at
`InnerProductSpace/Defs.lean:87`; it is spelled out here because this file opens
no notation namespace.

The carrier is SEMINORMED, not normed, which is weaker and is what the theorem is
actually stated over. The challenge takes it as Mathlib gives it.
-/
import Mathlib.Analysis.InnerProductSpace.Basic

namespace Comparator.NormAddSq

universe u

/-- Mathlib's theorem as a closed proposition, quantified over every real inner
product space rather than any fixed one. -/
def challenge : Prop :=
  ∀ (F : Type u) [SeminormedAddCommGroup F] [InnerProductSpace ℝ F] (x y : F),
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x y + ‖y‖ ^ 2

/-- `challenge` is Mathlib's theorem, checked by discharging it from Mathlib.
This says nothing about the tower; `Solution.lean` does that. -/
theorem challenge_is_mathlibs : challenge :=
  fun _ _ _ x y => norm_add_sq_real x y

end Comparator.NormAddSq
