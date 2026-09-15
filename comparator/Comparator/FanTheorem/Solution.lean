/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`.

THE TWO SIDES ARE ASYMMETRIC. `Challenge.lean` writes König's lemma for the
binary tree out in full, because the pinned Mathlib has König's theorem on
CARDINALS and nothing about binary trees. This file is a translation and one
citation, because the tower states the fan theorem as a named principle:

    Constructive.FANΔ : ∀ B, (∀ s, B s ∨ ¬ B s) → IsBar B → IsUniformBar B
    Constructive.fanΔ_of_decider (dec : ∀ q, Decider q) : FANΔ

WHAT THE TWO SIDES SPEND, WHICH IS WHAT THE ROW WANTS MEASURED. Mathlib's proof
DISCARDS the decidability hypothesis --- excluded middle in the foundation
decides every bar --- and spends the classical compactness argument instead.
The tower's `fanΔ_of_decider` spends a decider for every proposition, which is
`Constructive.em_of_decider`'s hypothesis and strictly more than the bar's own
decidability; supplying it here from `Classical.propDecidable` is what makes
`solution` audit with `Classical.choice`. NEITHER SIDE IS FREE, and that is the
honest reading of the row: the fan theorem is a principle in both libraries,
and they differ in where the price is paid rather than in whether it is paid.

`Constructive.Decider` is a `Type`, not a `Prop`, so it cannot be extracted from
an `EM` hypothesis (`Reverse.lean` records why, at the retired
`decider_of_em`). `Classical.propDecidable` is a `Decidable`, which is also a
`Type`, so the conversion below is a match and not a choice principle of its
own.
-/
import Comparator.FanTheorem.Challenge
import FromAxioms.Constructive.Omniscience

namespace Comparator.FanTheorem

/-- The challenge's `take` and the tower's are the same recursion; proved rather
than assumed, since they are different constants. -/
theorem take_eq (α : Nat → Bool) : ∀ n, take α n = Constructive.take α n
  | 0 => rfl
  | n + 1 => by rw [take, Constructive.take, take_eq α n]

/-- Mathlib's decidability, in the tower's `Type`-valued spelling. -/
noncomputable def decider (q : Prop) : Constructive.Decider q :=
  match Classical.propDecidable q with
  | isTrue h => .isTrue h
  | isFalse h => .isFalse h

/-- The challenge, from `FromAxioms`. -/
theorem solution : challenge := by
  intro B hdec hbar
  have hbar' : Constructive.IsBar B := by
    intro α
    obtain ⟨n, hn⟩ := hbar α
    refine ⟨n, ?_⟩
    rw [← take_eq]
    exact hn
  obtain ⟨N, hN⟩ := Constructive.fanΔ_of_decider decider B hdec hbar'
  refine ⟨N, fun α => ?_⟩
  obtain ⟨n, hle, hn⟩ := hN α
  refine ⟨n, hle, ?_⟩
  rw [take_eq]
  exact hn

#print axioms solution

end Comparator.FanTheorem
