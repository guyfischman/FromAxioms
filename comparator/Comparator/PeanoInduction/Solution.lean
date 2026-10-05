/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`.

The mathematics is `SetTheory.omega_isPeano.induct` --- the second-order
induction clause of the tower's `IsPeano`, proved for `omega` with `empty` and
`graphOn omega omega succ`. Nothing here uses Lean's `Nat.rec`, and the proof
runs no `induction` tactic.

What the bridge consumed and why this is still honest. Nothing: this Solution
uses no transfer bridge at all. `ofNat` is the tower's own map `Nat → omega`,
and the only facts about it are `ofNat_zero`, `ofNat_succ` (both `rfl`),
`ofNat_mem_omega` and `ofNat_injective` --- none of which is Lean's induction
principle. There is therefore no clause the challenge could be circular
against.

The content is the subset/predicate gap. `induct` quantifies over a set
`S ⊆ omega`; the challenge quantifies over a Lean predicate `S : Nat → Prop`.
`sep` is what bridges them --- separation carves the predicate's extension out of
`omega` --- and the existential spelling

    T := sep (fun x => ∃ n, x = ofNat n ∧ S n) omega

is used rather than `S (toNat x _)` because `toNat` needs a membership proof and
so cannot appear inside a Lean function of `x` alone. Writing it this way needs
no total `toNat` and no new bridge rung.
-/
import Comparator.PeanoInduction.Challenge
import FromAxioms.SetTheory.Relation

open SetTheory NumberTheory

namespace Comparator.PeanoInduction

/-- The tower's theorem this rests on, named where a reader of this file can
see it. -/
theorem rests_on_omega_isPeano : True := by
  have _ := @SetTheory.omega_isPeano.{0}
  trivial

/-- The challenge, from `FromAxioms`. -/
theorem solution : challenge := by
  intro S h0 hs n
  -- The predicate's extension inside `omega`, as a set --- the step the tower's
  -- second-order `induct` needs and Lean's `Nat.rec` never does. It is written
  -- out at each use rather than bound, since `set` is a Mathlib tactic and this
  -- file imports no Mathlib.
  have key : sep (fun x => ∃ m : Nat, x = ofNat.{0} m ∧ S m) omega.{0}
      = omega.{0} := by
    -- The tower's theorem.
    refine omega_isPeano.induct _ (fun w hw => ((mem_sep_iff _ w _).mp hw).left)
      ?_ ?_
    · exact (mem_sep_iff _ _ _).mpr ⟨empty_mem_omega, 0, ofNat_zero.symm, h0⟩
    · intro x hx
      obtain ⟨hxo, m, rfl, hSm⟩ := (mem_sep_iff _ x _).mp hx
      rw [app_graphOn succ_mem_omega hxo]
      exact (mem_sep_iff _ _ _).mpr
        ⟨succ_mem_omega _ hxo, m + 1, (ofNat_succ m).symm, hs m hSm⟩
  -- Read the conclusion back at `ofNat n`.
  have hmem : ofNat.{0} n
      ∈ sep (fun x => ∃ m : Nat, x = ofNat.{0} m ∧ S m) omega.{0} := by
    rw [key]; exact ofNat_mem_omega n
  obtain ⟨-, m, hEq, hSm⟩ := (mem_sep_iff _ _ _).mp hmem
  have hnm : n = m := ofNat_injective hEq
  rw [hnm]
  exact hSm

#print axioms rests_on_omega_isPeano
#print axioms solution

end Comparator.PeanoInduction
