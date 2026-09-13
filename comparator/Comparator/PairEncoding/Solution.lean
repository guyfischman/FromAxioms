/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`, RE-EMBEDDED.

THE MATHEMATICS IS `ZFSet.opair_eq_opair_iff` --- the tower's own theorem that
the Kuratowski encoding `opair a b = {{a}, {a,b}}` determines its coordinates.
Its proof is `opair_injective`, four cases through `pair_eq_singleton_iff`, and
nothing about products. That has not changed and is still the whole content of
this pair.

`Prod.mk.injEq` and `Prod.ext` are NOT cited, and no `simp` runs on the goal ---
mathlib's simp set closes the whole challenge from the inductive's own
injectivity, which is precisely the fact this pair exists to avoid using.

WHAT CHANGED IS THE EMBEDDING, NOT THE THEOREM, AND THIS PAIR IS THE ONE ON
THE RE-SITING LIST WHERE THAT WAS THE WHOLE FIX.

The previous version reached `ZFSet` through `Bridge/TypeTransferU.encodeU`,
which is a WELL-ORDERING and an injection --- `embU`, Mostowski's collapse
indexed by `WellOrderingRel`. Well-ordering an arbitrary type IS the axiom of
choice, so the pair's axiom line named `Classical.choice`.

BUT THIS CHALLENGE IS NOT STATED AT AN ARBITRARY TYPE. It is stated at `Nat`,
so that the statement names no bridge vocabulary, as the Challenge's header
explains. `Nat` embeds into `ZFSet` by `NumberTheory.ofNat`, the von Neumann
numerals, with `ofNat_injective` proved by induction. No well-ordering, no
collapse, no choice. The general machinery was being applied to a concrete type
that never needed it.

So this is the one pair of the seven where nothing had to be re-sited: the tower
already had the right embedding, and the Solution reached for the general one.
That is worth naming as its own failure shape --- a bridge built for the hard
case gets used in the easy case because it is the one in scope, and the axiom it
costs is invisible until someone reads the print.

WHAT THE EMBEDDING CONSUMED, AND WHY THIS IS STILL HONEST. `ofNat` and
`ofNat_injective` are about von Neumann numerals and consume NOTHING about
pairs --- not `Prod`, not `opair`, not injectivity of either. So there is no
clause here the embedding could have assumed. A transfer that consumed a fact
about pairs could not then prove one, and this one consumes none.

THE DIRECTION THAT CARRIES THE CONTENT IS THE FORWARD ONE. From the mathlib
equation, `congrArg` builds the ZFSet equation between two Kuratowski pairs;
the tower's theorem splits it; `ofNat_injective` brings both halves back. The
reverse direction is `rfl` on both sides and is not where the mathematics is
--- it is stated because the challenge is an `Iff`, not because it is content.
-/
import Comparator.PairEncoding.Challenge
import FromAxioms.NumberTheory.Natural
-- `opair` AND ITS INJECTIVITY LIVE IN `SetTheory/Pair.lean`, and dropping the
-- `Bridge/TypeTransferU` import dropped the module that was reaching them. The
-- report is `Unknown constant ZFSet.opair`, which reads as a wrong NAME --- it
-- is the right name and an absent module, and the two are indistinguishable
-- from the message.
import FromAxioms.SetTheory.Pair

open SetTheory NumberTheory

namespace Comparator.PairEncoding

/-- The tower's theorem this rests on, named where a reader of this file can
see it. -/
theorem rests_on_opair_eq_opair_iff : True := by
  have _ := @ZFSet.opair_eq_opair_iff.{0}
  trivial

/-- The challenge, from `FromAxioms`, with no well-ordering anywhere. -/
theorem solution : challenge := by
  intro a b c d
  constructor
  · intro h
    -- The mathlib equation, pushed into the tower along the NUMERAL embedding.
    have hz : ZFSet.opair (ofNat.{0} a) (ofNat.{0} b)
        = ZFSet.opair (ofNat.{0} c) (ofNat.{0} d) :=
      congrArg (fun p : Nat × Nat => ZFSet.opair (ofNat.{0} p.1) (ofNat.{0} p.2)) h
    -- THE TOWER'S THEOREM. This is the step mathlib gets from its constructor
    -- and the tower has to prove.
    obtain ⟨h1, h2⟩ := (ZFSet.opair_eq_opair_iff _ _ _ _).mp hz
    exact ⟨ofNat_injective h1, ofNat_injective h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

#print axioms rests_on_opair_eq_opair_iff
#print axioms solution

end Comparator.PairEncoding
