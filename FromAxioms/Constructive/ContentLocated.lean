/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The located outer measure as a content

`IsContentOn` asks for the content as a set-level FUNCTION; the located theory
has a RELATION, `LebesgueOuter E L`. `outerContent` (OuterExists.lean) bridges the two
by CONSTRUCTING the value as the infimum pair of the bound family, and
`exists_lebesgueOuter_iff_familyLocatedInf` shows the hypotheses that buys are
necessary rather than merely sufficient.

What is left is the two clauses `outerContent` does not itself supply --
the value at `∅`, and additivity over a disjoint union. Both are hypotheses
about the algebra `A` rather than about the outer measure, so they
appear in the signature: the interface's clauses quantify over members of `A`,
so an instance must say what `A` is closed under, and nothing weaker will do.

Every hypothesis here is discharged by a caller, not by a principle. The
file names no omniscience principle and decides nothing; `hdisj` is CARRIED as
a disjointness fact rather than decided, which is the same trade
`lebesgueOuter_add_of_measurableGe` makes and for the same reason.
-/

-- `NumberTheory` for `ofNat`, `ratNat` and their lemmas: the weak-law rungs
-- below name them throughout, and without the open they auto-bind as local
-- variables rather than failing, which is the quieter half of the failure.
namespace Constructive

/-! ### Nullity for a content, which is what an almost-sure statement needs -/
/-
THE STRONG LAW'S EXCEPTIONAL SET IS NOT A CYLINDER, AND THAT IS A STRUCTURAL
OBSTRUCTION RATHER THAN A GAP IN AN ARGUMENT.

WHAT DOES NOT SOLVE IT. `outerContent` is not a generic content-to-outer-measure
construction: `IsOuterBound` is `MeasuredCover`/`Covers` on rational intervals,
so `outerContent A` is the Lebesgue outer measure restricted to `A` and does not
reach a carrier of bit sequences.

SO NULLITY IS DEFINED HERE, BY FINITE COVERS FROM THE ALGEBRA. A set is null
when for every positive `eps` it is covered by finitely many algebra members
whose contents sum below `eps`. Finiteness is deliberate: a content is finitely
additive, and a definition quantifying over countable covers would be stating a
property the content cannot support.
-/

def walk (lv : Nat → Nat) : Nat → Nat
  | 0 => 0
  | l + 1 => if lv (walk lv l + 1) ≤ l + 1 then walk lv l + 1 else walk lv l

#print axioms walk
end Constructive

namespace ZFSet

end ZFSet
