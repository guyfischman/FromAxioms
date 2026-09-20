/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The located outer measure as a content

`IsContentOn` asks for the content as a set-level function; the located theory
has a relation, `LebesgueOuter E L`. `outerContent` (OuterExists.lean) bridges the two
by constructing the value as the infimum pair of the bound family, and
`exists_lebesgueOuter_iff_familyLocatedInf` shows the hypotheses that buys are
necessary rather than merely sufficient.

What is left is the two clauses `outerContent` does not itself supply --
the value at `∅`, and additivity over a disjoint union. Both are hypotheses
about the algebra `A` rather than about the outer measure, so they
appear in the signature: the interface's clauses quantify over members of `A`,
so an instance must say what `A` is closed under, and nothing weaker will do.

Every hypothesis here is discharged by a caller, not by a principle. The
file names no omniscience principle and decides nothing; `hdisj` is carried as
a disjointness fact rather than decided, which is the same trade
`lebesgueOuter_add_of_measurableGe` makes and for the same reason.
-/

-- `NumberTheory` for `ofNat`, `ratNat` and their lemmas: the weak-law rungs
-- below name them throughout, and without the open they auto-bind as local
-- variables rather than failing, which is the quieter half of the failure.
namespace Constructive

/-! ### Nullity for a content, which is what an almost-sure statement needs -/
/-
The strong law's exceptional set is not a cylinder, and that is a structural
obstruction rather than a gap in an argument.

What does not solve it. `outerContent` is not a generic content-to-outer-measure
construction: `IsOuterBound` is `MeasuredCover`/`Covers` on rational intervals,
so `outerContent A` is the Lebesgue outer measure restricted to `A` and does not
reach a carrier of bit sequences.

So nullity is defined here, by finite covers from the algebra. A set is null
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
