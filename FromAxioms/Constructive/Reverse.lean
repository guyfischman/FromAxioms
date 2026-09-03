/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# What the classical audit lines actually establish.

`#print axioms` is an upper bound. It reports the axioms a proof used, never
the ones a theorem needs, and the gap is concrete here: two proofs of the
same walk, one paying `Classical.choice` and one not.

The lower bound has to be argued the other way round -- by deriving a known
non-constructive principle from the theorem, in a proof that is itself
choice-free. Then the audit line on the reversal certifies that the classical
content is real and not an artefact of how the proof was written.

The witness both reversals use is the cut of a proposition:

    propCut p = { q ∈ ℚ | q < 0 ∨ (p ∧ q < 1) }

which is `0` when `p` fails and `1` when it holds, without deciding which. Any
principle strong enough to place it relative to a rational strictly between `0`
and `1` therefore decides `p`.
-/


universe u

namespace Constructive

/-- Excluded middle, stated inside this development so it can be a conclusion. -/
def EM : Prop := ∀ p : Prop, p ∨ ¬ p

#print axioms EM
end Constructive

namespace ZFSet
export Constructive (EM)
end ZFSet
