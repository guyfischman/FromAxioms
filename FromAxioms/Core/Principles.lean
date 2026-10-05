/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The three logical principles, stated where every layer can name them.

`EM` and `WEM` need no import at all, so they live at the bottom of the tree,
where a module below `Constructive/Reverse.lean` in the import order can name
them in a binder instead of spelling them out. The namespace is `Constructive`.
-/

namespace Constructive

/-- Excluded middle, stated inside this development so it can be a conclusion. -/
def EM : Prop := ∀ p : Prop, p ∨ ¬ p

/-- Weak excluded middle, the target for `sdiff_inter`, which is de Morgan's
third law and strictly weaker than `EM`. -/
def WEM : Prop := ∀ p : Prop, ¬ p ∨ ¬ ¬ p

#print axioms EM
#print axioms WEM
end Constructive
