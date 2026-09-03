/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Cantor's theorem.

The diagonal argument at the level of sets: no function from `x` reaches every
subset of `x`. The witness is the set of members that miss themselves,

    diagonal F x = { a ∈ x | a ∉ F a }

and if some `a ∈ x` had `F a = diagonal F x`, then `a` would belong to that set
exactly when it did not.

The argument is constructive. It never splits on whether `a ∈ F a`; it derives
`a ∉ diagonal F x` outright, and then derives membership from the same
hypothesis. `Not` is doing all the work, so no axiom is needed --
compare `regularity`, where the existence half needed excluded middle.

`F` here is an arbitrary function on sets rather than a `Definable` one. That
costs nothing: the theorem says a certain subset is missed, so quantifying
over more functions makes it stronger, and unlike `image` it never has to build
anything from `F`.
-/

import FromAxioms.SetTheory.ZFSet

universe u

namespace SetTheory

/-- The members of `x` that are not in their own image. -/
def diagonal (F : ZFSet.{u} → ZFSet.{u}) (x : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun a => a ∉ F a) x

end SetTheory

namespace ZFSet
export SetTheory (diagonal)
end ZFSet
