/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Conjugation, and the road to Sylow.

`Action.lean` builds orbits, stabilisers and orbit-stabiliser, and had no
concrete action to apply them to. Conjugation is the first, and it is the one
Sylow I needs: the class equation counts a group by its conjugacy classes,
whose stabilisers are the centralisers.

Why this route rather than Wielandt's. The subset-counting proof needs
`C(p^a*m, p^a)` to be prime to `p` -- a `p`-adic valuation of a binomial
coefficient, which this library does not have and which is a development in
itself. `Prime.lean` has `choose` and `prime_dvd_choose` (`p` divides `C(p,k)`),
which is a different statement. The class equation needs only orbits and
stabilisers, and it leaves centralisers and conjugacy classes behind as
machinery the rest of group theory wants anyway.
-/

import FromAxioms.SetTheory.Relation

universe u

open SetTheory
namespace Algebra

/-! ## The centre

The class equation splits `G` into the central elements, whose classes are
singletons, and the rest. The centre is where an equation-defined subset stops
being detachable: it is equation-defined like the centraliser, but the equation
quantifies over the group, so deciding membership is a decision over a
quantifier rather than a single comparison. -/

/-- The centre: the elements commuting with everything. -/
def centre (G op : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun g => ∀ h, h ∈ G → opAt op g h = opAt op h g) G

#print axioms centre
end Algebra

namespace ZFSet
export Algebra (centre)
end ZFSet
