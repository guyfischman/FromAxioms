/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Group actions, and orbit-stabiliser.

An action is a set function `G × X → X` respecting the identity and the
operation. The stabiliser of a point is a subgroup, the orbit is an image, and
the two are related by a bijection `G/Stab ≅ Orb` -- which is the first theorem
here that uses Lagrange's counting rather than establishing it.

The bijection is definable: a class determines its image, because two
representatives differ by an element of the stabiliser. No representative is
chosen, so nothing is classical.
-/

import FromAxioms.SetTheory.Relation

universe u

open SetTheory
namespace CategoryTheory

/-! ## The orbit -/

def orbitMap (act x G X : ZFSet.{u}) : ZFSet.{u} := graphOn G X (fun g => opAt act g x)

def orbit (act G X x : ZFSet.{u}) : ZFSet.{u} := imageIn (orbitMap act x G X) G X

end CategoryTheory

namespace ZFSet
export CategoryTheory (orbit orbitMap)
end ZFSet
