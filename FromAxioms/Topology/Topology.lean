/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Topological spaces.

A topology on a set `X` is a family of subsets containing `∅` and `X`, closed
under pairwise intersection and under arbitrary union. Everything here is
constructive: an arbitrary union is `sUnion` of a subfamily, which the axioms
already provide, and no separation axiom is assumed unless it is named.
-/

import FromAxioms.SetTheory.Pair

universe u

open SetTheory
namespace Topology

/-! ## The specialisation order

The up-set topology remembers the relation it came from: `a` is in every open
containing... rather, every open containing `a` contains `b` exactly when `a`
relates to `b`. So `upSets` and `spec` are inverse on preorders, which is the
Alexandrov correspondence in the one direction this file can state without a
category.

Only reflexivity and transitivity are used, and each is used once:
transitivity to make the principal up-set open, reflexivity to put `a` in it.
-/

/-- `a` specialises to `b` when every open containing `a` contains `b`. -/
def spec (T X : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => ∀ U, U ∈ T → fst z ∈ U → snd z ∈ U) (prod X X)

end Topology
namespace ZFSet
export Topology (spec)
end ZFSet
