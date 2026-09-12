/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The tower law by exchange.

`Module.lean`'s `dim_tower` proves `[M:K] = [L:K]·[M:L]` by counting: it needs
`K` finite and, because it never relates the three actions, no compatibility
between them at all. That makes it more general than a structural proof, not
less -- and useless over an infinite base.

This file builds the other theorem. For a tower of subrings `K ⊆ L ⊆ M` every
action is the ambient multiplication restricted, so the compatibilities are
theorems rather than hypotheses, and the products of the two bases can be shown
to be a basis. What it costs instead of finiteness is `DecidableVanishing K`,
which `exchange_le` already requires and which ℚ satisfies.
-/

import FromAxioms.Algebra.LinAlg
import FromAxioms.Algebra.Module
import FromAxioms.Constructive.Vanishing

universe u

open NumberTheory SetTheory
namespace Algebra

/-! ## Coordinates

A basis of length `d` writes every vector as a tuple in `R^d`. The list of
coefficients comes from `spanSet = V`, which is an EXISTENCE statement, so
nothing here can be a definition -- the same constraint `exists_round` records,
so the transport ahead is a theorem about a disjunction rather than a map. -/

theorem tupleToList_vecAdd (add : ZFSet.{u}) {d : Nat} (x y : ZFSet.{u}) :
    tupleToList (vecAdd add d x y) d
      = List.zipWith (opAt add) (tupleToList x d) (tupleToList y d) := by
  refine List.ext_getElem
    (by rw [tupleToList_length, List.length_zipWith, tupleToList_length, tupleToList_length,
      Nat.min_self]) (fun i h₁ h₂ => ?_)
  have hi : i < d := by rw [tupleToList_length] at h₁; exact h₁
  rw [tupleToList_getElem, List.getElem_zipWith, tupleToList_getElem, tupleToList_getElem,
    coeff_vecAdd i hi]

#print axioms tupleToList_vecAdd
end Algebra


namespace ZFSet
export Algebra (tupleToList_vecAdd)
end ZFSet
