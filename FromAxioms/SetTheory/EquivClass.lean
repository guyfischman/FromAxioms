/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Equivalence classes and quotient sets.

The set-theoretic quotient, built without choice. The class of `a` is carved out
of `x` by separation, and the quotient is carved out of `𝒫 x` -- every class is
a subset of `x`, so the power set bounds the construction and Replacement is not
needed.

`cls_eq_cls_iff` states it: two classes are equal as sets exactly when their
representatives are related. That is what lets a quotient stand in for the
relation.
-/

import FromAxioms.SetTheory.Pair

universe u

namespace SetTheory

structure IsEquivRel (r x : ZFSet.{u}) : Prop where
  refl : ∀ a, a ∈ x → opair a a ∈ r
  symm : ∀ a b, a ∈ x → b ∈ x → opair a b ∈ r → opair b a ∈ r
  trans : ∀ a b c, a ∈ x → b ∈ x → c ∈ x →
    opair a b ∈ r → opair b c ∈ r → opair a c ∈ r

end SetTheory

namespace ZFSet
export SetTheory (IsEquivRel)
end ZFSet
