/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Categories.

A category, single-sorted: a set `Ob` of objects, a set `Ar` of arrows, two set
functions `src` and `tgt` giving each arrow its endpoints, a partial binary
composition, and a set function `ids` naming each object's identity. The laws
are clauses, in the shape `Ring.lean` and `Group.lean` use for `IsRing` and
`IsMonoid`; composition is written `opAt comp g f`, which is `IsMonoid`'s
`opAt op a b` at a different reading.

The hom-set is derived -- `homSet Ar src tgt a b` is a separation over `Ar`
-- rather than primitive. Both halves of that choice matter: the two-sorted
presentation makes composition a seven-argument relation or else forces
hom-sets to be disjoint, which is false for the thin categories this tree can
most cheaply reach.

The first instance is not a stub. A monoid is a category with one object,
and composition is the monoid operation unchanged -- so `Group.lean`'s
`isGroup_intAdd` gives ℤ-under-addition as a concrete category with no new
construction at all.

Everything here is `[propext, Quot.sound]`. The clauses are stated over
composable arrows, and composability is a hypothesis rather than a decision.
What a decision would cost is measured in `CategoryStrength.lean`, and the
answer is not where the definition's shape suggests: partiality is free, and it
is deciding ISOMORPHISM that reverses to `WLPO`.
-/

import FromAxioms.SetTheory.Relation

universe u

open SetTheory
namespace CategoryTheory

/-! ## Hom-sets

Derived, not primitive. `sep` on `ZFSet` takes a Lean-level predicate with no
definability side condition, so this costs nothing and its membership lemma is
`mem_sep_iff` unchanged. -/

/-- The arrows from `a` to `b`. -/
def homSet (Ar src tgt a b : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun f => app src f = a ∧ app tgt f = b) Ar

/-! ## Products

An object with two projections through which every competing pair factors,
uniquely. Like `IsTerminal` the definition takes no `ids` -- the identity is
what the CONSEQUENCES need, not what the statement says. Unlike `IsTerminal` it
does take `comp`, because the factoring equations are about composition. -/

def IsProduct (Ob Ar src tgt comp x y p p1 p2 : ZFSet.{u}) : Prop :=
  p ∈ Ob ∧ p1 ∈ homSet Ar src tgt p x ∧ p2 ∈ homSet Ar src tgt p y ∧
    ∀ q, q ∈ Ob → ∀ f, f ∈ homSet Ar src tgt q x → ∀ g, g ∈ homSet Ar src tgt q y →
      ∃ h, h ∈ homSet Ar src tgt q p ∧ opAt comp p1 h = f ∧ opAt comp p2 h = g ∧
        ∀ k, k ∈ homSet Ar src tgt q p →
          opAt comp p1 k = f → opAt comp p2 k = g → k = h

/-- THE PRODUCT'S UNIVERSAL PROPERTY OVER LEAN TYPES.

`IsProduct` above is the categorical statement, stated over a ZFSet category
--- objects, arrows, `homSet` membership and `opAt`. This is the same universal
property where the objects are Lean TYPES and the arrows are Lean functions, so
every `homSet` binder disappears and `opAt comp p1 h` becomes `p₁ ∘ h`.

THE PRODUCT IS NOT `Prod`; IT IS ANY `P` WITH TWO PROJECTIONS, A PAIRING AND
THE THREE EQUATIONS. So this is a universal property rather than a fact about
one inductive type --- proved about `Prod` alone, the uniqueness half is just
`Prod.ext`, which is the constructor fact and not the theorem.

    h1     p₁ (pr a b) = a
    h2     p₂ (pr a b) = b
    heta   pr (p₁ w) (p₂ w) = w

Existence is `fun z => pr (f z) (g z)`, and uniqueness is `heta` read once: a
`k` with the right projections satisfies `k z = pr (p₁ (k z)) (p₂ (k z))`.

UNIQUENESS IS POINTWISE, `∀ z, k z = h z`, AND THAT IS DELIBERATE. The
equality-of-FUNCTIONS form needs `funext`, which is `Quot.sound`-priced here.
Pointwise is the same content at NO AXIOMS, and a consumer that wants the
function equality applies `funext` itself --- putting the cost at the call site
rather than in this tower, which is where it belongs.
-/
theorem prodT_universal {α β Z P : Type u}
    (p₁ : P → α) (p₂ : P → β) (pr : α → β → P)
    (h1 : ∀ a b, p₁ (pr a b) = a) (h2 : ∀ a b, p₂ (pr a b) = b)
    (heta : ∀ w, pr (p₁ w) (p₂ w) = w)
    (f : Z → α) (g : Z → β) :
    ∃ h : Z → P,
      (∀ z, p₁ (h z) = f z) ∧ (∀ z, p₂ (h z) = g z) ∧
      ∀ k : Z → P, (∀ z, p₁ (k z) = f z) → (∀ z, p₂ (k z) = g z) →
        ∀ z, k z = h z := by
  refine ⟨fun z => pr (f z) (g z), fun z => h1 _ _, fun z => h2 _ _, ?_⟩
  intro k hk1 hk2 z
  -- the only step: `k z` is its own pairing, and its components are `f z`, `g z`
  rw [← heta (k z), hk1 z, hk2 z]

#print axioms prodT_universal

end CategoryTheory

namespace ZFSet
export CategoryTheory (IsProduct homSet prodT_universal)
end ZFSet
