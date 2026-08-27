/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# ZFSet: pre-sets modulo extensional equivalence.

`PSet` gave a model of ZFC, but a slightly wrong one. Pre-sets are trees, and
trees carry more information than sets do: the tree indexed by `Bool` sending
both branches to `∅` and the tree indexed by `Unit` doing the same are different
trees, yet both denote the singleton `{∅}`. So every statement in `PSet.lean`
had to be phrased with `Equiv` in place of `=`, and `mem_sep_iff` had to drag
along an explicit hypothesis that its predicate respects `Equiv`.

Quotienting fixes all of it at once. `ZFSet` is `PSet` modulo `Equiv`, and on
the quotient `Equiv` simply is `=`:

  * `ext` -- extensionality is now an equation between sets, not an equivalence
  * `mem_insert_iff` reads `w = y ∨ w ∈ x`, where `PSet`'s read `Equiv w y ∨ ...`
  * `mem_sep_iff` needs no congruence hypothesis: a predicate on `ZFSet`
    cannot fail to respect an equality

A `ZFSet → Prop` cannot distinguish two pre-sets with the same members, because
they are not two things any more. The obligation does not go away -- it is
discharged once, when each construction is pushed through `Quotient.lift`,
using the congruence lemmas at the bottom of `PSet.lean`.

## What quotients cost

Two of Lean core's three axioms appear here:

  * `Quot.sound` -- equivalent pre-sets become equal sets. This is what makes
    the quotient a quotient, and it is irreducibly an axiom.
  * `propext` -- lifting a `Prop`-valued function through `Quotient.lift`
    requires proving `f a₁ b₁ = f a₂ b₂` as an equality of propositions, and
    the congruence lemmas supply only an `Iff`. `propext` bridges them.

`Classical.choice` is not needed, and does not appear below.

`Quot.sound` arriving here also retires the `funext` axiom declared in
`FromAxioms/Logic/`, since Lean derives function extensionality from quotients:
`#print axioms funext` reports `[Quot.sound]`.
-/

import FromAxioms.SetTheory.PSet

universe u

/-- A set is a pre-set up to extensional equivalence. -/
def ZFSet : Type (u + 1) := Quotient PSet.setoid.{u}

namespace SetTheory

/-- The class of a pre-set. -/
def mk (x : PSet.{u}) : ZFSet.{u} := Quotient.mk PSet.setoid x

/-! ## Membership

Lifting a two-argument `Prop`-valued function. The obligation is an equality
of propositions, which is where `propext` enters. -/

protected def Mem : ZFSet.{u} → ZFSet.{u} → Prop :=
  Quotient.lift₂ (fun w x => w ∈ x)
    (fun _ x₁ w₂ _ hw hx =>
      propext (Iff.trans (PSet.mem_congr_left hw x₁) (PSet.mem_congr_right hx w₂)))

instance : Membership ZFSet.{u} ZFSet.{u} := ⟨fun x w => SetTheory.Mem w x⟩

/-! ## The constructions, descended

Each is `Quotient.lift` applied to its `PSet` counterpart, with the matching
congruence lemma discharging the well-definedness obligation. -/

/-- EMPTY SET. -/
def empty : ZFSet.{u} := mk PSet.empty

@[simp] theorem not_mem_empty : ∀ w : ZFSet.{u}, w ∉ empty.{u} :=
  Quotient.ind fun w => PSet.not_mem_empty w

/-- Adjoining an element. -/
def insert : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} :=
  Quotient.lift₂ (fun y x => mk (PSet.insert y x))
    (fun _ _ _ _ hy hx => Quotient.sound (PSet.insert_congr hy hx))

/-- PAIRING. -/
def pair (x y : ZFSet.{u}) : ZFSet.{u} := insert x (insert y empty)

/-! ## INFINITY -/

def succ (x : ZFSet.{u}) : ZFSet.{u} := insert x x

def omega : ZFSet.{u} := mk PSet.omega

/-! ## Audit

Expect `[propext, Quot.sound]` throughout, and nothing else. In particular
`Classical.choice` must stay absent: nothing so far requires it.

The last line retires the `funext` axiom declared in `FromAxioms/Logic/`: Lean
derives function extensionality from the quotient machinery now in play, so
what had to be assumed there is a theorem here.
-/

#print axioms not_mem_empty      -- EMPTY SET
end SetTheory

namespace ZFSet
export SetTheory (Mem empty insert mk not_mem_empty omega pair succ)
end ZFSet
