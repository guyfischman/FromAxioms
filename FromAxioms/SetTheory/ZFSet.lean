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

/-- The defining property of the quotient: equality of classes is equivalence
of representatives. Lean core has no `Quotient.eq`, so this is assembled from
`Quotient.exact` and `Quotient.sound`. -/
theorem mk_eq_mk {x y : PSet.{u}} : mk x = mk y ↔ PSet.Equiv x y :=
  ⟨fun h => Quotient.exact (s := PSet.setoid) h,
   fun h => Quotient.sound (s := PSet.setoid) h⟩

/-! ## Membership

Lifting a two-argument `Prop`-valued function. The obligation is an equality
of propositions, which is where `propext` enters. -/

protected def Mem : ZFSet.{u} → ZFSet.{u} → Prop :=
  Quotient.lift₂ (fun w x => w ∈ x)
    (fun _ x₁ w₂ _ hw hx =>
      propext (Iff.trans (PSet.mem_congr_left hw x₁) (PSet.mem_congr_right hx w₂)))

instance : Membership ZFSet.{u} ZFSet.{u} := ⟨fun x w => SetTheory.Mem w x⟩

instance : HasSubset ZFSet.{u} := ⟨fun x y => ∀ w : ZFSet.{u}, w ∈ x → w ∈ y⟩

/-- `ZFSet` is a `def` for a `Quotient`, so unification will happily unfold it
and then fail to find the `Membership ZFSet ZFSet` instance. Supplying the
motive explicitly, at type `ZFSet`, keeps instance resolution on the rails. -/
theorem mk_subset_mk (w x : PSet.{u}) : mk w ⊆ mk x ↔ w ⊆ x := by
  constructor
  · intro h z hz
    exact h (mk z) hz
  · intro h
    show ∀ z : ZFSet.{u}, z ∈ mk w → z ∈ mk x
    exact Quotient.ind (motive := fun z : ZFSet.{u} => z ∈ mk w → z ∈ mk x)
      (fun z hz => h z hz)

/-! ## EXTENSIONALITY, as an equation

The payoff. On `PSet` this was `Equiv x y ↔ ∀ w, w ∈ x ↔ w ∈ y`. Here the
left-hand side is genuine equality, so two sets with the same members are
interchangeable everywhere, by `rfl`-style rewriting rather than by threading a
congruence lemma through every step. -/

theorem ext (x y : ZFSet.{u}) (h : ∀ z : ZFSet.{u}, z ∈ x ↔ z ∈ y) : x = y :=
  Quotient.inductionOn₂
    (motive := fun x y : ZFSet.{u} => (∀ z : ZFSet.{u}, z ∈ x ↔ z ∈ y) → x = y) x y
    (fun a b hab => Quotient.sound ((PSet.equiv_iff_ext a b).mpr (fun w => hab (mk w)))) h

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

/-- Note `w = y`, where the `PSet` version had `Equiv w y`. -/
theorem mem_insert_iff (w y x : ZFSet.{u}) : w ∈ insert y x ↔ w = y ∨ w ∈ x :=
  Quotient.inductionOn₃ w y x fun w y x =>
    ⟨fun h => ((PSet.mem_insert_iff w y x).mp h).imp Quotient.sound id,
     fun h => (PSet.mem_insert_iff w y x).mpr (h.imp Quotient.exact id)⟩

/-- PAIRING. -/
def pair (x y : ZFSet.{u}) : ZFSet.{u} := insert x (insert y empty)

theorem mem_pair_iff (w x y : ZFSet.{u}) : w ∈ pair x y ↔ w = x ∨ w = y := by
  refine Iff.trans (mem_insert_iff w x (insert y empty)) ?_
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · rcases (mem_insert_iff w y empty).mp h with h' | h'
      · exact Or.inr h'
      · exact absurd h' (not_mem_empty w)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ((mem_insert_iff w y empty).mpr (Or.inl h))

/-- UNION. -/
def sUnion : ZFSet.{u} → ZFSet.{u} :=
  Quotient.lift (fun x => mk (PSet.sUnion x))
    (fun _ _ h => Quotient.sound (PSet.sUnion_congr h))

theorem mem_sUnion_iff (w x : ZFSet.{u}) :
    w ∈ sUnion x ↔ ∃ z : ZFSet.{u}, z ∈ x ∧ w ∈ z := by
  refine Quotient.inductionOn₂ w x (fun w x => ?_)
  constructor
  · intro h
    obtain ⟨z, hzx, hwz⟩ := (PSet.mem_sUnion_iff w x).mp h
    exact ⟨mk z, hzx, hwz⟩
  · rintro ⟨z, hzx, hwz⟩
    obtain ⟨z, rfl⟩ := Quotient.exists_rep z
    exact (PSet.mem_sUnion_iff w x).mpr ⟨z, hzx, hwz⟩

/-- POWER SET. -/
def powerset : ZFSet.{u} → ZFSet.{u} :=
  Quotient.lift (fun x => mk (PSet.powerset x))
    (fun _ _ h => Quotient.sound (PSet.powerset_congr h))

theorem mem_powerset_iff (w x : ZFSet.{u}) : w ∈ powerset x ↔ w ⊆ x :=
  Quotient.inductionOn₂ w x fun w x =>
    Iff.trans (PSet.mem_powerset_iff w x) (mk_subset_mk w x).symm

/-! ### SEPARATION, without a side condition

The reason the quotient was worth building. `PSet.mem_sep_iff` required a proof
that `p` respects `Equiv`; here `p : ZFSet → Prop` and no such hypothesis is
possible to state, let alone required. The obligation is discharged once, in
`sep` below, and never again. -/

/-- Separation: the subset carved out by a predicate. This is Zermelo's
axiom, the one that makes axiomatic set theory consistent where naive
comprehension is not. -/
def sep (p : ZFSet.{u} → Prop) : ZFSet.{u} → ZFSet.{u} :=
  Quotient.lift (fun x => mk (PSet.sep (fun z => p (mk z)) x))
    (fun _ _ h =>
      Quotient.sound (PSet.sep_congr (fun hab hpa => mk_eq_mk.mpr hab ▸ hpa) h))

theorem mem_sep_iff (p : ZFSet.{u} → Prop) (w x : ZFSet.{u}) :
    w ∈ sep p x ↔ w ∈ x ∧ p w :=
  Quotient.inductionOn₂ w x fun w x =>
    PSet.mem_sep_iff (fun hab hpa => mk_eq_mk.mpr hab ▸ hpa) w x

/-! ## INFINITY -/

def succ (x : ZFSet.{u}) : ZFSet.{u} := insert x x

def omega : ZFSet.{u} := mk PSet.omega

theorem empty_mem_omega : empty.{u} ∈ omega.{u} := PSet.empty_mem_omega

/-! ## Audit

Expect `[propext, Quot.sound]` throughout, and nothing else. In particular
`Classical.choice` must stay absent: nothing so far requires it.

The last line retires the `funext` axiom declared in `FromAxioms/Logic/`: Lean
derives function extensionality from the quotient machinery now in play, so
what had to be assumed there is a theorem here.
-/

#print axioms ext                -- EXTENSIONALITY, as equality
#print axioms not_mem_empty      -- EMPTY SET
#print axioms mem_pair_iff       -- PAIRING
#print axioms mem_sUnion_iff     -- UNION
#print axioms mem_powerset_iff   -- POWER SET
#print axioms mem_sep_iff        -- SEPARATION, hypothesis-free
end SetTheory

namespace ZFSet
export SetTheory (Mem empty empty_mem_omega ext insert mem_insert_iff mem_pair_iff mem_powerset_iff mem_sUnion_iff mem_sep_iff mk mk_eq_mk mk_subset_mk not_mem_empty omega pair powerset sUnion sep succ)
end ZFSet
