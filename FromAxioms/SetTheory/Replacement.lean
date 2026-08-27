/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Replacement.

The last ZFC axiom, and the one that makes the theory strong: the image of a set
under a function is a set. Separation can only carve subsets out of something
you already have; replacement lets you build genuinely new sets of the same
size, and it is what makes ordinals and transfinite recursion possible.

## Why this is nearly free at the pre-set level

A pre-set is an index type plus a family. To take an image, keep the index type
and post-compose the family:

    image F ⟨α, A⟩ = ⟨α, fun a => F (A a)⟩

That is the entire construction, and it is why replacement is cheap here while
being a strong axiom in ZFC. Set theory has to assert that the collection
`{F y : y ∈ x}` is small enough to be a set; type theory already knows, because
the index type `α` is right there and did not change.

## Where the cost would fall, and why it does not

Not on the construction -- on the interface. `PSet.image` takes a
`PSet → PSet`, and everything about it is axiom-free. A `ZFSet → ZFSet` is a
function on equivalence classes, and post-composing it into a family means
getting back down to representatives. Choosing one is `Classical.choice`.

The way out is to notice what ZFC actually assumes. Replacement is a schema over
formulas, and a formula is precisely what supplies the pre-set-level map.
`Definable` carries that map as data, the descent is given rather than chosen,
and the whole file is choice-free.

The statement that does need choice is a different one: that every
`ZFSet → ZFSet` is definable. Lean's function space is larger than the language
of set theory, and that gap -- not replacement -- is what the axiom was paying
for.
-/

import FromAxioms.SetTheory.PSet
import FromAxioms.SetTheory.ZFSet

universe u

namespace PSet

/-- The image of a pre-set: same index type, family post-composed with `F`. -/
def image (F : PSet.{u} → PSet.{u}) (x : PSet.{u}) : PSet.{u} :=
  ⟨Idx x, fun a => F (Fam x a)⟩

/-- Replacement, at the pre-set level. Axiom-free. -/
theorem mem_image_iff {F : PSet.{u} → PSet.{u}}
    (hF : ∀ {a b : PSet.{u}}, Equiv a b → Equiv (F a) (F b)) (w x : PSet.{u}) :
    w ∈ image F x ↔ ∃ y : PSet.{u}, y ∈ x ∧ Equiv w (F y) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨Fam x a, ⟨a, Equiv.refl _⟩, ha⟩
  · rintro ⟨y, ⟨a, hya⟩, hw⟩
    exact ⟨a, hw.trans (hF hya)⟩

theorem image_congr {F : PSet.{u} → PSet.{u}}
    (hF : ∀ {a b : PSet.{u}}, Equiv a b → Equiv (F a) (F b)) {x y : PSet.{u}}
    (h : Equiv x y) : Equiv (image F x) (image F y) := by
  refine (equiv_iff_ext _ _).mpr (fun w => ?_)
  refine Iff.trans (mem_image_iff hF w x) (Iff.trans ?_ (mem_image_iff hF w y).symm)
  constructor
  · rintro ⟨z, hzx, hw⟩
    exact ⟨z, (mem_congr_right h z).mp hzx, hw⟩
  · rintro ⟨z, hzy, hw⟩
    exact ⟨z, (mem_congr_right h z).mpr hzy, hw⟩

end PSet

namespace SetTheory

/-! ## Supplying the representative instead of choosing it

`PSet.image` needs a `PSet → PSet`, and a `ZFSet → ZFSet` is a function on
equivalence classes. Getting back down to representatives is the whole
difficulty, and choosing one is `Classical.choice`.

But ZFC never quantifies over arbitrary functions. Its replacement is a schema
over formulas, and a formula is exactly what hands you the pre-set-level map.
`Definable` carries that map as data, so the descent is given rather than
chosen, and the axiom comes out at zero cost.

What is not provable here is that every `ZFSet → ZFSet` is definable. That
statement needs choice -- it is Mathlib's `allZFSetDefinable`, proved with it --
and it is strictly stronger than the ZFC schema, since Lean's function space
contains maps no formula names. -/

/-- A function on sets is definable when a function on pre-sets induces it. -/
structure Definable (F : ZFSet.{u} → ZFSet.{u}) : Type (u + 1) where
  /-- The pre-set level map. -/
  fam : PSet.{u} → PSet.{u}
  /-- It induces `F`. -/
  spec : ∀ p : PSet.{u}, F (mk p) = mk (fam p)

/-- A definable map respects `Equiv` for free: equivalent pre-sets have the same
class, so `F` cannot tell them apart. -/
theorem Definable.congr {F : ZFSet.{u} → ZFSet.{u}} (d : Definable F) {a b : PSet.{u}}
    (h : PSet.Equiv a b) : PSet.Equiv (d.fam a) (d.fam b) := by
  refine mk_eq_mk.mp ?_
  rw [← d.spec a, ← d.spec b, mk_eq_mk.mpr h]

/-- The image of a set under a definable function. No representative is chosen,
so nothing here is `noncomputable` and nothing depends on choice. -/
def imageOf {F : ZFSet.{u} → ZFSet.{u}} (d : Definable F) : ZFSet.{u} → ZFSet.{u} :=
  Quotient.lift (fun x => mk (PSet.image d.fam x))
    (fun _ _ h => Quotient.sound (PSet.image_congr d.congr h))

/-- Replacement, stated with `=` rather than `Equiv` -- the quotient's
payoff -- and now axiom-free apart from the quotient itself. -/
theorem mem_imageOf_iff {F : ZFSet.{u} → ZFSet.{u}} (d : Definable F) (w x : ZFSet.{u}) :
    w ∈ imageOf d x ↔ ∃ y : ZFSet.{u}, y ∈ x ∧ w = F y := by
  refine Quotient.inductionOn₂ w x (fun w x => ?_)
  refine Iff.trans (PSet.mem_image_iff d.congr w x) ?_
  constructor
  · rintro ⟨y, hyx, hw⟩
    exact ⟨mk y, hyx, (mk_eq_mk.mpr hw).trans (d.spec y).symm⟩
  · rintro ⟨y, hyx, hw⟩
    obtain ⟨y, rfl⟩ := Quotient.exists_rep y
    exact ⟨y, hyx, mk_eq_mk.mp (hw.trans (d.spec y))⟩

/-- ZFC's replacement, in the shape the axiom is usually stated: the image
collection is a set. -/
theorem replacement {F : ZFSet.{u} → ZFSet.{u}} (d : Definable F) (x : ZFSet.{u}) :
    ∃ img : ZFSet.{u}, ∀ w : ZFSet.{u}, w ∈ img ↔ ∃ y : ZFSet.{u}, y ∈ x ∧ w = F y :=
  ⟨imageOf d x, fun w => mem_imageOf_iff d w x⟩

/-! ## Audit

The contrast to read: `PSet.mem_image_iff` is the same mathematical fact as
`SetTheory.replacement`, and both cost nothing. What used to be classical here was
the descent from classes to representatives, and `Definable` supplies it instead
of choosing it.
-/

#print axioms PSet.mem_image_iff   -- expect: none
#print axioms imageOf              -- expect: Quot.sound
#print axioms mem_imageOf_iff      -- expect: propext, Quot.sound
#print axioms replacement          -- expect: propext, Quot.sound

end SetTheory

namespace ZFSet
export SetTheory (Definable imageOf mem_imageOf_iff replacement)
end ZFSet
