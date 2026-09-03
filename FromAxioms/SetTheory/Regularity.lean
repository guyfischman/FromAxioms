/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Regularity, and the ∈-induction it comes from.

ZFC's axiom of foundation says every non-empty set has an ∈-minimal member --
equivalently, there are no infinite descending membership chains. It is the
axiom that rules out `x ∈ x`.

Here it is a theorem, and an unusually cheap one, because `PSet` was defined as
an inductive type. Inductive types are well-founded by construction: the
recursor Lean generates is precisely a principle of induction along the
member-of relation. Foundation is not an assumption about our sets, it is a
property they could not have failed to have.

## Two statements, two costs

The constructive half is here:

* `inductionOn` -- ∈-induction. Constructive, modulo the quotient machinery
  (`propext`, `Quot.sound`).

Foundation itself is priced rather than proved: `Constructive.Regularity` is
the statement, `regularityProp_of_em` proves it from `EM`, and
`em_of_regularity` derives `EM` back, so foundation over this tree's other
axioms IS excluded middle rather than merely following from it.

The obstruction is the familiar one. Knowing that no
infinite descent exists does not hand you a minimal element; extracting one
from `x ≠ ∅` means reasoning by contradiction, and `x ≠ ∅` carries no witness.
That is the same barrier `Quantifiers.lean` demonstrated in Phase 1.
-/

import FromAxioms.SetTheory.ZFSet

universe u

namespace PSet

/-- ∈-induction for pre-sets, straight from the recursor.

To prove a property of every pre-set it suffices to prove it of `x` given that
it holds of every member of `x`. The recursive call is on `A a`, a strictly
smaller tree, so this is ordinary structural recursion.

The congruence hypothesis is the usual pre-set tax: membership is stated up to
`Equiv`, so a property that does not respect `Equiv` cannot be transported from
the branch `A a` to a `y` merely equivalent to it. It disappears on the
quotient. -/
theorem inductionOn {motive : PSet.{u} → Prop}
    (hcongr : ∀ {a b : PSet.{u}}, Equiv a b → motive a → motive b)
    (h : ∀ x : PSet.{u}, (∀ y : PSet.{u}, y ∈ x → motive y) → motive x) :
    ∀ x : PSet.{u}, motive x
  | ⟨α, A⟩ =>
    h ⟨α, A⟩ (fun _ hy =>
      let ⟨a, ha⟩ := hy
      hcongr (Equiv.symm ha) (inductionOn hcongr h (A a)))

end PSet

namespace SetTheory

/-- ∈-induction for sets. No congruence hypothesis: a `ZFSet → Prop` respects
equality automatically, which is exactly what the quotient bought. -/
theorem inductionOn {motive : ZFSet.{u} → Prop}
    (h : ∀ y : ZFSet.{u}, (∀ z : ZFSet.{u}, z ∈ y → motive z) → motive y) :
    ∀ x : ZFSet.{u}, motive x := by
  refine Quotient.ind (motive := fun x : ZFSet.{u} => motive x) ?_
  -- `▸` cannot be used here: the expected type is the unreduced application
  -- `(fun p => motive (mk p)) b`, which does not syntactically contain `mk b`.
  -- `congrArg` builds the equation of propositions explicitly instead.
  refine PSet.inductionOn (motive := fun p : PSet.{u} => motive (mk p))
    (fun hab hma => (congrArg motive (mk_eq_mk.mpr hab)).mp hma) ?_
  intro p hp
  refine h (mk p) ?_
  intro z hz
  obtain ⟨z, rfl⟩ := Quotient.exists_rep z
  exact hp z hz

/-- No set is a member of itself -- the headline consequence of foundation, and
constructive: `inductionOn` supplies it directly, with no appeal to choice.

Read the proof as: if `x ∈ x` were possible for some `x`, take an ∈-minimal
such `x`; but its members inherit the same property, contradiction. -/
theorem not_mem_self : ∀ x : ZFSet.{u}, x ∉ x :=
  inductionOn (motive := fun x => x ∉ x) (fun _ ih hx => ih _ hx hx)

#print axioms inductionOn     -- expect: propext, Quot.sound
#print axioms not_mem_self    -- expect: propext, Quot.sound

end SetTheory

namespace ZFSet
export SetTheory (inductionOn not_mem_self)
end ZFSet
