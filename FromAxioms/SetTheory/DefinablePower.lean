/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The subsets a formula picks out, and the set collecting them

The constructible hierarchy is built by iterating one operation: from a set,
take the subsets that a first-order formula defines over that set, with
parameters from it. This file is that operation and its membership
characterisation; the hierarchy itself is a separate construction on top.

Why `evalF` is already the relativised satisfaction. `evalF D F R env` reads
a formula with its quantifiers ranging over `D` -- the `all` clause is `∀ a, a ∈
D → ...` and the `ex` clause matches. Taking `D := x` therefore gives exactly
satisfaction in `x`, which is what the hierarchy's step needs. The syntactic
`relativise` (Relativise.lean) is the other way of arranging the same
restriction, for when the guard has to live inside the formula; nothing here
needs it.

The obstruction this construction was expected to hit, and why it does not.
A definable subset is one named by a `Formula` -- a Lean type, not a set -- so
the operation quantifies over syntax while having to return a `ZFSet`. That is
the shape which has blocked several constructions in this development. It does
not block here, because `sep` takes an ARBITRARY Lean predicate: the
quantification over `Formula` and over environments happens in the `Prop` that
`sep` is handed, and the result is a set because `sep` returns one. No
satisfaction predicate inside the set theory is needed, and `Godel.lean`'s
arithmetisation -- the route this development takes when the answer is no -- is
not required.

What this does NOT give is a definability predicate *expressible in the object
language*. `definablePower` is a Lean-level operation on sets; a formula of the
∈-language saying S is definable over x is a different object and would need
the arithmetised satisfaction. The distinction matters the moment one wants the
hierarchy's construction to be carried out inside the theory rather than about
it.
-/

import FromAxioms.Metamath.FirstOrder
import FromAxioms.SetTheory.Replacement

universe u

open Metamath
namespace SetTheory

/-! ## Being defined by a formula

`S` is what `φ` picks out of `x`: the members of `x` satisfying `φ` when the
tested element is bound at index `0` and the parameters come from the supplied
assignment. Stated
as an extensional condition on `S` rather than as an equation, so that a caller
holding an arbitrary set can discharge it pointwise. -/

/-- `S` is the extension of `φ` over `x`, with parameters from the assignment. -/
def DefinedBy (x : ZFSet.{u}) (F : Nat → List ZFSet.{u} → ZFSet.{u})
    (R : Nat → List ZFSet.{u} → Prop) (φ : Formula) (env : Nat → ZFSet.{u})
    (S : ZFSet.{u}) : Prop :=
  ∀ z, z ∈ S ↔ z ∈ x ∧ evalF x F R (cons z env) φ

/-! ## The operation

A separation over the power set, whose predicate quantifies over `Formula` and
over environments. That is a Lean-level quantification inside the `Prop` handed
to `sep`, which is exactly what `sep` permits. -/

/-- The definable power set: the subsets of `x` that some formula picks out
of `x`, with parameters from `x`'s ambient universe. -/
def definablePower (x : ZFSet.{u}) (F : Nat → List ZFSet.{u} → ZFSet.{u})
    (R : Nat → List ZFSet.{u} → Prop) : ZFSet.{u} :=
  sep (fun S => ∃ (φ : Formula) (env : Nat → ZFSet.{u}), DefinedBy x F R φ env S)
    (powerset x)

/-! ## The pre-set realisation, and why it is the gate

The constructible hierarchy iterates this operation, and iterating anything
over a set's members needs `replacement` -- which takes a `Definable`, a map
carrying a PRE-SET level realisation. `memRec` (Hierarchy.lean) is the general
∈-recursion and does NOT help: its step is handed a dependent
`∀ y, y ∈ x → ZFSet`, which is not a `ZFSet → ZFSet` at all, so no image of it
is formable.

What makes the hierarchy reachable is that this operation has the realisation
already: it is a separation over a power set, both of which are liftings of
pre-set operations, so the composite is their composite and `spec` is `rfl`. -/

/-- The pre-set map inducing `definablePower`. -/
def definablePowerFam (F : Nat → List ZFSet.{u} → ZFSet.{u})
    (R : Nat → List ZFSet.{u} → Prop) (p : PSet.{u}) : PSet.{u} :=
  PSet.sep (fun z => ∃ (φ : Formula) (env : Nat → ZFSet.{u}),
      DefinedBy (mk p) F R φ env (mk z)) (PSet.powerset p)

/-- The operation is definable, so `replacement` applies to it. -/
def definablePower_definable (F : Nat → List ZFSet.{u} → ZFSet.{u})
    (R : Nat → List ZFSet.{u} → Prop) :
    Definable (fun x => definablePower.{u} x F R) where
  fam := definablePowerFam.{u} F R
  spec _ := rfl

/-- Equivalent pre-sets have equivalent definable power sets -- `Definable`
gives this for free, and the hierarchy's congruence needs it at each stage. -/
theorem definablePowerFam_congr {F : Nat → List ZFSet.{u} → ZFSet.{u}}
    {R : Nat → List ZFSet.{u} → Prop} {a b : PSet.{u}} (h : PSet.Equiv a b) :
    PSet.Equiv (definablePowerFam.{u} F R a) (definablePowerFam.{u} F R b) :=
  (definablePower_definable.{u} F R).congr h

#print axioms DefinedBy
#print axioms definablePower
#print axioms definablePowerFam
#print axioms definablePower_definable
#print axioms definablePowerFam_congr

end SetTheory

namespace ZFSet
export SetTheory (DefinedBy definablePower definablePowerFam definablePowerFam_congr definablePower_definable)
end ZFSet
