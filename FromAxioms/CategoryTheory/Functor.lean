/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Functors.

A functor is two set functions -- one on objects, one on arrows -- respecting
the endpoints, the identities and composition. Both categories are passed
unbundled, in the convention `IsRing R add mul zero one` sets, so the structure
takes fourteen parameters. The count is paid once in the signature and never at
a call site.

The forgetful direction from rings to their additive groups is the first
instance a reader expects. It is not buildable: `IsCategory` takes
`Ob : ZFSet`, so a category here is SMALL, and the rings do not form a set. The
first functor every reader reaches for is the first one this development cannot
state.

What it can state is the one-object case, and there the instance was already in
`Group.lean` waiting to be recognised: a monoid homomorphism is exactly a
functor between the one-object categories, with the homomorphism unchanged on
arrows.
-/

import FromAxioms.SetTheory.Relation

universe u

open SetTheory
namespace CategoryTheory

/-! ## Composing with the identity functor -/

/-- The constant functor's object map: every object goes to `b`. -/
def constDiagOb (Ob₁ Ob₂ b : ZFSet.{u}) : ZFSet.{u} :=
  graphOn Ob₁ Ob₂ (fun _ => b)

theorem app_constDiagOb {Ob₁ Ob₂ b a : ZFSet.{u}} (hb : b ∈ Ob₂) (ha : a ∈ Ob₁) :
    app (constDiagOb Ob₁ Ob₂ b) a = b :=
  app_graphOn (fun _ _ => hb) ha

#print axioms constDiagOb
#print axioms app_constDiagOb
end CategoryTheory

namespace ZFSet
export CategoryTheory (app_constDiagOb constDiagOb)
end ZFSet
