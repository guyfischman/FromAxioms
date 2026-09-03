/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# A Hilbert system, for the proof predicate

`DerivesFO` is natural deduction, which is what proofs about the object language
want to be written in. It is the wrong system to arithmetise: every one of its
seventeen rules is relative to a context the rules themselves modify, so a
checker on codes would have to code contexts and do list surgery in each clause.

This file gives the system the checker will be about instead. Axioms are a
syntactic class, the rules are modus ponens and generalisation, and a derivation
is a list of formulas each of which is an axiom, a member of the theory, or a
consequence of two earlier ones. Nothing about that mentions a context.

The logic is intuitionistic, matching `DerivesFO`: there is no double-negation
scheme, and `fls_elim` is the only thing said about falsity.

Generalisation carries a side condition: every formula of the theory is a
sentence. Without it the deduction theorem is false -- from `x = 0` one could
generalise and then discharge, getting `x = 0 → ∀x. x = 0`, and the deduction
theorem is what natural deduction's `imp_intro` translates to. The condition is on the theory, not on the formula
being discharged, so `imp_intro` discharges an open formula: a derivation that
discharges one cannot have generalised under it.
-/

import FromAxioms.Metamath.FirstOrder

open Metamath
namespace Geometry

/-- The axiom schemes. Implication is `K` and `S`; each connective gets its
introduction and elimination as implications; the quantifier schemes are
instantiation and the two ways a quantifier commutes with an implication whose
other side does not mention the bound variable. -/
inductive HAxiom : Formula → Prop where
  | k (φ ψ : Formula) : HAxiom (.imp φ (.imp ψ φ))
  | s (φ ψ χ : Formula) :
      HAxiom (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ)))
  | conjI (φ ψ : Formula) : HAxiom (.imp φ (.imp ψ (.conj φ ψ)))
  | conjL (φ ψ : Formula) : HAxiom (.imp (.conj φ ψ) φ)
  | conjR (φ ψ : Formula) : HAxiom (.imp (.conj φ ψ) ψ)
  | disjL (φ ψ : Formula) : HAxiom (.imp φ (.disj φ ψ))
  | disjR (φ ψ : Formula) : HAxiom (.imp ψ (.disj φ ψ))
  | disjE (φ ψ χ : Formula) :
      HAxiom (.imp (.imp φ χ) (.imp (.imp ψ χ) (.imp (.disj φ ψ) χ)))
  | flsE (φ : Formula) : HAxiom (.imp .fls φ)
  | allE (φ : Formula) (t : Term) : HAxiom (.imp (.all φ) (subst (single t) φ))
  | allI (φ ψ : Formula) :
      HAxiom (.imp (.all (.imp (shift φ) ψ)) (.imp φ (.all ψ)))
  | exI (φ : Formula) (t : Term) : HAxiom (.imp (subst (single t) φ) (.ex φ))
  | exE (φ ψ : Formula) :
      HAxiom (.imp (.all (.imp φ (shift ψ))) (.imp (.ex φ) ψ))
  | eqRefl (t : Term) : HAxiom (.eq t t)
  | eqSubst (φ : Formula) (s t : Term) :
      HAxiom (.imp (.eq s t) (.imp (subst (single s) φ) (subst (single t) φ)))

/-- Derivability in the Hilbert system. No context: `T` is the theory and it
never changes. -/
inductive HDerives (A : Formula → Prop) (T : List Formula) : Formula → Prop where
  | ax {φ} : A φ → HDerives A T φ
  | thy {φ} : φ ∈ T → HDerives A T φ
  | mp {φ ψ} : HDerives A T (.imp φ ψ) → HDerives A T φ → HDerives A T ψ
  | gen {φ} : (∀ ψ, ψ ∈ T → FreeBelow 0 ψ) → HDerives A T φ →
      HDerives A T (.all φ)

/-- Citing one of the fifteen schemes, in a system whose axioms include them.
Every chain lemma below goes through this rather than `ax`, so they hold of the
classical system too. -/
theorem HDerives.scheme {A : Formula → Prop} {T : List Formula}
    (hA : ∀ φ, HAxiom φ → A φ) {φ : Formula} (h : HAxiom φ) :
    HDerives A T φ := .ax (hA _ h)

variable {A : Formula → Prop}

/-! ## Reasoning with implications

`S` and `K` are what a Hilbert system has instead of tactics. These two are the
shapes the translation needs: composing implications, and pushing one under a
common antecedent. -/

/-- Under a common antecedent. -/
theorem hmono (hA : ∀ φ, HAxiom φ → A φ) {T : List Formula} {φ ψ χ : Formula}
    (h : HDerives A T (.imp ψ χ)) :
    HDerives A T (.imp (.imp φ ψ) (.imp φ χ)) :=
  .mp (HDerives.scheme hA (.s φ ψ χ)) (.mp (HDerives.scheme hA (.k (.imp ψ χ) φ)) h)

#print axioms hmono

#print axioms HAxiom
end Geometry

namespace ZFSet
export Geometry (HAxiom HDerives hmono)
end ZFSet
