/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`.

THE MATHEMATICS IS `Algebra.soundness` --- the tower's own theorem, by induction
on its derivation relation. This file re-proves nothing: it TRANSLATES the
Challenge's syntax into the tower's, carries the derivation across, and reads the
semantics back.

`challenge_is_standard`'s ten-case induction is NOT reused; the Challenge proves
soundness directly and this Solution proves it by transport, so the two really
are independent derivations of the same statement.

WHY A TRANSLATION AND NOT A BRIDGE. There is no encoding here at all --- both
sides are Lean inductives over `Nat` and `Prop`. `toForm` is a structural
recursion between two identically-shaped types, `toDerives` carries each of the
ten rules to its namesake, and `eval_toForm` says the two semantics agree. That
is the cheapest possible shape for a pair whose two sides do not share a type.

AND IT IS ONLY POSSIBLE BECAUSE THE NAMESPACES DIFFER. The set-theory rows
cannot be paired at all: both libraries declare `PSet` and `ZFSet` at the ROOT,
so an environment holding both is rejected before elaboration. `Algebra.Form`
and `Comparator.Soundness.Form` coexist because one is qualified --- the same
situation, decided the other way by a naming choice.

NO CIRCULARITY. `toDerives` maps derivations to derivations; it says nothing
about truth. The semantic content is entirely in `Algebra.soundness`.
-/
import Comparator.Soundness.Challenge
import FromAxioms.Algebra.Heyting

namespace Comparator.Soundness

/-- The tower's theorem this rests on, named where a reader of THIS file
can see it. -/
theorem rests_on_soundness : True := by
  have _ := @Algebra.soundness
  trivial

/-- The syntax, translated. -/
def toForm : Form → Algebra.Form
  | .atom n => .atom n
  | .fls => .fls
  | .imp φ ψ => .imp (toForm φ) (toForm ψ)
  | .conj φ ψ => .conj (toForm φ) (toForm ψ)
  | .disj φ ψ => .disj (toForm φ) (toForm ψ)

/-- The two semantics agree, by the same recursion. -/
theorem eval_toForm (v : Nat → Prop) : ∀ φ : Form, eval v φ = Algebra.eval v (toForm φ)
  | .atom _ => rfl
  | .fls => rfl
  | .imp φ ψ => by rw [show eval v (.imp φ ψ) = (eval v φ → eval v ψ) from rfl,
      eval_toForm v φ, eval_toForm v ψ]; rfl
  | .conj φ ψ => by rw [show eval v (.conj φ ψ) = (eval v φ ∧ eval v ψ) from rfl,
      eval_toForm v φ, eval_toForm v ψ]; rfl
  | .disj φ ψ => by rw [show eval v (.disj φ ψ) = (eval v φ ∨ eval v ψ) from rfl,
      eval_toForm v φ, eval_toForm v ψ]; rfl

theorem evalCtx_toForm (v : Nat → Prop) :
    ∀ Γ : List Form, evalCtx v Γ → Algebra.evalCtx v (Γ.map toForm)
  | [], h => h
  | φ :: Γ, h => ⟨(eval_toForm v φ) ▸ h.left, evalCtx_toForm v Γ h.right⟩

/-- Membership survives the translation --- needed for the `assume` rule. -/
theorem mem_map_toForm {φ : Form} : ∀ {Γ : List Form}, φ ∈ Γ →
    toForm φ ∈ Γ.map toForm
  | _ :: _, .head _ => .head _
  | _ :: Γ, .tail _ hm => .tail _ (mem_map_toForm (Γ := Γ) hm)

/-- The derivation, carried across. Ten rules, each to its namesake. -/
theorem toDerives : ∀ {Γ : List Form} {φ : Form}, Derives Γ φ →
    Algebra.Derives (Γ.map toForm) (toForm φ) := by
  intro Γ φ d
  induction d with
  | assume hm => exact .assume (mem_map_toForm hm)
  | imp_intro _ ih => exact .imp_intro ih
  | imp_elim _ _ ih₁ ih₂ => exact .imp_elim ih₁ ih₂
  | conj_intro _ _ ih₁ ih₂ => exact .conj_intro ih₁ ih₂
  | conj_left _ ih => exact .conj_left ih
  | conj_right _ ih => exact .conj_right ih
  | disj_left _ ih => exact .disj_left ih
  | disj_right _ ih => exact .disj_right ih
  | disj_elim _ _ _ ih ihl ihr => exact .disj_elim ih ihl ihr
  | fls_elim _ ih => exact .fls_elim ih

/-- The challenge, from `FromAxioms`. -/
theorem solution : challenge := by
  intro Γ φ d v hc
  have h := Algebra.soundness (toDerives d) v (evalCtx_toForm v Γ hc)
  rwa [← eval_toForm v φ] at h

#print axioms rests_on_soundness
#print axioms solution

end Comparator.Soundness
