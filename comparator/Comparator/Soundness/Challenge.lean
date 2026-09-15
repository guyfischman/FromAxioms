/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-!
# The challenge: intuitionistic natural deduction is sound, in CORE vocabulary

Every symbol is Lean core's --- `Nat`, `Prop`, `List`, `∧`, `∨`, `→`, `False`.
The tower's `Algebra.Form`, `Algebra.Derives` and `Algebra.eval` are NOT
imported: the syntax, the derivation relation and the semantics are all declared
below, so this file depends on no tower definition and on no Mathlib.

## Which statement, and why it is the right one to ask for

This is the row `intuitionistic logic as a formal system`, whose `mathlib` field
reads FirstOrder soundness (classical). Mathlib's `FirstOrder.Language`
development is over its own `BoundedFormula` and is classical throughout; the
tower's `Algebra.soundness` is over an intuitionistic natural-deduction calculus
with no `⊥`-elimination to excluded middle and no double-negation rule.

So the two do not share a formula type, and no encoding relates them: the
comparison is made by RESTATING the calculus and translating, so the Challenge
declares its own inductives rather than importing either side's.

## The syntax here is the tower's, character for character

`Form`, `Derives`, `eval` and `evalCtx` below are `Algebra.Form`,
`Algebra.Derives`, `Algebra.eval` and `Algebra.evalCtx` rewritten in this
namespace. That is deliberate: the Solution's translation is then a structural
recursion with nothing to decide, and the pair tests the SOUNDNESS THEOREM
rather than an encoding.

AND THIS IS ONLY POSSIBLE BECAUSE THE TWO LIVE IN DIFFERENT NAMESPACES. The
set-theory rows cannot be paired at all --- both libraries declare `PSet` and
`ZFSet` at the ROOT, so an environment holding both is rejected at import time.
`Algebra.Form` and this file's `Form` coexist because one of them is qualified.
-/

namespace Comparator.Soundness

/-- Propositional syntax. This is `Algebra.Form`. -/
inductive Form where
  | atom : Nat → Form
  | fls : Form
  | imp : Form → Form → Form
  | conj : Form → Form → Form
  | disj : Form → Form → Form

/-- Intuitionistic natural deduction. This is `Algebra.Derives`: `fls_elim`
gives anything from absurdity, and there is NO double-negation rule. -/
inductive Derives : List Form → Form → Prop where
  | assume {Γ : List Form} {φ : Form} : φ ∈ Γ → Derives Γ φ
  | imp_intro {Γ φ ψ} : Derives (φ :: Γ) ψ → Derives Γ (Form.imp φ ψ)
  | imp_elim {Γ φ ψ} : Derives Γ (Form.imp φ ψ) → Derives Γ φ → Derives Γ ψ
  | conj_intro {Γ φ ψ} : Derives Γ φ → Derives Γ ψ → Derives Γ (Form.conj φ ψ)
  | conj_left {Γ φ ψ} : Derives Γ (Form.conj φ ψ) → Derives Γ φ
  | conj_right {Γ φ ψ} : Derives Γ (Form.conj φ ψ) → Derives Γ ψ
  | disj_left {Γ φ ψ} : Derives Γ φ → Derives Γ (Form.disj φ ψ)
  | disj_right {Γ φ ψ} : Derives Γ ψ → Derives Γ (Form.disj φ ψ)
  | disj_elim {Γ φ ψ χ} : Derives Γ (Form.disj φ ψ) →
      Derives (φ :: Γ) χ → Derives (ψ :: Γ) χ → Derives Γ χ
  | fls_elim {Γ φ} : Derives Γ Form.fls → Derives Γ φ

/-- The semantics, into `Prop` itself. This is `Algebra.eval`. -/
def eval (v : Nat → Prop) : Form → Prop
  | .atom n => v n
  | .fls => False
  | .imp φ ψ => eval v φ → eval v ψ
  | .conj φ ψ => eval v φ ∧ eval v ψ
  | .disj φ ψ => eval v φ ∨ eval v ψ

/-- Every formula of the context holds. This is `Algebra.evalCtx`. -/
def evalCtx (v : Nat → Prop) : List Form → Prop
  | [] => True
  | φ :: Γ => eval v φ ∧ evalCtx v Γ

/-- The challenge. Soundness: what is derivable is true under every
valuation.

`Solution.lean` must close this using the `FromAxioms` tower. Nothing in this
file may be changed to make that easier. -/
def challenge : Prop :=
  ∀ {Γ : List Form} {φ : Form}, Derives Γ φ →
    ∀ v : Nat → Prop, evalCtx v Γ → eval v φ

/-- Context membership gives truth. -/
theorem evalCtx_mem {v : Nat → Prop} : ∀ {Γ : List Form} {φ : Form},
    φ ∈ Γ → evalCtx v Γ → eval v φ
  | _ :: _, _, .head _, h => h.left
  | _ :: Γ, φ, .tail _ hm, h => evalCtx_mem (Γ := Γ) (φ := φ) hm h.right

/-- The challenge is not vacuous, and the calculus's own induction is the
witness --- ten cases, each the introduction or elimination rule read as its
semantic counterpart.

A `Prop` nobody has shown inhabited says nothing --- and a draft of the
`Adjunction` challenge factored its equation into a helper returning `True`,
which would have made that whole pair vacuous while still compiling. That is the
failure this theorem exists to exclude. -/
theorem challenge_is_standard : challenge := by
  intro Γ φ d
  induction d with
  | assume hm => exact fun v hc => evalCtx_mem hm hc
  | imp_intro _ ih => exact fun v hc hφ => ih v ⟨hφ, hc⟩
  | imp_elim _ _ ih₁ ih₂ => exact fun v hc => ih₁ v hc (ih₂ v hc)
  | conj_intro _ _ ih₁ ih₂ => exact fun v hc => ⟨ih₁ v hc, ih₂ v hc⟩
  | conj_left _ ih => exact fun v hc => (ih v hc).left
  | conj_right _ ih => exact fun v hc => (ih v hc).right
  | disj_left _ ih => exact fun v hc => Or.inl (ih v hc)
  | disj_right _ ih => exact fun v hc => Or.inr (ih v hc)
  | disj_elim _ _ _ ih ihl ihr =>
      exact fun v hc => (ih v hc).elim
        (fun h => ihl v ⟨h, hc⟩) (fun h => ihr v ⟨h, hc⟩)
  | fls_elim _ ih => exact fun v hc => (ih v hc).elim

end Comparator.Soundness
