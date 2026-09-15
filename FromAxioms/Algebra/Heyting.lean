/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Intuitionistic propositional logic as a formal system

Every landmark this development has reached is object-level: a definition, or a
theorem about sets. This one is not. Heyting's contribution was a *deductive
system* -- syntax, derivations, and provability as an inductive predicate -- and
formalising it means writing down the object language rather than reasoning in
it.

The alternative was to mark the row undetectable, as the geometry rows are. That
would have been a mistake for a reason this project has already recorded: a
permanently-missing entry pins the frontier behind it forever, which is what made
the ZF row meaningless until it was given a detector. Geometry
pins the global frontier, which the tool reports separately and expects to be
brutal. Heyting sits in foundations, which is the frontier meant to move.

What is here is the natural-deduction fragment and its soundness map into Lean's
`Prop`.

What is not here, and cannot be with this semantics: any claim that the system
fails to derive something. Soundness into `Prop` cannot witness underivability,
because Lean's `Prop` satisfies excluded middle -- a valuation into it is a
classical model, and every classically valid formula is validated. Showing that
`p ∨ ¬p` is not derivable needs a model that refutes it: a Kripke model or a
Heyting algebra, where the semantics is a structure rather than an
interpretation. That is a different project, and the row this file earns is
"the formal system", not "its metatheory".
-/


universe u

namespace Algebra

/-- Propositional formulas over `Nat`-indexed atoms. -/
inductive Form where
  | atom : Nat → Form
  | fls : Form
  | imp : Form → Form → Form
  | conj : Form → Form → Form
  | disj : Form → Form → Form

/-- Derivability in intuitionistic natural deduction.

No `⊥`-elimination to excluded middle and no double-negation rule: `fls_elim`
gives anything from absurdity, and that is the whole of the difference from a
classical system. -/
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

/-- Reading a formula as a proposition, given a valuation of the atoms. -/
def eval (v : Nat → Prop) : Form → Prop
  | .atom n => v n
  | .fls => False
  | .imp φ ψ => eval v φ → eval v ψ
  | .conj φ ψ => eval v φ ∧ eval v ψ
  | .disj φ ψ => eval v φ ∨ eval v ψ

/-- Every formula of the context holds. -/
def evalCtx (v : Nat → Prop) : List Form → Prop
  | [] => True
  | φ :: Γ => eval v φ ∧ evalCtx v Γ

theorem evalCtx_mem {v : Nat → Prop} : ∀ {Γ : List Form} {φ : Form},
    φ ∈ Γ → evalCtx v Γ → eval v φ
  | _ :: _, _, .head _, h => h.left
  | _ :: Γ, φ, .tail _ hm, h => evalCtx_mem (Γ := Γ) (φ := φ) hm h.right

/-- Soundness. A derivation is a proof, under any valuation.

The interesting clause is `disj_elim`, and it is interesting because it is
not: `Or.elim` into a `Prop` is exactly what the rule says, so the object
language's disjunction elimination and the metalanguage's are the same
operation. That correspondence is why no rule here needs a principle -- the
proof depends on no axioms at all. -/
theorem soundness {Γ : List Form} {φ : Form} (d : Derives Γ φ) :
    ∀ v : Nat → Prop, evalCtx v Γ → eval v φ := by
  induction d with
  | assume hm => exact fun v hc => evalCtx_mem hm hc
  | imp_intro _ ih => exact fun v hc hφ => ih v ⟨hφ, hc⟩
  | imp_elim _ _ ih₁ ih₂ => exact fun v hc => ih₁ v hc (ih₂ v hc)
  | conj_intro _ _ ih₁ ih₂ => exact fun v hc => ⟨ih₁ v hc, ih₂ v hc⟩
  | conj_left _ ih => exact fun v hc => (ih v hc).left
  | conj_right _ ih => exact fun v hc => (ih v hc).right
  | disj_left _ ih => exact fun v hc => Or.inl (ih v hc)
  | disj_right _ ih => exact fun v hc => Or.inr (ih v hc)
  | disj_elim _ _ _ ih ih₁ ih₂ =>
    exact fun v hc => (ih v hc).elim (fun h => ih₁ v ⟨h, hc⟩) (fun h => ih₂ v ⟨h, hc⟩)
  | fls_elim _ ih => exact fun v hc => (ih v hc).elim

end Algebra

#print axioms Algebra.evalCtx_mem
#print axioms Algebra.Derives
#print axioms Algebra.soundness

namespace ZFSet
export Algebra (Derives Form eval evalCtx evalCtx_mem soundness)
end ZFSet
