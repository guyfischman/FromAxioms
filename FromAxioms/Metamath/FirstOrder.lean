/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# First-order logic as a formal system

`Heyting.lean` writes down propositional derivation; this adds the quantifiers,
which is where a formal system stops being a table of connectives and starts
needing a treatment of binding.

Two choices fix the shape of the file, and both were taken to keep binding
cheap.

De Bruijn indices, not names. A named presentation pays for `∀`-introduction
with a freshness side condition, and then soundness needs a coincidence lemma
and a renaming lemma to discharge it. Indices move that cost into the syntax:
`all φ` binds index `0`, contexts are lifted rather than checked, and capture
cannot occur because there is nothing to capture.

Equality is primitive, not a relation symbol. Without it the language
cannot state the axioms of anything this library builds, which would leave the
file with no consumer. With it, `zfExt` below is the extensionality axiom
written in the object language and `zfExt_sound` reads it back through the
semantics.

A relational signature: terms are variables. Function symbols would make a
term an inductive type of its own, substitution a recursion over it, and the
substitution lemma a hierarchy of lifting lemmas at every cutoff. Dropping them
loses no expressive power -- a function is a relation with a uniqueness axiom --
and collapses the whole apparatus to renaming: instantiating `∀` at a variable
is the renaming `0 ↦ x`, lifting a context is the renaming `succ`, and one lemma
(`eval_rename`) proves both sound.

What is not here, as in the propositional file: any claim of underivability, and
completeness. Soundness maps derivations into `Prop`, and `Prop` is classical, so
this direction is the only one such a semantics can support.

The propositional soundness theorem depends on no axioms; this one depends on
`propext`, and the difference is the domain, not the quantifiers. `evalF`
mentions `a ∈ D` for a `ZFSet` `D`, and `SetTheory.Mem` is a `Quotient.lift₂` whose
respect proof is a literal `propext` -- so every declaration naming `evalF`
inherits it, down to `Iff.rfl`. Interpreting into a set rather than into `Prop`
is what costs, and the binding apparatus itself (`termRename`, `cons_up`) stays
axiom-free.
-/

import FromAxioms.SetTheory.Relation

universe u

namespace Metamath

/-- Terms: a variable, or a function symbol applied to arguments.

Both are `Nat`-indexed, and the arity is not tracked -- a symbol applied to the
wrong number of arguments is a legal term that no intended interpretation gives
a useful value to. Tracking arities would mean indexing the type by a signature,
which is the principled version and a much larger one. -/
inductive Term where
  | var : Nat → Term
  | func : Nat → List Term → Term

/-- Formulas over `Nat`-indexed relation symbols applied to terms, with `all`
and `ex` binding de Bruijn index `0`. -/
inductive Formula where
  | rel : Nat → List Term → Formula
  | eq : Term → Term → Formula
  | fls : Formula
  | imp : Formula → Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | all : Formula → Formula
  | ex : Formula → Formula

/-- A renaming, pushed under one binder: index `0` is the bound one and stays. -/
def up (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

mutual

/-- Renaming a term: the recursion mirrors the type, with the list case split
out because a nested inductive needs its own clause. -/
def termRename (ρ : Nat → Nat) : Term → Term
  | .var n => .var (ρ n)
  | .func f ts => .func f (termRenameList ρ ts)

def termRenameList (ρ : Nat → Nat) : List Term → List Term
  | [] => []
  | t :: ts => termRename ρ t :: termRenameList ρ ts

end

def rename (ρ : Nat → Nat) : Formula → Formula
  | .rel r ts => .rel r (termRenameList ρ ts)
  | .eq s t => .eq (termRename ρ s) (termRename ρ t)
  | .fls => .fls
  | .imp φ ψ => .imp (rename ρ φ) (rename ρ ψ)
  | .conj φ ψ => .conj (rename ρ φ) (rename ρ ψ)
  | .disj φ ψ => .disj (rename ρ φ) (rename ρ ψ)
  | .all φ => .all (rename (up ρ) φ)
  | .ex φ => .ex (rename (up ρ) φ)

/-- The negation of a formula: the object language has no primitive `¬`, and
implying `⊥` is what the derivation rules manipulate. -/
def fnot (φ : Formula) : Formula := .imp φ .fls

/-- Lifting past a binder: every free index moves up by one. -/
def shift : Formula → Formula := rename Nat.succ

/-- Instantiating the bound index at the variable `x`, and dropping the binder. -/
def inst (x : Nat) : Nat → Nat
  | 0 => x
  | n + 1 => n

/-- Extending an assignment with a value for the newly bound index. -/
def cons (a : ZFSet.{u}) (env : Nat → ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => a
  | n + 1 => env n

mutual

/-- The value of a term: a variable reads the assignment, a function symbol is
read through the interpretation `F`. -/
def evalT (F : Nat → List ZFSet.{u} → ZFSet.{u}) (env : Nat → ZFSet.{u}) :
    Term → ZFSet.{u}
  | .var n => env n
  | .func f ts => F f (evalTList F env ts)

def evalTList (F : Nat → List ZFSet.{u} → ZFSet.{u}) (env : Nat → ZFSet.{u}) :
    List Term → List ZFSet.{u}
  | [] => []
  | t :: ts => evalT F env t :: evalTList F env ts

end

/-- Reading a formula as a proposition: a domain `D`, interpretations `F` and
`R` of the function and relation symbols, and an assignment of the free
variables. -/
def evalF (D : ZFSet.{u}) (F : Nat → List ZFSet.{u} → ZFSet.{u})
    (R : Nat → List ZFSet.{u} → Prop) (env : Nat → ZFSet.{u}) : Formula → Prop
  | .rel r ts => R r (evalTList F env ts)
  | .eq s t => evalT F env s = evalT F env t
  | .fls => False
  | .imp φ ψ => evalF D F R env φ → evalF D F R env ψ
  | .conj φ ψ => evalF D F R env φ ∧ evalF D F R env ψ
  | .disj φ ψ => evalF D F R env φ ∨ evalF D F R env ψ
  | .all φ => ∀ a, a ∈ D → evalF D F R (cons a env) φ
  | .ex φ => ∃ a, a ∈ D ∧ evalF D F R (cons a env) φ

/-! ## Substitution

Renaming sends a variable to a variable, which is all the quantifier rules need
and strictly less than the diagonal lemma needs: instantiating at a numeral is
substituting a closed term. The apparatus is the same shape one level up --
`substUp` plays the role of `up`, and the semantic lemma relates the two
assignments pointwise rather than by composition, so this stays axiom-free
too. -/

mutual

def termSubst (σ : Nat → Term) : Term → Term
  | .var n => σ n
  | .func f ts => .func f (termSubstList σ ts)

def termSubstList (σ : Nat → Term) : List Term → List Term
  | [] => []
  | t :: ts => termSubst σ t :: termSubstList σ ts

end

/-- A substitution, pushed under one binder: index `0` becomes the bound
variable, and everything the substitution produces is lifted past it. -/
def substUp (σ : Nat → Term) : Nat → Term
  | 0 => .var 0
  | n + 1 => termRename Nat.succ (σ n)

def subst (σ : Nat → Term) : Formula → Formula
  | .rel r ts => .rel r (termSubstList σ ts)
  | .eq s t => .eq (termSubst σ s) (termSubst σ t)
  | .fls => .fls
  | .imp φ ψ => .imp (subst σ φ) (subst σ ψ)
  | .conj φ ψ => .conj (subst σ φ) (subst σ ψ)
  | .disj φ ψ => .disj (subst σ φ) (subst σ ψ)
  | .all φ => .all (subst (substUp σ) φ)
  | .ex φ => .ex (subst (substUp σ) φ)

/-- Instantiating the bound index at a term, and dropping the binder. The
term-level counterpart of `inst`. -/
def single (t : Term) : Nat → Term
  | 0 => t
  | n + 1 => .var n

/-! ### Substitution composes

Two substitutions in sequence are one substitution, and the composite is
computed pointwise. Without this every de Bruijn calculation is an unfolding of
nested `subst`s that only the elaborator can follow; with it, a calculation
about `subst σ (subst τ φ)` becomes a calculation about `n ↦ termSubst σ (τ n)`,
which is a function on numbers and can be evaluated case by case.

The binder case is the whole content, and it needs one commutation: substituting
under a lift is lifting the substitution. -/

/-- Intuitionistic natural deduction with quantifiers.

`all_intro` lifts the context rather than imposing a freshness condition, which
is the same restriction stated in the syntax: what the premise proves must not
mention the variable being generalised, and after lifting there is no index left
that could. -/
inductive DerivesFO : List Formula → Formula → Prop where
  | assume {Γ φ} : φ ∈ Γ → DerivesFO Γ φ
  | imp_intro {Γ φ ψ} : DerivesFO (φ :: Γ) ψ → DerivesFO Γ (Formula.imp φ ψ)
  | imp_elim {Γ φ ψ} : DerivesFO Γ (Formula.imp φ ψ) → DerivesFO Γ φ → DerivesFO Γ ψ
  | conj_intro {Γ φ ψ} : DerivesFO Γ φ → DerivesFO Γ ψ → DerivesFO Γ (Formula.conj φ ψ)
  | conj_left {Γ φ ψ} : DerivesFO Γ (Formula.conj φ ψ) → DerivesFO Γ φ
  | conj_right {Γ φ ψ} : DerivesFO Γ (Formula.conj φ ψ) → DerivesFO Γ ψ
  | disj_left {Γ φ ψ} : DerivesFO Γ φ → DerivesFO Γ (Formula.disj φ ψ)
  | disj_right {Γ φ ψ} : DerivesFO Γ ψ → DerivesFO Γ (Formula.disj φ ψ)
  | disj_elim {Γ φ ψ χ} : DerivesFO Γ (Formula.disj φ ψ) →
      DerivesFO (φ :: Γ) χ → DerivesFO (ψ :: Γ) χ → DerivesFO Γ χ
  | fls_elim {Γ φ} : DerivesFO Γ Formula.fls → DerivesFO Γ φ
  | all_intro {Γ φ} : DerivesFO (Γ.map shift) φ → DerivesFO Γ (Formula.all φ)
  | all_elim {Γ φ} (t : Term) : DerivesFO Γ (Formula.all φ) →
      DerivesFO Γ (subst (single t) φ)
  | ex_intro {Γ φ} (t : Term) : DerivesFO Γ (subst (single t) φ) →
      DerivesFO Γ (Formula.ex φ)
  | ex_elim {Γ φ ψ} : DerivesFO Γ (Formula.ex φ) →
      DerivesFO (φ :: Γ.map shift) (shift ψ) → DerivesFO Γ ψ
  | eq_refl {Γ} (t : Term) : DerivesFO Γ (Formula.eq t t)
  | eq_subst {Γ φ} (s t : Term) : DerivesFO Γ (Formula.eq s t) →
      DerivesFO Γ (subst (single s) φ) → DerivesFO Γ (subst (single t) φ)

/-! `List.Mem` is an inductive, and its `Iff` lemmas in core are not: both
`List.mem_cons` and `List.mem_map` audit at `propext`, and `List.mem_map` at
`Quot.sound` as well. Recursing on the membership instead keeps the whole
derivation layer free of axioms, so the syntactic half of incompleteness costs
nothing. -/

theorem cons_sub {Γ Δ : List Formula} (h : ∀ ψ, ψ ∈ Γ → ψ ∈ Δ) (χ : Formula) :
    ∀ ψ, ψ ∈ χ :: Γ → ψ ∈ χ :: Δ
  | _, .head _ => .head _
  | _, .tail _ hm => .tail _ (h _ hm)

theorem mem_map_shift : ∀ {Γ : List Formula} {ψ : Formula},
    ψ ∈ Γ.map shift → ∃ χ, χ ∈ Γ ∧ ψ = shift χ
  | [], _, hψ => nomatch hψ
  | χ :: Γ, _, .head _ => ⟨χ, .head _, rfl⟩
  | _ :: Γ, ψ, .tail _ hm =>
    let ⟨χ, hχ, he⟩ := mem_map_shift (Γ := Γ) (ψ := ψ) hm
    ⟨χ, .tail _ hχ, he⟩

theorem mem_map_shift_of_mem {Γ : List Formula} {χ : Formula} :
    χ ∈ Γ → shift χ ∈ Γ.map shift
  | .head _ => .head _
  | .tail _ hm => .tail _ (mem_map_shift_of_mem hm)

theorem map_shift_sub {Γ Δ : List Formula} (h : ∀ ψ, ψ ∈ Γ → ψ ∈ Δ) :
    ∀ ψ, ψ ∈ Γ.map shift → ψ ∈ Δ.map shift := fun _ hψ =>
  let ⟨_, hχ, he⟩ := mem_map_shift hψ
  he ▸ mem_map_shift_of_mem (h _ hχ)

/-- Weakening. A derivation survives any context that still holds its
assumptions.

Every rule that changes the context changes it by the same operation on both
sides -- `imp_intro` and the elimination rules push a formula on, `all_intro`
and `ex_elim` lift the whole list -- so the induction hypothesis applies with
the inclusion transported through that operation. `Γ.map shift` is the only
case needing anything more than `List.mem_cons`, and `List.mem_map` supplies
it. -/
theorem weaken {Γ Δ : List Formula} {φ : Formula} (h : ∀ ψ, ψ ∈ Γ → ψ ∈ Δ)
    (d : DerivesFO Γ φ) : DerivesFO Δ φ := by
  induction d generalizing Δ with
  | assume hm => exact DerivesFO.assume (h _ hm)
  | imp_intro _ ih => exact DerivesFO.imp_intro (ih (cons_sub h _))
  | imp_elim _ _ ih₁ ih₂ => exact DerivesFO.imp_elim (ih₁ h) (ih₂ h)
  | conj_intro _ _ ih₁ ih₂ => exact DerivesFO.conj_intro (ih₁ h) (ih₂ h)
  | conj_left _ ih => exact DerivesFO.conj_left (ih h)
  | conj_right _ ih => exact DerivesFO.conj_right (ih h)
  | disj_left _ ih => exact DerivesFO.disj_left (ih h)
  | disj_right _ ih => exact DerivesFO.disj_right (ih h)
  | disj_elim _ _ _ ih ih₁ ih₂ =>
    exact DerivesFO.disj_elim (ih h) (ih₁ (cons_sub h _)) (ih₂ (cons_sub h _))
  | fls_elim _ ih => exact DerivesFO.fls_elim (ih h)
  | all_intro _ ih => exact DerivesFO.all_intro (ih (map_shift_sub h))
  | all_elim t _ ih => exact DerivesFO.all_elim t (ih h)
  | ex_intro t _ ih => exact DerivesFO.ex_intro t (ih h)
  | ex_elim _ _ ih ih₂ =>
    exact DerivesFO.ex_elim (ih h) (ih₂ (cons_sub (map_shift_sub h) _))
  | eq_refl t => exact DerivesFO.eq_refl t
  | eq_subst a b _ _ ih₁ ih₂ => exact DerivesFO.eq_subst a b (ih₁ h) (ih₂ h)

/-! ## Which indices a formula reads

Separation's schema needs "φ mentions only its hole", and the honest form of
that is syntactic: a bound on the free indices, checkable on the formula itself
rather than assumed about its evaluation.
-/

mutual

/-- Every variable in a term is below `d`. -/
def TermFreeBelow : Nat → Term → Prop
  | d, .var n => n < d
  | d, .func _ ts => TermListFreeBelow d ts

def TermListFreeBelow : Nat → List Term → Prop
  | _, [] => True
  | d, t :: ts => TermFreeBelow d t ∧ TermListFreeBelow d ts

end

/-- Every free index is below `d`. -/
def FreeBelow : Nat → Formula → Prop
  | d, .rel _ ts => TermListFreeBelow d ts
  | d, .eq a b => TermFreeBelow d a ∧ TermFreeBelow d b
  | _, .fls => True
  | d, .imp φ ψ => FreeBelow d φ ∧ FreeBelow d ψ
  | d, .conj φ ψ => FreeBelow d φ ∧ FreeBelow d ψ
  | d, .disj φ ψ => FreeBelow d φ ∧ FreeBelow d ψ
  | d, .all φ => FreeBelow (d + 1) φ
  | d, .ex φ => FreeBelow (d + 1) φ

end Metamath

#print axioms Metamath.evalF
#print axioms Metamath.DerivesFO
namespace ZFSet
export Metamath (DerivesFO Formula FreeBelow Term cons cons_sub evalF fnot map_shift_sub mem_map_shift mem_map_shift_of_mem rename shift single subst substUp up weaken)
end ZFSet
