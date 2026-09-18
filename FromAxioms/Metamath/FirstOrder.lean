/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# First-order logic as a formal system

`Heyting.lean` writes down propositional derivation; this adds the quantifiers,
and with them binding.

De Bruijn indices, not names. A named presentation pays for `∀`-introduction
with a freshness side condition, and then soundness needs a coincidence lemma
and a renaming lemma to discharge it. Indices move that cost into the syntax:
`all φ` binds index `0`, contexts are lifted rather than checked, and capture
cannot occur because there is nothing to capture.

Equality is primitive, not a relation symbol. With it the axioms of set
theory can be written in the object language.

Soundness is proved; completeness and underivability are not.

The propositional soundness theorem depends on no axioms; this one depends on
`propext`, and the difference is the domain, not the quantifiers. `evalF`
mentions `a ∈ D` for a `ZFSet` `D`, and `SetTheory.Mem` is a `Quotient.lift₂`
whose respect proof is a literal `propext`, so every declaration naming `evalF`
inherits it, down to `Iff.rfl`. The cost is interpreting into a set rather than
into `Prop`; the binding apparatus itself (`termRename`, `cons_up`) is
axiom-free.
-/

import FromAxioms.Analysis.Ternary

universe u

open SetTheory
namespace Metamath

/-- Terms: a variable, or a function symbol applied to arguments.

Both are `Nat`-indexed, and arities are not tracked. -/
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

def evalCtxF (D : ZFSet.{u}) (F : Nat → List ZFSet.{u} → ZFSet.{u})
    (R : Nat → List ZFSet.{u} → Prop) (env : Nat → ZFSet.{u}) :
    List Formula → Prop
  | [] => True
  | φ :: Γ => evalF D F R env φ ∧ evalCtxF D F R env Γ

/-- The pointwise relation between assignments, pushed under a binder. -/
theorem cons_up {ρ : Nat → Nat} {env env' : Nat → ZFSet.{u}}
    (h : ∀ n, env' n = env (ρ n)) (a : ZFSet.{u}) :
    ∀ n, cons a env' n = cons a env (up ρ n)
  | 0 => rfl
  | n + 1 => h n

mutual

/-- Renaming a term and then reading it is reading the renamed assignment. The
term-level half of `eval_rename`, and the only place the nested list shows up. -/
theorem evalT_rename (F : Nat → List ZFSet.{u} → ZFSet.{u})
    {env env' : Nat → ZFSet.{u}} {ρ : Nat → Nat} (h : ∀ n, env' n = env (ρ n)) :
    ∀ t : Term, evalT F env (termRename ρ t) = evalT F env' t
  | .var n => (h n).symm
  | .func f ts => by
    show F f (evalTList F env (termRenameList ρ ts)) = F f (evalTList F env' ts)
    rw [evalTList_rename F h ts]

theorem evalTList_rename (F : Nat → List ZFSet.{u} → ZFSet.{u})
    {env env' : Nat → ZFSet.{u}} {ρ : Nat → Nat} (h : ∀ n, env' n = env (ρ n)) :
    ∀ ts : List Term, evalTList F env (termRenameList ρ ts) = evalTList F env' ts
  | [] => rfl
  | t :: ts => by
    show evalT F env (termRename ρ t) :: evalTList F env (termRenameList ρ ts)
        = evalT F env' t :: evalTList F env' ts
    rw [evalT_rename F h t, evalTList_rename F h ts]

end

/-- Renaming is a change of assignment. The one lemma the quantifier rules
need: `shift` and instantiation are both renamings, so both are read off this.

The two assignments are related pointwise rather than by composition, so
`funext` is not needed. Under a binder the relation is re-established by cases
on the index, by `up`. -/
theorem eval_rename (D : ZFSet.{u}) (F : Nat → List ZFSet.{u} → ZFSet.{u})
    (R : Nat → List ZFSet.{u} → Prop) :
    ∀ (φ : Formula) (ρ : Nat → Nat) (env env' : Nat → ZFSet.{u}),
      (∀ n, env' n = env (ρ n)) →
      (evalF D F R env (rename ρ φ) ↔ evalF D F R env' φ)
  | .rel r ts, ρ, env, env', h => by
    show R r (evalTList F env (termRenameList ρ ts)) ↔ R r (evalTList F env' ts)
    rw [evalTList_rename F h ts]
  | .eq a b, ρ, env, env', h => by
    show evalT F env (termRename ρ a) = evalT F env (termRename ρ b)
        ↔ evalT F env' a = evalT F env' b
    rw [evalT_rename F h a, evalT_rename F h b]
  | .fls, _, _, _, _ => Iff.rfl
  | .imp φ ψ, ρ, env, env', h =>
    ⟨fun hd hφ => (eval_rename D F R ψ ρ env env' h).mp
        (hd ((eval_rename D F R φ ρ env env' h).mpr hφ)),
      fun hd hφ => (eval_rename D F R ψ ρ env env' h).mpr
        (hd ((eval_rename D F R φ ρ env env' h).mp hφ))⟩
  | .conj φ ψ, ρ, env, env', h =>
    ⟨fun hd => ⟨(eval_rename D F R φ ρ env env' h).mp hd.left,
        (eval_rename D F R ψ ρ env env' h).mp hd.right⟩,
      fun hd => ⟨(eval_rename D F R φ ρ env env' h).mpr hd.left,
        (eval_rename D F R ψ ρ env env' h).mpr hd.right⟩⟩
  | .disj φ ψ, ρ, env, env', h =>
    ⟨fun hd => hd.elim (fun hl => Or.inl ((eval_rename D F R φ ρ env env' h).mp hl))
        (fun hr => Or.inr ((eval_rename D F R ψ ρ env env' h).mp hr)),
      fun hd => hd.elim (fun hl => Or.inl ((eval_rename D F R φ ρ env env' h).mpr hl))
        (fun hr => Or.inr ((eval_rename D F R ψ ρ env env' h).mpr hr))⟩
  | .all φ, ρ, env, env', h =>
    ⟨fun hd a ha => (eval_rename D F R φ (up ρ) (cons a env) (cons a env')
        (cons_up h a)).mp (hd a ha),
      fun hd a ha => (eval_rename D F R φ (up ρ) (cons a env) (cons a env')
        (cons_up h a)).mpr (hd a ha)⟩
  | .ex φ, ρ, env, env', h =>
    ⟨fun hd => hd.elim fun a ha => ⟨a, ha.left,
        (eval_rename D F R φ (up ρ) (cons a env) (cons a env') (cons_up h a)).mp ha.right⟩,
      fun hd => hd.elim fun a ha => ⟨a, ha.left,
        (eval_rename D F R φ (up ρ) (cons a env) (cons a env') (cons_up h a)).mpr ha.right⟩⟩

theorem eval_shift (D : ZFSet.{u}) (F : Nat → List ZFSet.{u} → ZFSet.{u})
    (R : Nat → List ZFSet.{u} → Prop)
    (φ : Formula) (a : ZFSet.{u}) (env : Nat → ZFSet.{u}) :
    evalF D F R (cons a env) (shift φ) ↔ evalF D F R env φ :=
  eval_rename D F R φ Nat.succ (cons a env) env fun _ => rfl

/-! ## Substitution

Renaming sends a variable to a variable, which is all the quantifier rules need
and strictly less than the diagonal lemma needs: instantiating at a numeral
is substituting a closed term. The apparatus is the same shape one level up --
`substUp` plays the role of `up`, and the semantic lemma relates the two
assignments pointwise rather than by composition. -/

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

mutual

theorem evalT_subst (F : Nat → List ZFSet.{u} → ZFSet.{u})
    {env env' : Nat → ZFSet.{u}} {σ : Nat → Term}
    (h : ∀ n, env' n = evalT F env (σ n)) :
    ∀ t : Term, evalT F env (termSubst σ t) = evalT F env' t
  | .var n => (h n).symm
  | .func f ts => by
    show F f (evalTList F env (termSubstList σ ts)) = F f (evalTList F env' ts)
    rw [evalTList_subst F h ts]

theorem evalTList_subst (F : Nat → List ZFSet.{u} → ZFSet.{u})
    {env env' : Nat → ZFSet.{u}} {σ : Nat → Term}
    (h : ∀ n, env' n = evalT F env (σ n)) :
    ∀ ts : List Term, evalTList F env (termSubstList σ ts) = evalTList F env' ts
  | [] => rfl
  | t :: ts => by
    show evalT F env (termSubst σ t) :: evalTList F env (termSubstList σ ts)
        = evalT F env' t :: evalTList F env' ts
    rw [evalT_subst F h t, evalTList_subst F h ts]

end

/-- The pointwise relation between assignments, pushed under a binder. The
lifting in `substUp` is a renaming, read by `evalT_rename`. -/
theorem cons_substUp (F : Nat → List ZFSet.{u} → ZFSet.{u})
    {σ : Nat → Term} {env env' : Nat → ZFSet.{u}}
    (h : ∀ n, env' n = evalT F env (σ n)) (a : ZFSet.{u}) :
    ∀ n, cons a env' n = evalT F (cons a env) (substUp σ n)
  | 0 => rfl
  | n + 1 =>
    (h n).trans (evalT_rename F (env := cons a env) (env' := env)
      (ρ := Nat.succ) (fun _ => rfl) (σ n)).symm


/-- Substitution is a change of assignment. The counterpart of
`eval_rename`. -/
theorem eval_subst (D : ZFSet.{u}) (F : Nat → List ZFSet.{u} → ZFSet.{u})
    (R : Nat → List ZFSet.{u} → Prop) :
    ∀ (φ : Formula) (σ : Nat → Term) (env env' : Nat → ZFSet.{u}),
      (∀ n, env' n = evalT F env (σ n)) →
      (evalF D F R env (subst σ φ) ↔ evalF D F R env' φ)
  | .rel r ts, σ, env, env', h => by
    show R r (evalTList F env (termSubstList σ ts)) ↔ R r (evalTList F env' ts)
    rw [evalTList_subst F h ts]
  | .eq a b, σ, env, env', h => by
    show evalT F env (termSubst σ a) = evalT F env (termSubst σ b)
        ↔ evalT F env' a = evalT F env' b
    rw [evalT_subst F h a, evalT_subst F h b]
  | .fls, _, _, _, _ => Iff.rfl
  | .imp φ ψ, σ, env, env', h =>
    ⟨fun hd hφ => (eval_subst D F R ψ σ env env' h).mp
        (hd ((eval_subst D F R φ σ env env' h).mpr hφ)),
      fun hd hφ => (eval_subst D F R ψ σ env env' h).mpr
        (hd ((eval_subst D F R φ σ env env' h).mp hφ))⟩
  | .conj φ ψ, σ, env, env', h =>
    ⟨fun hd => ⟨(eval_subst D F R φ σ env env' h).mp hd.left,
        (eval_subst D F R ψ σ env env' h).mp hd.right⟩,
      fun hd => ⟨(eval_subst D F R φ σ env env' h).mpr hd.left,
        (eval_subst D F R ψ σ env env' h).mpr hd.right⟩⟩
  | .disj φ ψ, σ, env, env', h =>
    ⟨fun hd => hd.elim (fun hl => Or.inl ((eval_subst D F R φ σ env env' h).mp hl))
        (fun hr => Or.inr ((eval_subst D F R ψ σ env env' h).mp hr)),
      fun hd => hd.elim (fun hl => Or.inl ((eval_subst D F R φ σ env env' h).mpr hl))
        (fun hr => Or.inr ((eval_subst D F R ψ σ env env' h).mpr hr))⟩
  | .all φ, σ, env, env', h =>
    ⟨fun hd a ha => (eval_subst D F R φ (substUp σ) (cons a env) (cons a env')
        (cons_substUp F h a)).mp (hd a ha),
      fun hd a ha => (eval_subst D F R φ (substUp σ) (cons a env) (cons a env')
        (cons_substUp F h a)).mpr (hd a ha)⟩
  | .ex φ, σ, env, env', h =>
    ⟨fun hd => hd.elim fun a ha => ⟨a, ha.left,
        (eval_subst D F R φ (substUp σ) (cons a env) (cons a env')
          (cons_substUp F h a)).mp ha.right⟩,
      fun hd => hd.elim fun a ha => ⟨a, ha.left,
        (eval_subst D F R φ (substUp σ) (cons a env) (cons a env')
          (cons_substUp F h a)).mpr ha.right⟩⟩

/-- Instantiating at a term reads the term's value. The form every later use
takes: `subst (single t) φ` holds exactly when `φ` holds of what `t` denotes. -/
theorem eval_single (D : ZFSet.{u}) (F : Nat → List ZFSet.{u} → ZFSet.{u})
    (R : Nat → List ZFSet.{u} → Prop)
    (φ : Formula) (t : Term) (env : Nat → ZFSet.{u}) :
    evalF D F R env (subst (single t) φ)
      ↔ evalF D F R (cons (evalT F env t) env) φ :=
  eval_subst D F R φ (single t) env (cons (evalT F env t) env) fun n => by
    cases n with
    | zero => rfl
    | succ k => rfl

/-- A domain closed under the interpretation of the function symbols. Vacuous
for a relational language, and the defining condition of a structure once there
are terms: `evalT` must land in `D` for the quantifier rules to instantiate
at a term at all. -/
def ClosedUnder (D : ZFSet.{u}) (F : Nat → List ZFSet.{u} → ZFSet.{u}) : Prop :=
  ∀ f as, (∀ a, a ∈ as → a ∈ D) → F f as ∈ D

mutual

theorem evalT_mem {D : ZFSet.{u}} {F : Nat → List ZFSet.{u} → ZFSet.{u}}
    (hF : ClosedUnder D F) {env : Nat → ZFSet.{u}} (he : ∀ n, env n ∈ D) :
    ∀ t : Term, evalT F env t ∈ D
  | .var n => he n
  | .func f ts => hF f _ (evalTList_mem hF he ts)

theorem evalTList_mem {D : ZFSet.{u}} {F : Nat → List ZFSet.{u} → ZFSet.{u}}
    (hF : ClosedUnder D F) {env : Nat → ZFSet.{u}} (he : ∀ n, env n ∈ D) :
    ∀ ts : List Term, ∀ a, a ∈ evalTList F env ts → a ∈ D
  | [], _, h => absurd h (List.not_mem_nil)
  | t :: ts, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact evalT_mem hF he t
    · exact evalTList_mem hF he ts a h

end

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

theorem evalCtxF_mem {D : ZFSet.{u}} {F : Nat → List ZFSet.{u} → ZFSet.{u}}
    {R : Nat → List ZFSet.{u} → Prop}
    {env : Nat → ZFSet.{u}} : ∀ {Γ : List Formula} {φ : Formula},
    φ ∈ Γ → evalCtxF D F R env Γ → evalF D F R env φ
  | _ :: _, _, .head _, h => h.left
  | _ :: Γ, φ, .tail _ hm, h => evalCtxF_mem (Γ := Γ) (φ := φ) hm h.right

/-- A lifted context holds under an extended assignment exactly when the
original held under the original. -/
theorem evalCtxF_map_shift {D : ZFSet.{u}} {F : Nat → List ZFSet.{u} → ZFSet.{u}}
    {R : Nat → List ZFSet.{u} → Prop}
    {env : Nat → ZFSet.{u}} {a : ZFSet.{u}} : ∀ {Γ : List Formula},
    evalCtxF D F R env Γ → evalCtxF D F R (cons a env) (Γ.map shift)
  | [], _ => trivial
  | φ :: Γ, h =>
    ⟨(eval_shift D F R φ a env).mpr h.left, evalCtxF_map_shift (Γ := Γ) h.right⟩

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
the inclusion transported through that operation, by `cons_sub` and
`map_shift_sub`. -/
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

/-- Soundness. A derivation is a proof, in any domain, under any
interpretation and any assignment taking its values there.

The premise of `all_intro` is about a lifted context, which
`evalCtxF_map_shift` supplies for the extended assignment; no freshness
argument appears. `all_elim` needs the assignment to land in `D`, which is the
only hypothesis the quantifiers add. -/
theorem soundnessFO {D : ZFSet.{u}} {F : Nat → List ZFSet.{u} → ZFSet.{u}}
    {R : Nat → List ZFSet.{u} → Prop}
    {Γ : List Formula} {φ : Formula} (hF : ClosedUnder D F) (d : DerivesFO Γ φ) :
    ∀ env : Nat → ZFSet.{u}, (∀ n, env n ∈ D) → evalCtxF D F R env Γ →
      evalF D F R env φ := by
  induction d with
  | assume hm => exact fun env _ hc => evalCtxF_mem hm hc
  | imp_intro _ ih => exact fun env he hc hφ => ih env he ⟨hφ, hc⟩
  | imp_elim _ _ ih₁ ih₂ => exact fun env he hc => ih₁ env he hc (ih₂ env he hc)
  | conj_intro _ _ ih₁ ih₂ => exact fun env he hc => ⟨ih₁ env he hc, ih₂ env he hc⟩
  | conj_left _ ih => exact fun env he hc => (ih env he hc).left
  | conj_right _ ih => exact fun env he hc => (ih env he hc).right
  | disj_left _ ih => exact fun env he hc => Or.inl (ih env he hc)
  | disj_right _ ih => exact fun env he hc => Or.inr (ih env he hc)
  | disj_elim _ _ _ ih ih₁ ih₂ =>
    exact fun env he hc => (ih env he hc).elim
      (fun h => ih₁ env he ⟨h, hc⟩) (fun h => ih₂ env he ⟨h, hc⟩)
  | fls_elim _ ih => exact fun env he hc => (ih env he hc).elim
  | all_intro _ ih =>
    refine fun env he hc a ha => ih (cons a env) ?_ (evalCtxF_map_shift hc)
    intro n
    cases n with
    | zero => exact ha
    | succ k => exact he k
  | all_elim t _ ih =>
    exact fun env he hc => (eval_single D F R _ t env).mpr
      (ih env he hc _ (evalT_mem hF he t))
  | ex_intro t _ ih =>
    exact fun env he hc => ⟨_, evalT_mem hF he t, (eval_single D F R _ t env).mp
      (ih env he hc)⟩
  | eq_refl t => exact fun _ _ _ => rfl
  | eq_subst a b _ _ iheq ihφ =>
    intro env he hc
    refine (eval_single D F R _ b env).mpr ?_
    have hab : evalT F env a = evalT F env b := iheq env he hc
    have := (eval_single D F R _ a env).mp (ihφ env he hc)
    rwa [hab] at this
  | ex_elim _ _ ih ih₂ =>
    intro env he hc
    obtain ⟨a, ha, hφ⟩ := ih env he hc
    refine (eval_shift D F R _ a env).mp (ih₂ (cons a env) ?_ ⟨hφ, evalCtxF_map_shift hc⟩)
    intro n
    cases n with
    | zero => exact ha
    | succ k => exact he k

/-! ## Which indices a formula reads

Separation's schema needs "φ mentions only its hole", stated syntactically: a
bound on the free indices, checked on the formula itself rather than assumed of
its evaluation.
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

#print axioms cons_substUp
#print axioms eval_subst
#print axioms eval_single
#print axioms evalCtxF_mem
#print axioms cons_sub
#print axioms mem_map_shift
#print axioms mem_map_shift_of_mem
#print axioms map_shift_sub
#print axioms weaken
end Metamath

#print axioms Metamath.cons_up
#print axioms Metamath.evalF
#print axioms Metamath.eval_rename
#print axioms Metamath.eval_shift
#print axioms Metamath.evalCtxF_map_shift
#print axioms Metamath.soundnessFO
#print axioms Metamath.DerivesFO
namespace ZFSet
export Metamath (ClosedUnder DerivesFO Formula FreeBelow Term cons cons_sub cons_substUp cons_up evalCtxF evalCtxF_map_shift evalCtxF_mem evalF eval_rename eval_shift eval_single eval_subst fnot map_shift_sub mem_map_shift mem_map_shift_of_mem rename shift single soundnessFO subst substUp up weaken)
end ZFSet
