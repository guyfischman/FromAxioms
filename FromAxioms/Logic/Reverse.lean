/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Reversals for Phase 1.

`Classical.lean` declares four axioms and derives results from them. The audit
at the bottom of that file records which axiom each result used -- an upper
bound, as always. This file supplies lower bounds for the ones it can: each
theorem below takes a Phase 1 result as a hypothesis and derives the axiom
back, so the two are equivalent rather than merely related.

Nothing here may use an axiom itself. An implication proved with `em` would say
nothing about whether the hypothesis is as strong as `em`, so every result in
this file must audit as does not depend on any axioms.

Two of `Classical.lean`'s consequences are not reversed here and are recorded
as open rather than settled: `drinker` and `exists_not_of_not_forall`. Both are
classical, and neither has been shown to give `em` back.
-/
prelude
import FromAxioms.Logic.Connectives
import FromAxioms.Logic.Equality
import FromAxioms.Logic.Quantifiers
import FromAxioms.Logic.Classical

universe u

/-! ## The principles, named

`Logic/` is `prelude` over its own connectives, so `Constructive.EM` --- stated
over core's `Or` --- is a different proposition and cannot be imported here.
The principles are named inside the foundation that states them, so the
reversals below can bind a name rather than a spelled-out binder; they form
their own node group in the lattice, since no file can import both roots. -/

/-- Excluded middle over this foundation's `Or` and `Not`. -/
def LogicEM : Prop := ∀ a : Prop, Or a (Not a)

/-- Weak excluded middle over this foundation's connectives. -/
def LogicWEM : Prop := ∀ a : Prop, Or (Not a) (Not (Not a))

/-- Double negation elimination. -/
def LogicDNE : Prop := ∀ a : Prop, Not (Not a) → a

/-- Peirce's law. -/
def LogicPeirce : Prop := ∀ a b : Prop, ((a → b) → a) → a

/-- Proof by contradiction, `dne` with `Not a` unfolded. -/
def LogicByContradiction : Prop := ∀ a : Prop, (Not a → False) → a

/-- The classical contrapositive. -/
def LogicContrapose : Prop := ∀ a b : Prop, (Not b → Not a) → a → b

/-- Material implication. -/
def LogicImpIffNotOr : Prop := ∀ a b : Prop, Iff (a → b) (Or (Not a) b)

/-- De Morgan's third law. -/
def LogicNotAndOr : Prop := ∀ a b : Prop, Not (And a b) → Or (Not a) (Not b)

/-- A failed universal has a counterexample. -/
def LogicExistsNotOfNotForall : Prop :=
  ∀ {α : Type} {p : α → Prop}, Not ((x : α) → p x) → Exists (fun x => Not (p x))

/-- The drinker paradox. -/
def LogicDrinker : Prop :=
  ∀ {α : Type} (_ : α) (p : α → Prop), Exists (fun x => p x → (y : α) → p y)

/-! ## Excluded middle

`dne` and `peirce` are each equivalent to `em`, not weaker. The witness in both
cases is the same self-referential trick: feed the negation of `Or a (Not a)`
back into itself, which is exactly the step `Or`'s two constructors are meant to
forbid. -/

/-- Double negation elimination gives `em` back. -/
theorem em_of_dne (h : LogicDNE) (a : Prop) : Or a (Not a) :=
  h (Or a (Not a)) (fun hn => hn (Or.inr (fun ha => hn (Or.inl ha))))

/-- Peirce's law gives `em` back, with `b := False`. -/
theorem em_of_peirce (h : LogicPeirce) (a : Prop) : Or a (Not a) :=
  h (Or a (Not a)) False (fun hn => Or.inr (fun ha => hn (Or.inl ha)))

/-- And `byContradiction`, which is `dne` under another name. -/
theorem em_of_byContradiction (h : LogicByContradiction) (a : Prop) :
    Or a (Not a) :=
  em_of_dne h a


/-- The contrapositive that `Connectives.lean` had to defer is `dne` in
disguise: instantiate it at `Not (Not q)` and `q`, where the hypothesis it wants
is the constructive triple-negation step. -/
theorem em_of_contrapose' (h : LogicContrapose) (a : Prop) :
    Or a (Not a) :=
  em_of_dne (fun q hq => h (Not (Not q)) q (fun hnq hnnq => hnnq hnq) hq) a

/-- Material implication gives `em` back at `a := b`, where the left-hand side
holds for free. -/
theorem em_of_imp_iff_not_or (h : LogicImpIffNotOr)
    (a : Prop) : Or a (Not a) :=
  Or.symm ((h a a).mp (fun ha => ha))

/-! ## Weak excluded middle

De Morgan's third law does not reverse to `em`. It reverses to this, which is
strictly weaker. -/

/-- `Not (And a b) → Or (Not a) (Not b)` gives weak excluded middle, at
`b := Not a`, where the hypothesis is a constructive non-contradiction. -/
theorem wem_of_not_and_or (h : LogicNotAndOr)
    (a : Prop) : Or (Not a) (Not (Not a)) :=
  h a (Not a) (fun hand => hand.right hand.left)

/-- And the converse: `WEM` is enough to prove it, so `WEM` is exactly its
strength. The same pair of proofs appears one phase later for `sdiff_inter`. -/
theorem not_and_or_of_wem (h : LogicWEM) (a b : Prop)
    (hab : Not (And a b)) : Or (Not a) (Not b) :=
  (h a).elim (fun hna => Or.inl hna)
    (fun hnna => Or.inr (fun hb => hnna (fun ha => hab (And.intro ha hb))))

/-! ## The two that only reach weak excluded middle

`exists_not_of_not_forall` and `drinker` were the open entries in
`tools/classical.json`. Both reverse, and both reverse to `WEM` rather than
`em`, so the earlier attempts over `Prop` kept failing: they were
aiming at the wrong target.

The witness is a genuine two-element type, so that a case split on the witness
is available -- over `Prop` there is nothing to split on. The family sends one
element to `a` and the other to `Not a`, making `∀` refutable outright while
`∃ ¬` lands on one side or the other. Landing on the second gives `Not (Not a)`,
not `a`, and that gap is exactly the distance between `WEM` and `em`. -/

/-- A two-element type: the point is that `Two.rec` can case-split on it. -/
inductive Two : Type where
  | zero : Two
  | one : Two

/-- `a` at one element and `Not a` at the other, so the universal is absurd. -/
def twoFam (a : Prop) : Two → Prop :=
  fun t => Two.rec (motive := fun _ => Prop) a (Not a) t

theorem wem_of_exists_not_of_not_forall
    (h : LogicExistsNotOfNotForall)
    (a : Prop) : Or (Not a) (Not (Not a)) :=
  (h (p := twoFam a) (fun hall => (hall Two.one) (hall Two.zero))).elim
    (fun t =>
      Two.rec (motive := fun t => Not (twoFam a t) → Or (Not a) (Not (Not a)))
        (fun hz => Or.inl hz) (fun ho => Or.inr ho) t)

theorem wem_of_drinker
    (h : LogicDrinker)
    (a : Prop) : Or (Not a) (Not (Not a)) :=
  (h Two.zero (twoFam a)).elim
    (fun t =>
      Two.rec
        (motive := fun t => (twoFam a t → (y : Two) → twoFam a y) →
          Or (Not a) (Not (Not a)))
        (fun hz => Or.inl (fun ha => (hz ha Two.one) ha))
        (fun ho => Or.inr (fun hna => hna (ho hna Two.zero)))
        t)

/-! ## The edges out of `em`

Everything above runs into `LogicEM`; the six theorems below run out of it, to
`LogicDNE`, `LogicPeirce`, `LogicByContradiction`, `LogicImpIffNotOr`,
`LogicExistsNotOfNotForall` and `LogicDrinker`. For `drinker` and
`exists_not_of_not_forall` this is the first edge in that direction and does not
bracket them: the direction `X -> LogicEM` stays open for both.

The names carry the `Logic` prefix because the short ones are taken:
`Constructive/Reverse.lean` holds `dne_of_em` over `Constructive.EM`, a
different proposition, since that one is stated over core's `Or` and this
foundation is `prelude` over its own, and that file `export`s it into the root
namespace.

Every one is axiom-free, as the rest of the file is; an implication proved with
`em` would say nothing at all. -/

/-- `em` gives double negation elimination back. -/
theorem logicDNE_of_em (h : LogicEM) : LogicDNE :=
  fun a hnn => (h a).rec (fun ha => ha) (fun hna => (hnn hna).rec)

/-- `em` gives Peirce's law back. The `a` branch is immediate; the `Not a`
branch feeds `a -> b` the refutation, and `False.rec` supplies the `b`. -/
theorem logicPeirce_of_em (h : LogicEM) : LogicPeirce :=
  fun a b hf => (h a).rec (fun ha => ha) (fun hna => hf (fun ha => (hna ha).rec))

/-- `em` gives proof by contradiction back. `LogicByContradiction` is `LogicDNE`
with `Not a` unfolded, so it is the same two cases. -/
theorem logicByContradiction_of_em (h : LogicEM) : LogicByContradiction :=
  fun a hf => (h a).rec (fun ha => ha) (fun hna => (hf hna).rec)

/-- `em` gives material implication back. -/
theorem logicImpIffNotOr_of_em (h : LogicEM) : LogicImpIffNotOr :=
  fun a b =>
    Iff.intro
      (fun hab => (h a).rec (fun ha => Or.inr (hab ha)) (fun hna => Or.inl hna))
      (fun hor ha => hor.rec (fun hna => (hna ha).rec) (fun hb => fun _ => hb) ha)

/-- `em` gives a counterexample to a failed universal.

The split is at the conclusion rather than at `p x`: if the existential holds we
are done, and if it does not then every `x` has `Not (Not (p x))`, which
`logicDNE_of_em` turns into `p x` -- contradicting the hypothesis. -/
theorem logicExistsNotOfNotForall_of_em (h : LogicEM) :
    LogicExistsNotOfNotForall :=
  fun {α} {p} hnf =>
    (h (Exists (fun x => Not (p x)))).rec
      (fun hex => hex)
      (fun hnex =>
        (hnf (fun x =>
          logicDNE_of_em h (p x) (fun hnp => hnex (Exists.intro x hnp)))).rec)

/-- `em` gives the drinker paradox back.

`em` on does every `y` satisfy `p`: if so, any inhabitant will do and the
implication ignores its premise; if not, the counterexample
`logicExistsNotOfNotForall_of_em` produces is a witness whose own premise is
refuted, so the implication holds vacuously. The first branch is what consumes
the inhabitant `LogicDrinker` binds, and is why it binds one. -/
theorem logicDrinker_of_em (h : LogicEM) : LogicDrinker :=
  fun {α} a p =>
    (h ((y : α) → p y)).rec
      (fun hall => Exists.intro a (fun _ => hall))
      (fun hnall =>
        (logicExistsNotOfNotForall_of_em h hnall).rec
          (fun x hnx => Exists.intro x (fun hx => (hnx hx).rec)))

/-- `em` gives the classical contrapositive back. `em_of_contrapose'` above runs
the other way, so the two are equivalent.

Split at `b`: that branch is immediate, and the `Not b` branch feeds the
hypothesis the refutation to get `Not a`, which `ha` contradicts, and `False.rec`
supplies the `b`. The same two cases as `logicByContradiction_of_em`. -/
theorem logicContrapose_of_em (h : LogicEM) : LogicContrapose :=
  fun _ b hba ha => (h b).rec (fun hb => hb) (fun hnb => (hba hnb ha).rec)

#print axioms logicContrapose_of_em

/-! ## Choice

`Exists.witness` and `Exists.witness_spec` split the axiom into its data and
its property, so putting them back together is the axiom. The reversal is a
one-liner: unlike the results above, these two are not a consequence of
`choice` that might have been weaker -- they are `choice`. -/

-- `def`, not `theorem`: `Subtype p` is data, so this lands in `Sort u`
def choice_of_witness
    (w : ∀ {α : Sort u} {p : α → Prop}, Exists p → α)
    (spec : ∀ {α : Sort u} {p : α → Prop} (h : Exists p), p (w h))
    {α : Sort u} {p : α → Prop} (h : Exists p) : Subtype p :=
  Subtype.mk (w h) (spec h)

/-! ## Proving by cases, and defining by cases

`em` gives `Or p (Not p)`, which lives in `Prop` and so cannot eliminate into
`Type`. A proof may split on it; a definition may not. The gap between the two
is measured here rather than described: `Decider` is the decision as data, and
the two directions below carry different audit lines.

Four classical results in Phase 2 sit on exactly this -- `realMul`, `dcNum`,
`dcDigit` and `dcNum` all define data by cases and so are marked `reversed`
with no forward direction. -/

/-- A decision as data: which side holds, in a `Type`. -/
inductive Decider (p : Prop) : Type where
  | isTrue : p -> Decider p
  | isFalse : Not p -> Decider p

/-- Data decides, so it proves. Axiom-free: `Decider` lands in `Type` and
eliminates into `Prop` without restriction. -/
theorem em_of_decider (d : (q : Prop) -> Decider q) (p : Prop) : Or p (Not p) :=
  (d p).rec (fun hp => Or.inl hp) (fun hn => Or.inr hn)

-- `def`, not `theorem`: `Decider p` is data. The audit line is the result --
-- `choice`, with `em` supplied as a hypothesis rather than used
noncomputable def decider_of_em
    (h : LogicEM) (p : Prop) : Decider p :=
  Exists.witness (α := Decider p) (p := fun _ => True)
    ((h p).rec (fun hp => Exists.intro (Decider.isTrue hp) True.intro)
      (fun hn => Exists.intro (Decider.isFalse hn) True.intro))

#print axioms em_of_dne
#print axioms em_of_peirce
#print axioms em_of_byContradiction
#print axioms em_of_contrapose'
#print axioms em_of_imp_iff_not_or
#print axioms logicDNE_of_em
#print axioms logicPeirce_of_em
#print axioms logicByContradiction_of_em
#print axioms logicImpIffNotOr_of_em
#print axioms logicExistsNotOfNotForall_of_em
#print axioms logicDrinker_of_em
#print axioms wem_of_not_and_or
#print axioms not_and_or_of_wem
#print axioms wem_of_exists_not_of_not_forall
#print axioms wem_of_drinker
#print axioms choice_of_witness
#print axioms em_of_decider
#print axioms decider_of_em
#print axioms LogicEM
#print axioms LogicWEM
#print axioms LogicDNE
#print axioms LogicPeirce
#print axioms LogicByContradiction
#print axioms LogicContrapose
#print axioms LogicImpIffNotOr
#print axioms LogicNotAndOr
#print axioms LogicExistsNotOfNotForall
#print axioms LogicDrinker
