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

/-! ## Excluded middle

`dne` and `peirce` are each equivalent to `em`, not weaker. The witness in both
cases is the same self-referential trick: feed the negation of `Or a (Not a)`
back into itself, which is exactly the step `Or`'s two constructors are meant to
forbid. -/

/-- Double negation elimination gives `em` back. -/
theorem em_of_dne (h : ∀ a : Prop, Not (Not a) → a) (a : Prop) : Or a (Not a) :=
  h (Or a (Not a)) (fun hn => hn (Or.inr (fun ha => hn (Or.inl ha))))

/-- Peirce's law gives `em` back, with `b := False`. -/
theorem em_of_peirce (h : ∀ a b : Prop, ((a → b) → a) → a) (a : Prop) : Or a (Not a) :=
  h (Or a (Not a)) False (fun hn => Or.inr (fun ha => hn (Or.inl ha)))

/-- And `byContradiction`, which is `dne` under another name. -/
theorem em_of_byContradiction (h : ∀ a : Prop, (Not a → False) → a) (a : Prop) :
    Or a (Not a) :=
  em_of_dne h a


/-- The contrapositive that `Connectives.lean` had to defer is `dne` in
disguise: instantiate it at `Not (Not q)` and `q`, where the hypothesis it wants
is the constructive triple-negation step. -/
theorem em_of_contrapose' (h : ∀ a b : Prop, (Not b → Not a) → a → b) (a : Prop) :
    Or a (Not a) :=
  em_of_dne (fun q hq => h (Not (Not q)) q (fun hnq hnnq => hnnq hnq) hq) a

/-- Material implication gives `em` back at `a := b`, where the left-hand side
holds for free. -/
theorem em_of_imp_iff_not_or (h : ∀ a b : Prop, Iff (a → b) (Or (Not a) b))
    (a : Prop) : Or a (Not a) :=
  Or.symm ((h a a).mp (fun ha => ha))

/-! ## Weak excluded middle

De Morgan's third law does not reverse to `em`. It reverses to this, which is
strictly weaker. -/

/-- `Not (And a b) → Or (Not a) (Not b)` gives weak excluded middle, at
`b := Not a`, where the hypothesis is a constructive non-contradiction. -/
theorem wem_of_not_and_or (h : ∀ a b : Prop, Not (And a b) → Or (Not a) (Not b))
    (a : Prop) : Or (Not a) (Not (Not a)) :=
  h a (Not a) (fun hand => hand.right hand.left)

/-- And the converse: `WEM` is enough to prove it, so `WEM` is exactly its
strength. The same pair of proofs appears one phase later for `sdiff_inter`. -/
theorem not_and_or_of_wem (h : ∀ a : Prop, Or (Not a) (Not (Not a))) (a b : Prop)
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
    (h : ∀ {α : Type} {p : α → Prop}, Not ((x : α) → p x) →
      Exists (fun x => Not (p x)))
    (a : Prop) : Or (Not a) (Not (Not a)) :=
  (h (p := twoFam a) (fun hall => (hall Two.one) (hall Two.zero))).elim
    (fun t =>
      Two.rec (motive := fun t => Not (twoFam a t) → Or (Not a) (Not (Not a)))
        (fun hz => Or.inl hz) (fun ho => Or.inr ho) t)

theorem wem_of_drinker
    (h : ∀ {α : Type} (_ : α) (p : α → Prop), Exists (fun x => p x → (y : α) → p y))
    (a : Prop) : Or (Not a) (Not (Not a)) :=
  (h Two.zero (twoFam a)).elim
    (fun t =>
      Two.rec
        (motive := fun t => (twoFam a t → (y : Two) → twoFam a y) →
          Or (Not a) (Not (Not a)))
        (fun hz => Or.inl (fun ha => (hz ha Two.one) ha))
        (fun ho => Or.inr (fun hna => hna (ho hna Two.zero)))
        t)

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
    (h : (q : Prop) -> Or q (Not q)) (p : Prop) : Decider p :=
  Exists.witness (α := Decider p) (p := fun _ => True)
    ((h p).rec (fun hp => Exists.intro (Decider.isTrue hp) True.intro)
      (fun hn => Exists.intro (Decider.isFalse hn) True.intro))

#print axioms em_of_dne
#print axioms em_of_peirce
#print axioms em_of_byContradiction
#print axioms em_of_contrapose'
#print axioms em_of_imp_iff_not_or
#print axioms wem_of_not_and_or
#print axioms not_and_or_of_wem
#print axioms wem_of_exists_not_of_not_forall
#print axioms wem_of_drinker
#print axioms choice_of_witness
#print axioms em_of_decider
#print axioms decider_of_em
