/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Classical logic.

This is the file where axioms enter, and the last file of Phase 1.

Everything up to now has been proved from the type theory alone, with zero
axioms verified mechanically at the bottom of each file. The boundary is now
sharp: from here on `#print axioms` distinguishes results that need classical
reasoning from those that do not.

Four axioms are declared below, each in its own section with the results it
unlocks:

  `em`       excluded middle
  `propext`  logically equivalent propositions are equal
  `funext`   pointwise-equal functions are equal
  `choice`   a proof of existence yields a witness

They are independent, and they are declared separately rather than as one lump
so that the audit can say precisely which of them any given theorem needed.
Lean's own standard library assumes essentially these same three-or-four; the
difference is only that here they are visible.
-/
prelude
import FromAxioms.Logic.Connectives
import FromAxioms.Logic.Equality
import FromAxioms.Logic.Quantifiers

universe u v

/-! ## Excluded middle

The first axiom, and the one that does the most work. Note what it asserts: not
that every proposition is true or false in some metaphysical sense, but that
`Or a (Not a)` is inhabited -- that we may case-split on any proposition
whatever, without knowing which side holds.

That is exactly the capability `Or` was built to deny. `Or` has two
constructors, so holding a proof of `Or a b` means knowing which side it came
from. `em` hands over such a proof for free, and the knowledge is fictitious.
-/

/-- Axiom. Excluded middle. -/
axiom em (a : Prop) : Or a (Not a)

/-- Double negation elimination. Constructively we could prove `a → Not (Not a)`
(that was `not_not_intro`); this is the converse, and it is equivalent to `em`
rather than weaker than it. -/
theorem dne {a : Prop} (h : Not (Not a)) : a :=
  (em a).elim (fun ha => ha) (fun hna => absurd hna h)

/-- Proof by contradiction. Definitionally this is `dne` -- `Not (Not a)`
unfolds to `Not a → False` -- but the two are worth distinguishing by name,
since they read as different proof strategies. -/
theorem byContradiction {a : Prop} (h : Not a → False) : a := dne h

/-- Case analysis on an arbitrary proposition. -/
theorem byCases {a b : Prop} (hpos : a → b) (hneg : Not a → b) : b :=
  (em a).elim hpos hneg

/-- Peirce's law. Purely implicational -- it mentions no connective other than
`→` -- yet it is not constructively provable. A good demonstration that the
constructive/classical split is not about negation specifically. -/
theorem peirce {a b : Prop} (h : (a → b) → a) : a :=
  byContradiction (fun hna => hna (h (fun ha => absurd ha hna)))

/-- The converse of `contrapose` from `Connectives.lean`, which had to be left
out there. -/
theorem contrapose' {a b : Prop} (h : Not b → Not a) : a → b :=
  fun ha => byContradiction (fun hnb => h hnb ha)

/-! ### The de Morgan laws that were missing

`Connectives.lean` and `Quantifiers.lean` each proved one direction and deferred
the other. Both deferred directions land here, and both have the same shape: the
hypothesis is a function into `False`, containing no positive information, while
the conclusion demands a choice of side or a witness. `em` supplies it.
-/

/-- Deferred from `Connectives.lean`. -/
theorem not_and_or {a b : Prop} (h : Not (And a b)) : Or (Not a) (Not b) :=
  (em a).elim
    (fun ha => Or.inr (fun hb => h (And.intro ha hb)))
    (fun hna => Or.inl hna)

/-- Deferred from `Quantifiers.lean`: from the failure of a universal, produce
an actual counterexample. Nothing in the hypothesis contains one. -/
theorem exists_not_of_not_forall {α : Sort u} {p : α → Prop}
    (h : Not ((a : α) → p a)) : Exists (fun a => Not (p a)) :=
  byContradiction (fun hne =>
    h (fun a => byContradiction (fun hna => hne (Exists.intro a hna))))

/-- Implication as disjunction. Constructively `Or (Not a) b` implies `a → b`,
but not conversely. -/
theorem imp_iff_not_or {a b : Prop} : Iff (a → b) (Or (Not a) b) :=
  Iff.intro
    (fun hab => (em a).elim (fun ha => Or.inr (hab ha)) (fun hna => Or.inl hna))
    (fun h ha => h.elim (fun hna => absurd ha hna) (fun hb => hb))

/-- The drinker paradox: in any nonempty room there is someone such that, if
they are drinking, everyone is. A compact illustration of how `em` produces
witnesses out of nothing -- the proof splits on whether some non-drinker exists
and never identifies the person in question. -/
theorem drinker {α : Sort u} (a₀ : α) (p : α → Prop) :
    Exists (fun x => p x → (y : α) → p y) :=
  (em (Exists (fun y => Not (p y)))).elim
    (fun hex => hex.elim (fun w hw => Exists.intro w (fun hpw => absurd hpw hw)))
    (fun hnex =>
      Exists.intro a₀ (fun _ y =>
        byContradiction (fun hny => hnex (Exists.intro y hny))))

/-! ## Propositional extensionality

Deferred from `Equality.lean`. This one is an axiom outright, in this project
and in Lean's standard library alike -- there is no derivation.

It is what makes `Prop` behave like a set of truth values rather than a
collection of distinct proof-objects: combined with the definitional proof
irrelevance noted in `Equality.lean`, it means a proposition is determined
entirely by whether it holds.
-/

/-- Axiom. Logically equivalent propositions are equal. -/
axiom propext {a b : Prop} (h : Iff a b) : Eq a b

/-- Any true proposition is `True`. Not merely equivalent to it -- equal, and
therefore interchangeable everywhere by `Eq.subst`. -/
theorem eq_true {a : Prop} (h : a) : Eq a True :=
  propext (Iff.intro (fun _ => True.intro) (fun _ => h))

theorem eq_false {a : Prop} (h : Not a) : Eq a False :=
  propext (Iff.intro h False.elim)

/-! ## Function extensionality

Also deferred from `Equality.lean`, where `congrFun` gave the easy direction:
equal functions agree pointwise. This is the converse.

Declared as an axiom here. Lean's standard library instead derives it, from
quotient types and the `Quot.sound` axiom -- a genuinely clever argument, but
one that needs the whole quotient apparatus first. Taking it as an axiom costs
one extra line in the audit and keeps Phase 1 self-contained.
-/

/-- Axiom. Pointwise-equal functions are equal. -/
axiom funext {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
    (h : (x : α) → Eq (f x) (g x)) : Eq f g

/-- With `funext`, the converse `congrFun` becomes a genuine equivalence. -/
theorem funext_iff {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x} :
    Iff (Eq f g) ((x : α) → Eq (f x) (g x)) :=
  Iff.intro (fun h a => congrFun h a) funext

/-! ## Choice

The last axiom, and the one that directly overturns the barrier established in
`Quantifiers.lean`.

There, `Exists p` was shown to withhold its witness: it lives in `Prop`, its
constructor carries data, and the kernel therefore refuses to eliminate it into
`Type`. `Subtype p` carries the same information in a sort where extraction is
permitted. The gap between them is precisely this axiom.

Stated in this form it is indefinite description. It is what licenses the
ordinary mathematical move of saying "let `x` be such an object" after merely
proving that one exists.
-/

/-- Axiom. A proof of existence yields a witness. -/
axiom choice {α : Sort u} {p : α → Prop} (h : Exists p) : Subtype p

/-- The extraction that `Quantifiers.lean` demonstrated to be impossible, now
possible. `noncomputable` because `choice` is an axiom: it has no code, so
nothing can be evaluated, and Lean records that fact in the declaration. -/
noncomputable def Exists.witness {α : Sort u} {p : α → Prop} (h : Exists p) : α :=
  (choice h).val

/-- The extracted witness does satisfy the predicate. -/
theorem Exists.witness_spec {α : Sort u} {p : α → Prop} (h : Exists p) :
    p h.witness :=
  (choice h).property

/-! ## Audit

The point of the whole exercise. Every result is now labelled, mechanically,
with the exact axioms it rests on -- and the labels were never written by hand.

Note especially the last two lines: results proved in the earlier files remain
axiom-free even though this module has been imported. Assuming classical logic
does not retroactively contaminate anything. That separation is what constraint
3 in `CLAUDE.md` is protecting, and it is worth re-checking whenever the earlier
files change.
-/

#print axioms dne                     -- expect: em
#print axioms peirce                  -- expect: em
#print axioms exists_not_of_not_forall -- expect: em
#print axioms drinker                 -- expect: em
#print axioms eq_true                 -- expect: propext
#print axioms funext_iff              -- expect: funext
#print axioms Exists.witness          -- expect: choice
#print axioms Exists.witness_spec     -- expect: choice

-- Still constructive, despite everything above being in scope:
