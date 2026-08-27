/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Propositional connectives, from nothing.

This file begins with `prelude`, which instructs Lean to import nothing --
not even `False`. Everything below is built from the two primitives the kernel
itself provides: the ability to declare an inductive type, and the dependent
function arrow.

The introduction rules are the constructors of an inductive type and the
elimination rule is the recursor, so the natural-deduction calculus is not
encoded here: it falls out of the type theory.

`prelude` mode has two consequences. There is no notation -- `notation` and
`infixr` expand into code mentioning `Lean.TrailingParserDescr`, which does
not exist this early -- so connectives are written `And a b` rather than
`a ∧ b`. And an eliminator landing in an arbitrary `Sort u` must be a `def`
rather than a `theorem`, which is why `False.elim` below is one.

Nothing here is classical. There is no excluded middle in this file.
-/
prelude

universe u

/-! ## Falsity and truth -/

/-- `False` is the proposition with no introduction rule: no constructor,
hence no way to prove it. -/
inductive False : Prop

/-- `True` has a trivial introduction rule and no content. -/
inductive True : Prop where
  | intro : True

/-- Ex falso quodlibet. `False` has no constructors, so its recursor has no
cases to handle, and therefore produces a proof of anything. -/
def False.elim {C : Sort u} (h : False) : C :=
  h.rec

/-- Negation is not primitive. -/
def Not (a : Prop) : Prop := a → False

/-- From a proposition and its negation, anything follows. -/
def absurd {a : Prop} {C : Sort u} (h : a) (hn : Not a) : C :=
  False.elim (hn h)

/-! ## Conjunction -/

/-- `And a b` has a single constructor, taking a proof of each side. -/
inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

/-- Left projection, written with the recursor rather than with pattern-matching
sugar, to keep the elimination step visible. -/
theorem And.left {a b : Prop} (h : And a b) : a :=
  h.rec (fun ha _ => ha)

theorem And.right {a b : Prop} (h : And a b) : b :=
  h.rec (fun _ hb => hb)

theorem And.symm {a b : Prop} (h : And a b) : And b a :=
  And.intro h.right h.left

/-! ## Disjunction -/

/-- `Or a b` has two constructors -- two distinct ways to introduce it. This is
exactly why disjunction is constructively stronger than its classical reading:
to hold a proof of `Or a b` is to know which side it came from. -/
inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

/-- Elimination by cases: to use `Or a b`, handle both ways it could have
arisen. This is precisely `Or.rec`. -/
theorem Or.elim {a b c : Prop} (h : Or a b) (hl : a → c) (hr : b → c) : c :=
  h.rec hl hr

theorem Or.symm {a b : Prop} (h : Or a b) : Or b a :=
  h.elim Or.inr Or.inl

/-! ## Bi-implication -/

/-- `Iff` bundles the two implications. -/
inductive Iff (a b : Prop) : Prop where
  | intro : (a → b) → (b → a) → Iff a b

theorem Iff.mp {a b : Prop} (h : Iff a b) : a → b :=
  h.rec (fun mp _ => mp)

theorem Iff.mpr {a b : Prop} (h : Iff a b) : b → a :=
  h.rec (fun _ mpr => mpr)

theorem Iff.refl (a : Prop) : Iff a a :=
  Iff.intro (fun ha => ha) (fun ha => ha)

theorem Iff.symm {a b : Prop} (h : Iff a b) : Iff b a :=
  Iff.intro h.mpr h.mp

theorem Iff.trans {a b c : Prop} (hab : Iff a b) (hbc : Iff b c) : Iff a c :=
  Iff.intro (fun ha => hbc.mp (hab.mp ha)) (fun hc => hab.mpr (hbc.mpr hc))

/-! ## A first batch of theorems

All proved constructively. Nothing below assumes `Or a (Not a)`.
-/

/-- Modus ponens is just function application. -/
theorem mp {a b : Prop} (hab : a → b) (ha : a) : b := hab ha

/-- Contraposition. The converse needs classical logic, and is deferred to
`Logic/Classical.lean`. -/
theorem contrapose {a b : Prop} (h : a → b) : Not b → Not a :=
  fun hnb ha => hnb (h ha)

/-- Introducing double negation is constructive. Eliminating it is not --
that is where excluded middle hides. -/
theorem not_not_intro {a : Prop} (ha : a) : Not (Not a) :=
  fun hna => hna ha

/-- Triple negation collapses, and constructively -- which is not in
tension with the note above. Eliminating `Not (Not a)` for an arbitrary `a` is
excluded middle (`Reverse.lean`); eliminating it for a NEGATION is a theorem,
because `not_not_intro` supplies the missing direction inside the proof.

The converse is `not_not_intro` at `Not a`, so the two together say a negation
is exactly its own double negation. -/
theorem not_not_not {a : Prop} (h : Not (Not (Not a))) : Not a :=
  fun ha => h (fun hna => hna ha)

/-- Non-contradiction. -/
theorem not_and_self {a : Prop} (h : And a (Not a)) : False :=
  h.right h.left

/-- One half of de Morgan. This direction is constructive; the other direction,
`Not (And a b) → Or (Not a) (Not b)`, genuinely requires excluded middle, and
so it too is deferred. -/
theorem not_or_of_not_and_not {a b : Prop} (h : And (Not a) (Not b)) :
    Not (Or a b) :=
  fun hab => hab.elim h.left h.right

theorem not_and_not_of_not_or {a b : Prop} (h : Not (Or a b)) :
    And (Not a) (Not b) :=
  And.intro (fun ha => h (Or.inl ha)) (fun hb => h (Or.inr hb))

/-- Currying: the deduction theorem for conjunction. -/
theorem curry {a b c : Prop} (h : And a b → c) : a → b → c :=
  fun ha hb => h (And.intro ha hb)

theorem uncurry {a b c : Prop} (h : a → b → c) : And a b → c :=
  fun hab => h hab.left hab.right

/-- Distribution of conjunction over disjunction, both directions. Written out
in full, this is the largest term in the file, and a fair taste of what
notation-free term-mode proof feels like. -/
theorem and_or_distrib {a b c : Prop} :
    Iff (And a (Or b c)) (Or (And a b) (And a c)) :=
  Iff.intro
    (fun h => h.right.elim
      (fun hb => Or.inl (And.intro h.left hb))
      (fun hc => Or.inr (And.intro h.left hc)))
    (fun h => h.elim
      (fun hab => And.intro hab.left (Or.inl hab.right))
      (fun hac => And.intro hac.left (Or.inr hac.right)))

/-! ## Audit

`#print axioms` reports which axioms a proof actually depends on. Every result
in this file must report `does not depend on any axioms`.
-/

#print axioms and_or_distrib
#print axioms not_and_not_of_not_or
#print axioms absurd
#print axioms not_not_not
