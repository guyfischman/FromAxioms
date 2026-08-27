/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Equality.

`Eq` is an inductive family, indexed by its right-hand argument, with a
single constructor `refl` that can only ever produce `Eq a a`. That indexing is
the whole content: because the only way to build a proof of `Eq a b` forces the
two sides to coincide, the recursor is entitled to assume they coincide, and so
can transport any property from one side to the other.

That transport is the elimination rule -- the J rule, or path induction -- and
it is why substitution is a theorem here rather than an inference rule bolted
onto the logic.

Every proof below is a direct application of `Eq.rec` with the motive written
out explicitly, since the motive says which property is transported and is
the step worth reading.
-/
prelude
import FromAxioms.Logic.Connectives

universe u v

/-! ## The definition -/

/-- `Eq` is an inductive family indexed by its second argument. The single
constructor `refl` can only produce `Eq a a`, and *that constraint is the
definition of equality*. Nothing else is asserted about it. -/
inductive Eq {α : Sort u} : α → α → Prop where
  | refl (a : α) : Eq a a

/-- The usual shorthand, with both arguments implicit. -/
theorem rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

/-! ## The three basic laws

Equality being an equivalence relation is not assumed. Reflexivity is the
constructor; symmetry and transitivity have to be earned from the recursor.
-/

/-- Symmetry. Transport the property "is equal to `a`" along `h`.

Read the motive `fun x _ => Eq x a` as: we are proving something about the
right-hand side, generalized. At `x := a` the goal is `Eq a a`, discharged by
`refl`; the recursor then hands it back at `x := b`. -/
theorem Eq.symm {α : Sort u} {a b : α} (h : Eq a b) : Eq b a :=
  h.rec (motive := fun x _ => Eq x a) (Eq.refl a)

/-- Transitivity. Same shape as `symm`, different motive: here we transport
"`a` is equal to it" along the second hypothesis. -/
theorem Eq.trans {α : Sort u} {a b c : α} (hab : Eq a b) (hbc : Eq b c) :
    Eq a c :=
  hbc.rec (motive := fun x _ => Eq a x) hab

/-! ## Substitution and congruence -/

/-- Substitution: any property `p` true of `a` is true of anything equal to `a`.

This is the Leibniz principle, and in most presentations of logic it is an
axiom schema. Here it is a one-line consequence of the recursor. -/
theorem Eq.subst {α : Sort u} {p : α → Prop} {a b : α} (h : Eq a b) (hp : p a) :
    p b :=
  h.rec (motive := fun x _ => p x) hp

/-- Congruence in the argument: functions respect equality.

Note what is not being claimed -- nothing about `f` is assumed. Every function
in type theory is automatically congruent, because there is no way to write one
that inspects its argument other than through the eliminators. -/
theorem congrArg {α : Sort u} {β : Sort v} {a b : α} (f : α → β) (h : Eq a b) :
    Eq (f a) (f b) :=
  h.rec (motive := fun x _ => Eq (f a) (f x)) (Eq.refl (f a))

/-- Congruence in the function, stated dependently: equal functions agree at
every argument.

The motive's binder needs its type spelled out here, unlike everywhere else in
this file. `β` is a family, so `x a` cannot be elaborated until Lean knows that
`x` is a dependent function; left to inference it produces an unsolved
metavariable rather than a motive. -/
theorem congrFun {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
    (h : Eq f g) (a : α) : Eq (f a) (g a) :=
  h.rec (motive := fun (x : (y : α) → β y) _ => Eq (f a) (x a)) (Eq.refl (f a))

/-- Congruence in both positions at once, assembled from the previous two. The
first real proof in this project that composes earlier results instead of
reaching for the recursor. -/
theorem congr {α : Sort u} {β : Sort v} {f g : α → β} {a b : α}
    (hf : Eq f g) (ha : Eq a b) : Eq (f a) (g b) :=
  Eq.trans (congrFun hf a) (congrArg g ha)

/-! ## Transport between types

The results above transport properties. The recursor will also transport
elements, because `Eq` admits large elimination: its motive may land in an
arbitrary `Sort v`, not merely in `Prop`.

These are `def`s rather than `theorem`s -- they compute, and their results are
data rather than proofs.
-/

/-- Coercion along an equality of types. Here `Eq` is instantiated at
`Sort u : Sort (u+1)`, so the two sides being compared are themselves types. -/
def cast {α β : Sort u} (h : Eq α β) (a : α) : β :=
  h.rec (motive := fun x _ => x) a

/-- Modus ponens for propositional equality. -/
def Eq.mp {α β : Prop} (h : Eq α β) (ha : α) : β :=
  h.rec (motive := fun x _ => x) ha

def Eq.mpr {α β : Prop} (h : Eq α β) (hb : β) : α :=
  (Eq.symm h).mp hb

/-! ## Disequality -/

/-- `Ne a b` is defined, not primitive: it is `Eq a b` implying absurdity. This
is the first result to depend on `Connectives.lean`. -/
def Ne {α : Sort u} (a b : α) : Prop := Not (Eq a b)

theorem Ne.symm {α : Sort u} {a b : α} (h : Ne a b) : Ne b a :=
  fun hba => h (Eq.symm hba)

/-- Nothing is unequal to itself. -/
theorem Ne.irrefl {α : Sort u} {a : α} (h : Ne a a) : False :=
  h rfl

/-- If `a = b` and `a ≠ b`, anything follows. -/
theorem ne_absurd {α : Sort u} {a b : α} (h : Eq a b) (hn : Ne a b) : False :=
  hn h

/-! ## Proof irrelevance, for free

Any two proofs of the same proposition are equal -- and the proof is `refl`,
meaning Lean considers them definitionally equal, not merely provably so.

This is a genuine choice baked into Lean's kernel rather than a consequence of
anything above, and it is worth noticing early: it is why `Prop` can be erased
at compile time, and why the specific proof term inside a structure never
affects that structure's identity.
-/

theorem proof_irrel {a : Prop} (h₁ h₂ : a) : Eq h₁ h₂ := rfl

/-! ## What is not here

Two principles that belong with equality are not here, because neither is
provable from what has been assumed so far:

* Function extensionality -- pointwise-equal functions are equal. In Lean
  this follows from quotient types, via the `Quot.sound` axiom. `congrFun`
  above is its converse, and the converse is the easy direction.
* Propositional extensionality -- logically equivalent propositions are
  equal. This is the `propext` axiom outright.

Both are honest axioms, and both will appear in `Logic/Classical.lean` where
they can be declared and audited alongside excluded middle. Leaving them out
here keeps this file at zero axiom dependencies.
-/

#print axioms Eq.symm
#print axioms Eq.subst
#print axioms congr
#print axioms cast
#print axioms proof_irrel
