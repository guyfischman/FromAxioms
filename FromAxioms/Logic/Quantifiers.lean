/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Quantifiers.

Universal quantification is not a new construct in type theory -- it is the
dependent function arrow. A proof of "for every `a`, `p a`" is literally a
function taking `a` to a proof of `p a`, so `∀`-introduction is lambda
abstraction and `∀`-elimination is function application.

Statements below therefore spell universals as `(a : α) → p a` rather than
`∀ a, p a`, to keep that identification in view.

Existential quantification is the new thing. `Exists` is an inductive family
whose constructor carries data -- a witness -- yet the family itself lives in
`Prop`. Those two facts are in tension, and the kernel resolves it by refusing
to let the witness back out; see the section on large elimination below.
-/
prelude
import FromAxioms.Logic.Connectives
import FromAxioms.Logic.Equality

universe u v

/-! ## Universal quantification is the dependent arrow

Nothing to define. These two are the introduction and elimination rules, and
both are already primitive -- stated here only to name them. -/

/-- ∀-introduction: a proof for an arbitrary `a` is a proof for all `a`. This is
lambda abstraction, and the proof term is the identity. -/
theorem forall_intro {α : Sort u} {p : α → Prop} (h : (a : α) → p a) :
    (a : α) → p a := h

/-- ∀-elimination, i.e. instantiation. This is function application. -/
theorem forall_elim {α : Sort u} {p : α → Prop} (h : (a : α) → p a) (a : α) :
    p a := h a

/-! ## Existential quantification -/

/-- `Exists p` has one constructor, which packages a witness `w` together with
a proof that `w` satisfies `p`.

The constructor takes `w : α`, which is data, not a proof -- yet `Exists p`
is a `Prop`. That combination is what makes the elimination rule restrictive. -/
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p

/-- ∃-elimination: to use an existential, prove your goal from an arbitrary
witness. The witness is bound inside `hb` and cannot escape it.

`b` here is a `Prop`; see below. -/
theorem Exists.elim {α : Sort u} {p : α → Prop} {b : Prop}
    (h : Exists p) (hb : (a : α) → p a → b) : b :=
  h.rec hb

/-- Existentials are covariant in the predicate. -/
theorem Exists.imp {α : Sort u} {p q : α → Prop}
    (hpq : (a : α) → p a → q a) (h : Exists p) : Exists q :=
  h.elim (fun w hw => Exists.intro w (hpq w hw))

/-- Anything is equal to something -- the smallest use of `Equality.lean`, and
the first result in this project to draw on two earlier files at once. -/
theorem exists_eq {α : Sort u} (a : α) : Exists (fun x => Eq x a) :=
  Exists.intro a rfl

/-! ## Large elimination, and why `Exists` does not have it

`Exists.elim` lands in `Prop`. It cannot be made to land in `Type`, and the
following is rejected by the kernel:

```
def Exists.witness {α : Sort u} {p : α → Prop} (h : Exists p) : α :=
  h.rec (fun w _ => w)
```
```
error: failed to elaborate eliminator, invalid motive
  fun x => α
```

The rule the kernel is enforcing: an inductive type in `Prop` may eliminate into
an arbitrary `Sort` only if it is a subsingleton -- at most one constructor,
all of whose arguments are themselves proofs. `And` and `Eq` qualify, which is
why `cast` was allowed in `Equality.lean`. `Exists` does not qualify: its `w`
argument is data.

If a witness could be extracted, `Prop` could no longer be erased at compile
time, and a proof by contradiction that something exists would yield an actual
object. The restriction separates the classical and the constructive readings
of `Exists`.

The Type-level counterpart, where extraction is allowed, is `Subtype`.
-/

/-- `Subtype p` is the existential's data-carrying twin: the same witness and
proof, packaged in a type that is not a `Prop`.

Lean infers the universe `Sort (max 1 u)`, which is never `Prop` no matter what
`u` is. So large elimination is unobstructed, and the generated projection
`Subtype.val` is exactly the witness-extraction that `Exists` is denied. The two
declarations carry identical information; only their sort differs, and that
difference alone decides whether the witness can be recovered.

Declared as a `structure` rather than an `inductive` with hand-written
projections: `structure` works in prelude mode and its projections compile,
whereas a `def` over the raw recursor is rejected by the code generator --
code generator does not support recursor `Subtype.rec` yet. That is a
limitation of Lean's compiler backend, not of the kernel; the mathematics is
unaffected. -/
structure Subtype {α : Sort u} (p : α → Prop) where
  mk ::
  val : α
  property : p val

/-- Forgetting the data recovers the proposition. The converse direction --
`Exists p → Subtype p`, choosing a witness from a mere proof of existence -- is
exactly the axiom of choice, and is absent. -/
theorem Subtype.exists {α : Sort u} {p : α → Prop} (s : Subtype p) : Exists p :=
  Exists.intro s.val s.property

/-! ## Quantifier duality

Three of the four de Morgan laws for quantifiers are constructive. The fourth is
not, and is deferred to `Logic/Classical.lean`. Which one fails is worth
predicting before reading on.
-/

/-- If nothing satisfies `p`, then nothing satisfies `p`. -/
theorem not_exists_of_forall_not {α : Sort u} {p : α → Prop}
    (h : (a : α) → Not (p a)) : Not (Exists p) :=
  fun he => he.elim (fun w hw => h w hw)

/-- The converse, also constructive. -/
theorem forall_not_of_not_exists {α : Sort u} {p : α → Prop}
    (h : Not (Exists p)) : (a : α) → Not (p a) :=
  fun a ha => h (Exists.intro a ha)

/-- A counterexample refutes a universal. Constructive: the witness is supplied,
so nothing needs to be conjured. -/
theorem not_forall_of_exists_not {α : Sort u} {p : α → Prop}
    (h : Exists (fun a => Not (p a))) : Not ((a : α) → p a) :=
  fun hf => h.elim (fun w hw => hw (hf w))

/-
The missing fourth law is `Not ((a : α) → p a) → Exists (fun a => Not (p a))`:
from the failure of a universal, produce a counterexample. It is not provable
here, for a structural reason -- the hypothesis is a function into `False` and
contains no witness anywhere, while the conclusion requires one. Nothing in the
type theory can manufacture it.

It appears in `Logic/Classical.lean`, where excluded middle supplies it.
-/

/-! ## Quantifiers against the connectives -/

/-- Existentials distribute over disjunction, in both directions. -/
theorem exists_or {α : Sort u} {p q : α → Prop} :
    Iff (Exists (fun a => Or (p a) (q a))) (Or (Exists p) (Exists q)) :=
  Iff.intro
    (fun h => h.elim (fun w hw => hw.elim
      (fun hp => Or.inl (Exists.intro w hp))
      (fun hq => Or.inr (Exists.intro w hq))))
    (fun h => h.elim
      (fun he => he.elim (fun w hw => Exists.intro w (Or.inl hw)))
      (fun he => he.elim (fun w hw => Exists.intro w (Or.inr hw))))

/-- Universals distribute over conjunction, in both directions. -/
theorem forall_and {α : Sort u} {p q : α → Prop} :
    Iff ((a : α) → And (p a) (q a))
        (And ((a : α) → p a) ((a : α) → q a)) :=
  Iff.intro
    (fun h => And.intro (fun a => (h a).left) (fun a => (h a).right))
    (fun h => fun a => And.intro (h.left a) (h.right a))

/-- One direction only. Existentials do not distribute over conjunction: from
witnesses for `p` and for `q` separately there is no reason they agree, so the
converse is not merely unproved here but false. -/
theorem exists_and_of_and_exists {α : Sort u} {p q : α → Prop}
    (h : Exists (fun a => And (p a) (q a))) : And (Exists p) (Exists q) :=
  And.intro
    (h.elim (fun w hw => Exists.intro w hw.left))
    (h.elim (fun w hw => Exists.intro w hw.right))

#print axioms Exists.elim
#print axioms exists_eq
#print axioms Subtype.exists
#print axioms not_forall_of_exists_not
#print axioms exists_or
