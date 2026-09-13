/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

import Mathlib.Data.Prod.Basic

/-!
# The challenge: an ordered pair is determined by its coordinates, in MATHLIB's words

`Prod` and its `(a, b)` notation are Mathlib's. `Prod.mk.injEq` and `Prod.ext`
are NOT named, and the Solution may not close this by `simp` --- which would
discharge it from the inductive's own injectivity and use nothing else.

## Which statement, and why it is the right one to ask for

This is the row `the ⟨a,b⟩ = {{a},{a,b}} encoding`, whose whole content is that
the KURATOWSKI encoding reproduces the defining property of an ordered pair.
Mathlib gets that property for free: `Prod` is an inductive with two fields, so
injectivity is a constructor fact and there is nothing to prove. The tower has no
primitive product --- it has sets --- so it must DERIVE the same property for
`opair a b = {{a}, {a,b}}`, which is `CategoryTheory`-free set theory and takes a
genuine argument (`opair_injective`, four cases through
`pair_eq_singleton_iff`).

So the comparison is exactly the interesting one: mathlib ASSUMES what the tower
PROVES, and this pair checks that what the tower proves really is what mathlib
assumes.

## Why the Solution is not circular

`Bridge/TypeTransferU` encodes a `Type` into `ZFSet` and consumes nothing
whatever about pairs --- no `Prod`, no `opair`, no injectivity. So the tower's
`ZFSet.opair_eq_opair_iff` is not a fact the bridge assumed, and routing this
statement through it is a real transfer rather than a restatement.

## Stated at `Nat`

`encodeU` needs a `Type u`; the statement is universally quantified over the four
coordinates, and nothing in the argument depends on the carrier beyond having an
injective encoding into `ZFSet`. `Nat` is written rather than a variable `α` only
so the challenge names no bridge vocabulary of its own.
-/

namespace Comparator.PairEncoding

/-- The challenge. An ordered pair determines its coordinates.

`Solution.lean` must close this using the `FromAxioms` tower. Nothing in this
file may be changed to make that easier. -/
def challenge : Prop :=
  ∀ a b c d : Nat, (a, b) = (c, d) ↔ a = c ∧ b = d

/-- The challenge is not vacuous, and Mathlib itself is the witness --- here
by the constructor fact the Solution is forbidden to use.

A `Prop` nobody has shown inhabited says nothing --- and a draft of the
`Adjunction` challenge factored its equation into a helper returning `True`,
which would have made that whole pair vacuous while still compiling. That is the
failure this theorem exists to exclude. -/
theorem challenge_is_mathlibs : challenge := by
  intro a b c d
  exact Prod.mk.injEq a b c d ▸ Iff.rfl

end Comparator.PairEncoding
