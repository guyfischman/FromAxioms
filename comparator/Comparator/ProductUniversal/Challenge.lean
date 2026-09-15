/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
CHALLENGE: the ordered pair has the universal property of a product.

Mathlib's vocabulary: `Prod`, `Prod.fst`, `Prod.snd`, `∃!`.

WHICH ROW, AND WHY THIS STATEMENT RATHER THAN INJECTIVITY. The row is `ordered
pair from sets`, whose `mathlib` field reads `Prod (primitive) / ZFSet.pair` and
whose `mathlib_form` names `SetTheory.opair_isProd` --- the tower's four-clause
bundle: two projection rules, an eta rule, and injectivity.

Injectivity alone is already paired, at `comparator/Comparator/PairEncoding/`,
credited to the row `the ⟨a,b⟩ = {{a},{a,b}} encoding`. Restating it over an
arbitrary type would be a generalisation of an existing pair rather than a new
one. The UNIVERSAL PROPERTY is the statement the other three clauses are for, and
no pair on this track carries it: a pair of maps out of any type factors through
the product, uniquely.

WHERE THE CONTENT SITS, WHICH IS NOT WHERE IT LOOKS. Existence is `rfl` in Lean
--- `fun z => (f z, g z)` satisfies both equations by computation, because
`Prod` is a primitive with definitional projections. UNIQUENESS is the half with
mathematics in it: it needs that a pair is determined by its coordinates, which
mathlib gets from `Prod.ext` and the tower has to prove about the Kuratowski
encoding. `Solution.lean` therefore routes uniqueness through
`SetTheory.opair_eq_opair_iff` and says so.
-/
import Mathlib.Data.Prod.Basic

namespace Comparator.ProductUniversal

/-- The challenge. Two maps out of a type factor uniquely through the
product.

`Solution.lean` must close this using the `FromAxioms` tower. Nothing in this
file may be changed to make that easier. -/
def challenge : Prop :=
  ∀ (α β Z : Type) (f : Z → α) (g : Z → β),
    ∃! h : Z → α × β, (∀ z, (h z).1 = f z) ∧ (∀ z, (h z).2 = g z)

/-- `challenge` is Mathlib's, checked by discharging it from Mathlib. The two
existence clauses are `rfl`; uniqueness is `Prod.ext`. -/
theorem challenge_is_mathlibs : challenge := by
  intro _α _β _Z f g
  refine ⟨fun z => (f z, g z), ⟨fun _ => rfl, fun _ => rfl⟩, ?_⟩
  rintro k ⟨h1, h2⟩
  funext z
  exact Prod.ext (h1 z) (h2 z)

#print axioms challenge_is_mathlibs

end Comparator.ProductUniversal
