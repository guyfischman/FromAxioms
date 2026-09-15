/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`, RE-SITED.

THE MATHEMATICS IS `CategoryTheory.prodT_universal` --- the product's universal
property over Lean types, with the product an ABSTRACT object: any `P` with two
projections, a pairing and three equations

    h1     p₁ (pr a b) = a
    h2     p₂ (pr a b) = b
    heta   pr (p₁ w) (p₂ w) = w

satisfies it. The tower supplies the DERIVATION --- that a pair of maps factors,
and that the factorisation is unique --- and this file instantiates it at
mathlib's `Prod`.

THIS PAIR MEASURES SOMETHING DIFFERENT FROM WHAT IT MEASURED BEFORE, AND THAT
MUST BE SAID RATHER THAN LET THROUGH. It is the one re-siting of the seven
where the trade is not free, so the change is written out here in full.

THE OLD PAIR routed uniqueness through `SetTheory.opair_eq_opair_iff` --- that
the Kuratowski encoding `opair a b = {{a}, {a,b}}` determines its coordinates,
proved in the tower from `opair_injective` through `pair_eq_singleton_iff`. That
is real tower mathematics about a set, and it was transported to Lean pairs by
`encP_injective` along `encodeU`. What it cost is `Classical.choice`:
`Bridge/TypeTransferU` is a WELL-ORDERING, `encodeU` factors through `embU`,
which is Mostowski's collapse indexed by `WellOrderingRel`, and well-ordering an
arbitrary type IS the axiom of choice. Not a proof-style artefact and no cheaper
encoding exists.

THE NEW PAIR pays no axiom and asks a different question. `heta` at `Prod` is
definitional eta --- `(w.1, w.2) = w` is `rfl` in Lean 4 --- so *a pair is
determined by its coordinates* is supplied by the type theory here rather than
proved about `{{a}, {a,b}}`. What the tower still owns is the UNIVERSAL PROPERTY
ITSELF: existence of the factorisation and, the half with the content,
uniqueness of it, derived from the three equations at an abstract object where
nothing computes.

That is the same shape as `VectorSpace` and `ModuleQuotient` on this track ---
mathlib supplies the structure's own facts, the tower supplies the derivation ---
and it is a legitimate pair. It is NOT the pair the Challenge's header describes,
which says uniqueness routes through `opair_eq_opair_iff`. The Challenge may not
be edited to match, so the discrepancy is recorded here instead: a reader
comparing the two files will find it, and should find this paragraph first.

A DEFECT IN THE FILE THIS REPLACES, recorded because it survived a build and
every checker. Its header read *`Prod.ext`, `Prod.ext_iff` and `Prod.mk.injEq`
are NOT cited*, and its `encP_injective` ended `exact Prod.ext e1 e2`. The prose
and the proof disagreed, and nothing elaborates prose --- the same reason a
docstring can name a theorem that is not in the tree. The claim was false as
written even though the pair's real content was in `opair_eq_opair_iff` as
described.

UNIQUENESS ARRIVES POINTWISE AND THE `funext` IS DELIBERATE.
`prodT_universal` concludes `∀ z, k z = h z`, which needs no axioms. The
challenge's `∃!` is an equality of FUNCTIONS and reaching it needs `funext`,
which is `Quot.sound`-priced. The tower's theorem is stated pointwise, so the
pair applies `funext` and pays that cost here.
-/
import Comparator.ProductUniversal.Challenge
import FromAxioms.CategoryTheory.Category

namespace Comparator.ProductUniversal

/-- The tower's theorem this rests on, named where a reader of THIS file can
see it rather than an import away. -/
theorem rests_on_prodT_universal : True := by
  have _ := @CategoryTheory.prodT_universal.{0}
  trivial

/-- The challenge, from `FromAxioms`, with no encoding anywhere.

The three equations `Prod` satisfies are passed in; everything after that is the
tower's derivation. `heta` is `rfl` by structure eta, which is the one place
where this pair is thinner than the encoded version it replaces --- see the
header. -/
theorem solution : challenge := by
  intro α β Z f g
  obtain ⟨h, hf, hg, huniq⟩ :=
    CategoryTheory.prodT_universal (α := α) (β := β) (Z := Z) (P := α × β)
      (p₁ := Prod.fst) (p₂ := Prod.snd) (pr := Prod.mk)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) f g
  refine ⟨h, ⟨hf, hg⟩, ?_⟩
  rintro k ⟨k1, k2⟩
  funext z
  exact huniq k k1 k2 z

#print axioms rests_on_prodT_universal
#print axioms solution

end Comparator.ProductUniversal
