/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The reals.

A real is a Dedekind cut of ℚ: a set of rationals that is non-empty, proper,
downward closed, and has no greatest element. `Real` is carved out of `𝒫 ℚ` by
separation, so nothing here needs replacement -- the same bounding move that
placed the quotient set inside a power set.

The order is `⊆`, which makes reflexivity and transitivity trivial and
antisymmetry extensionality. Completeness is then literally a union: `⋃ S` is a
cut whenever `S` is a non-empty family of cuts with an upper bound, and
`subset_sUnion` and `sUnion_subset` say it is the least one.

Classical logic USED TO enter at exactly two places, and both were the same
step: deciding a comparison that no witness has been produced for.
`realLe_of_witness` -- a rational in `x` but not in `y` forces `y ⊆ x` -- is
constructive, and it is the whole mathematical content of linearity; the retired
`realLe_total` paid `em` only to decide that such a rational exists.
Multiplication was the same story one level up: the four sign cases are each
constructive, and choosing between them is not. On ℚ the corresponding
trichotomy was free, because equality of rationals reduces to equality of
naturals.

NEITHER PLACE IS IN THIS FILE ANY MORE. The comparisons are stated in
`Constructive/` with `EM` as a binder and reversed back to it, so each is priced
exactly rather than merely bounded; the sign decision is a `Decidable` parameter
of `realMulOf`. Nothing here depends on `Classical.choice`.

Addition, negation and multiplication on the non-negative cone are all
choice-free. `x + (-x) = 0` is not: it needs locatedness, which a one-sided cut
does not carry.
-/

import FromAxioms.NumberTheory.Rational

universe u

open NumberTheory SetTheory
namespace Analysis

/-- The four conditions defining a Dedekind cut. -/
structure IsCut (c : ZFSet.{u}) : Prop where
  subset : c ⊆ NumberTheory.Rat.{u}
  nonempty : ∃ q, q ∈ c
  proper : ∃ q, q ∈ NumberTheory.Rat.{u} ∧ q ∉ c
  down : ∀ q, q ∈ c → ∀ p, p ∈ NumberTheory.Rat.{u} → ratLt p q → p ∈ c
  no_greatest : ∀ q, q ∈ c → ∃ p, p ∈ c ∧ ratLt q p

/-- The real numbers, defined by Dedekind cuts. -/
def Real : ZFSet.{u} := sep IsCut.{u} (powerset NumberTheory.Rat.{u})

/-! ## ℚ inside ℝ -/

/-- The cut of a rational: everything strictly below it. -/
def ratCut (q : ZFSet.{u}) : ZFSet.{u} := sep (fun p => ratLt p q) NumberTheory.Rat.{u}

theorem mem_ratCut_iff (q p : ZFSet.{u}) : p ∈ ratCut q ↔ p ∈ NumberTheory.Rat.{u} ∧ ratLt p q :=
  mem_sep_iff _ _ _

/-! ## Order -/

def realLe (x y : ZFSet.{u}) : Prop := x ⊆ y

/-! ## Addition

`x + y` is the set of sums, `{q + r | q ∈ x, r ∈ y}`. Each cut condition
transfers directly except properness, which needs the observation below: a
rational inside a cut is strictly below every rational outside it. That is the
same fact `realLe_of_witness` turns on, and it is constructive. -/

/-- Zero. -/
def realZero : ZFSet.{u} := ratCut ratZero.{u}

/-! ## Negation

`-x` is `{p | p < -q for some q outside x}`. Quantifying over the complement
is what makes the result a cut: taking `{-q | q ∉ x}` directly would have a
greatest element whenever `x` has a least upper bound in ℚ. -/

def realNeg (x : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ q, q ∈ NumberTheory.Rat.{u} ∧ q ∉ x ∧ ratLt p (ratNeg q)) NumberTheory.Rat.{u}

/-! ## Multiplication on the non-negative cone

`{q·r}` is only the right set of products when both factors are non-negative,
so multiplication is given on the cone first. Extending it to all of ℝ is a
different matter: the textbook definition splits on the sign of each factor, and
deciding the sign of a real is the same comparison `Constructive.realLe_total_of_em`
prices at excluded middle. Nothing below uses it, because `realNonneg` is a
hypothesis here rather than something to be decided. -/

def realNonneg (x : ZFSet.{u}) : Prop := realLe realZero.{u} x


def realMulNonneg (x y : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ratLt p ratZero.{u} ∨ ∃ q, q ∈ x ∧ ∃ r, r ∈ y ∧
        ratLe ratZero.{u} q ∧ ratLe ratZero.{u} r ∧ ratLt p (ratMul q r)) NumberTheory.Rat.{u}

#print axioms Real
#print axioms IsCut
end Analysis

namespace ZFSet
export Analysis (IsCut Real mem_ratCut_iff ratCut realLe realMulNonneg realNeg realNonneg realZero)
end ZFSet
