/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Cauchy sequences, and the map into the Dedekind reals.

A sequence of rationals is a set function `ω → ℚ`, so `Relation.lean`'s `app`
supplies the terms and nothing here needs choice to use a sequence. The Cauchy
condition is stated two-sidedly -- `f m - f n < ε` for all large `m, n`, in both
orders by symmetry of the quantifiers -- because `abs` would be a definition by
cases, and those cost choice.

A Cauchy sequence determines a located pair: the rationals eventually below the
terms by a margin, and those eventually above by a margin. That is the
constructive direction of the comparison between the two presentations of ℝ.

The converse -- that every located pair arises this way -- needs countable
choice from `IsLocated` alone: `located_bracket` gives a bracket for each
`n`, and assembling them into a sequence means choosing one for every `n` at
once. `hasApprox_of_ACOmega` below is that route. The cost belongs to the
hypothesis and not to the converse: given a `LocatedReadout` as well, the same
conclusion is reached choice-free, because the index is computed rather than
chosen.
-/

import FromAxioms.Analysis.Located

universe u

open NumberTheory SetTheory
namespace Analysis

/-! ## Sequences of rationals -/

def ratSeqs : ZFSet.{u} :=
  sep (fun f => IsFunction f ∧ domain f = omega.{u}) (powerset (prod omega.{u} NumberTheory.Rat.{u}))

theorem mem_ratSeqs_iff (f : ZFSet.{u}) :
    f ∈ ratSeqs.{u} ↔ f ⊆ prod omega.{u} NumberTheory.Rat.{u} ∧ IsFunction f ∧ domain f = omega.{u} :=
  Iff.trans (mem_sep_iff _ _ _)
    ⟨fun h => ⟨(mem_powerset_iff _ _).mp h.left, h.right⟩,
     fun h => ⟨(mem_powerset_iff _ _).mpr h.left, h.right⟩⟩

theorem app_mem_Rat {f : ZFSet.{u}} (hf : f ∈ ratSeqs.{u}) {n : ZFSet.{u}}
    (hn : n ∈ omega.{u}) : app f n ∈ NumberTheory.Rat.{u} := by
  obtain ⟨hsub, hfun, hdom⟩ := (mem_ratSeqs_iff f).mp hf
  have hmem := opair_app_mem hfun (hdom ▸ hn)
  exact mem_prod_right (hsub _ hmem)

/-- A rational sequence from a Lean-level family; `natSeq` itself is in
`Relation.lean`. -/
theorem natSeq_mem_ratSeqs {K : Nat → ZFSet.{u}} (hK : ∀ m, K m ∈ NumberTheory.Rat.{u}) :
    natSeq NumberTheory.Rat.{u} K ∈ ratSeqs.{u} :=
  (mem_ratSeqs_iff _).mpr ⟨graphOn_subset _ _ _, graphOn_isFunction _ _ _,
    graphOn_domain (natFun_mem hK)⟩

/-- Any two indices are below a common one -- `ofNat` of the sum will do, which
avoids needing a maximum. -/
theorem exists_upper_omega {m n : ZFSet.{u}} (hm : m ∈ omega.{u}) (hn : n ∈ omega.{u}) :
    ∃ k, k ∈ omega.{u} ∧ m ⊆ k ∧ n ⊆ k := by
  obtain ⟨a, rfl⟩ := (mem_omega_iff m).mp hm
  obtain ⟨b, rfl⟩ := (mem_omega_iff n).mp hn
  exact ⟨ofNat (a + b), ofNat_mem_omega _,
    (ofNat_subset_iff a (a + b)).mpr (by omega),
    (ofNat_subset_iff b (a + b)).mpr (by omega)⟩

/-! ## Where the converse would need choice

The embedding above is one-way. Going back -- from a located pair to a Cauchy
sequence converging to it -- means producing a sequence of brackets, and
`located_bracket` only produces one bracket at a time. Turning "for each `n`
there is a bracket of width below `1/(n+1)`" into a single function of `n` is
exactly countable choice -- for `IsLocated` alone, which is the hypothesis
this section has, rather than of the converse: given a `LocatedReadout` as
well, the same sequence is produced choice-free, because the index is computed
rather than chosen. What `ACω` collapses here is a family of `Prop`
disjunctions, and a set-level bit collapses it by computation.

`ACOmega` states it in this setting: a set function `F` on `ω` whose values are
all inhabited has a choice function. `HasApprox` states what the converse
embedding would need. Neither is assumed anywhere; they are here so the
implication between them can be measured, the way `Reverse.lean` measures the
classical results. -/

/-- Countable choice, for an `ω`-indexed family of inhabited sets. -/
def ACOmega : Prop :=
  ∀ F : ZFSet.{u}, IsFunction F → domain F = omega.{u} →
    (∀ n, n ∈ omega.{u} → ∃ y, y ∈ app F n) →
    ∃ g, IsFunction g ∧ domain g = omega.{u} ∧
      ∀ n, n ∈ omega.{u} → app g n ∈ app F n

/-- The brackets of width below `d`, as a set: the pairs `(q, r)` with `q` in
the lower half, `r` in the upper, and `r < q + d`. `located_bracket` says this
is inhabited for every positive `d`, and an `ω`-indexed family of these is what
the converse embedding has to choose from. -/
def brackets (L U d : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => ∃ q, q ∈ L ∧ ∃ r, r ∈ U ∧ z = opair q r ∧ ratLt r (ratAdd q d))
    (prod NumberTheory.Rat.{u} NumberTheory.Rat.{u})

#print axioms mem_ratSeqs_iff
#print axioms app_mem_Rat
#print axioms exists_upper_omega
end Analysis

namespace ZFSet
export Analysis (ACOmega app_mem_Rat brackets exists_upper_omega mem_ratSeqs_iff natSeq_mem_ratSeqs ratSeqs)
end ZFSet
