/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`, without citing mathlib's
proof of it.

The mathematics is `Metamath.ExactIVT01` together with
`Analysis.exactIVT01Top_of_em`, which proves it: the exact intermediate value
theorem on `[0,1]`, priced at excluded middle. The tower also measures that the
price is real --- `Metamath.llpo_of_exact_ivt` derives LLPO from the same
statement --- so `Classical.em` is the price this row reports.

The tower's form is narrower in two ways --- the interval fixed at `[0,1]`
where mathlib takes any `Icc a b` with `a ≤ b`, and the straddle strict
(`G 0 < 0 < G 1`) where mathlib concludes an image containment that includes
the non-strict case. Both are closed below.

    the interval   an affine reparametrisation `t ↦ a + t*(b-a)` of `[0,1]` onto
                   `[a,b]`, which is where `a < b` is needed and where it comes
                   from: `f a < c < f b` forces `f a ≠ f b`, hence `a ≠ b`.
    the straddle   a three-way split on `c`. `c = f a` and `c = f b` are
                   witnessed by the endpoints with no IVT at all; only the
                   strict middle case reaches the tower. `f b < f a` makes the
                   hypothesis set empty and never arises, since `c` is given in
                   `Icc (f a) (f b)`.

The bridge pieces this needs:

    toRL_close_iff              the tower's `Close x y e` is `|x - y| ≤ e`
    toRat_invWidth              its width `invWidth (ofNat m)` is `1/(m+1)`
    uniformlyContinuousOn_liftFun   a mathlib ε-δ modulus becomes the tower's
                                    rational-width `UniformlyContinuousOn`
    toRL_lt_iff                 the strict order, which is the classical half
    exists_root_of_lt           the tower's IVT delivered in mathlib's words

`exists_root_of_lt` is the whole of the tower's contribution; everything in this
file is the reparametrisation and the case split.

The modulus comes from compactness, which is Mathlib's to give. The challenge
hypothesis is `ContinuousOn f (Icc a b)`, pointwise; the tower's IVT wants a
uniform modulus. `IsCompact.uniformContinuousOn_of_continuous` is Heine-Cantor
and `Metric.uniformContinuousOn_iff_le` is its ε-δ form. Neither touches the
theorem being discharged: `exists_root_of_lt` consumes nothing from mathlib's
`IntermediateValue` file, and `intermediate_value_Icc` --- the theorem being
discharged --- appears nowhere in this Solution's dependency set.

The axiom print names `Classical.choice` and here it is the mathematics, not the
encoding. That distinguishes this pair from `DetMul` and `DetLeibniz`, where the
same line was the `TypeTransfer` encoding and mathlib's own proof carried it too.
Here the tower's theorem is `exactIVT01Top_of_em`, whose `EM` binder
`#print axioms` cannot see --- it is a `def : Prop` passed as an argument --- and
this file supplies it as `fun p => Classical.em p`. The row's
`principle: SignDisjunction` is the honest reading of what that costs, and
`Metamath.llpo_of_exact_ivt` is the tree's own proof that it cannot be avoided.
-/
import Comparator.IvtExact.Challenge
import Comparator.Bridge.RealTransfer
import Mathlib.Topology.UniformSpace.HeineCantor

open SetTheory NumberTheory Analysis
open Comparator

namespace Comparator.IvtExact

/-- The tower's theorem this rests on, named where a reader of this file can
see it. -/
theorem rests_on_exactIVT01 : True := by
  -- Pinned to `.{0}`: both are universe-polymorphic and a bare `have` cannot
  -- infer the level.
  have _ := @Analysis.exactIVT01Top_of_em.{0}
  have _ := @Metamath.exactIVT01_of_top.{0}
  trivial

/-- The challenge, from `FromAxioms`. -/
theorem solution : challenge := by
  intro a b f hab hcont c hc
  obtain ⟨hca, hcb⟩ := hc
  -- The two boundary cases need no intermediate value: the endpoint is the
  -- witness. Splitting here rather than later is what lets the tower's strict
  -- straddle be used without weakening it.
  rcases eq_or_lt_of_le hca with hEq | hlt
  · exact ⟨a, ⟨le_refl a, hab⟩, hEq⟩
  rcases eq_or_lt_of_le hcb with hEq | hgt
  · exact ⟨b, ⟨hab, le_refl b⟩, hEq.symm⟩
  -- `f a < c < f b` forces `f a ≠ f b`, hence `a ≠ b`, hence `a < b`.
  have hne : a ≠ b := by
    intro h
    rw [h] at hlt
    exact absurd (hlt.trans hgt) (lt_irrefl _)
  have hlt_ab : a < b := lt_of_le_of_ne hab hne
  have hw : (0 : ℝ) < b - a := by linarith
  -- The reparametrisation, and the interval it lands in.
  set φ : ℝ → ℝ := fun t => a + t * (b - a) with hφ
  have hφmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ t ∈ Set.Icc a b := by
    rintro t ⟨ht0, ht1⟩
    constructor
    · rw [hφ]; nlinarith
    · rw [hφ]; nlinarith
  have hφ0 : φ 0 = a := by rw [hφ]; ring
  have hφ1 : φ 1 = b := by rw [hφ]; ring
  -- The modulus, from Heine-Cantor on the compact interval.
  have huc : UniformContinuousOn f (Set.Icc a b) :=
    (isCompact_Icc (a := a) (b := b)).uniformContinuousOn_of_continuous hcont
  have hucd := Metric.uniformContinuousOn_iff_le.mp huc
  -- and transported along `φ`, which is Lipschitz with constant `b - a`.
  have hg : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |x - y| ≤ δ → |(f (φ x) - c) - (f (φ y) - c)| ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := hucd ε hε
    refine ⟨δ / (b - a), by positivity, fun x hx y hy hxy => ?_⟩
    have hdist : dist (φ x) (φ y) ≤ δ := by
      rw [Real.dist_eq, hφ]
      have : a + x * (b - a) - (a + y * (b - a)) = (x - y) * (b - a) := by ring
      rw [this, abs_mul, abs_of_pos hw]
      calc |x - y| * (b - a) ≤ (δ / (b - a)) * (b - a) := by nlinarith [abs_nonneg (x - y)]
        _ = δ := by field_simp
    have := hd (φ x) (hφmem x hx) (φ y) (hφmem y hy) hdist
    rw [Real.dist_eq] at this
    have heq : f (φ x) - c - (f (φ y) - c) = f (φ x) - f (φ y) := by ring
    rw [heq]
    exact this
  -- The tower's IVT.
  -- The two straddle goals arrive beta-unreduced (`(fun t => f (φ t) - c) 0`),
  -- so `show` reduces them before the rewrite.
  obtain ⟨t, ht, hroot⟩ := exists_root_of_lt (fun t => f (φ t) - c) hg
    (by show f (φ 0) - c < 0; rw [hφ0]; linarith)
    (by show (0 : ℝ) < f (φ 1) - c; rw [hφ1]; linarith)
  have hr : f (φ t) - c = 0 := hroot
  exact ⟨φ t, hφmem t ht, by linarith [hr]⟩

#print axioms solution

end Comparator.IvtExact
