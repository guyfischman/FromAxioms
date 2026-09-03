/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Nested intervals.

A shrinking sequence of rational intervals determines a real. Given `a`
increasing, `b` decreasing, `aₙ < bₙ` throughout, and the widths `bₙ - aₙ`
eventually below every positive rational, the pair

    L = { q | q < aₙ for some n }        U = { r | bₙ < r for some n }

is located. This is the analytic content that constructions like a binary or
ternary expansion need, and it is strictly less than a theory of limits: no sum
is formed, and the sequences are the data rather than something extracted from a
series.

Locatedness uses the same trick as everywhere else in this development: the decision `p ∈ L or q ∈ U` is not made by splitting on membership --
which would cost excluded middle -- but by comparing two rationals, where
trichotomy is a theorem. Pick a stage whose width is below `q - p`; then
`p < aₙ` puts `p` in `L`, and `aₙ ≤ p` forces `bₙ < q` and puts `q` in `U`.

`nest_ne_of_apart` is the separating half: intervals that come apart at some
stage give different reals. Injectivity of any expansion built this way reduces
to it.
-/

import FromAxioms.Analysis.Cauchy

universe u

open NumberTheory SetTheory
namespace Analysis

/-- Rationals strictly below some left endpoint. -/
def nestLower (a : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun q => ∃ n, n ∈ omega.{u} ∧ ratLt q (app a n)) NumberTheory.Rat.{u}

/-- Rationals strictly above some right endpoint. -/
def nestUpper (b : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun r => ∃ n, n ∈ omega.{u} ∧ ratLt (app b n) r) NumberTheory.Rat.{u}

theorem mem_nestLower_iff (a q : ZFSet.{u}) :
    q ∈ nestLower a ↔ q ∈ NumberTheory.Rat.{u} ∧ ∃ n, n ∈ omega.{u} ∧ ratLt q (app a n) :=
  mem_sep_iff _ _ _

theorem mem_nestUpper_iff (b r : ZFSet.{u}) :
    r ∈ nestUpper b ↔ r ∈ NumberTheory.Rat.{u} ∧ ∃ n, n ∈ omega.{u} ∧ ratLt (app b n) r :=
  mem_sep_iff _ _ _

/-- Nested rational intervals with shrinking width. -/
structure IsNested (a b : ZFSet.{u}) : Prop where
  lower_seq : a ∈ ratSeqs.{u}
  upper_seq : b ∈ ratSeqs.{u}
  lower_mono : ∀ m, m ∈ omega.{u} → ∀ n, n ∈ omega.{u} → m ⊆ n →
    ratLe (app a m) (app a n)
  upper_mono : ∀ m, m ∈ omega.{u} → ∀ n, n ∈ omega.{u} → m ⊆ n →
    ratLe (app b n) (app b m)
  bracket : ∀ n, n ∈ omega.{u} → ratLt (app a n) (app b n)
  shrink : ∀ ε, ε ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} ε → ∃ N, N ∈ omega.{u} ∧
    ratLt (ratAdd (app b N) (ratNeg (app a N))) ε

/-- Any left endpoint is below any right endpoint, not only the one at its own
stage: pass to a common later stage, where both have moved inward. -/
theorem IsNested.cross {a b : ZFSet.{u}} (h : IsNested a b) {m n : ZFSet.{u}}
    (hm : m ∈ omega.{u}) (hn : n ∈ omega.{u}) : ratLt (app a m) (app b n) := by
  obtain ⟨k, hk, hkm, hkn⟩ := exists_upper_omega hm hn
  exact ratLt_of_le_of_lt (app_mem_Rat h.lower_seq hm) (app_mem_Rat h.lower_seq hk)
    (app_mem_Rat h.upper_seq hn) (h.lower_mono m hm k hk hkm)
    (ratLt_of_lt_of_le (app_mem_Rat h.lower_seq hk) (app_mem_Rat h.upper_seq hk)
      (app_mem_Rat h.upper_seq hn) (h.bracket k hk) (h.upper_mono n hn k hk hkn))

/-- Nested intervals define a real. -/
theorem isLocated_nest {a b : ZFSet.{u}} (h : IsNested a b) :
    IsLocated (nestLower a) (nestUpper b) where
  lower_subset q hq := ((mem_nestLower_iff a q).mp hq).left
  upper_subset r hr := ((mem_nestUpper_iff b r).mp hr).left
  lower_inhabited := by
    obtain ⟨s, hsQ, hlt⟩ := rat_no_least (app_mem_Rat h.lower_seq (ofNat_mem_omega.{u} 0))
    exact ⟨s, (mem_nestLower_iff a s).mpr ⟨hsQ, ofNat.{u} 0, ofNat_mem_omega 0, hlt⟩⟩
  upper_inhabited := by
    obtain ⟨s, hsQ, hlt⟩ := rat_no_greatest (app_mem_Rat h.upper_seq (ofNat_mem_omega.{u} 0))
    exact ⟨s, (mem_nestUpper_iff b s).mpr ⟨hsQ, ofNat.{u} 0, ofNat_mem_omega 0, hlt⟩⟩
  ordered q hq r hr := by
    obtain ⟨hqQ, m, hm, hqm⟩ := (mem_nestLower_iff a q).mp hq
    obtain ⟨hrQ, n, hn, hnr⟩ := (mem_nestUpper_iff b r).mp hr
    exact ratLt_trans hqQ (app_mem_Rat h.lower_seq hm) hrQ hqm
      (ratLt_trans (app_mem_Rat h.lower_seq hm) (app_mem_Rat h.upper_seq hn) hrQ
        (h.cross hm hn) hnr)
  lower_down q hq p hpQ hlt := by
    obtain ⟨hqQ, n, hn, hqn⟩ := (mem_nestLower_iff a q).mp hq
    exact (mem_nestLower_iff a p).mpr
      ⟨hpQ, n, hn, ratLt_trans hpQ hqQ (app_mem_Rat h.lower_seq hn) hlt hqn⟩
  upper_up r hr p hpQ hlt := by
    obtain ⟨hrQ, n, hn, hnr⟩ := (mem_nestUpper_iff b r).mp hr
    exact (mem_nestUpper_iff b p).mpr
      ⟨hpQ, n, hn, ratLt_trans (app_mem_Rat h.upper_seq hn) hrQ hpQ hnr hlt⟩
  lower_open q hq := by
    obtain ⟨hqQ, n, hn, hqn⟩ := (mem_nestLower_iff a q).mp hq
    obtain ⟨t, htQ, h₁, h₂⟩ := rat_dense hqQ (app_mem_Rat h.lower_seq hn) hqn
    exact ⟨t, (mem_nestLower_iff a t).mpr ⟨htQ, n, hn, h₂⟩, h₁⟩
  upper_open r hr := by
    obtain ⟨hrQ, n, hn, hnr⟩ := (mem_nestUpper_iff b r).mp hr
    obtain ⟨t, htQ, h₁, h₂⟩ := rat_dense (app_mem_Rat h.upper_seq hn) hrQ hnr
    exact ⟨t, (mem_nestUpper_iff b t).mpr ⟨htQ, n, hn, h₁⟩, h₂⟩
  located p hpQ s hsQ hps := by
    have hnp := ratNeg_mem_Rat hpQ
    have hgap : ratLt ratZero.{u} (ratAdd s (ratNeg p)) := by
      have hstep := (ratAdd_lt_add_right_iff hnp hpQ hsQ).mpr hps
      rwa [ratAdd_neg hpQ] at hstep
    obtain ⟨N, hN, hwidth⟩ := h.shrink _ (ratAdd_mem_Rat hsQ hnp) hgap
    have haN := app_mem_Rat h.lower_seq hN
    have hbN := app_mem_Rat h.upper_seq hN
    have hXQ := ratAdd_mem_Rat hsQ hnp
    -- the width bound, read as `bₙ < aₙ + (s - p)`
    have hb : ratLt (app b N) (ratAdd (app a N) (ratAdd s (ratNeg p))) :=
      (sub_lt_iff_lt_add hbN haN hXQ).mp hwidth
    rcases ratLt_trichotomy hpQ haN with hlt | heq | hgt
    · exact Or.inl ((mem_nestLower_iff a p).mpr ⟨hpQ, N, hN, hlt⟩)
    · refine Or.inr ((mem_nestUpper_iff b s).mpr ⟨hsQ, N, hN, ?_⟩)
      rw [← heq, ratAdd_sub_cancel hsQ hpQ] at hb
      exact hb
    · refine Or.inr ((mem_nestUpper_iff b s).mpr ⟨hsQ, N, hN, ?_⟩)
      -- `aₙ ≤ p`, so `aₙ + (s - p) ≤ p + (s - p) = s`
      have hshift : ratLe (ratAdd (app a N) (ratAdd s (ratNeg p))) s := by
        have hstep := (ratAdd_le_add_right_iff hXQ haN hpQ).mpr hgt.left
        rwa [ratAdd_sub_cancel hsQ hpQ] at hstep
      exact ratLt_of_lt_of_le hbN (ratAdd_mem_Rat haN hXQ) hsQ hb hshift

/-! ### Where the limit sits

The real a nest defines lies between every pair of endpoints. Both halves are
`IsNested.cross`: a rational strictly below a left endpoint and strictly above
some right endpoint would cross the nest, which no pair does. -/

theorem nest_ge {a b : ZFSet.{u}} (h : IsNested a b) {n : ZFSet.{u}}
    (hn : n ∈ omega.{u}) :
    realLLe (realLOf (app a n)) (opair (nestLower a) (nestUpper b)) := by
  rintro ⟨t, htU, htL⟩
  rw [snd_opair] at htU
  rw [realLOf, fst_opair] at htL
  obtain ⟨htQ, m, hm, hmt⟩ := (mem_nestUpper_iff b t).mp htU
  have hta : ratLt t (app a n) := ((mem_ratCut_iff _ t).mp htL).right
  have hab : ratLt (app a n) (app b m) := h.cross hn hm
  exact ratLt_irrefl (ratLt_trans (app_mem_Rat h.upper_seq hm) htQ
    (app_mem_Rat h.upper_seq hm) hmt
    (ratLt_trans htQ (app_mem_Rat h.lower_seq hn) (app_mem_Rat h.upper_seq hm)
      hta hab))

theorem nest_le {a b : ZFSet.{u}} (h : IsNested a b) {n : ZFSet.{u}}
    (hn : n ∈ omega.{u}) :
    realLLe (opair (nestLower a) (nestUpper b)) (realLOf (app b n)) := by
  rintro ⟨t, htU, htL⟩
  rw [realLOf, snd_opair] at htU
  rw [fst_opair] at htL
  obtain ⟨htQ, m, hm, htm⟩ := (mem_nestLower_iff a t).mp htL
  have hbt : ratLt (app b n) t := ((mem_sep_iff _ t _).mp htU).right
  have hab : ratLt (app a m) (app b n) := h.cross hm hn
  exact ratLt_irrefl (ratLt_trans (app_mem_Rat h.lower_seq hm)
    (app_mem_Rat h.upper_seq hn) (app_mem_Rat h.lower_seq hm) hab
    (ratLt_trans (app_mem_Rat h.upper_seq hn) htQ (app_mem_Rat h.lower_seq hm)
      hbt htm))

#print axioms IsNested

/-- The usual way a construction supplies `shrink`: widths bounded by `1/(n+1)`.
Anything shrinking geometrically clears this bar, and Archimedes
(`exists_invWidth_lt`) does the rest. -/
theorem shrink_of_invWidth {a b : ZFSet.{u}} (ha : a ∈ ratSeqs.{u}) (hb : b ∈ ratSeqs.{u})
    (hw : ∀ n, n ∈ omega.{u} → ratLe (ratAdd (app b n) (ratNeg (app a n))) (invWidth n)) :
    ∀ ε, ε ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} ε → ∃ N, N ∈ omega.{u} ∧
      ratLt (ratAdd (app b N) (ratNeg (app a N))) ε := by
  intro ε hεQ hε
  obtain ⟨N, hN, hlt⟩ := exists_invWidth_lt hεQ hε
  exact ⟨N, hN, ratLt_of_le_of_lt
    (ratAdd_mem_Rat (app_mem_Rat hb hN) (ratNeg_mem_Rat (app_mem_Rat ha hN)))
    (invWidth_mem_Rat hN) hεQ (hw N hN) hlt⟩

#print axioms isLocated_nest
end Analysis
#print axioms Analysis.nest_ge
#print axioms Analysis.nest_le
namespace ZFSet
export Analysis (IsNested isLocated_nest mem_nestLower_iff mem_nestUpper_iff nestLower nestUpper nest_ge nest_le shrink_of_invWidth)
end ZFSet
