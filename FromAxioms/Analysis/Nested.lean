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

/-- The nest's lower set is a generic cut, over the predicate *is a left
endpoint*. `nestLower` is not `cutLower` by `rfl` --- it asks for a stage below
`q` directly, where `cutLower` interposes a rational witness --- so this is the
one instance of the six that needs a bridge, and the bridge is
`app_mem_Rat` supplying the witness's membership. -/
theorem nestLower_eq_cut {a : ZFSet.{u}} (ha : a ∈ ratSeqs.{u}) :
    nestLower a = cutLower (fun p' => ∃ n, n ∈ omega.{u} ∧ p' = app a n) := by
  apply ZFSet.ext
  intro q
  rw [mem_nestLower_iff, mem_cutLower_iff]
  constructor
  · rintro ⟨hqQ, n, hn, hlt⟩
    exact ⟨hqQ, app a n, app_mem_Rat ha hn, hlt, n, hn, rfl⟩
  · rintro ⟨hqQ, p', _, hqp', n, hn, rfl⟩
    exact ⟨hqQ, n, hn, hqp'⟩

#print axioms nestLower_eq_cut

/-- The nest's upper set is a generic cut, the mirror of
`nestLower_eq_cut`. -/
theorem nestUpper_eq_cut {b : ZFSet.{u}} (hb : b ∈ ratSeqs.{u}) :
    nestUpper b = cutUpper (fun r' => ∃ n, n ∈ omega.{u} ∧ r' = app b n) := by
  apply ZFSet.ext
  intro r
  rw [mem_nestUpper_iff, mem_cutUpper_iff]
  constructor
  · rintro ⟨hrQ, n, hn, hlt⟩
    exact ⟨hrQ, app b n, app_mem_Rat hb hn, hlt, n, hn, rfl⟩
  · rintro ⟨hrQ, r', _, hr'r, n, hn, rfl⟩
    exact ⟨hrQ, n, hn, hr'r⟩

#print axioms nestUpper_eq_cut

/-- The located disjunction of a nest, stated over the raw endpoint
predicates rather than over the two cut sets. `p < s` gives a stage `N` whose
width is under `s - p`, and the trichotomy at `a N` sends `p` below a left
endpoint or `s` above a right one.

This is the `located` clause of `isLocated_nest` lifted out of the structure
instance, so that `isLocated_cut` can supply the other eight clauses
generically. Lifting it costs nothing here: the clause never used another
field. -/
theorem nest_left_or_right {a b : ZFSet.{u}} (h : IsNested a b)
    {p s : ZFSet.{u}} (hpQ : p ∈ NumberTheory.Rat.{u})
    (hsQ : s ∈ NumberTheory.Rat.{u}) (hps : ratLt p s) :
    (∃ p', p' ∈ NumberTheory.Rat.{u} ∧ ratLt p p' ∧
      ∃ n, n ∈ omega.{u} ∧ p' = app a n) ∨
    (∃ r', r' ∈ NumberTheory.Rat.{u} ∧ ratLt r' s ∧
      ∃ n, n ∈ omega.{u} ∧ r' = app b n) := by
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
  · exact Or.inl ⟨app a N, haN, hlt, N, hN, rfl⟩
  · refine Or.inr ⟨app b N, hbN, ?_, N, hN, rfl⟩
    rw [← heq, ratAdd_sub_cancel hsQ hpQ] at hb
    exact hb
  · refine Or.inr ⟨app b N, hbN, ?_, N, hN, rfl⟩
    -- `aₙ ≤ p`, so `aₙ + (s - p) ≤ p + (s - p) = s`
    have hshift : ratLe (ratAdd (app a N) (ratAdd s (ratNeg p))) s := by
      have hstep := (ratAdd_le_add_right_iff hXQ haN hpQ).mpr hgt.left
      rwa [ratAdd_sub_cancel hsQ hpQ] at hstep
    exact ratLt_of_lt_of_le hbN (ratAdd_mem_Rat haN hXQ) hsQ hb hshift

#print axioms nest_left_or_right

/-- Nested intervals define a real. -/
theorem isLocated_nest {a b : ZFSet.{u}} (h : IsNested a b) :
    IsLocated (nestLower a) (nestUpper b) := by
  rw [nestLower_eq_cut h.lower_seq, nestUpper_eq_cut h.upper_seq]
  refine isLocated_cut
    (Left := fun p' => ∃ n, n ∈ omega.{u} ∧ p' = app a n)
    (Right := fun r' => ∃ n, n ∈ omega.{u} ∧ r' = app b n)
    ?_ ?_ ?_ ?_
  · rintro p' r' _ _ ⟨m, hm, rfl⟩ ⟨n, hn, rfl⟩
    exact h.cross hm hn
  · obtain ⟨s, hsQ, hlt⟩ := rat_no_least (app_mem_Rat h.lower_seq (ofNat_mem_omega.{u} 0))
    exact ⟨s, app a (ofNat.{u} 0), hsQ,
      app_mem_Rat h.lower_seq (ofNat_mem_omega.{u} 0), hlt, ofNat.{u} 0,
      ofNat_mem_omega 0, rfl⟩
  · obtain ⟨s, hsQ, hlt⟩ := rat_no_greatest (app_mem_Rat h.upper_seq (ofNat_mem_omega.{u} 0))
    exact ⟨s, app b (ofNat.{u} 0), hsQ,
      app_mem_Rat h.upper_seq (ofNat_mem_omega.{u} 0), hlt, ofNat.{u} 0,
      ofNat_mem_omega 0, rfl⟩
  · intro p q hp hq hpq
    exact nest_left_or_right h hp hq hpq

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

/-- The nest's cut is a located real. -/
theorem nest_mem_RealL {a b : ZFSet.{u}} (h : IsNested a b) :
    opair (nestLower a) (nestUpper b) ∈ RealL.{u} :=
  (mem_RealL_iff _).mpr ⟨nestLower a, nestUpper b, rfl, isLocated_nest h⟩

#print axioms nest_mem_RealL
#print axioms IsNested

/-- The standard form: a nested family of intervals contains exactly one
real.

This is the completeness statement the landmark names, and it is not
`isLocated_nest`: that says the nest determines a located cut, while this says
the cut is a point lying in every interval and the only one.

Uniqueness costs neither `shrink` nor density. `realLLt x y` is a rational `p`
above `x` and below `y`; if `y` lies under every `b m` and some `b m` lies under
`p`, that same `p` witnesses `realLOf (b m) < y`, which the bracketing forbids.
So any two points bracketed by one nest are equal on the order alone --- the
widths shrinking is what makes the bracket non-trivial, not what makes it
unique. -/
theorem exists_unique_mem_nest {a b : ZFSet.{u}} (h : IsNested a b) :
    ∃ x, And (x ∈ RealL.{u})
      (And (∀ n, n ∈ omega.{u} →
              And (realLLe (realLOf (app a n)) x)
                  (realLLe x (realLOf (app b n))))
        (∀ y, y ∈ RealL.{u} →
          (∀ n, n ∈ omega.{u} →
            And (realLLe (realLOf (app a n)) y)
                (realLLe y (realLOf (app b n)))) → y = opair (nestLower a) (nestUpper b))) := by
  refine ⟨opair (nestLower a) (nestUpper b), nest_mem_RealL h,
    fun n hn => ⟨nest_ge h hn, nest_le h hn⟩, ?_⟩
  intro y hy hbr
  refine realLLe_antisymm hy (nest_mem_RealL h) ?_ ?_
  · -- `y ≤ x`: a witness `p` for `x < y` sits above some `b m`, and `y ≤ b m`
    rintro ⟨p, hpU, hpL⟩
    rw [snd_opair] at hpU
    obtain ⟨hpQ, m, hm, hbm⟩ := (mem_nestUpper_iff b p).mp hpU
    exact (hbr m hm).right ⟨p, by
      rw [realLOf, snd_opair]
      exact (mem_sep_iff _ p _).mpr ⟨hpQ, hbm⟩, hpL⟩
  · -- `x ≤ y`: a witness `p` for `y < x` sits below some `a m`, and `a m ≤ y`
    rintro ⟨p, hpU, hpL⟩
    rw [fst_opair] at hpL
    obtain ⟨hpQ, m, hm, hpa⟩ := (mem_nestLower_iff a p).mp hpL
    exact (hbr m hm).left ⟨p, hpU, by
      rw [realLOf, fst_opair]
      exact (mem_ratCut_iff _ p).mpr ⟨hpQ, hpa⟩⟩

#print axioms exists_unique_mem_nest

/-- Shrinking from a scaled width bound.  `shrink_of_invWidth` is this at
`W = 1`.

A nested family whose width at stage `n` is at most `W * invWidth n`, for any
positive rational `W`, still comes below every positive `eps` --- the scale
only moves which stage is reached. A bisection on `[p, q]` needs this, where
the natural bound carries the factor `q - p`. -/
theorem shrink_of_scaled_invWidth {a b W : ZFSet.{u}} (ha : a ∈ ratSeqs.{u})
    (hb : b ∈ ratSeqs.{u}) (hW : W ∈ NumberTheory.Rat.{u})
    (hW0 : ratLt ratZero.{u} W)
    (hw : ∀ n, n ∈ omega.{u} → ratLe (ratAdd (app b n) (ratNeg (app a n)))
      (ratMul W (invWidth n))) :
    ∀ ε, ε ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} ε → ∃ N, N ∈ omega.{u} ∧
      ratLt (ratAdd (app b N) (ratNeg (app a N))) ε := by
  intro ε hεQ hε
  -- `W ≠ 0` is the right component of `0 < W`; asking for it separately would
  -- over-demand the hypothesis.
  have hWne : W ≠ ratZero.{u} := fun he => hW0.right he.symm
  have hinvW := ratInv_mem_Rat hW hWne
  have hinvW0 := ratInv_pos hW hW0
  have hδQ := ratMul_mem_Rat hεQ hinvW
  have hδ0 := ratMul_pos hεQ hinvW hε hinvW0
  obtain ⟨N, hN, hlt⟩ := exists_invWidth_lt hδQ hδ0
  have hinvN := invWidth_mem_Rat hN
  -- `invWidth N < ε·W⁻¹` scaled by `W`, then `W·(ε·W⁻¹) = ε`
  have hscaled := ratMul_lt_mul_right hinvN hδQ hW hWne
    (ratLe_of_lt ratZero_mem_Rat hW hW0) hlt
  have hcancel : ratMul (ratMul ε (ratInv W)) W = ε := by
    rw [ratMul_assoc hεQ hinvW hW, ratMul_comm hinvW hW,
      ratMul_inv hW hWne, ratMul_one hεQ]
  rw [hcancel] at hscaled
  refine ⟨N, hN, ratLt_of_le_of_lt
    (ratAdd_mem_Rat (app_mem_Rat hb hN) (ratNeg_mem_Rat (app_mem_Rat ha hN)))
    (ratMul_mem_Rat hW hinvN) hεQ (hw N hN) ?_⟩
  rwa [ratMul_comm hinvN hW] at hscaled

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
#print axioms mem_nestLower_iff
#print axioms mem_nestUpper_iff
#print axioms IsNested.cross
#print axioms shrink_of_invWidth
end Analysis
#print axioms Analysis.nest_ge
#print axioms Analysis.nest_le
#print axioms Analysis.shrink_of_scaled_invWidth

namespace ZFSet
export Analysis (IsNested exists_unique_mem_nest isLocated_nest mem_nestLower_iff mem_nestUpper_iff nestLower nestLower_eq_cut nestUpper nestUpper_eq_cut nest_ge nest_le nest_left_or_right nest_mem_RealL shrink_of_invWidth shrink_of_scaled_invWidth)
end ZFSet
