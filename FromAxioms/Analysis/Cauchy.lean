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

/-- Cauchy: the terms eventually differ by less than any positive `ε`. Stated
one-sidedly; the other side is the same statement with `m` and `n` swapped. -/
def IsCauchy (f : ZFSet.{u}) : Prop :=
  ∀ ε, ε ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} ε → ∃ N, N ∈ omega.{u} ∧
    ∀ m, m ∈ omega.{u} → ∀ n, n ∈ omega.{u} → N ⊆ m → N ⊆ n →
      ratLt (ratAdd (app f m) (ratNeg (app f n))) ε

/-! ## The pair a Cauchy sequence determines -/

def limLower (f : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun q => ∃ ε, ε ∈ NumberTheory.Rat.{u} ∧ ratLt ratZero.{u} ε ∧ ∃ N, N ∈ omega.{u} ∧
        ∀ n, n ∈ omega.{u} → N ⊆ n → ratLt (ratAdd q ε) (app f n)) NumberTheory.Rat.{u}

def limUpper (f : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun q => ∃ ε, ε ∈ NumberTheory.Rat.{u} ∧ ratLt ratZero.{u} ε ∧ ∃ N, N ∈ omega.{u} ∧
        ∀ n, n ∈ omega.{u} → N ⊆ n → ratLt (ratAdd (app f n) ε) q) NumberTheory.Rat.{u}

theorem mem_limLower_iff (f q : ZFSet.{u}) :
    q ∈ limLower f ↔ q ∈ NumberTheory.Rat.{u} ∧ ∃ ε, ε ∈ NumberTheory.Rat.{u} ∧ ratLt ratZero.{u} ε ∧
      ∃ N, N ∈ omega.{u} ∧ ∀ n, n ∈ omega.{u} → N ⊆ n → ratLt (ratAdd q ε) (app f n) :=
  mem_sep_iff _ _ _

theorem mem_limUpper_iff (f q : ZFSet.{u}) :
    q ∈ limUpper f ↔ q ∈ NumberTheory.Rat.{u} ∧ ∃ ε, ε ∈ NumberTheory.Rat.{u} ∧ ratLt ratZero.{u} ε ∧
      ∃ N, N ∈ omega.{u} ∧ ∀ n, n ∈ omega.{u} → N ⊆ n → ratLt (ratAdd (app f n) ε) q :=
  mem_sep_iff _ _ _

/-! ## The same pair as the cut of a margin-free predicate

The margin and the cut's witness are the same device, written twice. `cutLower`
is the open downset of a predicate --- `q` is in it when some `q' > q`
satisfies the predicate --- and that interior witness is what makes
`lower_open` free in `Located.lean`. `limLower` supplies its own interior
witness instead, as the margin `ε`, so its `lower_open` clause had to halve `ε`
through `exists_mul_lt`. Dropping the margin to plain `p' < f n` and letting
the cut carry the witness names the same set and retires the halving.

A bridge rather than a redefinition. Spelling `limLower` as `cutLower` of the
predicate outright would make the bridge `rfl`, as it is for `acosLower`,
`piCut` and `integralCut`, but `mem_limUpper_iff` would stop being
`mem_sep_iff`: its forward direction needs `app f n ∈ NumberTheory.Rat`, which
only `hf` supplies, so the `iff` would grow a hypothesis at every unfolding
site in this file and `Limit.lean`. The bridge pays that cost once, here, where
`hf` is in scope. -/

/-- `limLower` is a generic cut, over the predicate *eventually below every
term*. The margin is recovered as `p' - q` one way and supplied as
`p' := q + ε` the other; no halving in either direction.

Takes no `hf`: both directions move only `q` and `p'` about, and never have to
know that `app f n` is rational; `limUpper_eq_cut` does. -/
theorem limLower_eq_cut (f : ZFSet.{u}) :
    limLower f = cutLower (fun p' => ∃ N, N ∈ omega.{u} ∧
      ∀ n, n ∈ omega.{u} → N ⊆ n → ratLt p' (app f n)) := by
  apply ZFSet.ext
  intro q
  rw [mem_limLower_iff, mem_cutLower_iff]
  constructor
  · rintro ⟨hqQ, ε, hεQ, hε, N, hN, h⟩
    refine ⟨hqQ, ratAdd q ε, ratAdd_mem_Rat hqQ hεQ, ?_, N, hN, h⟩
    have hstep := (ratAdd_lt_add_left_iff hqQ ratZero_mem_Rat hεQ).mpr hε
    rwa [ratAdd_zero hqQ] at hstep
  · rintro ⟨hqQ, p', hp'Q, hqp', N, hN, h⟩
    refine ⟨hqQ, ratAdd p' (ratNeg q), ratAdd_mem_Rat hp'Q (ratNeg_mem_Rat hqQ),
      ?_, N, hN, fun n hn hNn => ?_⟩
    · have hstep := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat hqQ) hqQ hp'Q).mpr hqp'
      rwa [ratAdd_neg hqQ] at hstep
    · rw [ratAdd_comm hp'Q (ratNeg_mem_Rat hqQ),
        ← ratAdd_assoc hqQ (ratNeg_mem_Rat hqQ) hp'Q, ratAdd_neg hqQ,
        ratZero_add hp'Q]
      exact h n hn hNn

/-- `limUpper` is a generic cut, the mirror of `limLower_eq_cut`, with
`r' := q - ε` forward and `ε := q - r'` back.

Takes `hf` where the lower bridge does not, because both directions compare
`app f n` against a shifted `q` and every order lemma in this tree is
membership-guarded. -/
theorem limUpper_eq_cut {f : ZFSet.{u}} (hf : f ∈ ratSeqs.{u}) :
    limUpper f = cutUpper (fun r' => ∃ N, N ∈ omega.{u} ∧
      ∀ n, n ∈ omega.{u} → N ⊆ n → ratLt (app f n) r') := by
  apply ZFSet.ext
  intro q
  rw [mem_limUpper_iff, mem_cutUpper_iff]
  constructor
  · rintro ⟨hqQ, ε, hεQ, hε, N, hN, h⟩
    have hnε := ratNeg_mem_Rat hεQ
    refine ⟨hqQ, ratAdd q (ratNeg ε), ratAdd_mem_Rat hqQ hnε, ?_, N, hN,
      fun n hn hNn => ?_⟩
    · have hneg : ratLt (ratNeg ε) ratZero.{u} := by
        have hs2 := (ratNeg_lt_neg_iff hεQ ratZero_mem_Rat).mpr hε
        rwa [ratNeg_zero] at hs2
      have hstep := (ratAdd_lt_add_left_iff hqQ hnε ratZero_mem_Rat).mpr hneg
      rwa [ratAdd_zero hqQ] at hstep
    · have hfn := app_mem_Rat hf hn
      refine (ratAdd_lt_add_right_iff hεQ hfn (ratAdd_mem_Rat hqQ hnε)).mp ?_
      rw [sub_add_cancel hqQ hεQ]
      exact h n hn hNn
  · rintro ⟨hqQ, r', hr'Q, hr'q, N, hN, h⟩
    have hnr := ratNeg_mem_Rat hr'Q
    have hEQ := ratAdd_mem_Rat hqQ hnr
    refine ⟨hqQ, ratAdd q (ratNeg r'), hEQ, ?_, N, hN, fun n hn hNn => ?_⟩
    · have hstep := (ratAdd_lt_add_right_iff hnr hr'Q hqQ).mpr hr'q
      rwa [ratAdd_neg hr'Q] at hstep
    · have hfn := app_mem_Rat hf hn
      have hstep := (ratAdd_lt_add_right_iff hEQ hfn hr'Q).mpr (h n hn hNn)
      rwa [ratAdd_comm hr'Q hEQ, sub_add_cancel hqQ hr'Q] at hstep

/-- Separation at the margin-free pair: pass to a common stage and chain.

Needs no Cauchy hypothesis: two eventual bounds are compared at any index past
both, and `exists_upper_omega` supplies one without a maximum. The twin of
`realLim_sep`. -/
theorem lim_sep {f : ZFSet.{u}} (hf : f ∈ ratSeqs.{u})
    {p' r' : ZFSet.{u}} (hp' : p' ∈ NumberTheory.Rat.{u})
    (hr' : r' ∈ NumberTheory.Rat.{u})
    (hL : ∃ N, N ∈ omega.{u} ∧ ∀ n, n ∈ omega.{u} → N ⊆ n → ratLt p' (app f n))
    (hR : ∃ M, M ∈ omega.{u} ∧ ∀ n, n ∈ omega.{u} → M ⊆ n → ratLt (app f n) r') :
    ratLt p' r' := by
  obtain ⟨N, hN, h1⟩ := hL
  obtain ⟨M, hM, h2⟩ := hR
  obtain ⟨k, hk, hkN, hkM⟩ := exists_upper_omega hN hM
  exact ratLt_trans hp' (app_mem_Rat hf hk) hr' (h1 k hk hkN) (h2 k hk hkM)

private theorem two_nonneg : ratLe ratZero.{u} (ratAdd ratOne.{u} ratOne.{u}) := by
  have hstep := (ratAdd_le_add_left_iff ratOne_mem_Rat ratZero_mem_Rat
    ratOne_mem_Rat).mpr ratZero_lt_one.left
  rw [ratAdd_zero ratOne_mem_Rat] at hstep
  exact ratLe_trans ratZero_mem_Rat ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat) ratZero_lt_one.left hstep

/-- A Cauchy sequence determines a located pair: the rationals eventually below
its terms by a margin, and those eventually above by one. This is the embedding
of the Cauchy reals into the Dedekind reals, and it needs no choice.

Proved through `isLocated_cut`: seven of the ten clauses --- both subsets, both
`_down`/`_up` monotonicities, both `_open`s and `ordered` --- are properties of
`cutLower` and `cutUpper` themselves, so the two bridges above discharge them,
and `ordered` is `lim_sep`. The two inhabitedness witnesses and the disjunction
are proved below and carried across the bridges, which turn membership into the
interior witness `isLocated_cut` wants. The disjunction is the `3D` split
against the Cauchy modulus, deciding by `ratLe_total` on a rational comparison
rather than a real one. -/
theorem isLocated_lim {f : ZFSet.{u}} (hf : f ∈ ratSeqs.{u}) (hc : IsCauchy f) :
    IsLocated (limLower f) (limUpper f) := by
  rw [limLower_eq_cut f, limUpper_eq_cut hf]
  refine isLocated_cut
    (Left := fun p' => ∃ N, N ∈ omega.{u} ∧
      ∀ n, n ∈ omega.{u} → N ⊆ n → ratLt p' (app f n))
    (Right := fun r' => ∃ N, N ∈ omega.{u} ∧
      ∀ n, n ∈ omega.{u} → N ⊆ n → ratLt (app f n) r')
    (fun hp' hr' hL hR => lim_sep hf hp' hr' hL hR) ?_ ?_ ?_
  · -- `f N - 1 - 1` is in the lower set, by the Cauchy bound at `ε = 1`
    have hlow : ∃ p, p ∈ limLower f := by
      obtain ⟨N, hN, hcau⟩ := hc ratOne.{u} ratOne_mem_Rat ratZero_lt_one
      have hfN := app_mem_Rat hf hN
      have hn1 := ratNeg_mem_Rat ratOne_mem_Rat
      refine ⟨ratAdd (ratAdd (app f N) (ratNeg ratOne.{u})) (ratNeg ratOne.{u}),
        (mem_limLower_iff f _).mpr ⟨ratAdd_mem_Rat (ratAdd_mem_Rat hfN hn1) hn1,
          ratOne.{u}, ratOne_mem_Rat, ratZero_lt_one, N, hN, fun n hn hNn => ?_⟩⟩
      have hfn := app_mem_Rat hf hn
      rw [sub_add_cancel (ratAdd_mem_Rat hfN hn1) ratOne_mem_Rat]
      -- `f N - f n < 1` gives `f N - 1 < f n`
      have hstep := hcau N hN n hn (fun _ h => h) hNn
      rw [sub_lt_iff_lt_add hfN hfn ratOne_mem_Rat] at hstep
      rw [sub_lt_iff_lt_add hfN ratOne_mem_Rat hfn, ratAdd_comm ratOne_mem_Rat hfn]
      exact hstep
    obtain ⟨p, hp⟩ := hlow
    rw [limLower_eq_cut f, mem_cutLower_iff] at hp
    obtain ⟨hpQ, p', hp'Q, hpp', hL⟩ := hp
    exact ⟨p, p', hpQ, hp'Q, hpp', hL⟩
  · -- `f N + 1 + 1` is in the upper set, the same way
    have hup : ∃ r, r ∈ limUpper f := by
      obtain ⟨N, hN, hcau⟩ := hc ratOne.{u} ratOne_mem_Rat ratZero_lt_one
      have hfN := app_mem_Rat hf hN
      refine ⟨ratAdd (ratAdd (app f N) ratOne.{u}) ratOne.{u},
        (mem_limUpper_iff f _).mpr ⟨ratAdd_mem_Rat (ratAdd_mem_Rat hfN ratOne_mem_Rat)
          ratOne_mem_Rat, ratOne.{u}, ratOne_mem_Rat, ratZero_lt_one, N, hN,
          fun n hn hNn => ?_⟩⟩
      have hfn := app_mem_Rat hf hn
      -- `f n - f N < 1` gives `f n + 1 < (f N + 1) + 1`
      have hstep := hcau n hn N hN hNn (fun _ h => h)
      rw [sub_lt_iff_lt_add hfn hfN ratOne_mem_Rat] at hstep
      exact (ratAdd_lt_add_right_iff ratOne_mem_Rat hfn
        (ratAdd_mem_Rat hfN ratOne_mem_Rat)).mpr hstep
    obtain ⟨r, hr⟩ := hup
    rw [limUpper_eq_cut hf, mem_cutUpper_iff] at hr
    obtain ⟨hrQ, r', hr'Q, hr'r, hR⟩ := hr
    exact ⟨r, r', hrQ, hr'Q, hr'r, hR⟩
  · -- the located disjunction, then across the bridges
    intro p s hpQ hsQ hps
    have hset : p ∈ limLower f ∨ s ∈ limUpper f := by
      have hnp := ratNeg_mem_Rat hpQ
      have hε : ratLt ratZero.{u} (ratAdd s (ratNeg p)) := by
        have hstep := (ratAdd_lt_add_right_iff hnp hpQ hsQ).mpr hps
        rwa [ratAdd_neg hpQ] at hstep
      -- `D` with `3D < s - p`
      obtain ⟨D, hDQ, hD0, hDlt⟩ := exists_mul_lt
        (ratAdd_mem_Rat (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat) ratOne_mem_Rat)
        (ratAdd_mem_Rat hsQ hnp)
        (ratLe_trans ratZero_mem_Rat (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)
          (ratAdd_mem_Rat (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat) ratOne_mem_Rat)
          two_nonneg (by
            have hstep := (ratAdd_le_add_left_iff (ratAdd_mem_Rat ratOne_mem_Rat
              ratOne_mem_Rat) ratZero_mem_Rat ratOne_mem_Rat).mpr ratZero_lt_one.left
            rwa [ratAdd_zero (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat)] at hstep))
        hε
      have h3D : ratLt (ratAdd (ratAdd D D) D) (ratAdd s (ratNeg p)) := by
        rwa [ratAdd_mul (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat) ratOne_mem_Rat hDQ,
            ratAdd_mul ratOne_mem_Rat ratOne_mem_Rat hDQ, ratOne_mul hDQ] at hDlt
      have hP3Q := ratAdd_mem_Rat (ratAdd_mem_Rat (ratAdd_mem_Rat hpQ hDQ) hDQ) hDQ
      have hP3 : ratLt (ratAdd (ratAdd (ratAdd p D) D) D) s := by
        have hassoc : ratAdd (ratAdd (ratAdd p D) D) D
            = ratAdd p (ratAdd (ratAdd D D) D) := by
          rw [ratAdd_assoc hpQ hDQ hDQ, ratAdd_assoc hpQ (ratAdd_mem_Rat hDQ hDQ) hDQ]
        rw [hassoc]
        have hstep := (ratAdd_lt_add_left_iff hpQ (ratAdd_mem_Rat (ratAdd_mem_Rat hDQ hDQ) hDQ)
          (ratAdd_mem_Rat hsQ hnp)).mpr h3D
        rwa [ratAdd_sub_cancel hsQ hpQ] at hstep
      obtain ⟨N, hN, hcau⟩ := hc D hDQ hD0
      have hfN := app_mem_Rat hf hN
      -- does the sequence stay above `p + 2D`, or below it?
      rcases ratLe_total (ratAdd_mem_Rat (ratAdd_mem_Rat hpQ hDQ) hDQ) hfN with hle | hle
      · refine Or.inl ((mem_limLower_iff f p).mpr ⟨hpQ, D, hDQ, hD0, N, hN,
          fun n hn hNn => ?_⟩)
        have hfn := app_mem_Rat hf hn
        -- `f N < f n + D`, and `(p + D) + D ≤ f N`
        have hstep := hcau N hN n hn (fun _ h => h) hNn
        rw [sub_lt_iff_lt_add hfN hfn hDQ] at hstep
        refine (ratAdd_lt_add_right_iff hDQ (ratAdd_mem_Rat hpQ hDQ) hfn).mp ?_
        exact ratLt_of_le_of_lt (ratAdd_mem_Rat (ratAdd_mem_Rat hpQ hDQ) hDQ) hfN
          (ratAdd_mem_Rat hfn hDQ) hle hstep
      · refine Or.inr ((mem_limUpper_iff f s).mpr ⟨hsQ,
          ratAdd s (ratNeg (ratAdd (ratAdd (ratAdd p D) D) D)),
          ratAdd_mem_Rat hsQ (ratNeg_mem_Rat hP3Q), ?_, N, hN, fun n hn hNn => ?_⟩)
        · have hstep := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat hP3Q) hP3Q hsQ).mpr hP3
          rwa [ratAdd_neg hP3Q] at hstep
        · have hfn := app_mem_Rat hf hn
          -- `f n < f N + D ≤ ((p + D) + D) + D`, so `f n + (s - that) < s`
          have hstep := hcau n hn N hN hNn (fun _ h => h)
          rw [sub_lt_iff_lt_add hfn hfN hDQ] at hstep
          have hlt3 : ratLt (app f n) (ratAdd (ratAdd (ratAdd p D) D) D) :=
            ratLt_of_lt_of_le hfn (ratAdd_mem_Rat hfN hDQ) hP3Q hstep
              ((ratAdd_le_add_right_iff hDQ hfN (ratAdd_mem_Rat (ratAdd_mem_Rat hpQ hDQ) hDQ)).mpr hle)
          have hgoal := (ratAdd_lt_add_right_iff (ratAdd_mem_Rat hsQ (ratNeg_mem_Rat hP3Q))
            hfn hP3Q).mpr hlt3
          rwa [ratAdd_sub_cancel hsQ hP3Q] at hgoal
    rcases hset with h | h
    · rw [limLower_eq_cut f, mem_cutLower_iff] at h
      exact Or.inl h.right
    · rw [limUpper_eq_cut hf, mem_cutUpper_iff] at h
      exact Or.inr h.right

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

/-- Every located pair is the pair of a Cauchy sequence -- the converse of
`isLocated_lim`. -/
def HasApprox : Prop :=
  ∀ L U : ZFSet.{u}, IsLocated L U →
    ∃ f, f ∈ ratSeqs.{u} ∧ IsCauchy f ∧ limLower f = L ∧ limUpper f = U

/-- The brackets of width below `d`, as a set: the pairs `(q, r)` with `q` in
the lower half, `r` in the upper, and `r < q + d`. `located_bracket` says this
is inhabited for every positive `d`, and an `ω`-indexed family of these is what
the converse embedding has to choose from. -/
def brackets (L U d : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => ∃ q, q ∈ L ∧ ∃ r, r ∈ U ∧ z = opair q r ∧ ratLt r (ratAdd q d))
    (prod NumberTheory.Rat.{u} NumberTheory.Rat.{u})

theorem mem_brackets_iff (L U d z : ZFSet.{u}) :
    z ∈ brackets L U d ↔ z ∈ prod NumberTheory.Rat.{u} NumberTheory.Rat.{u} ∧
      ∃ q, q ∈ L ∧ ∃ r, r ∈ U ∧ z = opair q r ∧ ratLt r (ratAdd q d) :=
  mem_sep_iff _ _ _

/-- The set of brackets is inhabited exactly when `located_bracket` says so. -/
theorem brackets_inhabited {L U d : ZFSet.{u}} (h : IsLocated L U) (hdQ : d ∈ NumberTheory.Rat.{u})
    (hd : ratLt ratZero.{u} d) : ∃ z, z ∈ brackets L U d := by
  obtain ⟨q, hq, r, hr, hlt⟩ := located_bracket h hdQ hd
  exact ⟨opair q r, (mem_brackets_iff L U d _).mpr
    ⟨opair_mem_prod (h.lower_subset _ hq) (h.upper_subset _ hr),
     q, hq, r, hr, rfl, hlt⟩⟩

/-- Widths that shrink below every positive rational.

This is the epsilon-delta definition of a sequence tending to a value,
written for the one value the development needs it at: for every positive
rational there is an index beyond which the width is smaller. Convergence and
limits are stated through this predicate throughout, so a search for limits
should land here. -/
def TendsToZero (w : ZFSet.{u}) : Prop :=
  ∀ ε, ε ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} ε → ∃ N, N ∈ omega.{u} ∧
    ∀ n, n ∈ omega.{u} → N ⊆ n → ratLt (app w n) ε

/-- The estimate both Cauchy forms are made of, with the width bound supplied
rather than searched for: `f m < r < f n + w n < f n + δ`, so `f m - f n < δ`.
Whether `δ` came from an arbitrary `ε` or from a scale is the only difference
between the two theorems below. -/
theorem sub_lt_of_bracket {L U f w : ZFSet.{u}} (h : IsLocated L U)
    (hf : f ∈ ratSeqs.{u}) (hw : w ∈ ratSeqs.{u})
    (hlow : ∀ n, n ∈ omega.{u} → app f n ∈ L)
    (hbr : ∀ n, n ∈ omega.{u} → ∃ r, r ∈ U ∧ ratLt r (ratAdd (app f n) (app w n)))
    {δ : ZFSet.{u}} (hδQ : δ ∈ NumberTheory.Rat.{u}) {m n : ZFSet.{u}}
    (hm : m ∈ omega.{u}) (hn : n ∈ omega.{u}) (hwn : ratLt (app w n) δ) :
    ratLt (ratAdd (app f m) (ratNeg (app f n))) δ := by
  obtain ⟨r, hr, hrlt⟩ := hbr n hn
  have hfm := app_mem_Rat hf hm
  have hfn := app_mem_Rat hf hn
  have hwn' := app_mem_Rat hw hn
  have hrQ := h.upper_subset _ hr
  have h₁ : ratLt (app f m) r := h.ordered _ (hlow m hm) _ hr
  have h₂ : ratLt (ratAdd (app f n) (app w n)) (ratAdd (app f n) δ) :=
    (ratAdd_lt_add_left_iff hfn hwn' hδQ).mpr hwn
  refine (sub_lt_iff_lt_add hfm hfn hδQ).mpr ?_
  exact ratLt_trans hfm hrQ (ratAdd_mem_Rat hfn hδQ) h₁
    (ratLt_trans hrQ (ratAdd_mem_Rat hfn hwn') (ratAdd_mem_Rat hfn hδQ) hrlt h₂)

/-- A sequence of lower-bracket points whose brackets shrink to nothing is
Cauchy, and the argument is two lines of ordering: `f m` is in the lower half,
the bracket at `n` puts something of the upper half below `f n + w n`, and
`ordered` separates them.

This is the mathematical content of the converse embedding. What it does not
do is produce the sequence -- that is the choice, and it is the hypothesis
here. -/
theorem isCauchy_of_brackets {L U f w : ZFSet.{u}} (h : IsLocated L U)
    (hf : f ∈ ratSeqs.{u}) (hw : w ∈ ratSeqs.{u})
    (hlow : ∀ n, n ∈ omega.{u} → app f n ∈ L)
    (hbr : ∀ n, n ∈ omega.{u} → ∃ r, r ∈ U ∧ ratLt r (ratAdd (app f n) (app w n)))
    (hw0 : TendsToZero w) : IsCauchy f := by
  intro ε hεQ hε
  obtain ⟨N, hN, hwN⟩ := hw0 ε hεQ hε
  exact ⟨N, hN, fun m hm n hn _ hNn =>
    sub_lt_of_bracket h hf hw hlow hbr hεQ hm hn (hwN n hn hNn)⟩

/-- And its limit pair is the one it brackets, in the lower half: a rational
below some term is in `L`, and a rational in `L` is eventually below the terms
by a margin. The second direction uses the brackets twice: `lower_open` twice,
then a width small enough to fit inside the gap. -/
theorem limLower_of_brackets {L U f w : ZFSet.{u}} (h : IsLocated L U)
    (hf : f ∈ ratSeqs.{u}) (hw : w ∈ ratSeqs.{u})
    (hlow : ∀ n, n ∈ omega.{u} → app f n ∈ L)
    (hbr : ∀ n, n ∈ omega.{u} → ∃ r, r ∈ U ∧ ratLt r (ratAdd (app f n) (app w n)))
    (hw0 : TendsToZero w) : limLower f = L := by
  refine ext _ _ fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · -- `q + ε < f n` for some `n`, and `f n ∈ L`
    obtain ⟨hqQ, ε, hεQ, hε, N, hN, hlt⟩ := (mem_limLower_iff f q).mp hq
    have hstep := hlt N hN (fun _ hx => hx)
    have hfN := app_mem_Rat hf hN
    refine h.lower_down _ (hlow N hN) q hqQ ?_
    have hq1 : ratLt q (ratAdd q ε) := by
      have hs := (ratAdd_lt_add_left_iff hqQ ratZero_mem_Rat hεQ).mpr hε
      rwa [ratAdd_zero hqQ] at hs
    exact ratLt_trans hqQ (ratAdd_mem_Rat hqQ hεQ) hfN hq1 hstep
  · -- open `q` twice inside `L`, then take widths below the gap
    have hqQ := h.lower_subset _ hq
    obtain ⟨q', hq', hqq'⟩ := h.lower_open _ hq
    obtain ⟨q'', hq'', hq'q''⟩ := h.lower_open _ hq'
    have hq'Q := h.lower_subset _ hq'
    have hq''Q := h.lower_subset _ hq''
    have hgap : ratLt ratZero.{u} (ratAdd q'' (ratNeg q')) := by
      have hs := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat hq'Q) hq'Q hq''Q).mpr hq'q''
      rwa [ratAdd_neg hq'Q] at hs
    obtain ⟨N, hN, hwN⟩ := hw0 _ (ratAdd_mem_Rat hq''Q (ratNeg_mem_Rat hq'Q)) hgap
    refine (mem_limLower_iff f q).mpr ⟨hqQ, ratAdd q' (ratNeg q), ?_, ?_, N, hN,
      fun n hn hNn => ?_⟩
    · exact ratAdd_mem_Rat hq'Q (ratNeg_mem_Rat hqQ)
    · have hs := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat hqQ) hqQ hq'Q).mpr hqq'
      rwa [ratAdd_neg hqQ] at hs
    · -- `q + (q' - q) = q' < f n`, because `q'' < r < f n + w n < f n + (q'' - q')`
      obtain ⟨r, hr, hrlt⟩ := hbr n hn
      have hfn := app_mem_Rat hf hn
      have hwn := app_mem_Rat hw hn
      have hrQ := h.upper_subset _ hr
      have hq''r : ratLt q'' r := h.ordered _ hq'' _ hr
      have hchain : ratLt q'' (ratAdd (app f n) (ratAdd q'' (ratNeg q'))) :=
        ratLt_trans hq''Q hrQ (ratAdd_mem_Rat hfn (ratAdd_mem_Rat hq''Q
          (ratNeg_mem_Rat hq'Q))) hq''r
          (ratLt_trans hrQ (ratAdd_mem_Rat hfn hwn)
            (ratAdd_mem_Rat hfn (ratAdd_mem_Rat hq''Q (ratNeg_mem_Rat hq'Q))) hrlt
            ((ratAdd_lt_add_left_iff hfn hwn (ratAdd_mem_Rat hq''Q
              (ratNeg_mem_Rat hq'Q))).mpr (hwN n hn hNn)))
      -- so `q' < f n`, and the goal is `q + (q' - q) < f n`
      have hq'fn : ratLt q' (app f n) := by
        refine (ratAdd_lt_add_right_iff (ratAdd_mem_Rat hq''Q (ratNeg_mem_Rat hq'Q))
          hq'Q hfn).mp ?_
        have hrw : ratAdd q' (ratAdd q'' (ratNeg q')) = q'' := by
          rw [ratAdd_comm hq''Q (ratNeg_mem_Rat hq'Q),
              ← ratAdd_assoc hq'Q (ratNeg_mem_Rat hq'Q) hq''Q,
              ratAdd_neg hq'Q, ratZero_add hq''Q]
        rw [hrw]
        exact hchain
      have hrw2 : ratAdd q (ratAdd q' (ratNeg q)) = q' := ratAdd_sub_cancel hq'Q hqQ
      rw [hrw2]
      exact hq'fn

/-- The upper half, likewise. One direction needs no brackets at all -- every
term is in `L`, so every term is below everything in `U` -- and the other picks
a width below the margin. -/
theorem limUpper_of_brackets {L U f w : ZFSet.{u}} (h : IsLocated L U)
    (hf : f ∈ ratSeqs.{u}) (hw : w ∈ ratSeqs.{u})
    (hlow : ∀ n, n ∈ omega.{u} → app f n ∈ L)
    (hbr : ∀ n, n ∈ omega.{u} → ∃ r, r ∈ U ∧ ratLt r (ratAdd (app f n) (app w n)))
    (hw0 : TendsToZero w) : limUpper f = U := by
  refine ext _ _ fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · -- a width below the margin puts something of `U` below `q`
    obtain ⟨hqQ, ε, hεQ, hε, N, hN, hlt⟩ := (mem_limUpper_iff f q).mp hq
    obtain ⟨M, hM, hwM⟩ := hw0 ε hεQ hε
    obtain ⟨n, hn, hNn, hMn⟩ := exists_upper_omega hN hM
    obtain ⟨r, hr, hrlt⟩ := hbr n hn
    have hfn := app_mem_Rat hf hn
    have hwn := app_mem_Rat hw hn
    refine h.upper_up _ hr q hqQ ?_
    exact ratLt_trans (h.upper_subset _ hr) (ratAdd_mem_Rat hfn hεQ) hqQ
      (ratLt_trans (h.upper_subset _ hr) (ratAdd_mem_Rat hfn hwn)
        (ratAdd_mem_Rat hfn hεQ) hrlt
        ((ratAdd_lt_add_left_iff hfn hwn hεQ).mpr (hwM n hn hMn)))
      (hlt n hn hNn)
  · -- open `q` twice inside `U`; every term is below the inner one
    have hqQ := h.upper_subset _ hq
    obtain ⟨q', hq', hq'q⟩ := h.upper_open _ hq
    have hq'Q := h.upper_subset _ hq'
    have hgap : ratLt ratZero.{u} (ratAdd q (ratNeg q')) := by
      have hs := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat hq'Q) hq'Q hqQ).mpr hq'q
      rwa [ratAdd_neg hq'Q] at hs
    refine (mem_limUpper_iff f q).mpr ⟨hqQ, ratAdd q (ratNeg q'),
      ratAdd_mem_Rat hqQ (ratNeg_mem_Rat hq'Q), hgap, empty.{u}, empty_mem_omega,
      fun n hn _ => ?_⟩
    have hfn := app_mem_Rat hf hn
    -- `f n < q'`, so `f n + (q - q') < q' + (q - q') = q`
    have hstep : ratLt (app f n) q' := h.ordered _ (hlow n hn) _ hq'
    have hmono := (ratAdd_lt_add_right_iff (ratAdd_mem_Rat hqQ (ratNeg_mem_Rat hq'Q))
      hfn hq'Q).mpr hstep
    rwa [ratAdd_sub_cancel hqQ hq'Q] at hmono

/-! ## The canonical widths

`1/(n+1)`, as a rational depending on a set-theoretic natural. These are the
widths the converse embedding brackets with, and `exists_invWidth_lt` is the
Archimedean step that makes them shrink past every positive rational. -/










/-- Cauchy with the rate as data, indexed by the scale rather than by an
arbitrary `ε`. The indexing is what makes the data form free: converting
`∀ ε, ∃ N` to a function needs an Archimedean index on an arbitrary rational,
and a rational is an equivalence class, whereas over the scales `1/(k+1)` there
is nothing to convert, because they are already indexed by a `Nat`.

Every Cauchy sequence this development builds satisfies this form;
`IsCauchy` is what a sequence supplied by a hypothesis
satisfies. -/
def IsCauchyWith (f : ZFSet.{u}) (N : Nat → Nat) : Prop :=
  ∀ k m n : Nat, N k ≤ m → N k ≤ n →
    ratLt (ratAdd (app f (ofNat.{u} m)) (ratNeg (app f (ofNat.{u} n))))
      (invWidth (ofNat.{u} k))

/-! ## Countable choice suffices

The last step of the converse. `bracketFam` is the family of bracket sets, one
per index, each inhabited by `brackets_inhabited`; `ACOmega` picks one from each;
`fst` reads off the lower endpoints; and the three lemmas above do the rest.

Nothing in this proof is classical except the appeal to `ACOmega`, which is a
hypothesis. That is the measurement: the converse embedding is exactly one
choice away from constructive. -/

def widthSeq : ZFSet.{u} := graphOn omega.{u} NumberTheory.Rat.{u} invWidth

theorem widthSeq_mem_ratSeqs : widthSeq.{u} ∈ ratSeqs.{u} :=
  (mem_ratSeqs_iff _).mpr ⟨graphOn_subset _ _ _, graphOn_isFunction _ _ _,
    graphOn_domain (fun n hn => invWidth_mem_Rat hn)⟩

theorem app_widthSeq {n : ZFSet.{u}} (hn : n ∈ omega.{u}) :
    app widthSeq.{u} n = invWidth n :=
  app_graphOn (fun m hm => invWidth_mem_Rat hm) hn

theorem tendsToZero_widthSeq : TendsToZero widthSeq.{u} := by
  intro ε hεQ hε
  obtain ⟨N, hN, hlt⟩ := exists_invWidth_lt hεQ hε
  refine ⟨N, hN, fun n hn hNn => ?_⟩
  rw [app_widthSeq hn]
  exact ratLt_of_le_of_lt (invWidth_mem_Rat hn) (invWidth_mem_Rat hN) hεQ
    (invWidth_antitone hN hn hNn) hlt

def bracketFam (L U : ZFSet.{u}) : ZFSet.{u} :=
  graphOn omega.{u} (powerset (prod NumberTheory.Rat.{u} NumberTheory.Rat.{u}))
    (fun n => brackets L U (invWidth n))

theorem brackets_mem_powerset (L U d : ZFSet.{u}) :
    brackets L U d ∈ powerset (prod NumberTheory.Rat.{u} NumberTheory.Rat.{u}) :=
  (mem_powerset_iff _ _).mpr (fun _ hz => ((mem_brackets_iff L U d _).mp hz).left)

/-- Countable choice turns the brackets into a sequence, and the sequence into
the Cauchy representation. -/
theorem hasApprox_of_ACOmega (hac : ACOmega.{u}) : HasApprox.{u} := by
  intro L U h
  have hfamF := graphOn_isFunction omega.{u} (powerset (prod NumberTheory.Rat.{u} NumberTheory.Rat.{u}))
    (fun n => brackets L U (invWidth n))
  have hfamD := graphOn_domain (x := omega.{u}) (y := powerset (prod NumberTheory.Rat.{u} NumberTheory.Rat.{u}))
    (F := fun n => brackets L U (invWidth n)) (fun n _ => brackets_mem_powerset L U _)
  have happ : ∀ n, n ∈ omega.{u} → app (bracketFam L U) n = brackets L U (invWidth n) :=
    fun n hn => app_graphOn (fun m _ => brackets_mem_powerset L U _) hn
  -- each bracket set is inhabited
  obtain ⟨g, hgF, hgD, hgmem⟩ := hac (bracketFam L U) hfamF hfamD (fun n hn => by
    rw [happ n hn]
    exact brackets_inhabited h (invWidth_mem_Rat hn) (invWidth_pos hn))
  -- read off the lower endpoints
  have hpair : ∀ n, n ∈ omega.{u} → ∃ q, q ∈ L ∧ ∃ r, r ∈ U ∧
      app g n = opair q r ∧ ratLt r (ratAdd q (invWidth n)) := by
    intro n hn
    have := hgmem n hn
    rw [happ n hn] at this
    obtain ⟨-, q, hq, r, hr, he, hlt⟩ := (mem_brackets_iff L U _ _).mp this
    exact ⟨q, hq, r, hr, he, hlt⟩
  have hfst : ∀ n, n ∈ omega.{u} → fst (app g n) ∈ L := by
    intro n hn
    obtain ⟨q, hq, r, -, he, -⟩ := hpair n hn
    rw [he, fst_opair]
    exact hq
  have hfstQ : ∀ n, n ∈ omega.{u} → fst (app g n) ∈ NumberTheory.Rat.{u} :=
    fun n hn => h.lower_subset _ (hfst n hn)
  have hf : graphOn omega.{u} NumberTheory.Rat.{u} (fun n => fst (app g n)) ∈ ratSeqs.{u} :=
    (mem_ratSeqs_iff _).mpr ⟨graphOn_subset _ _ _, graphOn_isFunction _ _ _,
      graphOn_domain hfstQ⟩
  have hlow : ∀ n, n ∈ omega.{u} →
      app (graphOn omega.{u} NumberTheory.Rat.{u} (fun n => fst (app g n))) n ∈ L :=
    fun n hn => by rw [app_graphOn hfstQ hn]; exact hfst n hn
  have hbr : ∀ n, n ∈ omega.{u} →
      ∃ r, r ∈ U ∧ ratLt r (ratAdd
        (app (graphOn omega.{u} NumberTheory.Rat.{u} (fun n => fst (app g n))) n) (app widthSeq.{u} n)) :=
    fun n hn => by
      obtain ⟨q, hq, r, hr, he, hlt⟩ := hpair n hn
      rw [app_graphOn hfstQ hn, app_widthSeq hn, he, fst_opair]
      exact ⟨r, hr, hlt⟩
  exact ⟨_, hf,
    isCauchy_of_brackets h hf widthSeq_mem_ratSeqs hlow hbr tendsToZero_widthSeq,
    limLower_of_brackets h hf widthSeq_mem_ratSeqs hlow hbr tendsToZero_widthSeq,
    limUpper_of_brackets h hf widthSeq_mem_ratSeqs hlow hbr tendsToZero_widthSeq⟩

#print axioms mem_ratSeqs_iff
#print axioms IsCauchy
#print axioms app_mem_Rat
#print axioms exists_upper_omega
#print axioms isLocated_lim
#print axioms limLower_eq_cut
#print axioms limUpper_eq_cut
#print axioms lim_sep
#print axioms brackets_inhabited
#print axioms isCauchy_of_brackets
#print axioms limLower_of_brackets
#print axioms limUpper_of_brackets
#print axioms IsCauchyWith
#print axioms sub_lt_of_bracket
#print axioms tendsToZero_widthSeq
#print axioms hasApprox_of_ACOmega


#print axioms two_nonneg

#print axioms natSeq_mem_ratSeqs
#print axioms mem_limLower_iff
#print axioms mem_limUpper_iff
#print axioms mem_brackets_iff
#print axioms widthSeq_mem_ratSeqs
#print axioms app_widthSeq
#print axioms brackets_mem_powerset
end Analysis

namespace ZFSet
export Analysis (ACOmega HasApprox IsCauchy IsCauchyWith TendsToZero app_mem_Rat app_widthSeq bracketFam brackets brackets_inhabited brackets_mem_powerset exists_upper_omega hasApprox_of_ACOmega isCauchy_of_brackets isLocated_lim lim_sep limLower limLower_eq_cut limLower_of_brackets limUpper limUpper_eq_cut limUpper_of_brackets mem_brackets_iff mem_limLower_iff mem_limUpper_iff mem_ratSeqs_iff natSeq_mem_ratSeqs ratSeqs sub_lt_of_bracket tendsToZero_widthSeq widthSeq widthSeq_mem_ratSeqs)
end ZFSet
