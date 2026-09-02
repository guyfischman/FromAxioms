/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Reals as located pairs.

`Real.lean` presents a real as a single lower cut, and locatedness on that
encoding is not free: a member and a non-member arbitrarily close together has
to be found by scanning a ladder and deciding membership at each rung, which is
`Classical.em`.

This file asks whether that cost is the encoding's rather than the theorem's. A
located pair carries both a lower set `L` and an upper set `U`, with the
clause `p < q → p ∈ L ∨ q ∈ U` as part of the structure. The same ladder scan
then runs on that disjunction instead of on excluded middle, and
`located_bracket` comes out choice-free.

What is not here: multiplication. The four-corner definition that avoids the
sign split of `realMul` lives on this encoding, and the estimates it needs are
a separate piece of work.
-/

import FromAxioms.Analysis.Real

universe u

open NumberTheory SetTheory
namespace Analysis

/-- A Dedekind real presented as a located pair of sets of rationals. -/
structure IsLocated (L U : ZFSet.{u}) : Prop where
  lower_subset : L ⊆ NumberTheory.Rat.{u}
  upper_subset : U ⊆ NumberTheory.Rat.{u}
  lower_inhabited : ∃ q, q ∈ L
  upper_inhabited : ∃ r, r ∈ U
  ordered : ∀ q, q ∈ L → ∀ r, r ∈ U → ratLt q r
  lower_down : ∀ q, q ∈ L → ∀ p, p ∈ NumberTheory.Rat.{u} → ratLt p q → p ∈ L
  upper_up : ∀ r, r ∈ U → ∀ p, p ∈ NumberTheory.Rat.{u} → ratLt r p → p ∈ U
  lower_open : ∀ q, q ∈ L → ∃ q', q' ∈ L ∧ ratLt q q'
  upper_open : ∀ r, r ∈ U → ∃ r', r' ∈ U ∧ ratLt r' r
  located : ∀ p, p ∈ NumberTheory.Rat.{u} → ∀ q, q ∈ NumberTheory.Rat.{u} → ratLt p q → p ∈ L ∨ q ∈ U

/-- The located pair of a rational. -/
theorem isLocated_ratCut {q : ZFSet.{u}} (hq : q ∈ NumberTheory.Rat.{u}) :
    IsLocated (ratCut q) (sep (fun p => ratLt q p) NumberTheory.Rat.{u}) where
  lower_subset p hp := ((mem_ratCut_iff q p).mp hp).left
  upper_subset p hp := ((mem_sep_iff _ p _).mp hp).left
  lower_inhabited := by
    obtain ⟨s, hs, hlt⟩ := rat_no_least hq
    exact ⟨s, (mem_ratCut_iff q s).mpr ⟨hs, hlt⟩⟩
  upper_inhabited := by
    obtain ⟨s, hs, hlt⟩ := rat_no_greatest hq
    exact ⟨s, (mem_sep_iff _ s _).mpr ⟨hs, hlt⟩⟩
  ordered p hp r hr := by
    obtain ⟨hpQ, hpq⟩ := (mem_ratCut_iff q p).mp hp
    obtain ⟨hrQ, hqr⟩ := (mem_sep_iff _ r _).mp hr
    exact ratLt_trans hpQ hq hrQ hpq hqr
  lower_down r hr p hp hlt := by
    obtain ⟨hrQ, hrq⟩ := (mem_ratCut_iff q r).mp hr
    exact (mem_ratCut_iff q p).mpr ⟨hp, ratLt_trans hp hrQ hq hlt hrq⟩
  upper_up r hr p hp hlt := by
    obtain ⟨hrQ, hqr⟩ := (mem_sep_iff _ r _).mp hr
    exact (mem_sep_iff _ p _).mpr ⟨hp, ratLt_trans hq hrQ hp hqr hlt⟩
  lower_open p hp := by
    obtain ⟨hpQ, hpq⟩ := (mem_ratCut_iff q p).mp hp
    obtain ⟨t, htQ, h₁, h₂⟩ := rat_dense hpQ hq hpq
    exact ⟨t, (mem_ratCut_iff q t).mpr ⟨htQ, h₂⟩, h₁⟩
  upper_open r hr := by
    obtain ⟨hrQ, hqr⟩ := (mem_sep_iff _ r _).mp hr
    obtain ⟨t, htQ, h₁, h₂⟩ := rat_dense hq hrQ hqr
    exact ⟨t, (mem_sep_iff _ t _).mpr ⟨htQ, h₁⟩, h₂⟩
  located p hp r hr hlt := by
    -- the disjunction is decided by trichotomy on ℚ, which is constructive
    rcases ratLt_trichotomy hp hq with h | h | h
    · exact Or.inl ((mem_ratCut_iff q p).mpr ⟨hp, h⟩)
    · exact Or.inr ((mem_sep_iff _ r _).mpr ⟨hr, h ▸ hlt⟩)
    · exact Or.inr ((mem_sep_iff _ r _).mpr ⟨hr, ratLt_trans hq hp hr h hlt⟩)

/-! ## Locatedness, constructively -/

/-- A readout for `located`, indexed on the cuts rather than on a real.
`SideReadout` names which side of a rational pair a given real falls; this
names which disjunct of `IsLocated.located` holds, as a set-level bit.

Set-level and not a Lean `Bool`, which is the library's idiom: `condP`
branches on a `Prop` with no decidability hypothesis, so a readout composes
into a function at no principle. -/
structure LocatedReadout (L U : ZFSet.{u}) : Type (u + 1) where
  bit : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}
  mem_two : ∀ p q, p ∈ NumberTheory.Rat.{u} → q ∈ NumberTheory.Rat.{u} → ratLt p q →
    bit p q ∈ ofNat.{u} 2
  lower : ∀ p q, p ∈ NumberTheory.Rat.{u} → q ∈ NumberTheory.Rat.{u} → ratLt p q →
    bit p q = ofNat.{u} 1 → p ∈ L
  upper : ∀ p q, p ∈ NumberTheory.Rat.{u} → q ∈ NumberTheory.Rat.{u} → ratLt p q →
    bit p q = empty.{u} → q ∈ U

/-- A located pair together with a rational bracket, carried as data.

`exists_rat_bound` already proves every located real has such a bracket, and
proves it choice-free -- but its conclusion is an `∃`, so the number cannot be
released into `Type` and no construction can consume it. This is the same
content in the universe where one can.

The distinction is not constructivity. `exists_rat_bound` is fully
constructive and still will not hand the bound over; what separates the two is
the universe the statement lives in.

WHAT THE FAMILY BELOW MEASURES, since the members alone do not say it.
Bound-carrying is closed under the RING operations --
the members named ratCut, neg, add and mul, each with a bound-computing companion
for the resulting bracket -- so a real built from rationals by `+`, `-` and `×`
carries a bound as data where an arbitrary located one does not. It stops at the
ring, and that boundary is the result: there is no inverse member and there
cannot be, because
bounding an inverse needs a LOWER bound on the input, which is apartness from
zero.

The family has no consumer outside this file. That is not neglect -- nothing yet
needs a bound as DATA -- and it is why the members name only each other. -/
structure BoundedLocated (L U : ZFSet.{u}) : Type (u + 1) where
  bound : ZFSet.{u}
  bound_mem : bound ∈ NumberTheory.Rat.{u}
  lower_lt : ratNeg bound ∈ L
  upper_gt : bound ∈ U

theorem located_bracket {L U ε : ZFSet.{u}} (h : IsLocated L U) (hεQ : ε ∈ NumberTheory.Rat.{u})
    (hε : ratLt ratZero.{u} ε) :
    ∃ q, q ∈ L ∧ ∃ r, r ∈ U ∧ ratLt r (ratAdd q ε) := by
  obtain ⟨e, heQ, h0e, heε⟩ := rat_dense ratZero_mem_Rat hεQ hε
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Rat_iff e).mp heQ
  have haP := intPositive_num ha hb h0e
  have htwo : intAdd intOne.{u} intOne.{u} ∈ intPositive.{u} :=
    intAdd_mem_intPositive one_mem_intPositive one_mem_intPositive
  have hB : intMul (intAdd intOne.{u} intOne.{u}) b ∈ intPositive.{u} :=
    intMul_mem_intPositive htwo hb
  have hstepQ : ratOf intOne.{u} (intMul (intAdd intOne.{u} intOne.{u}) b) ∈ NumberTheory.Rat.{u} :=
    ratOf_mem_Rat intOne_mem_Int hB
  have hstep0 := ratOf_one_pos hB
  obtain ⟨q₀, hq₀⟩ := h.lower_inhabited
  have hq₀Q := h.lower_subset q₀ hq₀
  obtain ⟨r₀, hr₀⟩ := h.upper_inhabited
  have hr₀Q := h.upper_subset r₀ hr₀
  -- the ladder, and the facts about one and two of its rungs
  have hfQ : ∀ n : Nat, ratAdd q₀ (ratOf (intOfNat.{u} n)
      (intMul (intAdd intOne.{u} intOne.{u}) b)) ∈ NumberTheory.Rat.{u} := fun n =>
    ratAdd_mem_Rat hq₀Q (ratOf_mem_Rat (intOfNat_mem_Int n) hB)
  have hsucc : ∀ n : Nat, ratAdd q₀ (ratOf (intOfNat.{u} (n + 1))
        (intMul (intAdd intOne.{u} intOne.{u}) b))
      = ratAdd (ratAdd q₀ (ratOf (intOfNat.{u} n)
          (intMul (intAdd intOne.{u} intOne.{u}) b)))
        (ratOf intOne.{u} (intMul (intAdd intOne.{u} intOne.{u}) b)) := fun n => by
    rw [ratOf_intOfNat_succ hB n, ratAdd_assoc hq₀Q
      (ratOf_mem_Rat (intOfNat_mem_Int n) hB) hstepQ]
  have hmono : ∀ n : Nat, ratLt (ratAdd q₀ (ratOf (intOfNat.{u} n)
        (intMul (intAdd intOne.{u} intOne.{u}) b)))
      (ratAdd q₀ (ratOf (intOfNat.{u} (n + 1))
        (intMul (intAdd intOne.{u} intOne.{u}) b))) := fun n => by
    rw [hsucc n]
    have hstep := (ratAdd_lt_add_left_iff (hfQ n) ratZero_mem_Rat hstepQ).mpr hstep0
    rwa [ratAdd_zero (hfQ n)] at hstep
  -- the ladder starts inside L and eventually passes r₀
  have hP0 : ratAdd q₀ (ratOf (intOfNat.{u} 0)
      (intMul (intAdd intOne.{u} intOne.{u}) b)) ∈ L := by
    rw [intOfNat_zero, ratOf_intZero hB, ratAdd_zero hq₀Q]
    exact hq₀
  obtain ⟨N, hN⟩ := rat_archimedean (ratAdd_mem_Rat hr₀Q (ratNeg_mem_Rat hq₀Q)) hB
  have hNout : ratAdd q₀ (ratOf (intOfNat.{u} N)
      (intMul (intAdd intOne.{u} intOne.{u}) b)) ∈ U := by
    refine h.upper_up r₀ hr₀ _ (hfQ N) ?_
    have hstep := (ratAdd_lt_add_left_iff hq₀Q
      (ratAdd_mem_Rat hr₀Q (ratNeg_mem_Rat hq₀Q))
      (ratOf_mem_Rat (intOfNat_mem_Int N) hB)).mpr hN
    rwa [ratAdd_sub_cancel hr₀Q hq₀Q] at hstep
  -- walk the ladder: `located` on consecutive rungs, never excluded middle
  have walk : ∀ n : Nat,
      (∃ k : Nat, ratAdd q₀ (ratOf (intOfNat.{u} k)
          (intMul (intAdd intOne.{u} intOne.{u}) b)) ∈ L ∧
        ratAdd q₀ (ratOf (intOfNat.{u} (k + 2))
          (intMul (intAdd intOne.{u} intOne.{u}) b)) ∈ U) ∨
      ratAdd q₀ (ratOf (intOfNat.{u} n)
        (intMul (intAdd intOne.{u} intOne.{u}) b)) ∈ L := by
    intro n
    induction n with
    | zero => exact Or.inr hP0
    | succ m ih =>
      rcases ih with hfound | hm
      · exact Or.inl hfound
      · rcases h.located _ (hfQ (m + 1)) _ (hfQ (m + 2)) (hmono (m + 1)) with hl | hu
        · exact Or.inr hl
        · exact Or.inl ⟨m, hm, hu⟩
  rcases walk N with ⟨k, hk, hk2⟩ | hNin
  · refine ⟨_, hk, _, hk2, ?_⟩
    -- the bracket spans two rungs, which is `1/b`, which is below `ε`
    have htwostep : ratAdd q₀ (ratOf (intOfNat.{u} (k + 2))
          (intMul (intAdd intOne.{u} intOne.{u}) b))
        = ratAdd (ratAdd q₀ (ratOf (intOfNat.{u} k)
            (intMul (intAdd intOne.{u} intOne.{u}) b))) (ratOf intOne.{u} b) := by
      rw [hsucc (k + 1), hsucc k, ratAdd_assoc (hfQ k) hstepQ hstepQ,
          ratOf_add_same_denom intOne_mem_Int intOne_mem_Int hB]
      congr 1
      have hcancel := ratOf_cancel htwo intOne_mem_Int hb
      rwa [intMul_one (intPositive_subset _ htwo)] at hcancel
    rw [htwostep]
    refine (ratAdd_lt_add_left_iff (hfQ k) (ratOf_mem_Rat intOne_mem_Int hb) hεQ).mpr ?_
    exact ratLt_of_le_of_lt (ratOf_mem_Rat intOne_mem_Int hb)
      (ratOf_mem_Rat (intPositive_subset _ haP) hb) hεQ (ratOf_one_le haP hb) heε
  · exact absurd (h.ordered _ hNin _ hNout) ratLt_irrefl


/-! ## Completeness, for located families

    for all rationals `p < q`, either some member reaches above `p`,
    or every member stays below `q`.

With that hypothesis the supremum is a located pair and nothing here is
classical. The upper set is defined rounded -- `r` counts as an upper bound
only when some strictly smaller rational already is one -- so `upper_open` is
immediate rather than another ladder. -/

/-- The located reals, as a set of ordered pairs. -/
def RealL : ZFSet.{u} :=
  sep (fun z => ∃ L U, z = opair L U ∧ IsLocated L U)
    (prod (powerset NumberTheory.Rat.{u}) (powerset NumberTheory.Rat.{u}))

theorem mem_RealL_iff (z : ZFSet.{u}) :
    z ∈ RealL.{u} ↔ ∃ L U, z = opair L U ∧ IsLocated L U := by
  refine Iff.trans (mem_sep_iff _ _ _) ⟨And.right, ?_⟩
  rintro ⟨L, U, rfl, hloc⟩
  exact ⟨opair_mem_prod ((mem_powerset_iff _ _).mpr hloc.lower_subset)
    ((mem_powerset_iff _ _).mpr hloc.upper_subset), L, U, rfl, hloc⟩

/-- `q' + r' < s`, given that both brackets have width below `D`, that
`2D < s - p`, and that `q + r` has not exceeded `p`. -/
private theorem add_window {q q' r r' p s D : ZFSet.{u}} (hqQ : q ∈ NumberTheory.Rat.{u})
    (hq'Q : q' ∈ NumberTheory.Rat.{u}) (hrQ : r ∈ NumberTheory.Rat.{u}) (hr'Q : r' ∈ NumberTheory.Rat.{u})
    (hpQ : p ∈ NumberTheory.Rat.{u}) (hsQ : s ∈ NumberTheory.Rat.{u}) (hDQ : D ∈ NumberTheory.Rat.{u})
    (hqw : ratLt q' (ratAdd q D)) (hrw : ratLt r' (ratAdd r D))
    (hDD : ratLt (ratAdd D D) (ratAdd s (ratNeg p)))
    (hle : ratLe (ratAdd q r) p) : ratLt (ratAdd q' r') s := by
  have hqr := ratAdd_mem_Rat hqQ hrQ
  have hDDQ := ratAdd_mem_Rat hDQ hDQ
  -- `q' + r' < (q + D) + (r + D) = (q + r) + (D + D) ≤ p + (D + D) < s`
  have h₁ : ratLt (ratAdd q' r') (ratAdd (ratAdd q D) (ratAdd r D)) :=
    ratAdd_lt_add hq'Q (ratAdd_mem_Rat hqQ hDQ) hr'Q (ratAdd_mem_Rat hrQ hDQ) hqw hrw
  have h₂ : ratAdd (ratAdd q D) (ratAdd r D) = ratAdd (ratAdd q r) (ratAdd D D) := by
    rw [ratAdd_assoc hqQ hDQ (ratAdd_mem_Rat hrQ hDQ),
        ← ratAdd_assoc hDQ hrQ hDQ, ratAdd_comm hDQ hrQ,
        ratAdd_assoc hrQ hDQ hDQ, ← ratAdd_assoc hqQ hrQ hDDQ]
  have h₃ : ratLe (ratAdd (ratAdd q r) (ratAdd D D)) (ratAdd p (ratAdd D D)) :=
    (ratAdd_le_add_right_iff hDDQ hqr hpQ).mpr hle
  have h₄ : ratLt (ratAdd p (ratAdd D D)) s := by
    have hstep := (ratAdd_lt_add_left_iff hpQ hDDQ
      (ratAdd_mem_Rat hsQ (ratNeg_mem_Rat hpQ))).mpr hDD
    rwa [ratAdd_sub_cancel hsQ hpQ] at hstep
  rw [h₂] at h₁
  exact ratLt_trans (ratAdd_mem_Rat hq'Q hr'Q) (ratAdd_mem_Rat hpQ hDDQ) hsQ
    (ratLt_of_lt_of_le (ratAdd_mem_Rat hq'Q hr'Q) (ratAdd_mem_Rat hqr hDDQ)
      (ratAdd_mem_Rat hpQ hDDQ) h₁ h₃) h₄

/-! ## The order

Comparison of lower halves, as for one-sided cuts. The upper half carries no
extra information -- `mem_upper_iff` shows it is determined by the lower one --
so this really is a comparison of pairs. -/

def pairLe (L₁ L₂ : ZFSet.{u}) : Prop := L₁ ⊆ L₂

/-- The upper half is exactly the rationals with something below them outside
the lower half. Locatedness is what makes the `←` direction work. -/
theorem mem_upper_iff {L U : ZFSet.{u}} (h : IsLocated L U) (r : ZFSet.{u}) :
    r ∈ U ↔ r ∈ NumberTheory.Rat.{u} ∧ ∃ q, q ∈ NumberTheory.Rat.{u} ∧ ratLt q r ∧ q ∉ L := by
  constructor
  · intro hr
    obtain ⟨q, hq, hlt⟩ := h.upper_open r hr
    exact ⟨h.upper_subset r hr, q, h.upper_subset q hq, hlt,
      fun hqL => ratLt_irrefl (h.ordered q hqL q hq)⟩
  · rintro ⟨hrQ, q, hqQ, hlt, hqL⟩
    rcases h.located q hqQ r hrQ hlt with hl | hu
    · exact absurd hl hqL
    · exact hu

/-- So a located pair is determined by its lower half. -/
theorem upper_eq_of_lower_eq {L U U' : ZFSet.{u}} (h : IsLocated L U)
    (h' : IsLocated L U') : U = U' :=
  ext U U' fun r => Iff.trans (mem_upper_iff h r) (mem_upper_iff h' r).symm

theorem pairLe_antisymm {L₁ U₁ L₂ U₂ : ZFSet.{u}} (h₁ : IsLocated L₁ U₁)
    (h₂ : IsLocated L₂ U₂) (ha : pairLe L₁ L₂) (hb : pairLe L₂ L₁) :
    L₁ = L₂ ∧ U₁ = U₂ := by
  have hL : L₁ = L₂ := ext L₁ L₂ fun w => ⟨ha w, hb w⟩
  exact ⟨hL, upper_eq_of_lower_eq h₁ (hL ▸ h₂)⟩

/-! ## Addition and negation

The same shape as multiplication, and easier: the sum of two brackets is one
bracket, so no corners and no estimate beyond splitting `s - p` in two. -/

def addLower (L₁ L₂ : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ q, q ∈ L₁ ∧ ∃ r, r ∈ L₂ ∧ ratLt p (ratAdd q r)) NumberTheory.Rat.{u}

def addUpper (U₁ U₂ : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ q, q ∈ U₁ ∧ ∃ r, r ∈ U₂ ∧ ratLt (ratAdd q r) p) NumberTheory.Rat.{u}

theorem mem_addLower_iff (L₁ L₂ p : ZFSet.{u}) :
    p ∈ addLower L₁ L₂ ↔ p ∈ NumberTheory.Rat.{u} ∧
      ∃ q, q ∈ L₁ ∧ ∃ r, r ∈ L₂ ∧ ratLt p (ratAdd q r) :=
  mem_sep_iff _ _ _

theorem mem_addUpper_iff (U₁ U₂ p : ZFSet.{u}) :
    p ∈ addUpper U₁ U₂ ↔ p ∈ NumberTheory.Rat.{u} ∧
      ∃ q, q ∈ U₁ ∧ ∃ r, r ∈ U₂ ∧ ratLt (ratAdd q r) p :=
  mem_sep_iff _ _ _

theorem isLocated_add {L₁ U₁ L₂ U₂ : ZFSet.{u}} (h₁ : IsLocated L₁ U₁)
    (h₂ : IsLocated L₂ U₂) : IsLocated (addLower L₁ L₂) (addUpper U₁ U₂) where
  lower_subset p hp := ((mem_addLower_iff _ _ p).mp hp).left
  upper_subset p hp := ((mem_addUpper_iff _ _ p).mp hp).left
  lower_inhabited := by
    obtain ⟨q, hq⟩ := h₁.lower_inhabited
    obtain ⟨r, hr⟩ := h₂.lower_inhabited
    obtain ⟨t, htQ, hlt⟩ := rat_no_least
      (ratAdd_mem_Rat (h₁.lower_subset _ hq) (h₂.lower_subset _ hr))
    exact ⟨t, (mem_addLower_iff _ _ t).mpr ⟨htQ, q, hq, r, hr, hlt⟩⟩
  upper_inhabited := by
    obtain ⟨q, hq⟩ := h₁.upper_inhabited
    obtain ⟨r, hr⟩ := h₂.upper_inhabited
    obtain ⟨t, htQ, hlt⟩ := rat_no_greatest
      (ratAdd_mem_Rat (h₁.upper_subset _ hq) (h₂.upper_subset _ hr))
    exact ⟨t, (mem_addUpper_iff _ _ t).mpr ⟨htQ, q, hq, r, hr, hlt⟩⟩
  ordered p hp t ht := by
    obtain ⟨hpQ, q, hq, r, hr, hlt⟩ := (mem_addLower_iff _ _ p).mp hp
    obtain ⟨htQ, q', hq', r', hr', hlt'⟩ := (mem_addUpper_iff _ _ t).mp ht
    have hsum : ratLt (ratAdd q r) (ratAdd q' r') :=
      ratAdd_lt_add (h₁.lower_subset _ hq) (h₁.upper_subset _ hq')
        (h₂.lower_subset _ hr) (h₂.upper_subset _ hr')
        (h₁.ordered _ hq _ hq') (h₂.ordered _ hr _ hr')
    exact ratLt_trans hpQ (ratAdd_mem_Rat (h₁.lower_subset _ hq)
      (h₂.lower_subset _ hr)) htQ hlt
      (ratLt_trans (ratAdd_mem_Rat (h₁.lower_subset _ hq) (h₂.lower_subset _ hr))
        (ratAdd_mem_Rat (h₁.upper_subset _ hq') (h₂.upper_subset _ hr')) htQ hsum hlt')
  lower_down p hp p' hp'Q hlt := by
    obtain ⟨hpQ, q, hq, r, hr, h⟩ := (mem_addLower_iff _ _ p).mp hp
    exact (mem_addLower_iff _ _ p').mpr ⟨hp'Q, q, hq, r, hr,
      ratLt_trans hp'Q hpQ (ratAdd_mem_Rat (h₁.lower_subset _ hq)
        (h₂.lower_subset _ hr)) hlt h⟩
  upper_up p hp p' hp'Q hlt := by
    obtain ⟨hpQ, q, hq, r, hr, h⟩ := (mem_addUpper_iff _ _ p).mp hp
    exact (mem_addUpper_iff _ _ p').mpr ⟨hp'Q, q, hq, r, hr,
      ratLt_trans (ratAdd_mem_Rat (h₁.upper_subset _ hq) (h₂.upper_subset _ hr))
        hpQ hp'Q h hlt⟩
  lower_open p hp := by
    obtain ⟨hpQ, q, hq, r, hr, h⟩ := (mem_addLower_iff _ _ p).mp hp
    obtain ⟨t, htQ, h₁', h₂'⟩ := rat_dense hpQ (ratAdd_mem_Rat
      (h₁.lower_subset _ hq) (h₂.lower_subset _ hr)) h
    exact ⟨t, (mem_addLower_iff _ _ t).mpr ⟨htQ, q, hq, r, hr, h₂'⟩, h₁'⟩
  upper_open p hp := by
    obtain ⟨hpQ, q, hq, r, hr, h⟩ := (mem_addUpper_iff _ _ p).mp hp
    obtain ⟨t, htQ, h₁', h₂'⟩ := rat_dense (ratAdd_mem_Rat
      (h₁.upper_subset _ hq) (h₂.upper_subset _ hr)) hpQ h
    exact ⟨t, (mem_addUpper_iff _ _ t).mpr ⟨htQ, q, hq, r, hr, h₁'⟩, h₂'⟩
  located p hpQ s hsQ hps := by
    have hnp := ratNeg_mem_Rat hpQ
    have hε : ratLt ratZero.{u} (ratAdd s (ratNeg p)) := by
      have hstep := (ratAdd_lt_add_right_iff hnp hpQ hsQ).mpr hps
      rwa [ratAdd_neg hpQ] at hstep
    obtain ⟨D, hDQ, hD0, hDlt⟩ := exists_mul_lt (ratAdd_mem_Rat ratOne_mem_Rat
      ratOne_mem_Rat) (ratAdd_mem_Rat hsQ hnp)
      (by
        have hstep := (ratAdd_le_add_left_iff ratOne_mem_Rat ratZero_mem_Rat
          ratOne_mem_Rat).mpr ratZero_lt_one.left
        rw [ratAdd_zero ratOne_mem_Rat] at hstep
        exact ratLe_trans ratZero_mem_Rat ratOne_mem_Rat
          (ratAdd_mem_Rat ratOne_mem_Rat ratOne_mem_Rat) ratZero_lt_one.left hstep)
      hε
    have hDD : ratLt (ratAdd D D) (ratAdd s (ratNeg p)) := by
      rwa [ratAdd_mul ratOne_mem_Rat ratOne_mem_Rat hDQ, ratOne_mul hDQ] at hDlt
    obtain ⟨q, hq, q', hq', hqw⟩ := located_bracket h₁ hDQ hD0
    obtain ⟨r, hr, r', hr', hrw⟩ := located_bracket h₂ hDQ hD0
    have hqQ := h₁.lower_subset _ hq
    have hq'Q := h₁.upper_subset _ hq'
    have hrQ := h₂.lower_subset _ hr
    have hr'Q := h₂.upper_subset _ hr'
    rcases ratLt_trichotomy hpQ (ratAdd_mem_Rat hqQ hrQ) with hlt | heq | hgt
    · exact Or.inl ((mem_addLower_iff _ _ p).mpr ⟨hpQ, q, hq, r, hr, hlt⟩)
    · exact Or.inr ((mem_addUpper_iff _ _ s).mpr ⟨hsQ, q', hq', r', hr',
        add_window hqQ hq'Q hrQ hr'Q hpQ hsQ hDQ hqw hrw hDD
          (by rw [← heq]; exact ratLe_refl hpQ)⟩)
    · exact Or.inr ((mem_addUpper_iff _ _ s).mpr ⟨hsQ, q', hq', r', hr',
        add_window hqQ hq'Q hrQ hr'Q hpQ hsQ hDQ hqw hrw hDD hgt.left⟩)

def negLower (U₁ : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ r, r ∈ U₁ ∧ ratLt p (ratNeg r)) NumberTheory.Rat.{u}

def negUpper (L₁ : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ q, q ∈ L₁ ∧ ratLt (ratNeg q) p) NumberTheory.Rat.{u}

theorem mem_negLower_iff (U₁ p : ZFSet.{u}) :
    p ∈ negLower U₁ ↔ p ∈ NumberTheory.Rat.{u} ∧ ∃ r, r ∈ U₁ ∧ ratLt p (ratNeg r) :=
  mem_sep_iff _ _ _

theorem mem_negUpper_iff (L₁ p : ZFSet.{u}) :
    p ∈ negUpper L₁ ↔ p ∈ NumberTheory.Rat.{u} ∧ ∃ q, q ∈ L₁ ∧ ratLt (ratNeg q) p :=
  mem_sep_iff _ _ _

/-- Negation just swaps the two halves and reflects them. Unlike the one-sided
`realNeg`, no quantification over the complement is needed -- the upper set is
already there. -/
theorem isLocated_neg {L₁ U₁ : ZFSet.{u}} (h₁ : IsLocated L₁ U₁) :
    IsLocated (negLower U₁) (negUpper L₁) where
  lower_subset p hp := ((mem_negLower_iff _ p).mp hp).left
  upper_subset p hp := ((mem_negUpper_iff _ p).mp hp).left
  lower_inhabited := by
    obtain ⟨r, hr⟩ := h₁.upper_inhabited
    obtain ⟨t, htQ, hlt⟩ := rat_no_least (ratNeg_mem_Rat (h₁.upper_subset _ hr))
    exact ⟨t, (mem_negLower_iff _ t).mpr ⟨htQ, r, hr, hlt⟩⟩
  upper_inhabited := by
    obtain ⟨q, hq⟩ := h₁.lower_inhabited
    obtain ⟨t, htQ, hlt⟩ := rat_no_greatest (ratNeg_mem_Rat (h₁.lower_subset _ hq))
    exact ⟨t, (mem_negUpper_iff _ t).mpr ⟨htQ, q, hq, hlt⟩⟩
  ordered p hp t ht := by
    obtain ⟨hpQ, r, hr, hlt⟩ := (mem_negLower_iff _ p).mp hp
    obtain ⟨htQ, q, hq, hlt'⟩ := (mem_negUpper_iff _ t).mp ht
    have hqr : ratLt q r := h₁.ordered _ hq _ hr
    have hneg : ratLt (ratNeg r) (ratNeg q) :=
      (ratNeg_lt_neg_iff (h₁.upper_subset _ hr) (h₁.lower_subset _ hq)).mpr hqr
    exact ratLt_trans hpQ (ratNeg_mem_Rat (h₁.upper_subset _ hr)) htQ hlt
      (ratLt_trans (ratNeg_mem_Rat (h₁.upper_subset _ hr))
        (ratNeg_mem_Rat (h₁.lower_subset _ hq)) htQ hneg hlt')
  lower_down p hp p' hp'Q hlt := by
    obtain ⟨hpQ, r, hr, h⟩ := (mem_negLower_iff _ p).mp hp
    exact (mem_negLower_iff _ p').mpr ⟨hp'Q, r, hr,
      ratLt_trans hp'Q hpQ (ratNeg_mem_Rat (h₁.upper_subset _ hr)) hlt h⟩
  upper_up p hp p' hp'Q hlt := by
    obtain ⟨hpQ, q, hq, h⟩ := (mem_negUpper_iff _ p).mp hp
    exact (mem_negUpper_iff _ p').mpr ⟨hp'Q, q, hq,
      ratLt_trans (ratNeg_mem_Rat (h₁.lower_subset _ hq)) hpQ hp'Q h hlt⟩
  lower_open p hp := by
    obtain ⟨hpQ, r, hr, h⟩ := (mem_negLower_iff _ p).mp hp
    obtain ⟨t, htQ, ha, hb⟩ := rat_dense hpQ (ratNeg_mem_Rat (h₁.upper_subset _ hr)) h
    exact ⟨t, (mem_negLower_iff _ t).mpr ⟨htQ, r, hr, hb⟩, ha⟩
  upper_open p hp := by
    obtain ⟨hpQ, q, hq, h⟩ := (mem_negUpper_iff _ p).mp hp
    obtain ⟨t, htQ, ha, hb⟩ := rat_dense (ratNeg_mem_Rat (h₁.lower_subset _ hq)) hpQ h
    exact ⟨t, (mem_negUpper_iff _ t).mpr ⟨htQ, q, hq, ha⟩, hb⟩
  located p hpQ s hsQ hps := by
    -- `-s < -p`, so locatedness of the factor at that pair transfers
    have hnp := ratNeg_mem_Rat hpQ
    have hns := ratNeg_mem_Rat hsQ
    rcases h₁.located _ hns _ hnp ((ratNeg_lt_neg_iff hsQ hpQ).mpr hps) with hl | hu
    · -- `-s ∈ L₁`; open it to a strictly larger `q`, so `-q < s`
      obtain ⟨q, hq, hlt⟩ := h₁.lower_open _ hl
      refine Or.inr ((mem_negUpper_iff _ s).mpr ⟨hsQ, q, hq, ?_⟩)
      have hstep := (ratNeg_lt_neg_iff (h₁.lower_subset _ hq) hns).mpr hlt
      rwa [ratNeg_ratNeg hsQ] at hstep
    · obtain ⟨r, hr, hlt⟩ := h₁.upper_open _ hu
      refine Or.inl ((mem_negLower_iff _ p).mpr ⟨hpQ, r, hr, ?_⟩)
      have hstep := (ratNeg_lt_neg_iff hnp (h₁.upper_subset _ hr)).mpr hlt
      rwa [ratNeg_ratNeg hpQ] at hstep

#print axioms Analysis.IsLocated
#print axioms Analysis.RealL
#print axioms isLocated_ratCut
#print axioms located_bracket        -- the point: no Classical.choice
#print axioms mem_upper_iff
#print axioms pairLe_antisymm
#print axioms isLocated_add
#print axioms isLocated_neg
#print axioms Analysis.LocatedReadout
#print axioms Analysis.BoundedLocated
end Analysis





namespace ZFSet
export Analysis (BoundedLocated IsLocated LocatedReadout RealL addLower addUpper isLocated_add isLocated_neg isLocated_ratCut located_bracket mem_RealL_iff mem_addLower_iff mem_addUpper_iff mem_negLower_iff mem_negUpper_iff mem_upper_iff negLower negUpper pairLe pairLe_antisymm upper_eq_of_lower_eq)
end ZFSet
