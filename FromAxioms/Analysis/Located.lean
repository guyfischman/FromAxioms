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

open Algebra NumberTheory SetTheory
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

/-! ## Multiplication, without a sign split

The product of two intervals is bounded by its four corner products, so the
lower set of `x · y` is the rationals strictly below all four, and the upper
set those strictly above all four. Written as a conjunction rather than with
`min`, which keeps the definition free of any decision, and is the reason this
can be choice-free where `realMul` is not.

Its proof is not yet written, and the pieces it needs are. Given `p < s`, put
`ε := s - p`, bound all four initial bracket endpoints by some `K > 0`, and take
`δ := ε · (4K + 1)⁻¹`, which is positive and satisfies `4Kδ < ε`. Feeding `δ` to
`located_bracket` on each factor and refining the results into the initial
brackets gives `Q ≤ Q'` and `R ≤ R'` inside `[-K, K]` with `Q' - Q < δ` and
`R' - R < δ`. `corner_close` then puts every corner within `2Kδ` of `Q·R`, so
all four lie in a window narrower than `ε`; four nested trichotomies on `p`
against the corners finish it, each `c ≤ p` branch exiting on the right. What
remains is that assembly, not a missing idea. -/

def mulLower (L₁ U₁ L₂ U₂ : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ q, q ∈ L₁ ∧ ∃ q', q' ∈ U₁ ∧ ∃ r, r ∈ L₂ ∧ ∃ r', r' ∈ U₂ ∧
        ratLt p (ratMul q r) ∧ ratLt p (ratMul q r') ∧
        ratLt p (ratMul q' r) ∧ ratLt p (ratMul q' r')) NumberTheory.Rat.{u}

def mulUpper (L₁ U₁ L₂ U₂ : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ q, q ∈ L₁ ∧ ∃ q', q' ∈ U₁ ∧ ∃ r, r ∈ L₂ ∧ ∃ r', r' ∈ U₂ ∧
        ratLt (ratMul q r) p ∧ ratLt (ratMul q r') p ∧
        ratLt (ratMul q' r) p ∧ ratLt (ratMul q' r') p) NumberTheory.Rat.{u}

theorem mem_mulLower_iff (L₁ U₁ L₂ U₂ p : ZFSet.{u}) :
    p ∈ mulLower L₁ U₁ L₂ U₂ ↔ p ∈ NumberTheory.Rat.{u} ∧
      ∃ q, q ∈ L₁ ∧ ∃ q', q' ∈ U₁ ∧ ∃ r, r ∈ L₂ ∧ ∃ r', r' ∈ U₂ ∧
        ratLt p (ratMul q r) ∧ ratLt p (ratMul q r') ∧
        ratLt p (ratMul q' r) ∧ ratLt p (ratMul q' r') :=
  mem_sep_iff _ _ _

theorem mem_mulUpper_iff (L₁ U₁ L₂ U₂ p : ZFSet.{u}) :
    p ∈ mulUpper L₁ U₁ L₂ U₂ ↔ p ∈ NumberTheory.Rat.{u} ∧
      ∃ q, q ∈ L₁ ∧ ∃ q', q' ∈ U₁ ∧ ∃ r, r ∈ L₂ ∧ ∃ r', r' ∈ U₂ ∧
        ratLt (ratMul q r) p ∧ ratLt (ratMul q r') p ∧
        ratLt (ratMul q' r) p ∧ ratLt (ratMul q' r') p :=
  mem_sep_iff _ _ _

/-- Two members of a lower set have a common one above both -- no `max` needed,
just the total order. -/
private theorem larger_mem {L a b : ZFSet.{u}} (ha : a ∈ L) (hb : b ∈ L)
    (haQ : a ∈ NumberTheory.Rat.{u}) (hbQ : b ∈ NumberTheory.Rat.{u}) :
    ∃ c, c ∈ L ∧ ratLe a c ∧ ratLe b c := by
  rcases ratLe_total haQ hbQ with h | h
  · exact ⟨b, hb, h, ratLe_refl hbQ⟩
  · exact ⟨a, ha, ratLe_refl haQ, h⟩

private theorem smaller_mem {U a b : ZFSet.{u}} (ha : a ∈ U) (hb : b ∈ U)
    (haQ : a ∈ NumberTheory.Rat.{u}) (hbQ : b ∈ NumberTheory.Rat.{u}) :
    ∃ c, c ∈ U ∧ ratLe c a ∧ ratLe c b := by
  rcases ratLe_total haQ hbQ with h | h
  · exact ⟨a, ha, ratLe_refl haQ, h⟩
  · exact ⟨b, hb, h, ratLe_refl hbQ⟩

/-- The product is a located pair, given locatedness of the product itself --
the one clause that needs an estimate rather than a case split. -/
theorem isLocated_mul_of_located {L₁ U₁ L₂ U₂ : ZFSet.{u}} (h₁ : IsLocated L₁ U₁)
    (h₂ : IsLocated L₂ U₂)
    (hloc : ∀ p, p ∈ NumberTheory.Rat.{u} → ∀ s, s ∈ NumberTheory.Rat.{u} → ratLt p s →
      p ∈ mulLower L₁ U₁ L₂ U₂ ∨ s ∈ mulUpper L₁ U₁ L₂ U₂) :
    IsLocated (mulLower L₁ U₁ L₂ U₂) (mulUpper L₁ U₁ L₂ U₂) where
  lower_subset p hp := ((mem_mulLower_iff _ _ _ _ p).mp hp).left
  upper_subset p hp := ((mem_mulUpper_iff _ _ _ _ p).mp hp).left
  lower_inhabited := by
    obtain ⟨q, hq⟩ := h₁.lower_inhabited
    obtain ⟨q', hq'⟩ := h₁.upper_inhabited
    obtain ⟨r, hr⟩ := h₂.lower_inhabited
    obtain ⟨r', hr'⟩ := h₂.upper_inhabited
    have hqQ := h₁.lower_subset q hq
    have hq'Q := h₁.upper_subset q' hq'
    have hrQ := h₂.lower_subset r hr
    have hr'Q := h₂.upper_subset r' hr'
    obtain ⟨t₁, ht₁Q, ha, hb⟩ :=
      exists_lt_two (ratMul_mem_Rat hqQ hrQ) (ratMul_mem_Rat hqQ hr'Q)
    obtain ⟨t₂, ht₂Q, hc, hd⟩ :=
      exists_lt_two (ratMul_mem_Rat hq'Q hrQ) (ratMul_mem_Rat hq'Q hr'Q)
    obtain ⟨t, htQ, he, hf⟩ := exists_lt_two ht₁Q ht₂Q
    exact ⟨t, (mem_mulLower_iff _ _ _ _ t).mpr ⟨htQ, q, hq, q', hq', r, hr, r', hr',
      ratLt_trans htQ ht₁Q (ratMul_mem_Rat hqQ hrQ) he ha,
      ratLt_trans htQ ht₁Q (ratMul_mem_Rat hqQ hr'Q) he hb,
      ratLt_trans htQ ht₂Q (ratMul_mem_Rat hq'Q hrQ) hf hc,
      ratLt_trans htQ ht₂Q (ratMul_mem_Rat hq'Q hr'Q) hf hd⟩⟩
  upper_inhabited := by
    obtain ⟨q, hq⟩ := h₁.lower_inhabited
    obtain ⟨q', hq'⟩ := h₁.upper_inhabited
    obtain ⟨r, hr⟩ := h₂.lower_inhabited
    obtain ⟨r', hr'⟩ := h₂.upper_inhabited
    have hqQ := h₁.lower_subset q hq
    have hq'Q := h₁.upper_subset q' hq'
    have hrQ := h₂.lower_subset r hr
    have hr'Q := h₂.upper_subset r' hr'
    obtain ⟨t₁, ht₁Q, ha, hb⟩ :=
      exists_gt_two (ratMul_mem_Rat hqQ hrQ) (ratMul_mem_Rat hqQ hr'Q)
    obtain ⟨t₂, ht₂Q, hc, hd⟩ :=
      exists_gt_two (ratMul_mem_Rat hq'Q hrQ) (ratMul_mem_Rat hq'Q hr'Q)
    obtain ⟨t, htQ, he, hf⟩ := exists_gt_two ht₁Q ht₂Q
    exact ⟨t, (mem_mulUpper_iff _ _ _ _ t).mpr ⟨htQ, q, hq, q', hq', r, hr, r', hr',
      ratLt_trans (ratMul_mem_Rat hqQ hrQ) ht₁Q htQ ha he,
      ratLt_trans (ratMul_mem_Rat hqQ hr'Q) ht₁Q htQ hb he,
      ratLt_trans (ratMul_mem_Rat hq'Q hrQ) ht₂Q htQ hc hf,
      ratLt_trans (ratMul_mem_Rat hq'Q hr'Q) ht₂Q htQ hd hf⟩⟩
  ordered p hp s hs := by
    obtain ⟨hpQ, q, hq, q', hq', r, hr, r', hr', c₁, c₂, c₃, c₄⟩ :=
      (mem_mulLower_iff _ _ _ _ p).mp hp
    obtain ⟨hsQ, t, ht, t', ht', u, hu, u', hu', d₁, d₂, d₃, d₄⟩ :=
      (mem_mulUpper_iff _ _ _ _ s).mp hs
    -- refine both boxes to a common one, then read off a corner on each side
    obtain ⟨Q, hQ, hqQ', htQ'⟩ := larger_mem hq ht (h₁.lower_subset q hq)
      (h₁.lower_subset t ht)
    obtain ⟨Q', hQ', hQ'q, hQ't⟩ := smaller_mem hq' ht' (h₁.upper_subset q' hq')
      (h₁.upper_subset t' ht')
    obtain ⟨R, hR, hrR, huR⟩ := larger_mem hr hu (h₂.lower_subset r hr)
      (h₂.lower_subset u hu)
    obtain ⟨R', hR'', hR'r, hR'u⟩ := smaller_mem hr' hu' (h₂.upper_subset r' hr')
      (h₂.upper_subset u' hu')
    have hQQ := h₁.lower_subset Q hQ
    have hRQ := h₂.lower_subset R hR
    have hQle : ratLe Q Q' := (h₁.ordered Q hQ Q' hQ').left
    have hRle : ratLe R R' := (h₂.ordered R hR R' hR'').left
    have hQq'' : ratLe Q q' := ratLe_trans hQQ (h₁.upper_subset Q' hQ')
      (h₁.upper_subset q' hq') hQle hQ'q
    have hQt'' : ratLe Q t' := ratLe_trans hQQ (h₁.upper_subset Q' hQ')
      (h₁.upper_subset t' ht') hQle hQ't
    have hRr'' : ratLe R r' := ratLe_trans hRQ (h₂.upper_subset R' hR'')
      (h₂.upper_subset r' hr') hRle hR'r
    have hRu'' : ratLe R u' := ratLe_trans hRQ (h₂.upper_subset R' hR'')
      (h₂.upper_subset u' hu') hRle hR'u
    have hprod := ratMul_mem_Rat hQQ hRQ
    -- `p` is below every corner of its own box, hence below `Q·R`
    have hpQR : ratLt p (ratMul Q R) := by
      rcases corner_le_mul (h₁.lower_subset q hq) (h₁.upper_subset q' hq')
        (h₂.lower_subset r hr) (h₂.upper_subset r' hr') hQQ hRQ hqQ' hQq'' hrR hRr''
        with h | h | h | h
      · exact ratLt_of_lt_of_le hpQ (ratMul_mem_Rat (h₁.lower_subset q hq)
          (h₂.lower_subset r hr)) hprod c₁ h
      · exact ratLt_of_lt_of_le hpQ (ratMul_mem_Rat (h₁.lower_subset q hq)
          (h₂.upper_subset r' hr')) hprod c₂ h
      · exact ratLt_of_lt_of_le hpQ (ratMul_mem_Rat (h₁.upper_subset q' hq')
          (h₂.lower_subset r hr)) hprod c₃ h
      · exact ratLt_of_lt_of_le hpQ (ratMul_mem_Rat (h₁.upper_subset q' hq')
          (h₂.upper_subset r' hr')) hprod c₄ h
    -- and `Q·R` is below every corner of the other box, hence below `s`
    rcases mul_le_corner (h₁.lower_subset t ht) (h₁.upper_subset t' ht')
      (h₂.lower_subset u hu) (h₂.upper_subset u' hu') hQQ hRQ htQ' hQt'' huR hRu''
      with h | h | h | h
    · exact ratLt_trans hpQ hprod hsQ hpQR (ratLt_of_le_of_lt hprod
        (ratMul_mem_Rat (h₁.lower_subset t ht) (h₂.lower_subset u hu)) hsQ h d₁)
    · exact ratLt_trans hpQ hprod hsQ hpQR (ratLt_of_le_of_lt hprod
        (ratMul_mem_Rat (h₁.lower_subset t ht) (h₂.upper_subset u' hu')) hsQ h d₂)
    · exact ratLt_trans hpQ hprod hsQ hpQR (ratLt_of_le_of_lt hprod
        (ratMul_mem_Rat (h₁.upper_subset t' ht') (h₂.lower_subset u hu)) hsQ h d₃)
    · exact ratLt_trans hpQ hprod hsQ hpQR (ratLt_of_le_of_lt hprod
        (ratMul_mem_Rat (h₁.upper_subset t' ht') (h₂.upper_subset u' hu')) hsQ h d₄)
  lower_down p hp p' hp'Q hlt := by
    obtain ⟨hpQ, q, hq, q', hq', r, hr, r', hr', c₁, c₂, c₃, c₄⟩ :=
      (mem_mulLower_iff _ _ _ _ p).mp hp
    have m₁ := ratMul_mem_Rat (h₁.lower_subset q hq) (h₂.lower_subset r hr)
    have m₂ := ratMul_mem_Rat (h₁.lower_subset q hq) (h₂.upper_subset r' hr')
    have m₃ := ratMul_mem_Rat (h₁.upper_subset q' hq') (h₂.lower_subset r hr)
    have m₄ := ratMul_mem_Rat (h₁.upper_subset q' hq') (h₂.upper_subset r' hr')
    exact (mem_mulLower_iff _ _ _ _ p').mpr ⟨hp'Q, q, hq, q', hq', r, hr, r', hr',
      ratLt_trans hp'Q hpQ m₁ hlt c₁, ratLt_trans hp'Q hpQ m₂ hlt c₂,
      ratLt_trans hp'Q hpQ m₃ hlt c₃, ratLt_trans hp'Q hpQ m₄ hlt c₄⟩
  upper_up p hp p' hp'Q hlt := by
    obtain ⟨hpQ, q, hq, q', hq', r, hr, r', hr', c₁, c₂, c₃, c₄⟩ :=
      (mem_mulUpper_iff _ _ _ _ p).mp hp
    have m₁ := ratMul_mem_Rat (h₁.lower_subset q hq) (h₂.lower_subset r hr)
    have m₂ := ratMul_mem_Rat (h₁.lower_subset q hq) (h₂.upper_subset r' hr')
    have m₃ := ratMul_mem_Rat (h₁.upper_subset q' hq') (h₂.lower_subset r hr)
    have m₄ := ratMul_mem_Rat (h₁.upper_subset q' hq') (h₂.upper_subset r' hr')
    exact (mem_mulUpper_iff _ _ _ _ p').mpr ⟨hp'Q, q, hq, q', hq', r, hr, r', hr',
      ratLt_trans m₁ hpQ hp'Q c₁ hlt, ratLt_trans m₂ hpQ hp'Q c₂ hlt,
      ratLt_trans m₃ hpQ hp'Q c₃ hlt, ratLt_trans m₄ hpQ hp'Q c₄ hlt⟩
  lower_open p hp := by
    obtain ⟨hpQ, q, hq, q', hq', r, hr, r', hr', c₁, c₂, c₃, c₄⟩ :=
      (mem_mulLower_iff _ _ _ _ p).mp hp
    have m₁ := ratMul_mem_Rat (h₁.lower_subset q hq) (h₂.lower_subset r hr)
    have m₂ := ratMul_mem_Rat (h₁.lower_subset q hq) (h₂.upper_subset r' hr')
    have m₃ := ratMul_mem_Rat (h₁.upper_subset q' hq') (h₂.lower_subset r hr)
    have m₄ := ratMul_mem_Rat (h₁.upper_subset q' hq') (h₂.upper_subset r' hr')
    obtain ⟨t₁, ht₁Q, hp1, ha, hb⟩ := exists_between_two hpQ m₁ m₂ c₁ c₂
    obtain ⟨t₂, ht₂Q, hp2, hc, hd⟩ := exists_between_two hpQ m₃ m₄ c₃ c₄
    obtain ⟨t, htQ, hpt, he, hf⟩ := exists_between_two hpQ ht₁Q ht₂Q hp1 hp2
    exact ⟨t, (mem_mulLower_iff _ _ _ _ t).mpr ⟨htQ, q, hq, q', hq', r, hr, r', hr',
      ratLt_trans htQ ht₁Q m₁ he ha, ratLt_trans htQ ht₁Q m₂ he hb,
      ratLt_trans htQ ht₂Q m₃ hf hc, ratLt_trans htQ ht₂Q m₄ hf hd⟩, hpt⟩
  upper_open p hp := by
    obtain ⟨hpQ, q, hq, q', hq', r, hr, r', hr', c₁, c₂, c₃, c₄⟩ :=
      (mem_mulUpper_iff _ _ _ _ p).mp hp
    have m₁ := ratMul_mem_Rat (h₁.lower_subset q hq) (h₂.lower_subset r hr)
    have m₂ := ratMul_mem_Rat (h₁.lower_subset q hq) (h₂.upper_subset r' hr')
    have m₃ := ratMul_mem_Rat (h₁.upper_subset q' hq') (h₂.lower_subset r hr)
    have m₄ := ratMul_mem_Rat (h₁.upper_subset q' hq') (h₂.upper_subset r' hr')
    obtain ⟨t₁, ht₁Q, hp1, ha, hb⟩ := exists_between_two' hpQ m₁ m₂ c₁ c₂
    obtain ⟨t₂, ht₂Q, hp2, hc, hd⟩ := exists_between_two' hpQ m₃ m₄ c₃ c₄
    obtain ⟨t, htQ, htp, he, hf⟩ := exists_between_two' hpQ ht₁Q ht₂Q hp1 hp2
    exact ⟨t, (mem_mulUpper_iff _ _ _ _ t).mpr ⟨htQ, q, hq, q', hq', r, hr, r', hr',
      ratLt_trans m₁ ht₁Q htQ ha he, ratLt_trans m₂ ht₁Q htQ hb he,
      ratLt_trans m₃ ht₂Q htQ hc hf, ratLt_trans m₄ ht₂Q htQ hd hf⟩, htp⟩
  located := hloc

/-- The heart of locatedness for a product, with the brackets and the bound
already chosen. Every corner sits within `W = K·D + K·D` of `Q·R`, so once
`W + W` is below `s - p`, comparing `p` with the corners in turn decides the
disjunction: the first corner that fails to exceed `p` puts all four below `s`. -/
private theorem mul_located_of_brackets {L₁ U₁ L₂ U₂ p s K D Q Q' R R' : ZFSet.{u}}
    (hQ : Q ∈ L₁) (hQ' : Q' ∈ U₁) (hR : R ∈ L₂) (hR' : R' ∈ U₂)
    (hQQ : Q ∈ NumberTheory.Rat.{u}) (hQ'Q : Q' ∈ NumberTheory.Rat.{u}) (hRQ : R ∈ NumberTheory.Rat.{u}) (hR'Q : R' ∈ NumberTheory.Rat.{u})
    (hpQ : p ∈ NumberTheory.Rat.{u}) (hsQ : s ∈ NumberTheory.Rat.{u}) (hKQ : K ∈ NumberTheory.Rat.{u}) (hDQ : D ∈ NumberTheory.Rat.{u})
    (hK0 : ratLe ratZero.{u} K) (hD0 : ratLt ratZero.{u} D)
    (hQlo : ratLe (ratNeg K) Q) (hQhi : ratLe Q K)
    (hQ'lo : ratLe (ratNeg K) Q') (hQ'hi : ratLe Q' K)
    (hRlo : ratLe (ratNeg K) R) (hRhi : ratLe R K)
    (hR'lo : ratLe (ratNeg K) R') (hR'hi : ratLe R' K)
    (hQle : ratLe Q Q') (hQw : ratLt Q' (ratAdd Q D))
    (hRle : ratLe R R') (hRw : ratLt R' (ratAdd R D))
    (hwin : ratLt (ratAdd (ratAdd (ratMul K D) (ratMul K D))
      (ratAdd (ratMul K D) (ratMul K D))) (ratAdd s (ratNeg p))) :
    p ∈ mulLower L₁ U₁ L₂ U₂ ∨ s ∈ mulUpper L₁ U₁ L₂ U₂ := by
  have hW := ratAdd_mem_Rat (ratMul_mem_Rat hKQ hDQ) (ratMul_mem_Rat hKQ hDQ)
  have hc := ratMul_mem_Rat hQQ hRQ
  obtain ⟨dq1, dq2, dq3, dq4⟩ := diff_bounds hQQ hQ'Q hDQ hQle hQw hD0
  obtain ⟨dr1, dr2, dr3, dr4⟩ := diff_bounds hRQ hR'Q hDQ hRle hRw hD0
  obtain ⟨sq1, sq2⟩ := diff_self_bounds hQQ hDQ hD0
  obtain ⟨sr1, sr2⟩ := diff_self_bounds hRQ hDQ hD0
  -- every corner is within `W` of `Q·R`, in both directions
  have u₁ := corner_close hQQ hQQ hRQ hRQ hKQ hDQ hQlo hQhi hRlo hRhi sr1 sr2 sq1 sq2 hK0
  have u₂ := corner_close hQQ hQQ hR'Q hRQ hKQ hDQ hQlo hQhi hRlo hRhi dr3 dr4 sq1 sq2 hK0
  have u₃ := corner_close hQ'Q hQQ hRQ hRQ hKQ hDQ hQ'lo hQ'hi hRlo hRhi sr1 sr2 dq3 dq4 hK0
  have u₄ := corner_close hQ'Q hQQ hR'Q hRQ hKQ hDQ hQ'lo hQ'hi hRlo hRhi dr3 dr4 dq3 dq4 hK0
  have d₁ := u₁
  have d₂ := corner_close hQQ hQQ hRQ hR'Q hKQ hDQ hQlo hQhi hR'lo hR'hi dr1 dr2 sq1 sq2 hK0
  have d₃ := corner_close hQQ hQ'Q hRQ hRQ hKQ hDQ hQlo hQhi hRlo hRhi sr1 sr2 dq1 dq2 hK0
  have d₄ := corner_close hQQ hQ'Q hRQ hR'Q hKQ hDQ hQlo hQhi hR'lo hR'hi dr1 dr2 dq1 dq2 hK0
  -- a corner at or below `p` puts all four below `s`
  have exitR : ∀ x, x ∈ NumberTheory.Rat.{u} → ratLe (ratMul Q R) (ratAdd x
      (ratAdd (ratMul K D) (ratMul K D))) → ratLe x p →
      s ∈ mulUpper L₁ U₁ L₂ U₂ := by
    intro x hxQ hcx hxp
    have hps : ratLt (ratAdd p (ratAdd (ratAdd (ratMul K D) (ratMul K D))
        (ratAdd (ratMul K D) (ratMul K D)))) s := by
      have hstep := (ratAdd_lt_add_left_iff hpQ (ratAdd_mem_Rat hW hW)
        (ratAdd_mem_Rat hsQ (ratNeg_mem_Rat hpQ))).mpr hwin
      rwa [ratAdd_sub_cancel hsQ hpQ] at hstep
    have hstep : ∀ y, y ∈ NumberTheory.Rat.{u} → ratLe y (ratAdd (ratMul Q R)
        (ratAdd (ratMul K D) (ratMul K D))) → ratLt y s := by
      intro y hyQ hy
      have h1 : ratLe (ratAdd (ratMul Q R) (ratAdd (ratMul K D) (ratMul K D)))
          (ratAdd (ratAdd x (ratAdd (ratMul K D) (ratMul K D)))
            (ratAdd (ratMul K D) (ratMul K D))) :=
        (ratAdd_le_add_right_iff hW hc (ratAdd_mem_Rat hxQ hW)).mpr hcx
      have h3 : ratLe (ratAdd (ratAdd x (ratAdd (ratMul K D) (ratMul K D)))
          (ratAdd (ratMul K D) (ratMul K D)))
          (ratAdd p (ratAdd (ratAdd (ratMul K D) (ratMul K D))
            (ratAdd (ratMul K D) (ratMul K D)))) := by
        rw [ratAdd_assoc hxQ hW hW]
        exact (ratAdd_le_add_right_iff (ratAdd_mem_Rat hW hW) hxQ hpQ).mpr hxp
      exact ratLt_of_le_of_lt hyQ (ratAdd_mem_Rat hpQ (ratAdd_mem_Rat hW hW)) hsQ
        (ratLe_trans hyQ (ratAdd_mem_Rat hc hW)
          (ratAdd_mem_Rat hpQ (ratAdd_mem_Rat hW hW)) hy
          (ratLe_trans (ratAdd_mem_Rat hc hW)
            (ratAdd_mem_Rat (ratAdd_mem_Rat hxQ hW) hW)
            (ratAdd_mem_Rat hpQ (ratAdd_mem_Rat hW hW)) h1 h3)) hps
    exact (mem_mulUpper_iff _ _ _ _ s).mpr ⟨hsQ, Q, hQ, Q', hQ', R, hR, R', hR',
      hstep _ hc u₁, hstep _ (ratMul_mem_Rat hQQ hR'Q) u₂,
      hstep _ (ratMul_mem_Rat hQ'Q hRQ) u₃, hstep _ (ratMul_mem_Rat hQ'Q hR'Q) u₄⟩
  -- compare `p` with each corner in turn
  rcases ratLt_trichotomy hpQ hc with c₁ | c₁ | c₁
  · rcases ratLt_trichotomy hpQ (ratMul_mem_Rat hQQ hR'Q) with c₂ | c₂ | c₂
    · rcases ratLt_trichotomy hpQ (ratMul_mem_Rat hQ'Q hRQ) with c₃ | c₃ | c₃
      · rcases ratLt_trichotomy hpQ (ratMul_mem_Rat hQ'Q hR'Q) with c₄ | c₄ | c₄
        · exact Or.inl ((mem_mulLower_iff _ _ _ _ p).mpr
            ⟨hpQ, Q, hQ, Q', hQ', R, hR, R', hR', c₁, c₂, c₃, c₄⟩)
        · exact Or.inr (exitR _ (ratMul_mem_Rat hQ'Q hR'Q) d₄
            (by rw [← c₄]; exact ratLe_refl hpQ))
        · exact Or.inr (exitR _ (ratMul_mem_Rat hQ'Q hR'Q) d₄ c₄.left)
      · exact Or.inr (exitR _ (ratMul_mem_Rat hQ'Q hRQ) d₃
          (by rw [← c₃]; exact ratLe_refl hpQ))
      · exact Or.inr (exitR _ (ratMul_mem_Rat hQ'Q hRQ) d₃ c₃.left)
    · exact Or.inr (exitR _ (ratMul_mem_Rat hQQ hR'Q) d₂
        (by rw [← c₂]; exact ratLe_refl hpQ))
    · exact Or.inr (exitR _ (ratMul_mem_Rat hQQ hR'Q) d₂ c₂.left)
  · exact Or.inr (exitR _ hc d₁ (by rw [← c₁]; exact ratLe_refl hpQ))
  · exact Or.inr (exitR _ hc d₁ c₁.left)

/-- Locatedness of the product: the clause `isLocated_mul_of_located` takes as a
hypothesis, now discharged. Bound the initial brackets by `K`, choose `D` small
enough that `4KD` is still below `s - p`, bracket both factors within `D`, and
`mul_located_of_brackets` finishes. -/
theorem mul_located {L₁ U₁ L₂ U₂ : ZFSet.{u}} (h₁ : IsLocated L₁ U₁)
    (h₂ : IsLocated L₂ U₂) (p : ZFSet.{u}) (hpQ : p ∈ NumberTheory.Rat.{u}) (s : ZFSet.{u})
    (hsQ : s ∈ NumberTheory.Rat.{u}) (hps : ratLt p s) :
    p ∈ mulLower L₁ U₁ L₂ U₂ ∨ s ∈ mulUpper L₁ U₁ L₂ U₂ := by
  have hnp := ratNeg_mem_Rat hpQ
  have hεQ := ratAdd_mem_Rat hsQ hnp
  have hε : ratLt ratZero.{u} (ratAdd s (ratNeg p)) := by
    have hstep := (ratAdd_lt_add_right_iff hnp hpQ hsQ).mpr hps
    rwa [ratAdd_neg hpQ] at hstep
  -- a bound `K > 0` on the initial brackets
  obtain ⟨q₀, hq₀⟩ := h₁.lower_inhabited
  obtain ⟨q₀', hq₀'⟩ := h₁.upper_inhabited
  obtain ⟨r₀, hr₀⟩ := h₂.lower_inhabited
  obtain ⟨r₀', hr₀'⟩ := h₂.upper_inhabited
  have hq₀Q := h₁.lower_subset _ hq₀
  have hq₀'Q := h₁.upper_subset _ hq₀'
  have hr₀Q := h₂.lower_subset _ hr₀
  have hr₀'Q := h₂.upper_subset _ hr₀'
  obtain ⟨k₁, hk₁Q, hk₁a, hk₁b⟩ := exists_gt_two hq₀'Q hr₀'Q
  obtain ⟨k₂, hk₂Q, hk₂a, hk₂b⟩ :=
    exists_gt_two (ratNeg_mem_Rat hq₀Q) (ratNeg_mem_Rat hr₀Q)
  obtain ⟨k₃, hk₃Q, hk₃a, hk₃b⟩ := exists_gt_two hk₁Q hk₂Q
  obtain ⟨K, hKQ, hKa, hKb⟩ := exists_gt_two hk₃Q ratZero_mem_Rat
  have hK0 : ratLe ratZero.{u} K := hKb.left
  have hk₁K : ratLt k₁ K := ratLt_trans hk₁Q hk₃Q hKQ hk₃a hKa
  have hk₂K : ratLt k₂ K := ratLt_trans hk₂Q hk₃Q hKQ hk₃b hKa
  have hq₀'K : ratLe q₀' K := (ratLt_trans hq₀'Q hk₁Q hKQ hk₁a hk₁K).left
  have hr₀'K : ratLe r₀' K := (ratLt_trans hr₀'Q hk₁Q hKQ hk₁b hk₁K).left
  have hnegK : ∀ x : ZFSet.{u}, x ∈ NumberTheory.Rat.{u} → ratLe (ratNeg x) K →
      ratLe (ratNeg K) x := by
    intro x hxQ hx
    have hstep := (ratNeg_le_neg_iff hKQ (ratNeg_mem_Rat hxQ)).mpr hx
    rwa [ratNeg_ratNeg hxQ] at hstep
  have hKq₀ : ratLe (ratNeg K) q₀ :=
    hnegK q₀ hq₀Q (ratLt_trans (ratNeg_mem_Rat hq₀Q) hk₂Q hKQ hk₂a hk₂K).left
  have hKr₀ : ratLe (ratNeg K) r₀ :=
    hnegK r₀ hr₀Q (ratLt_trans (ratNeg_mem_Rat hr₀Q) hk₂Q hKQ hk₂b hk₂K).left
  -- a width `D` with `4KD < s - p`
  obtain ⟨D, hDQ, hD0, hwin⟩ : ∃ D, D ∈ NumberTheory.Rat.{u} ∧ ratLt ratZero.{u} D ∧
      ratLt (ratAdd (ratAdd (ratMul K D) (ratMul K D))
        (ratAdd (ratMul K D) (ratMul K D))) (ratAdd s (ratNeg p)) := by
    have hSQ := ratAdd_mem_Rat (ratAdd_mem_Rat hKQ hKQ) (ratAdd_mem_Rat hKQ hKQ)
    have hMQ := ratAdd_mem_Rat hSQ ratOne_mem_Rat
    have hS0 : ratLe ratZero.{u} (ratAdd (ratAdd K K) (ratAdd K K)) := by
      have h₀ : ratLe ratZero.{u} (ratAdd K K) := by
        have hstep := (ratAdd_le_add_left_iff hKQ ratZero_mem_Rat hKQ).mpr hK0
        rw [ratAdd_zero hKQ] at hstep
        exact ratLe_trans ratZero_mem_Rat hKQ (ratAdd_mem_Rat hKQ hKQ) hK0 hstep
      have hstep := (ratAdd_le_add_left_iff (ratAdd_mem_Rat hKQ hKQ) ratZero_mem_Rat
        (ratAdd_mem_Rat hKQ hKQ)).mpr h₀
      rw [ratAdd_zero (ratAdd_mem_Rat hKQ hKQ)] at hstep
      exact ratLe_trans ratZero_mem_Rat (ratAdd_mem_Rat hKQ hKQ) hSQ h₀ hstep
    have hSM : ratLt (ratAdd (ratAdd K K) (ratAdd K K))
        (ratAdd (ratAdd (ratAdd K K) (ratAdd K K)) ratOne.{u}) := by
      have hstep := (ratAdd_lt_add_left_iff hSQ ratZero_mem_Rat ratOne_mem_Rat).mpr
        ratZero_lt_one
      rwa [ratAdd_zero hSQ] at hstep
    have hM0 : ratLt ratZero.{u} (ratAdd (ratAdd (ratAdd K K) (ratAdd K K)) ratOne.{u}) :=
      ratLt_of_le_of_lt ratZero_mem_Rat hSQ hMQ hS0 hSM
    have hMne : ratAdd (ratAdd (ratAdd K K) (ratAdd K K)) ratOne.{u} ≠ ratZero.{u} :=
      fun he => hM0.right he.symm
    have hinvQ := ratInv_mem_Rat hMQ hMne
    have hinv0 := ratInv_pos hMQ hM0
    have hinvne := fun he => hinv0.right (Eq.symm he)
    refine ⟨ratMul (ratAdd s (ratNeg p)) (ratInv
      (ratAdd (ratAdd (ratAdd K K) (ratAdd K K)) ratOne.{u})),
      ratMul_mem_Rat hεQ hinvQ, ?_, ?_⟩
    · have hstep := ratMul_lt_mul_right ratZero_mem_Rat hεQ hinvQ hinvne hinv0.left hε
      rwa [ratZero_mul hinvQ] at hstep
    · -- the window is `S · D`, and `S · D < ε` because `S < M`
      have hone : ratLt (ratMul (ratAdd (ratAdd K K) (ratAdd K K)) (ratInv
          (ratAdd (ratAdd (ratAdd K K) (ratAdd K K)) ratOne.{u}))) ratOne.{u} := by
        have hstep := ratMul_lt_mul_right hSQ hMQ hinvQ hinvne hinv0.left hSM
        rwa [ratMul_inv hMQ hMne] at hstep
      have htwo := ratMul_lt_mul_right (ratMul_mem_Rat hSQ hinvQ) ratOne_mem_Rat hεQ
        (fun he => hε.right he.symm) hε.left hone
      rw [ratOne_mul hεQ] at htwo
      have hthree : ratMul (ratAdd (ratAdd K K) (ratAdd K K))
          (ratMul (ratAdd s (ratNeg p)) (ratInv
            (ratAdd (ratAdd (ratAdd K K) (ratAdd K K)) ratOne.{u})))
          = ratMul (ratMul (ratAdd (ratAdd K K) (ratAdd K K)) (ratInv
            (ratAdd (ratAdd (ratAdd K K) (ratAdd K K)) ratOne.{u}))) (ratAdd s (ratNeg p)) := by
        rw [ratMul_comm hεQ hinvQ, ← ratMul_assoc hSQ hinvQ hεQ]
      rw [ratAdd_mul (ratAdd_mem_Rat hKQ hKQ) (ratAdd_mem_Rat hKQ hKQ)
        (ratMul_mem_Rat hεQ hinvQ), ratAdd_mul hKQ hKQ (ratMul_mem_Rat hεQ hinvQ)]
        at hthree
      rw [hthree]
      exact htwo
  -- brackets of width `D`, refined into the initial ones
  obtain ⟨qa, hqa, qb, hqb, hqlt⟩ := located_bracket h₁ hDQ hD0
  obtain ⟨ra, hra, rb, hrb, hrlt⟩ := located_bracket h₂ hDQ hD0
  have hqaQ := h₁.lower_subset _ hqa
  have hqbQ := h₁.upper_subset _ hqb
  have hraQ := h₂.lower_subset _ hra
  have hrbQ := h₂.upper_subset _ hrb
  obtain ⟨Q, hQ, hqaQ', hq₀Q'⟩ := larger_mem hqa hq₀ hqaQ hq₀Q
  obtain ⟨Q', hQ', hQ'qb, hQ'q₀'⟩ := smaller_mem hqb hq₀' hqbQ hq₀'Q
  obtain ⟨R, hR, hraR, hr₀R⟩ := larger_mem hra hr₀ hraQ hr₀Q
  obtain ⟨R', hR', hR'rb, hR'r₀'⟩ := smaller_mem hrb hr₀' hrbQ hr₀'Q
  have hQQ := h₁.lower_subset _ hQ
  have hQ'Q := h₁.upper_subset _ hQ'
  have hRQ := h₂.lower_subset _ hR
  have hR'Q := h₂.upper_subset _ hR'
  have hQle : ratLe Q Q' := (h₁.ordered _ hQ _ hQ').left
  have hRle : ratLe R R' := (h₂.ordered _ hR _ hR').left
  have hQw : ratLt Q' (ratAdd Q D) :=
    ratLt_of_le_of_lt hQ'Q hqbQ (ratAdd_mem_Rat hQQ hDQ) hQ'qb
      (ratLt_of_lt_of_le hqbQ (ratAdd_mem_Rat hqaQ hDQ) (ratAdd_mem_Rat hQQ hDQ)
        hqlt ((ratAdd_le_add_right_iff hDQ hqaQ hQQ).mpr hqaQ'))
  have hRw : ratLt R' (ratAdd R D) :=
    ratLt_of_le_of_lt hR'Q hrbQ (ratAdd_mem_Rat hRQ hDQ) hR'rb
      (ratLt_of_lt_of_le hrbQ (ratAdd_mem_Rat hraQ hDQ) (ratAdd_mem_Rat hRQ hDQ)
        hrlt ((ratAdd_le_add_right_iff hDQ hraQ hRQ).mpr hraR))
  have hQhi : ratLe Q K := ratLe_trans hQQ hQ'Q hKQ hQle
    (ratLe_trans hQ'Q hq₀'Q hKQ hQ'q₀' hq₀'K)
  have hRhi : ratLe R K := ratLe_trans hRQ hR'Q hKQ hRle
    (ratLe_trans hR'Q hr₀'Q hKQ hR'r₀' hr₀'K)
  have hQlo : ratLe (ratNeg K) Q :=
    ratLe_trans (ratNeg_mem_Rat hKQ) hq₀Q hQQ hKq₀ hq₀Q'
  have hRlo : ratLe (ratNeg K) R :=
    ratLe_trans (ratNeg_mem_Rat hKQ) hr₀Q hRQ hKr₀ hr₀R
  exact mul_located_of_brackets hQ hQ' hR hR' hQQ hQ'Q hRQ hR'Q hpQ hsQ hKQ hDQ hK0 hD0
    hQlo hQhi (ratLe_trans (ratNeg_mem_Rat hKQ) hQQ hQ'Q hQlo hQle)
    (ratLe_trans hQ'Q hq₀'Q hKQ hQ'q₀' hq₀'K) hRlo hRhi
    (ratLe_trans (ratNeg_mem_Rat hKQ) hRQ hR'Q hRlo hRle)
    (ratLe_trans hR'Q hr₀'Q hKQ hR'r₀' hr₀'K) hQle hQw hRle hRw hwin

/-- The product of two located pairs is a located pair. No sign split anywhere:
the definition is the four corners, and the estimate replaces the case analysis
that `realMul` needs. -/
theorem isLocated_mul {L₁ U₁ L₂ U₂ : ZFSet.{u}} (h₁ : IsLocated L₁ U₁)
    (h₂ : IsLocated L₂ U₂) :
    IsLocated (mulLower L₁ U₁ L₂ U₂) (mulUpper L₁ U₁ L₂ U₂) :=
  isLocated_mul_of_located h₁ h₂ (fun p hp s hs hps => mul_located h₁ h₂ p hp s hs hps)

/-! ## The operations, at the level of the reals -/

def realLAdd (z w : ZFSet.{u}) : ZFSet.{u} :=
  opair (addLower (fst z) (fst w)) (addUpper (snd z) (snd w))

def realLNeg (z : ZFSet.{u}) : ZFSet.{u} :=
  opair (negLower (snd z)) (negUpper (fst z))

def realLMul (z w : ZFSet.{u}) : ZFSet.{u} :=
  opair (mulLower (fst z) (snd z) (fst w) (snd w))
    (mulUpper (fst z) (snd z) (fst w) (snd w))

theorem realLAdd_mem {z w : ZFSet.{u}} (hz : z ∈ RealL.{u}) (hw : w ∈ RealL.{u}) :
    realLAdd z w ∈ RealL.{u} := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff z).mp hz
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff w).mp hw
  refine (mem_RealL_iff _).mpr ⟨addLower L₁ L₂, addUpper U₁ U₂, ?_, ?_⟩
  · rw [realLAdd, fst_opair, fst_opair, snd_opair, snd_opair]
  · exact isLocated_add h₁ h₂

theorem realLNeg_mem {z : ZFSet.{u}} (hz : z ∈ RealL.{u}) :
    realLNeg z ∈ RealL.{u} := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff z).mp hz
  refine (mem_RealL_iff _).mpr ⟨negLower U₁, negUpper L₁, ?_, ?_⟩
  · rw [realLNeg, fst_opair, snd_opair]
  · exact isLocated_neg h₁

theorem realLMul_mem {z w : ZFSet.{u}} (hz : z ∈ RealL.{u}) (hw : w ∈ RealL.{u}) :
    realLMul z w ∈ RealL.{u} := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff z).mp hz
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff w).mp hw
  refine (mem_RealL_iff _).mpr ⟨mulLower L₁ U₁ L₂ U₂, mulUpper L₁ U₁ L₂ U₂, ?_, ?_⟩
  · rw [realLMul, fst_opair, fst_opair, snd_opair, snd_opair]
  · exact isLocated_mul h₁ h₂

/-- A rational, as a located real. -/
def realLOf (q : ZFSet.{u}) : ZFSet.{u} :=
  opair (ratCut q) (sep (fun p => ratLt q p) NumberTheory.Rat.{u})

def realLZero : ZFSet.{u} := realLOf ratZero.{u}

def realLOne : ZFSet.{u} := realLOf ratOne.{u}

theorem realLOf_mem {q : ZFSet.{u}} (hq : q ∈ NumberTheory.Rat.{u}) : realLOf q ∈ RealL.{u} :=
  (mem_RealL_iff _).mpr ⟨_, _, rfl, isLocated_ratCut hq⟩

/-- The scale `1/(n+1)`, as a real. -/
def invScale (n : Nat) : ZFSet.{u} := realLOf (invWidth (ofNat.{u} n))

theorem invScale_mem (n : Nat) : invScale.{u} n ∈ RealL.{u} :=
  realLOf_mem (invWidth_mem_Rat (ofNat_mem_omega n))


#print axioms invScale
#print axioms Analysis.IsLocated
#print axioms Analysis.RealL
#print axioms invScale_mem

theorem realLZero_mem : realLZero.{u} ∈ RealL.{u} := realLOf_mem ratZero_mem_Rat

theorem realLOne_mem : realLOne.{u} ∈ RealL.{u} := realLOf_mem ratOne_mem_Rat

/-! ## The additive laws

Nothing above proves an equation between located reals -- the file constructs
them and shows the constructions stay located. A ring structure needs the laws,
and they are set equalities between the halves. Commutativity and associativity
of `+` come from `ratAdd`'s, one existential at a time. -/

theorem addLower_comm {L₁ L₂ : ZFSet.{u}} (h₁ : ∀ q, q ∈ L₁ → q ∈ NumberTheory.Rat.{u})
    (h₂ : ∀ r, r ∈ L₂ → r ∈ NumberTheory.Rat.{u}) : addLower L₁ L₂ = addLower L₂ L₁ := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨hpQ, q, hq, r, hr, hlt⟩ := (mem_addLower_iff _ _ p).mp hp
    refine (mem_addLower_iff _ _ p).mpr ⟨hpQ, r, hr, q, hq, ?_⟩
    rw [ratAdd_comm (h₂ r hr) (h₁ q hq)]
    exact hlt
  · obtain ⟨hpQ, q, hq, r, hr, hlt⟩ := (mem_addLower_iff _ _ p).mp hp
    refine (mem_addLower_iff _ _ p).mpr ⟨hpQ, r, hr, q, hq, ?_⟩
    rw [ratAdd_comm (h₁ r hr) (h₂ q hq)]
    exact hlt

theorem addUpper_comm {U₁ U₂ : ZFSet.{u}} (h₁ : ∀ q, q ∈ U₁ → q ∈ NumberTheory.Rat.{u})
    (h₂ : ∀ r, r ∈ U₂ → r ∈ NumberTheory.Rat.{u}) : addUpper U₁ U₂ = addUpper U₂ U₁ := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨hpQ, q, hq, r, hr, hlt⟩ := (mem_addUpper_iff _ _ p).mp hp
    refine (mem_addUpper_iff _ _ p).mpr ⟨hpQ, r, hr, q, hq, ?_⟩
    rw [ratAdd_comm (h₂ r hr) (h₁ q hq)]
    exact hlt
  · obtain ⟨hpQ, q, hq, r, hr, hlt⟩ := (mem_addUpper_iff _ _ p).mp hp
    refine (mem_addUpper_iff _ _ p).mpr ⟨hpQ, r, hr, q, hq, ?_⟩
    rw [ratAdd_comm (h₁ r hr) (h₂ q hq)]
    exact hlt

theorem realLAdd_comm {z w : ZFSet.{u}} (hz : z ∈ RealL.{u}) (hw : w ∈ RealL.{u}) :
    realLAdd z w = realLAdd w z := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff z).mp hz
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff w).mp hw
  rw [realLAdd, realLAdd, fst_opair, fst_opair, snd_opair, snd_opair,
    addLower_comm h₁.lower_subset h₂.lower_subset,
    addUpper_comm h₁.upper_subset h₂.upper_subset]

/-! ## Associativity

The witness for the inner sum is not `b + r` -- that is a bound, not a member of
the cut -- but a rational strictly between `p - a` and it, which density
supplies. Both directions run the same way with the grouping swapped. -/

private theorem addLower_assoc_le {L₁ L₂ L₃ : ZFSet.{u}}
    (h₁ : ∀ q, q ∈ L₁ → q ∈ NumberTheory.Rat.{u}) (h₂ : ∀ q, q ∈ L₂ → q ∈ NumberTheory.Rat.{u})
    (h₃ : ∀ q, q ∈ L₃ → q ∈ NumberTheory.Rat.{u}) {p : ZFSet.{u}}
    (hp : p ∈ addLower (addLower L₁ L₂) L₃) : p ∈ addLower L₁ (addLower L₂ L₃) := by
  obtain ⟨hpQ, q, hq, r, hr, hlt⟩ := (mem_addLower_iff _ _ p).mp hp
  obtain ⟨hqQ, a, ha, b, hb, hqab⟩ := (mem_addLower_iff _ _ q).mp hq
  have haQ := h₁ a ha
  have hbQ := h₂ b hb
  have hrQ := h₃ r hr
  have hbr := ratAdd_mem_Rat hbQ hrQ
  -- `p < q + r < (a+b) + r = a + (b+r)`
  have habr : ratLt p (ratAdd a (ratAdd b r)) := by
    rw [← ratAdd_assoc haQ hbQ hrQ]
    exact ratLt_trans hpQ (ratAdd_mem_Rat hqQ hrQ) (ratAdd_mem_Rat (ratAdd_mem_Rat haQ hbQ) hrQ)
      hlt ((ratAdd_lt_add_right_iff hrQ hqQ (ratAdd_mem_Rat haQ hbQ)).mpr hqab)
  -- so `p - a < b + r`, and density gives a member of the inner cut above it
  have hsub : ratLt (ratAdd p (ratNeg a)) (ratAdd b r) := by
    refine (ratAdd_lt_add_left_iff haQ (ratAdd_mem_Rat hpQ (ratNeg_mem_Rat haQ)) hbr).mp ?_
    rw [ratAdd_sub_cancel hpQ haQ]
    exact habr
  obtain ⟨s, hsQ, hps, hsbr⟩ := rat_dense (ratAdd_mem_Rat hpQ (ratNeg_mem_Rat haQ)) hbr hsub
  refine (mem_addLower_iff _ _ p).mpr ⟨hpQ, a, ha, s,
    (mem_addLower_iff _ _ s).mpr ⟨hsQ, b, hb, r, hr, hsbr⟩, ?_⟩
  have := (ratAdd_lt_add_left_iff haQ (ratAdd_mem_Rat hpQ (ratNeg_mem_Rat haQ)) hsQ).mpr hps
  rwa [ratAdd_sub_cancel hpQ haQ] at this

theorem addLower_assoc {L₁ L₂ L₃ : ZFSet.{u}} (h₁ : ∀ q, q ∈ L₁ → q ∈ NumberTheory.Rat.{u})
    (h₂ : ∀ q, q ∈ L₂ → q ∈ NumberTheory.Rat.{u}) (h₃ : ∀ q, q ∈ L₃ → q ∈ NumberTheory.Rat.{u}) :
    addLower (addLower L₁ L₂) L₃ = addLower L₁ (addLower L₂ L₃) := by
  have hin : ∀ A B : ZFSet.{u}, ∀ w, w ∈ addLower A B → w ∈ NumberTheory.Rat.{u} :=
    fun A B w hw => ((mem_addLower_iff A B w).mp hw).left
  refine ext _ _ fun p => ⟨fun hp => addLower_assoc_le h₁ h₂ h₃ hp, fun hp => ?_⟩
  -- the same lemma, with every pair commuted
  rw [addLower_comm h₁ (hin L₂ L₃), addLower_comm h₂ h₃] at hp
  have hstep := addLower_assoc_le h₃ h₂ h₁ hp
  rw [addLower_comm h₃ (hin L₂ L₁), addLower_comm h₂ h₁] at hstep
  exact hstep

private theorem addUpper_assoc_le {U₁ U₂ U₃ : ZFSet.{u}}
    (h₁ : ∀ q, q ∈ U₁ → q ∈ NumberTheory.Rat.{u}) (h₂ : ∀ q, q ∈ U₂ → q ∈ NumberTheory.Rat.{u})
    (h₃ : ∀ q, q ∈ U₃ → q ∈ NumberTheory.Rat.{u}) {p : ZFSet.{u}}
    (hp : p ∈ addUpper (addUpper U₁ U₂) U₃) : p ∈ addUpper U₁ (addUpper U₂ U₃) := by
  obtain ⟨hpQ, q, hq, r, hr, hlt⟩ := (mem_addUpper_iff _ _ p).mp hp
  obtain ⟨hqQ, a, ha, b, hb, hqab⟩ := (mem_addUpper_iff _ _ q).mp hq
  have haQ := h₁ a ha
  have hbQ := h₂ b hb
  have hrQ := h₃ r hr
  have hbr := ratAdd_mem_Rat hbQ hrQ
  have habr : ratLt (ratAdd a (ratAdd b r)) p := by
    rw [← ratAdd_assoc haQ hbQ hrQ]
    exact ratLt_trans (ratAdd_mem_Rat (ratAdd_mem_Rat haQ hbQ) hrQ) (ratAdd_mem_Rat hqQ hrQ)
      hpQ ((ratAdd_lt_add_right_iff hrQ (ratAdd_mem_Rat haQ hbQ) hqQ).mpr hqab) hlt
  have hsub : ratLt (ratAdd b r) (ratAdd p (ratNeg a)) := by
    refine (ratAdd_lt_add_left_iff haQ hbr (ratAdd_mem_Rat hpQ (ratNeg_mem_Rat haQ))).mp ?_
    rw [ratAdd_sub_cancel hpQ haQ]
    exact habr
  obtain ⟨s, hsQ, hbrs, hsp⟩ := rat_dense hbr (ratAdd_mem_Rat hpQ (ratNeg_mem_Rat haQ)) hsub
  refine (mem_addUpper_iff _ _ p).mpr ⟨hpQ, a, ha, s,
    (mem_addUpper_iff _ _ s).mpr ⟨hsQ, b, hb, r, hr, hbrs⟩, ?_⟩
  have := (ratAdd_lt_add_left_iff haQ hsQ (ratAdd_mem_Rat hpQ (ratNeg_mem_Rat haQ))).mpr hsp
  rwa [ratAdd_sub_cancel hpQ haQ] at this

theorem addUpper_assoc {U₁ U₂ U₃ : ZFSet.{u}} (h₁ : ∀ q, q ∈ U₁ → q ∈ NumberTheory.Rat.{u})
    (h₂ : ∀ q, q ∈ U₂ → q ∈ NumberTheory.Rat.{u}) (h₃ : ∀ q, q ∈ U₃ → q ∈ NumberTheory.Rat.{u}) :
    addUpper (addUpper U₁ U₂) U₃ = addUpper U₁ (addUpper U₂ U₃) := by
  have hin : ∀ A B : ZFSet.{u}, ∀ w, w ∈ addUpper A B → w ∈ NumberTheory.Rat.{u} :=
    fun A B w hw => ((mem_addUpper_iff A B w).mp hw).left
  refine ext _ _ fun p => ⟨fun hp => addUpper_assoc_le h₁ h₂ h₃ hp, fun hp => ?_⟩
  rw [addUpper_comm h₁ (hin U₂ U₃), addUpper_comm h₂ h₃] at hp
  have hstep := addUpper_assoc_le h₃ h₂ h₁ hp
  rw [addUpper_comm h₃ (hin U₂ U₁), addUpper_comm h₂ h₁] at hstep
  exact hstep

/-- Addition of located reals is associative. -/
theorem realLAdd_assoc {x y z : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (hz : z ∈ RealL.{u}) :
    realLAdd (realLAdd x y) z = realLAdd x (realLAdd y z) := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff y).mp hy
  obtain ⟨L₃, U₃, rfl, h₃⟩ := (mem_RealL_iff z).mp hz
  rw [realLAdd, realLAdd, realLAdd, realLAdd, fst_opair, fst_opair, fst_opair,
    snd_opair, snd_opair, snd_opair, fst_opair, snd_opair, fst_opair, snd_opair,
    addLower_assoc h₁.lower_subset h₂.lower_subset h₃.lower_subset,
    addUpper_assoc h₁.upper_subset h₂.upper_subset h₃.upper_subset]

/-! ## Zero -/

theorem addLower_zero {L U : ZFSet.{u}} (h : IsLocated L U) :
    addLower L (ratCut ratZero.{u}) = L := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨hpQ, q, hq, r, hr, hlt⟩ := (mem_addLower_iff _ _ p).mp hp
    obtain ⟨hrQ, hr0⟩ := (mem_ratCut_iff _ r).mp hr
    have hqQ := h.lower_subset q hq
    -- `q + r < q + 0 = q`, so `p < q` and downward closure applies
    refine h.lower_down q hq p hpQ (ratLt_trans hpQ (ratAdd_mem_Rat hqQ hrQ) hqQ hlt ?_)
    have := (ratAdd_lt_add_left_iff hqQ hrQ ratZero_mem_Rat).mpr hr0
    rwa [ratAdd_zero hqQ] at this
  · obtain ⟨q, hq, hpq⟩ := h.lower_open p hp
    have hpQ := h.lower_subset p hp
    have hqQ := h.lower_subset q hq
    have hd := ratAdd_mem_Rat hpQ (ratNeg_mem_Rat hqQ)
    -- `p - q < 0`, and the witness must be strictly between the two
    have hneg : ratLt (ratAdd p (ratNeg q)) ratZero.{u} := by
      refine (ratAdd_lt_add_left_iff hqQ hd ratZero_mem_Rat).mp ?_
      rw [ratAdd_sub_cancel hpQ hqQ, ratAdd_zero hqQ]
      exact hpq
    obtain ⟨r, hrQ, hdr, hr0⟩ := rat_dense hd ratZero_mem_Rat hneg
    refine (mem_addLower_iff _ _ p).mpr ⟨hpQ, q, hq, r,
      (mem_ratCut_iff _ _).mpr ⟨hrQ, hr0⟩, ?_⟩
    have := (ratAdd_lt_add_left_iff hqQ hd hrQ).mpr hdr
    rwa [ratAdd_sub_cancel hpQ hqQ] at this

theorem addUpper_zero {L U : ZFSet.{u}} (h : IsLocated L U) :
    addUpper U (sep (fun p => ratLt ratZero.{u} p) NumberTheory.Rat.{u}) = U := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨hpQ, q, hq, r, hr, hlt⟩ := (mem_addUpper_iff _ _ p).mp hp
    obtain ⟨hrQ, hr0⟩ := (mem_sep_iff _ r _).mp hr
    have hqQ := h.upper_subset q hq
    refine h.upper_up q hq p hpQ (ratLt_trans hqQ (ratAdd_mem_Rat hqQ hrQ) hpQ ?_ hlt)
    have := (ratAdd_lt_add_left_iff hqQ ratZero_mem_Rat hrQ).mpr hr0
    rwa [ratAdd_zero hqQ] at this
  · obtain ⟨q, hq, hqp⟩ := h.upper_open p hp
    have hpQ := h.upper_subset p hp
    have hqQ := h.upper_subset q hq
    have hd := ratAdd_mem_Rat hpQ (ratNeg_mem_Rat hqQ)
    have hpos : ratLt ratZero.{u} (ratAdd p (ratNeg q)) := by
      refine (ratAdd_lt_add_left_iff hqQ ratZero_mem_Rat hd).mp ?_
      rw [ratAdd_sub_cancel hpQ hqQ, ratAdd_zero hqQ]
      exact hqp
    obtain ⟨r, hrQ, hr0, hrd⟩ := rat_dense ratZero_mem_Rat hd hpos
    refine (mem_addUpper_iff _ _ p).mpr ⟨hpQ, q, hq, r,
      (mem_sep_iff _ _ _).mpr ⟨hrQ, hr0⟩, ?_⟩
    have := (ratAdd_lt_add_left_iff hqQ hrQ hd).mpr hrd
    rwa [ratAdd_sub_cancel hpQ hqQ] at this

/-- Zero is the additive identity. -/
theorem realLAdd_zero {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    realLAdd x realLZero.{u} = x := by
  obtain ⟨L, U, rfl, h⟩ := (mem_RealL_iff x).mp hx
  rw [realLAdd, realLZero, realLOf, fst_opair, fst_opair, snd_opair, snd_opair,
    addLower_zero h, addUpper_zero h]

/-- Adding zero on the left, which the located reals have only on the right. -/
theorem realLZero_add {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    realLAdd realLZero.{u} x = x := by
  rw [realLAdd_comm realLZero_mem hx, realLAdd_zero hx]

/-! ## The additive inverse

`x + (-x) = 0`. The inclusion into the negatives is the ordering of the cut; the
reverse is `located_bracket` -- given `p < 0`, a bracket of width `-p` supplies
`q ∈ L` and `s ∈ U` close enough that `p < q - s`. This is the theorem the
located encoding exists for, now at the level of halves. -/

theorem addLower_neg {L U : ZFSet.{u}} (h : IsLocated L U) :
    addLower L (negLower U) = ratCut ratZero.{u} := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨hpQ, q, hq, r, hr, hlt⟩ := (mem_addLower_iff _ _ p).mp hp
    obtain ⟨hrQ, s, hs, hrs⟩ := (mem_negLower_iff _ r).mp hr
    have hqQ := h.lower_subset q hq
    have hsQ := h.upper_subset s hs
    have hns := ratNeg_mem_Rat hsQ
    refine (mem_ratCut_iff _ _).mpr ⟨hpQ, ?_⟩
    -- `p < q + r < q + (-s) < s + (-s) = 0`
    refine ratLt_trans hpQ (ratAdd_mem_Rat hqQ hrQ) ratZero_mem_Rat hlt ?_
    refine ratLt_trans (ratAdd_mem_Rat hqQ hrQ) (ratAdd_mem_Rat hqQ hns) ratZero_mem_Rat
      ((ratAdd_lt_add_left_iff hqQ hrQ hns).mpr hrs) ?_
    have := (ratAdd_lt_add_right_iff hns hqQ hsQ).mpr (h.ordered q hq s hs)
    rwa [ratAdd_neg hsQ] at this
  · obtain ⟨hpQ, hp0⟩ := (mem_ratCut_iff _ p).mp hp
    -- a bracket of width `-p`
    have hnp := ratNeg_mem_Rat hpQ
    have hnpos : ratLt ratZero.{u} (ratNeg p) := by
      have := (ratAdd_lt_add_right_iff hnp hpQ ratZero_mem_Rat).mpr hp0
      rwa [ratAdd_neg hpQ, ratZero_add hnp] at this
    obtain ⟨q, hq, s, hs, hqs⟩ := located_bracket h hnp hnpos
    have hqQ := h.lower_subset q hq
    have hsQ := h.upper_subset s hs
    -- `-s` needs a strictly smaller member of `U` beneath it, which openness gives
    obtain ⟨s', hs', hss'⟩ := h.upper_open s hs
    have hs'Q := h.upper_subset s' hs'
    refine (mem_addLower_iff _ _ p).mpr ⟨hpQ, q, hq, ratNeg s,
      (mem_negLower_iff _ _).mpr ⟨ratNeg_mem_Rat hsQ, s', hs',
        (ratNeg_lt_neg_iff hsQ hs'Q).mpr hss'⟩, ?_⟩
    -- `s < q + (-p)` rearranges to `p < q + (-s)`, both by cancelling on the right
    have hns := ratNeg_mem_Rat hsQ
    have h1 := (ratAdd_lt_add_right_iff hpQ hsQ (ratAdd_mem_Rat hqQ hnp)).mpr hqs
    rw [ratAdd_assoc hqQ hnp hpQ, ratAdd_comm hnp hpQ, ratAdd_neg hpQ,
      ratAdd_zero hqQ] at h1
    refine (ratAdd_lt_add_right_iff hsQ hpQ (ratAdd_mem_Rat hqQ hns)).mp ?_
    rw [ratAdd_assoc hqQ hns hsQ, ratAdd_comm hns hsQ, ratAdd_neg hsQ,
      ratAdd_zero hqQ, ratAdd_comm hpQ hsQ]
    exact h1

theorem addUpper_neg {L U : ZFSet.{u}} (h : IsLocated L U) :
    addUpper U (negUpper L) = sep (fun p => ratLt ratZero.{u} p) NumberTheory.Rat.{u} := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨hpQ, q, hq, r, hr, hlt⟩ := (mem_addUpper_iff _ _ p).mp hp
    obtain ⟨hrQ, a, ha, har⟩ := (mem_negUpper_iff _ r).mp hr
    have hqQ := h.upper_subset q hq
    have haQ := h.lower_subset a ha
    have hna := ratNeg_mem_Rat haQ
    refine (mem_sep_iff _ _ _).mpr ⟨hpQ, ?_⟩
    -- `0 = a + (-a) < q + (-a) < q + r < p`
    refine ratLt_trans ratZero_mem_Rat (ratAdd_mem_Rat hqQ hrQ) hpQ ?_ hlt
    refine ratLt_trans ratZero_mem_Rat (ratAdd_mem_Rat hqQ hna) (ratAdd_mem_Rat hqQ hrQ) ?_
      ((ratAdd_lt_add_left_iff hqQ hna hrQ).mpr har)
    have := (ratAdd_lt_add_right_iff hna haQ hqQ).mpr (h.ordered a ha q hq)
    rwa [ratAdd_neg haQ] at this
  · obtain ⟨hpQ, hp0⟩ := (mem_sep_iff _ p _).mp hp
    obtain ⟨q, hq, s, hs, hqs⟩ := located_bracket h hpQ hp0
    have hqQ := h.lower_subset q hq
    have hsQ := h.upper_subset s hs
    obtain ⟨q', hq', hqq'⟩ := h.lower_open q hq
    have hq'Q := h.lower_subset q' hq'
    have hnq := ratNeg_mem_Rat hqQ
    refine (mem_addUpper_iff _ _ p).mpr ⟨hpQ, s, hs, ratNeg q,
      (mem_negUpper_iff _ _).mpr ⟨hnq, q', hq',
        (ratNeg_lt_neg_iff hq'Q hqQ).mpr hqq'⟩, ?_⟩
    -- `s < q + p` rearranges to `s + (-q) < p`
    have h1 := (ratAdd_lt_add_right_iff hnq hsQ (ratAdd_mem_Rat hqQ hpQ)).mpr hqs
    rw [ratAdd_comm hqQ hpQ, ratAdd_assoc hpQ hqQ hnq, ratAdd_neg hqQ,
      ratAdd_zero hpQ] at h1
    exact h1

/-- `x + (-x) = 0`, choice-free. The theorem the located encoding exists
for, now between elements of `RealL`. -/
theorem realLAdd_neg {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    realLAdd x (realLNeg x) = realLZero.{u} := by
  obtain ⟨L, U, rfl, h⟩ := (mem_RealL_iff x).mp hx
  rw [realLAdd, realLNeg, realLZero, realLOf, fst_opair, snd_opair, fst_opair,
    snd_opair, addLower_neg h, addUpper_neg h]

/-! ## Multiplication is commutative

The four corners `q·r`, `q·r'`, `q'·r`, `q'·r'` permute when the factors swap --
the two mixed corners exchange -- so commutativity is `ratMul_comm` applied four
times with the middle pair reordered. -/

/-- The corner swap, shared by both halves. `cmp` is `ratLt` for the upper half
and its converse for the lower, which is the only difference between the two
proofs -- so it is a parameter rather than a second copy. -/
private theorem mulCorners_comm {cmp : ZFSet.{u} → ZFSet.{u} → Prop}
    {L₁ U₁ L₂ U₂ p : ZFSet.{u}} (hL₁ : ∀ q, q ∈ L₁ → q ∈ NumberTheory.Rat.{u})
    (hU₁ : ∀ q, q ∈ U₁ → q ∈ NumberTheory.Rat.{u}) (hL₂ : ∀ q, q ∈ L₂ → q ∈ NumberTheory.Rat.{u})
    (hU₂ : ∀ q, q ∈ U₂ → q ∈ NumberTheory.Rat.{u})
    (h : ∃ q, q ∈ L₁ ∧ ∃ q', q' ∈ U₁ ∧ ∃ r, r ∈ L₂ ∧ ∃ r', r' ∈ U₂ ∧
      cmp (ratMul q r) p ∧ cmp (ratMul q r') p ∧
        cmp (ratMul q' r) p ∧ cmp (ratMul q' r') p) :
    ∃ q, q ∈ L₂ ∧ ∃ q', q' ∈ U₂ ∧ ∃ r, r ∈ L₁ ∧ ∃ r', r' ∈ U₁ ∧
      cmp (ratMul q r) p ∧ cmp (ratMul q r') p ∧
        cmp (ratMul q' r) p ∧ cmp (ratMul q' r') p := by
  obtain ⟨q, hq, q', hq', r, hr, r', hr', h₁, h₂, h₃, h₄⟩ := h
  refine ⟨r, hr, r', hr', q, hq, q', hq', ?_, ?_, ?_, ?_⟩
  · rwa [ratMul_comm (hL₂ r hr) (hL₁ q hq)]
  · rwa [ratMul_comm (hL₂ r hr) (hU₁ q' hq')]
  · rwa [ratMul_comm (hU₂ r' hr') (hL₁ q hq)]
  · rwa [ratMul_comm (hU₂ r' hr') (hU₁ q' hq')]

theorem mulLower_comm {L₁ U₁ L₂ U₂ : ZFSet.{u}} (hL₁ : ∀ q, q ∈ L₁ → q ∈ NumberTheory.Rat.{u})
    (hU₁ : ∀ q, q ∈ U₁ → q ∈ NumberTheory.Rat.{u}) (hL₂ : ∀ q, q ∈ L₂ → q ∈ NumberTheory.Rat.{u})
    (hU₂ : ∀ q, q ∈ U₂ → q ∈ NumberTheory.Rat.{u}) :
    mulLower L₁ U₁ L₂ U₂ = mulLower L₂ U₂ L₁ U₁ := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩ <;>
    · obtain ⟨hpQ, hcorners⟩ := (mem_sep_iff _ p _).mp hp
      exact (mem_sep_iff _ p _).mpr ⟨hpQ,
        mulCorners_comm (cmp := fun a b => ratLt b a) ‹_› ‹_› ‹_› ‹_› hcorners⟩

theorem mulUpper_comm {L₁ U₁ L₂ U₂ : ZFSet.{u}} (hL₁ : ∀ q, q ∈ L₁ → q ∈ NumberTheory.Rat.{u})
    (hU₁ : ∀ q, q ∈ U₁ → q ∈ NumberTheory.Rat.{u}) (hL₂ : ∀ q, q ∈ L₂ → q ∈ NumberTheory.Rat.{u})
    (hU₂ : ∀ q, q ∈ U₂ → q ∈ NumberTheory.Rat.{u}) :
    mulUpper L₁ U₁ L₂ U₂ = mulUpper L₂ U₂ L₁ U₁ := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩ <;>
    · obtain ⟨hpQ, hcorners⟩ := (mem_sep_iff _ p _).mp hp
      exact (mem_sep_iff _ p _).mpr ⟨hpQ,
        mulCorners_comm (cmp := ratLt) ‹_› ‹_› ‹_› ‹_› hcorners⟩

/-- Multiplication of located reals is commutative. -/
theorem realLMul_comm {x y : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u}) :
    realLMul x y = realLMul y x := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff y).mp hy
  rw [realLMul, realLMul, fst_opair, fst_opair, snd_opair, snd_opair,
    mulLower_comm h₁.lower_subset h₁.upper_subset h₂.lower_subset h₂.upper_subset,
    mulUpper_comm h₁.lower_subset h₁.upper_subset h₂.lower_subset h₂.upper_subset]

/-! ## Common refinements

Two brackets around the same real need not be nested, and comparing corner
products across them is what associativity will ask for. They always have a
common refinement, because a cut is closed under taking the larger of two
members -- and which is larger is a question about rationals. -/

theorem lower_pair_bound {L U q s : ZFSet.{u}} (h : IsLocated L U) (hq : q ∈ L)
    (hs : s ∈ L) : ∃ t, t ∈ L ∧ ratLe q t ∧ ratLe s t := by
  rcases ratLe_total (h.lower_subset q hq) (h.lower_subset s hs) with hle | hle
  · exact ⟨s, hs, hle, ratLe_refl (h.lower_subset s hs)⟩
  · exact ⟨q, hq, ratLe_refl (h.lower_subset q hq), hle⟩

theorem upper_pair_bound {L U r s : ZFSet.{u}} (h : IsLocated L U) (hr : r ∈ U)
    (hs : s ∈ U) : ∃ t, t ∈ U ∧ ratLe t r ∧ ratLe t s := by
  rcases ratLe_total (h.upper_subset r hr) (h.upper_subset s hs) with hle | hle
  · exact ⟨r, hr, ratLe_refl (h.upper_subset r hr), hle⟩
  · exact ⟨s, hs, hle, ratLe_refl (h.upper_subset s hs)⟩

/-- A bracket tighter than a given one still puts `p` below every corner. This
is `ratLt_mul_of_corners` read as stability of membership under refinement. -/
theorem corners_of_refinement {L₁ U₁ L₂ U₂ p q q' r r' s s' t t' : ZFSet.{u}}
    (h₁ : IsLocated L₁ U₁) (h₂ : IsLocated L₂ U₂) (hpQ : p ∈ NumberTheory.Rat.{u})
    (hq : q ∈ L₁) (hq' : q' ∈ U₁) (hr : r ∈ L₂) (hr' : r' ∈ U₂)
    (hs : s ∈ L₁) (hs' : s' ∈ U₁) (ht : t ∈ L₂) (ht' : t' ∈ U₂)
    (hqs : ratLe q s) (hs'q' : ratLe s' q') (hrt : ratLe r t) (ht'r' : ratLe t' r')
    (c₁ : ratLt p (ratMul q r)) (c₂ : ratLt p (ratMul q r'))
    (c₃ : ratLt p (ratMul q' r)) (c₄ : ratLt p (ratMul q' r')) :
    ratLt p (ratMul s t) ∧ ratLt p (ratMul s t') ∧
      ratLt p (ratMul s' t) ∧ ratLt p (ratMul s' t') := by
  have hqQ := h₁.lower_subset q hq
  have hq'Q := h₁.upper_subset q' hq'
  have hrQ := h₂.lower_subset r hr
  have hr'Q := h₂.upper_subset r' hr'
  have hsQ := h₁.lower_subset s hs
  have hs'Q := h₁.upper_subset s' hs'
  have htQ := h₂.lower_subset t ht
  have ht'Q := h₂.upper_subset t' ht'
  have hsq' : ratLe s q' := ratLe_trans hsQ hs'Q hq'Q (h₁.ordered s hs s' hs').left hs'q'
  have hqs' : ratLe q s' := ratLe_trans hqQ hsQ hs'Q hqs (h₁.ordered s hs s' hs').left
  have htr' : ratLe t r' := ratLe_trans htQ ht'Q hr'Q (h₂.ordered t ht t' ht').left ht'r'
  have hrt' : ratLe r t' := ratLe_trans hrQ htQ ht'Q hrt (h₂.ordered t ht t' ht').left
  exact ⟨ratLt_mul_of_corners hpQ hqQ hq'Q hrQ hr'Q hsQ htQ hqs hsq' hrt htr' c₁ c₂ c₃ c₄,
    ratLt_mul_of_corners hpQ hqQ hq'Q hrQ hr'Q hsQ ht'Q hqs hsq' hrt' ht'r' c₁ c₂ c₃ c₄,
    ratLt_mul_of_corners hpQ hqQ hq'Q hrQ hr'Q hs'Q htQ hqs' hs'q' hrt htr' c₁ c₂ c₃ c₄,
    ratLt_mul_of_corners hpQ hqQ hq'Q hrQ hr'Q hs'Q ht'Q hqs' hs'q' hrt' ht'r' c₁ c₂ c₃ c₄⟩

theorem corners_of_refinement' {L₁ U₁ L₂ U₂ p q q' r r' s s' t t' : ZFSet.{u}}
    (h₁ : IsLocated L₁ U₁) (h₂ : IsLocated L₂ U₂) (hpQ : p ∈ NumberTheory.Rat.{u})
    (hq : q ∈ L₁) (hq' : q' ∈ U₁) (hr : r ∈ L₂) (hr' : r' ∈ U₂)
    (hs : s ∈ L₁) (hs' : s' ∈ U₁) (ht : t ∈ L₂) (ht' : t' ∈ U₂)
    (hqs : ratLe q s) (hs'q' : ratLe s' q') (hrt : ratLe r t) (ht'r' : ratLe t' r')
    (c₁ : ratLt (ratMul q r) p) (c₂ : ratLt (ratMul q r') p)
    (c₃ : ratLt (ratMul q' r) p) (c₄ : ratLt (ratMul q' r') p) :
    ratLt (ratMul s t) p ∧ ratLt (ratMul s t') p ∧
      ratLt (ratMul s' t) p ∧ ratLt (ratMul s' t') p := by
  have hqQ := h₁.lower_subset q hq
  have hq'Q := h₁.upper_subset q' hq'
  have hrQ := h₂.lower_subset r hr
  have hr'Q := h₂.upper_subset r' hr'
  have hsQ := h₁.lower_subset s hs
  have hs'Q := h₁.upper_subset s' hs'
  have htQ := h₂.lower_subset t ht
  have ht'Q := h₂.upper_subset t' ht'
  have hsq' : ratLe s q' := ratLe_trans hsQ hs'Q hq'Q (h₁.ordered s hs s' hs').left hs'q'
  have hqs' : ratLe q s' := ratLe_trans hqQ hsQ hs'Q hqs (h₁.ordered s hs s' hs').left
  have htr' : ratLe t r' := ratLe_trans htQ ht'Q hr'Q (h₂.ordered t ht t' ht').left ht'r'
  have hrt' : ratLe r t' := ratLe_trans hrQ htQ ht'Q hrt (h₂.ordered t ht t' ht').left
  exact ⟨ratMul_lt_of_corners hpQ hqQ hq'Q hrQ hr'Q hsQ htQ hqs hsq' hrt htr' c₁ c₂ c₃ c₄,
    ratMul_lt_of_corners hpQ hqQ hq'Q hrQ hr'Q hsQ ht'Q hqs hsq' hrt' ht'r' c₁ c₂ c₃ c₄,
    ratMul_lt_of_corners hpQ hqQ hq'Q hrQ hr'Q hs'Q htQ hqs' hs'q' hrt htr' c₁ c₂ c₃ c₄,
    ratMul_lt_of_corners hpQ hqQ hq'Q hrQ hr'Q hs'Q ht'Q hqs' hs'q' hrt' ht'r' c₁ c₂ c₃ c₄⟩

/-! ## Multiplying by a rational constant -/

theorem mulLower_const {L U c p : ZFSet.{u}} (h : IsLocated L U) (hc : c ∈ NumberTheory.Rat.{u})
    (hp : p ∈ mulLower L U (ratCut c) (sep (fun s => ratLt c s) NumberTheory.Rat.{u})) :
    p ∈ NumberTheory.Rat.{u} ∧ ∃ q, q ∈ L ∧ ratLt p (ratMul q c) := by
  obtain ⟨hpQ, q, hq, q', hq', r, hr, r', hr', c₁, c₂, c₃, c₄⟩ := (mem_sep_iff _ p _).mp hp
  obtain ⟨hrQ, hrc⟩ := (mem_ratCut_iff _ r).mp hr
  obtain ⟨hr'Q, hcr'⟩ := (mem_sep_iff _ r' _).mp hr'
  exact ⟨hpQ, q, hq, ratLt_mul_of_corners hpQ (h.lower_subset q hq) (h.upper_subset q' hq')
    hrQ hr'Q (h.lower_subset q hq) hc (ratLe_refl (h.lower_subset q hq))
    (h.ordered q hq q' hq').left hrc.left hcr'.left c₁ c₂ c₃ c₄⟩

theorem mulUpper_const {L U c p : ZFSet.{u}} (h : IsLocated L U) (hc : c ∈ NumberTheory.Rat.{u})
    (hp : p ∈ mulUpper L U (ratCut c) (sep (fun s => ratLt c s) NumberTheory.Rat.{u})) :
    p ∈ NumberTheory.Rat.{u} ∧ ∃ q', q' ∈ U ∧ ratLt (ratMul q' c) p := by
  obtain ⟨hpQ, q, hq, q', hq', r, hr, r', hr', c₁, c₂, c₃, c₄⟩ := (mem_sep_iff _ p _).mp hp
  obtain ⟨hrQ, hrc⟩ := (mem_ratCut_iff _ r).mp hr
  obtain ⟨hr'Q, hcr'⟩ := (mem_sep_iff _ r' _).mp hr'
  exact ⟨hpQ, q', hq', ratMul_lt_of_corners hpQ (h.lower_subset q hq) (h.upper_subset q' hq')
    hrQ hr'Q (h.upper_subset q' hq') hc (h.ordered q hq q' hq').left
    (ratLe_refl (h.upper_subset q' hq')) hrc.left hcr'.left c₁ c₂ c₃ c₄⟩

/-! ## The unit

`x · 1 = x`. The easy inclusion is the corner bound at `y := 1`. The other needs
a bracket around `1` serving all four corners, and only one scale on each side
has to be found: the bracket's ends satisfy `q ≤ w`, so a positive scale
carries a corner at `q` to the corner at `w` by monotonicity in the bound. Both
scales are therefore chosen for `q` alone. -/

theorem mulLower_one {L U : ZFSet.{u}} (h : IsLocated L U) :
    mulLower L U (ratCut ratOne.{u}) (sep (fun p => ratLt ratOne.{u} p) NumberTheory.Rat.{u}) = L := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨hpQ, q, hq, hlt⟩ := mulLower_const h ratOne_mem_Rat hp
    rw [ratMul_one (h.lower_subset q hq)] at hlt
    exact h.lower_down q hq p hpQ hlt
  · have hpQ := h.lower_subset p hp
    obtain ⟨q, hq, hpq⟩ := h.lower_open p hp
    obtain ⟨w, hw⟩ := h.upper_inhabited
    have hqQ := h.lower_subset q hq
    have hwQ := h.upper_subset w hw
    have hqw : ratLe q w := (h.ordered q hq w hw).left
    obtain ⟨r, hrQ, h0r, hr1, hqr⟩ := exists_scale_below hpQ hqQ hpq
    obtain ⟨s, hsQ, h1s, hqs⟩ := exists_scale_above hpQ hqQ hpq
    have h0s : ratLe ratZero.{u} s := (ratLt_trans ratZero_mem_Rat ratOne_mem_Rat hsQ
      ratZero_lt_one h1s).left
    -- `q ≤ w` and the scale is positive, so the `w` corners follow
    have hwr : ratLt p (ratMul w r) := by
      refine ratLt_of_lt_of_le hpQ (ratMul_mem_Rat hqQ hrQ) (ratMul_mem_Rat hwQ hrQ) hqr ?_
      have := ratMul_le_mul_right hqQ hwQ hrQ hqw h0r.left
      rwa [ratMul_comm hqQ hrQ, ratMul_comm hwQ hrQ, ratMul_comm hrQ hqQ,
        ratMul_comm hrQ hwQ] at this
    have hws : ratLt p (ratMul w s) := by
      refine ratLt_of_lt_of_le hpQ (ratMul_mem_Rat hqQ hsQ) (ratMul_mem_Rat hwQ hsQ) hqs ?_
      have := ratMul_le_mul_right hqQ hwQ hsQ hqw h0s
      rwa [ratMul_comm hqQ hsQ, ratMul_comm hwQ hsQ, ratMul_comm hsQ hqQ,
        ratMul_comm hsQ hwQ] at this
    exact (mem_sep_iff _ p _).mpr ⟨hpQ, q, hq, w, hw, r,
      (mem_ratCut_iff _ _).mpr ⟨hrQ, hr1⟩, s, (mem_sep_iff _ _ _).mpr ⟨hsQ, h1s⟩,
      hqr, hqs, hwr, hws⟩

theorem mulUpper_one {L U : ZFSet.{u}} (h : IsLocated L U) :
    mulUpper L U (ratCut ratOne.{u}) (sep (fun p => ratLt ratOne.{u} p) NumberTheory.Rat.{u}) = U := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨hpQ, q', hq', hlt⟩ := mulUpper_const h ratOne_mem_Rat hp
    rw [ratMul_one (h.upper_subset q' hq')] at hlt
    exact h.upper_up q' hq' p hpQ hlt
  · have hpQ := h.upper_subset p hp
    obtain ⟨w, hw, hwp⟩ := h.upper_open p hp
    obtain ⟨q, hq⟩ := h.lower_inhabited
    have hwQ := h.upper_subset w hw
    have hqQ := h.lower_subset q hq
    have hqw : ratLe q w := (h.ordered q hq w hw).left
    have hqp : ratLt q p := ratLt_trans hqQ hwQ hpQ (h.ordered q hq w hw) hwp
    -- scales chosen for `w`, the upper end; `q ≤ w` carries them to the other corner
    obtain ⟨r, hrQ, h0r, hr1, hwr⟩ := exists_scale_below_upper hpQ hwQ hwp
    obtain ⟨s, hsQ, h1s, hws⟩ := exists_scale_above_upper hpQ hwQ hwp
    have h0s : ratLe ratZero.{u} s := (ratLt_trans ratZero_mem_Rat ratOne_mem_Rat hsQ
      ratZero_lt_one h1s).left
    have hqr : ratLt (ratMul q r) p := by
      refine ratLt_of_le_of_lt (ratMul_mem_Rat hqQ hrQ) (ratMul_mem_Rat hwQ hrQ) hpQ ?_ hwr
      have := ratMul_le_mul_right hqQ hwQ hrQ hqw h0r.left
      rwa [ratMul_comm hqQ hrQ, ratMul_comm hwQ hrQ, ratMul_comm hrQ hqQ,
        ratMul_comm hrQ hwQ] at this
    have hqs : ratLt (ratMul q s) p := by
      refine ratLt_of_le_of_lt (ratMul_mem_Rat hqQ hsQ) (ratMul_mem_Rat hwQ hsQ) hpQ ?_ hws
      have := ratMul_le_mul_right hqQ hwQ hsQ hqw h0s
      rwa [ratMul_comm hqQ hsQ, ratMul_comm hwQ hsQ, ratMul_comm hsQ hqQ,
        ratMul_comm hsQ hwQ] at this
    exact (mem_sep_iff _ p _).mpr ⟨hpQ, q, hq, w, hw, r,
      (mem_ratCut_iff _ _).mpr ⟨hrQ, hr1⟩, s, (mem_sep_iff _ _ _).mpr ⟨hsQ, h1s⟩,
      hqr, hqs, hwr, hws⟩

/-- One is the multiplicative identity. -/
theorem realLMul_one {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    realLMul x realLOne.{u} = x := by
  obtain ⟨L, U, rfl, h⟩ := (mem_RealL_iff x).mp hx
  rw [realLMul, realLOne, realLOf, fst_opair, snd_opair, fst_opair, snd_opair,
    mulLower_one h, mulUpper_one h]

/-- And multiplying by one on the left. -/
theorem realLOne_mul {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    realLMul realLOne.{u} x = x := by
  rw [realLMul_comm realLOne_mem hx, realLMul_one hx]

/-! ## Zero

`x · 0 = 0`. The bracket around `0` is symmetric, `-d < 0 < d`, and `d` is small
enough that every corner sits inside `(p, -p)`. Both ends of the bracket on `x`
need their own `d`, since `q ≤ w` says nothing about `|q|` and `|w|`; the
smaller of the two serves both. -/

theorem mulLower_zero {L U : ZFSet.{u}} (h : IsLocated L U) :
    mulLower L U (ratCut ratZero.{u}) (sep (fun p => ratLt ratZero.{u} p) NumberTheory.Rat.{u})
      = ratCut ratZero.{u} := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨hpQ, q, hq, hlt⟩ := mulLower_const h ratZero_mem_Rat hp
    rw [ratMul_zero (h.lower_subset q hq)] at hlt
    exact (mem_ratCut_iff _ _).mpr ⟨hpQ, hlt⟩
  · obtain ⟨hpQ, hp0⟩ := (mem_ratCut_iff _ p).mp hp
    obtain ⟨q, hq⟩ := h.lower_inhabited
    obtain ⟨w, hw⟩ := h.upper_inhabited
    have hqQ := h.lower_subset q hq
    have hwQ := h.upper_subset w hw
    have hnp := ratNeg_mem_Rat hpQ
    have hnp0 : ratLt ratZero.{u} (ratNeg p) := by
      have := (ratNeg_lt_neg_iff ratZero_mem_Rat hpQ).mpr hp0
      rwa [ratNeg_zero] at this
    obtain ⟨dq, hdqQ, h0dq, hqhi, hqlo⟩ := exists_small_scale hqQ hnp hnp0
    obtain ⟨dw, hdwQ, h0dw, hwhi, hwlo⟩ := exists_small_scale hwQ hnp hnp0
    -- the smaller of the two scales serves both bounds
    obtain ⟨d, hdQ, h0d, hq2, hw2⟩ :
        ∃ d, d ∈ NumberTheory.Rat.{u} ∧ ratLt ratZero.{u} d ∧
          (ratLt (ratMul q d) (ratNeg p) ∧ ratLt (ratNeg (ratNeg p)) (ratMul q d)) ∧
          (ratLt (ratMul w d) (ratNeg p) ∧ ratLt (ratNeg (ratNeg p)) (ratMul w d)) := by
      rcases ratLe_total hdqQ hdwQ with hle | hle
      · exact ⟨dq, hdqQ, h0dq, ⟨hqhi, hqlo⟩,
          small_scale_mono hwQ hdwQ hdqQ hnp hnp0 h0dq hle hwhi hwlo⟩
      · exact ⟨dw, hdwQ, h0dw,
          small_scale_mono hqQ hdqQ hdwQ hnp hnp0 h0dw hle hqhi hqlo, ⟨hwhi, hwlo⟩⟩
    have hnn : ratNeg (ratNeg p) = p := ratNeg_ratNeg hpQ
    rw [hnn] at hq2 hw2
    have hnd0 : ratLt (ratNeg d) ratZero.{u} := by
      have := (ratNeg_lt_neg_iff hdQ ratZero_mem_Rat).mpr h0d
      rwa [ratNeg_zero] at this
    -- the two remaining corners are the negatives of the two just bounded
    have hneg : ∀ c, c ∈ NumberTheory.Rat.{u} → ratLt (ratMul c d) (ratNeg p) →
        ratLt p (ratMul c (ratNeg d)) := by
      intro c hcQ hhi
      rw [ratMul_neg hcQ hdQ]
      have := (ratNeg_lt_neg_iff hnp (ratMul_mem_Rat hcQ hdQ)).mpr hhi
      rwa [ratNeg_ratNeg hpQ] at this
    exact (mem_sep_iff _ p _).mpr ⟨hpQ, q, hq, w, hw, ratNeg d,
      (mem_ratCut_iff _ _).mpr ⟨ratNeg_mem_Rat hdQ, hnd0⟩,
      d, (mem_sep_iff _ _ _).mpr ⟨hdQ, h0d⟩,
      hneg q hqQ hq2.left, hq2.right, hneg w hwQ hw2.left, hw2.right⟩

theorem mulUpper_zero {L U : ZFSet.{u}} (h : IsLocated L U) :
    mulUpper L U (ratCut ratZero.{u}) (sep (fun p => ratLt ratZero.{u} p) NumberTheory.Rat.{u})
      = sep (fun p => ratLt ratZero.{u} p) NumberTheory.Rat.{u} := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨hpQ, q', hq', hlt⟩ := mulUpper_const h ratZero_mem_Rat hp
    rw [ratMul_zero (h.upper_subset q' hq')] at hlt
    exact (mem_sep_iff _ _ _).mpr ⟨hpQ, hlt⟩
  · obtain ⟨hpQ, h0p⟩ := (mem_sep_iff _ p _).mp hp
    obtain ⟨q, hq⟩ := h.lower_inhabited
    obtain ⟨w, hw⟩ := h.upper_inhabited
    have hqQ := h.lower_subset q hq
    have hwQ := h.upper_subset w hw
    obtain ⟨dq, hdqQ, h0dq, hqhi, hqlo⟩ := exists_small_scale hqQ hpQ h0p
    obtain ⟨dw, hdwQ, h0dw, hwhi, hwlo⟩ := exists_small_scale hwQ hpQ h0p
    obtain ⟨d, hdQ, h0d, hq2, hw2⟩ :
        ∃ d, d ∈ NumberTheory.Rat.{u} ∧ ratLt ratZero.{u} d ∧
          (ratLt (ratMul q d) p ∧ ratLt (ratNeg p) (ratMul q d)) ∧
          (ratLt (ratMul w d) p ∧ ratLt (ratNeg p) (ratMul w d)) := by
      rcases ratLe_total hdqQ hdwQ with hle | hle
      · exact ⟨dq, hdqQ, h0dq, ⟨hqhi, hqlo⟩,
          small_scale_mono hwQ hdwQ hdqQ hpQ h0p h0dq hle hwhi hwlo⟩
      · exact ⟨dw, hdwQ, h0dw,
          small_scale_mono hqQ hdqQ hdwQ hpQ h0p h0dw hle hqhi hqlo, ⟨hwhi, hwlo⟩⟩
    have hnd0 : ratLt (ratNeg d) ratZero.{u} := by
      have := (ratNeg_lt_neg_iff hdQ ratZero_mem_Rat).mpr h0d
      rwa [ratNeg_zero] at this
    have hneg : ∀ c, c ∈ NumberTheory.Rat.{u} → ratLt (ratNeg p) (ratMul c d) →
        ratLt (ratMul c (ratNeg d)) p := by
      intro c hcQ hlo
      rw [ratMul_neg hcQ hdQ]
      have := (ratNeg_lt_neg_iff (ratMul_mem_Rat hcQ hdQ) (ratNeg_mem_Rat hpQ)).mpr hlo
      rwa [ratNeg_ratNeg hpQ] at this
    exact (mem_sep_iff _ p _).mpr ⟨hpQ, q, hq, w, hw, ratNeg d,
      (mem_ratCut_iff _ _).mpr ⟨ratNeg_mem_Rat hdQ, hnd0⟩,
      d, (mem_sep_iff _ _ _).mpr ⟨hdQ, h0d⟩,
      hneg q hqQ hq2.right, hq2.left, hneg w hwQ hw2.right, hw2.left⟩

/-- Zero annihilates. -/
theorem realLMul_zero {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    realLMul x realLZero.{u} = realLZero.{u} := by
  obtain ⟨L, U, rfl, h⟩ := (mem_RealL_iff x).mp hx
  rw [realLMul, realLZero, realLOf, fst_opair, snd_opair, fst_opair, snd_opair,
    mulLower_zero h, mulUpper_zero h]

/-- Zero annihilates on the left. The located reals carry `x * 0 = 0` directly;
this is the orientation `realLPow` needs, since it multiplies on the left. -/
theorem realLZero_mul {y : ZFSet.{u}} (hy : y ∈ RealL.{u}) :
    realLMul realLZero.{u} y = realLZero.{u} := by
  rw [realLMul_comm realLZero_mem hy, realLMul_zero hy]

/-- A located pair is determined by either containment. If both pairs are
located and each half of one is contained in the other's, the containments
reverse and the pairs are equal. So an equation between located reals needs only
one inclusion per half, not two -- locatedness supplies the rest. -/
theorem located_eq_of_subset {L U L' U' : ZFSet.{u}} (h : IsLocated L U)
    (h' : IsLocated L' U') (hL : ∀ p, p ∈ L → p ∈ L') (hU : ∀ p, p ∈ U → p ∈ U') :
    L = L' ∧ U = U' := by
  have hLback : ∀ p, p ∈ L' → p ∈ L := by
    intro p hp
    obtain ⟨p'', hp'', hlt⟩ := h'.lower_open p hp
    rcases h.located p (h'.lower_subset p hp) p'' (h'.lower_subset p'' hp'') hlt with hin | hin
    · exact hin
    · exact absurd (h'.ordered p'' hp'' p'' (hU p'' hin)) ratLt_irrefl
  have hUback : ∀ p, p ∈ U' → p ∈ U := by
    intro p hp
    obtain ⟨p'', hp'', hlt⟩ := h'.upper_open p hp
    rcases h.located p'' (h'.upper_subset p'' hp'') p (h'.upper_subset p hp) hlt with hin | hin
    · exact absurd (h'.ordered p'' (hL p'' hin) p'' hp'') ratLt_irrefl
    · exact hin
  exact ⟨ext _ _ fun p => ⟨hL p, hLback p⟩, ext _ _ fun p => ⟨hU p, hUback p⟩⟩

/-! ## Distributivity

`x · (y + z) = x · y + x · z`. The inclusion proved here is the one that needs
the machinery: a point below `a + b`, with `a` and `b` in the two products'
cuts, sits below every corner of the distributed bracket. Refine the two
brackets on `x` to one, add the corners pairwise (`lt_mul_add_of_lt`), then
replace the two bounds `r + t` and `r' + t'` by members of the sum's cuts
(`exists_lt_of_mul_lt₂`, `exists_gt_of_mul_lt₂`). -/

theorem mulLower_distrib_le {L₁ U₁ L₂ U₂ L₃ U₃ p : ZFSet.{u}} (h₁ : IsLocated L₁ U₁)
    (h₂ : IsLocated L₂ U₂) (h₃ : IsLocated L₃ U₃)
    (hp : p ∈ addLower (mulLower L₁ U₁ L₂ U₂) (mulLower L₁ U₁ L₃ U₃)) :
    p ∈ mulLower L₁ U₁ (addLower L₂ L₃) (addUpper U₂ U₃) := by
  obtain ⟨hpQ, a, ha, b, hb, hab⟩ := (mem_addLower_iff _ _ p).mp hp
  obtain ⟨haQ, q, hq, q', hq', r, hr, r', hr', a₁, a₂, a₃, a₄⟩ := (mem_sep_iff _ a _).mp ha
  obtain ⟨hbQ, s, hs, s', hs', t, ht, t', ht', b₁, b₂, b₃, b₄⟩ := (mem_sep_iff _ b _).mp hb
  -- one bracket on `x` for both products
  obtain ⟨m, hm, hqm, hsm⟩ := lower_pair_bound h₁ hq hs
  obtain ⟨m', hm', hm'q', hm's'⟩ := upper_pair_bound h₁ hq' hs'
  obtain ⟨A₁, A₂, A₃, A₄⟩ := corners_of_refinement h₁ h₂ haQ hq hq' hr hr' hm hm' hr hr'
    hqm hm'q' (ratLe_refl (h₂.lower_subset r hr)) (ratLe_refl (h₂.upper_subset r' hr'))
    a₁ a₂ a₃ a₄
  obtain ⟨B₁, B₂, B₃, B₄⟩ := corners_of_refinement h₁ h₃ hbQ hs hs' ht ht' hm hm' ht ht'
    hsm hm's' (ratLe_refl (h₃.lower_subset t ht)) (ratLe_refl (h₃.upper_subset t' ht'))
    b₁ b₂ b₃ b₄
  have hmQ := h₁.lower_subset m hm
  have hm'Q := h₁.upper_subset m' hm'
  have hrQ := h₂.lower_subset r hr
  have hr'Q := h₂.upper_subset r' hr'
  have htQ := h₃.lower_subset t ht
  have ht'Q := h₃.upper_subset t' ht'
  -- the four corners of the distributed bracket, before shrinking
  have c₁ := lt_mul_add_of_lt hpQ haQ hbQ hmQ hrQ htQ hab A₁ B₁
  have c₂ := lt_mul_add_of_lt hpQ haQ hbQ hmQ hr'Q ht'Q hab A₂ B₂
  have c₃ := lt_mul_add_of_lt hpQ haQ hbQ hm'Q hrQ htQ hab A₃ B₃
  have c₄ := lt_mul_add_of_lt hpQ haQ hbQ hm'Q hr'Q ht'Q hab A₄ B₄
  -- `r + t` bounds the sum's lower cut without belonging to it, so shrink
  obtain ⟨R, hRQ, hRlt, hmR, hm'R⟩ := exists_lt_of_mul_lt₂ hpQ hmQ hm'Q
    (ratAdd_mem_Rat hrQ htQ) c₁ c₃
  obtain ⟨R', hR'Q, hR'gt, hmR', hm'R'⟩ := exists_gt_of_mul_lt₂ hpQ hmQ hm'Q
    (ratAdd_mem_Rat hr'Q ht'Q) c₂ c₄
  exact (mem_sep_iff _ p _).mpr ⟨hpQ, m, hm, m', hm',
    R, (mem_addLower_iff _ _ R).mpr ⟨hRQ, r, hr, t, ht, hRlt⟩,
    R', (mem_addUpper_iff _ _ R').mpr ⟨hR'Q, r', hr', t', ht', hR'gt⟩,
    hmR, hmR', hm'R, hm'R'⟩

theorem mulUpper_distrib_le {L₁ U₁ L₂ U₂ L₃ U₃ p : ZFSet.{u}} (h₁ : IsLocated L₁ U₁)
    (h₂ : IsLocated L₂ U₂) (h₃ : IsLocated L₃ U₃)
    (hp : p ∈ addUpper (mulUpper L₁ U₁ L₂ U₂) (mulUpper L₁ U₁ L₃ U₃)) :
    p ∈ mulUpper L₁ U₁ (addLower L₂ L₃) (addUpper U₂ U₃) := by
  obtain ⟨hpQ, a, ha, b, hb, hab⟩ := (mem_addUpper_iff _ _ p).mp hp
  obtain ⟨haQ, q, hq, q', hq', r, hr, r', hr', a₁, a₂, a₃, a₄⟩ := (mem_sep_iff _ a _).mp ha
  obtain ⟨hbQ, s, hs, s', hs', t, ht, t', ht', b₁, b₂, b₃, b₄⟩ := (mem_sep_iff _ b _).mp hb
  obtain ⟨m, hm, hqm, hsm⟩ := lower_pair_bound h₁ hq hs
  obtain ⟨m', hm', hm'q', hm's'⟩ := upper_pair_bound h₁ hq' hs'
  obtain ⟨A₁, A₂, A₃, A₄⟩ := corners_of_refinement' h₁ h₂ haQ hq hq' hr hr' hm hm' hr hr'
    hqm hm'q' (ratLe_refl (h₂.lower_subset r hr)) (ratLe_refl (h₂.upper_subset r' hr'))
    a₁ a₂ a₃ a₄
  obtain ⟨B₁, B₂, B₃, B₄⟩ := corners_of_refinement' h₁ h₃ hbQ hs hs' ht ht' hm hm' ht ht'
    hsm hm's' (ratLe_refl (h₃.lower_subset t ht)) (ratLe_refl (h₃.upper_subset t' ht'))
    b₁ b₂ b₃ b₄
  have hmQ := h₁.lower_subset m hm
  have hm'Q := h₁.upper_subset m' hm'
  have hrQ := h₂.lower_subset r hr
  have hr'Q := h₂.upper_subset r' hr'
  have htQ := h₃.lower_subset t ht
  have ht'Q := h₃.upper_subset t' ht'
  have c₁ := mul_add_lt_of_lt hpQ haQ hbQ hmQ hrQ htQ hab A₁ B₁
  have c₂ := mul_add_lt_of_lt hpQ haQ hbQ hmQ hr'Q ht'Q hab A₂ B₂
  have c₃ := mul_add_lt_of_lt hpQ haQ hbQ hm'Q hrQ htQ hab A₃ B₃
  have c₄ := mul_add_lt_of_lt hpQ haQ hbQ hm'Q hr'Q ht'Q hab A₄ B₄
  obtain ⟨R, hRQ, hRlt, hmR, hm'R⟩ := exists_lt_of_lt_mul₂ hpQ hmQ hm'Q
    (ratAdd_mem_Rat hrQ htQ) c₁ c₃
  obtain ⟨R', hR'Q, hR'gt, hmR', hm'R'⟩ := exists_gt_of_lt_mul₂ hpQ hmQ hm'Q
    (ratAdd_mem_Rat hr'Q ht'Q) c₂ c₄
  exact (mem_sep_iff _ p _).mpr ⟨hpQ, m, hm, m', hm',
    R, (mem_addLower_iff _ _ R).mpr ⟨hRQ, r, hr, t, ht, hRlt⟩,
    R', (mem_addUpper_iff _ _ R').mpr ⟨hR'Q, r', hr', t', ht', hR'gt⟩,
    hmR, hmR', hm'R, hm'R'⟩

/-- Multiplication distributes over addition. Only one inclusion per half is
proved; `located_eq_of_subset` supplies the reverse from locatedness. -/
theorem realLMul_distrib {x y z : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (hz : z ∈ RealL.{u}) :
    realLMul x (realLAdd y z) = realLAdd (realLMul x y) (realLMul x z) := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff y).mp hy
  obtain ⟨L₃, U₃, rfl, h₃⟩ := (mem_RealL_iff z).mp hz
  have hsum := isLocated_add h₂ h₃
  have hleft := isLocated_mul h₁ hsum
  have hright := isLocated_add (isLocated_mul h₁ h₂) (isLocated_mul h₁ h₃)
  obtain ⟨hL, hU⟩ := located_eq_of_subset hright hleft
    (fun p hp => mulLower_distrib_le h₁ h₂ h₃ hp)
    (fun p hp => mulUpper_distrib_le h₁ h₂ h₃ hp)
  rw [realLAdd, realLMul, realLMul, realLMul, realLAdd,
    fst_opair, fst_opair, fst_opair, snd_opair, snd_opair, snd_opair,
    fst_opair, snd_opair, fst_opair, snd_opair, fst_opair, snd_opair, ← hL, ← hU]

/-! ## Associativity

The corners of `(xy)z` and `x(yz)` do not correspond
-- the outer bracket's ends are members of the inner cuts, not products. The
way through is that `[a, a']` is itself a bracket around every corner `e·f` of
`x·y`, so `ratLt_mul_of_corners` applies to it, and `p` lands below `(e·f)·g`
for all eight choices. `ratMul_assoc` reassociates each, and the least of the
four inner products is then shrunk into the inner cut. -/

theorem mulLower_assoc_le {L₁ U₁ L₂ U₂ L₃ U₃ p : ZFSet.{u}} (h₁ : IsLocated L₁ U₁)
    (h₂ : IsLocated L₂ U₂) (h₃ : IsLocated L₃ U₃)
    (hp : p ∈ mulLower (mulLower L₁ U₁ L₂ U₂) (mulUpper L₁ U₁ L₂ U₂) L₃ U₃) :
    p ∈ mulLower L₁ U₁ (mulLower L₂ U₂ L₃ U₃) (mulUpper L₂ U₂ L₃ U₃) := by
  obtain ⟨hpQ, a, ha, a', ha', c, hc, c', hc', p₁, p₂, p₃, p₄⟩ := (mem_sep_iff _ p _).mp hp
  obtain ⟨haQ, q, hq, q', hq', r, hr, r', hr', A₁, A₂, A₃, A₄⟩ := (mem_sep_iff _ a _).mp ha
  obtain ⟨ha'Q, s, hs, s', hs', t, ht, t', ht', B₁, B₂, B₃, B₄⟩ := (mem_sep_iff _ a' _).mp ha'
  obtain ⟨m, hm, hqm, hsm⟩ := lower_pair_bound h₁ hq hs
  obtain ⟨m', hm', hm'q', hm's'⟩ := upper_pair_bound h₁ hq' hs'
  obtain ⟨n, hn, hrn, htn⟩ := lower_pair_bound h₂ hr ht
  obtain ⟨n', hn', hn'r', hn't'⟩ := upper_pair_bound h₂ hr' ht'
  obtain ⟨A₁', A₂', A₃', A₄'⟩ := corners_of_refinement h₁ h₂ haQ hq hq' hr hr' hm hm' hn hn'
    hqm hm'q' hrn hn'r' A₁ A₂ A₃ A₄
  obtain ⟨B₁', B₂', B₃', B₄'⟩ := corners_of_refinement' h₁ h₂ ha'Q hs hs' ht ht' hm hm' hn hn'
    hsm hm's' htn hn't' B₁ B₂ B₃ B₄
  have hmQ := h₁.lower_subset m hm
  have hm'Q := h₁.upper_subset m' hm'
  have hnQ := h₂.lower_subset n hn
  have hn'Q := h₂.upper_subset n' hn'
  have hcQ := h₃.lower_subset c hc
  have hc'Q := h₃.upper_subset c' hc'
  -- `[a, a']` brackets every corner of `x·y`, so `p` is below `(e·f)·g` for all eight
  have eight : ∀ e f, e ∈ NumberTheory.Rat.{u} → f ∈ NumberTheory.Rat.{u} → ratLt a (ratMul e f) →
      ratLt (ratMul e f) a' → ∀ g, g ∈ NumberTheory.Rat.{u} → ratLe c g → ratLe g c' →
      ratLt p (ratMul (ratMul e f) g) :=
    fun e f heQ hfQ hlo hhi g hgQ hcg hgc' =>
      ratLt_mul_of_corners hpQ haQ ha'Q hcQ hc'Q (ratMul_mem_Rat heQ hfQ) hgQ
        hlo.left hhi.left hcg hgc' p₁ p₂ p₃ p₄
  have E₁ := eight m n hmQ hnQ A₁' B₁' c hcQ (ratLe_refl hcQ) (h₃.ordered c hc c' hc').left
  have E₂ := eight m n hmQ hnQ A₁' B₁' c' hc'Q (h₃.ordered c hc c' hc').left (ratLe_refl hc'Q)
  have E₃ := eight m n' hmQ hn'Q A₂' B₂' c hcQ (ratLe_refl hcQ) (h₃.ordered c hc c' hc').left
  have E₄ := eight m n' hmQ hn'Q A₂' B₂' c' hc'Q (h₃.ordered c hc c' hc').left (ratLe_refl hc'Q)
  have E₅ := eight m' n hm'Q hnQ A₃' B₃' c hcQ (ratLe_refl hcQ) (h₃.ordered c hc c' hc').left
  have E₆ := eight m' n hm'Q hnQ A₃' B₃' c' hc'Q (h₃.ordered c hc c' hc').left (ratLe_refl hc'Q)
  have E₇ := eight m' n' hm'Q hn'Q A₄' B₄' c hcQ (ratLe_refl hcQ) (h₃.ordered c hc c' hc').left
  have E₈ := eight m' n' hm'Q hn'Q A₄' B₄' c' hc'Q (h₃.ordered c hc c' hc').left (ratLe_refl hc'Q)
  rw [ratMul_assoc hmQ hnQ hcQ] at E₁
  rw [ratMul_assoc hmQ hnQ hc'Q] at E₂
  rw [ratMul_assoc hmQ hn'Q hcQ] at E₃
  rw [ratMul_assoc hmQ hn'Q hc'Q] at E₄
  rw [ratMul_assoc hm'Q hnQ hcQ] at E₅
  rw [ratMul_assoc hm'Q hnQ hc'Q] at E₆
  rw [ratMul_assoc hm'Q hn'Q hcQ] at E₇
  rw [ratMul_assoc hm'Q hn'Q hc'Q] at E₈
  -- the least of the four inner products, shrunk into the inner cut
  obtain ⟨w, hwQ, w₁, w₂, w₃, w₄, hwis⟩ := exists_min_four (ratMul_mem_Rat hnQ hcQ)
    (ratMul_mem_Rat hnQ hc'Q) (ratMul_mem_Rat hn'Q hcQ) (ratMul_mem_Rat hn'Q hc'Q)
  obtain ⟨v, hvQ, v₁, v₂, v₃, v₄, hvis⟩ := exists_max_four (ratMul_mem_Rat hnQ hcQ)
    (ratMul_mem_Rat hnQ hc'Q) (ratMul_mem_Rat hn'Q hcQ) (ratMul_mem_Rat hn'Q hc'Q)
  have hmw : ratLt p (ratMul m w) :=
    of_one_of_four (P := fun z => ratLt p (ratMul m z)) hwis E₁ E₂ E₃ E₄
  have hm'w : ratLt p (ratMul m' w) :=
    of_one_of_four (P := fun z => ratLt p (ratMul m' z)) hwis E₅ E₆ E₇ E₈
  have hmv : ratLt p (ratMul m v) :=
    of_one_of_four (P := fun z => ratLt p (ratMul m z)) hvis E₁ E₂ E₃ E₄
  have hm'v : ratLt p (ratMul m' v) :=
    of_one_of_four (P := fun z => ratLt p (ratMul m' z)) hvis E₅ E₆ E₇ E₈
  obtain ⟨W, hWQ, hWlt, hmW, hm'W⟩ := exists_lt_of_mul_lt₂ hpQ hmQ hm'Q hwQ hmw hm'w
  obtain ⟨V, hVQ, hVgt, hmV, hm'V⟩ := exists_gt_of_mul_lt₂ hpQ hmQ hm'Q hvQ hmv hm'v
  exact (mem_sep_iff _ p _).mpr ⟨hpQ, m, hm, m', hm',
    W, (mem_sep_iff _ W _).mpr ⟨hWQ, n, hn, n', hn', c, hc, c', hc',
      ratLt_of_lt_of_le hWQ hwQ (ratMul_mem_Rat hnQ hcQ) hWlt w₁,
      ratLt_of_lt_of_le hWQ hwQ (ratMul_mem_Rat hnQ hc'Q) hWlt w₂,
      ratLt_of_lt_of_le hWQ hwQ (ratMul_mem_Rat hn'Q hcQ) hWlt w₃,
      ratLt_of_lt_of_le hWQ hwQ (ratMul_mem_Rat hn'Q hc'Q) hWlt w₄⟩,
    V, (mem_sep_iff _ V _).mpr ⟨hVQ, n, hn, n', hn', c, hc, c', hc',
      ratLt_of_le_of_lt (ratMul_mem_Rat hnQ hcQ) hvQ hVQ v₁ hVgt,
      ratLt_of_le_of_lt (ratMul_mem_Rat hnQ hc'Q) hvQ hVQ v₂ hVgt,
      ratLt_of_le_of_lt (ratMul_mem_Rat hn'Q hcQ) hvQ hVQ v₃ hVgt,
      ratLt_of_le_of_lt (ratMul_mem_Rat hn'Q hc'Q) hvQ hVQ v₄ hVgt⟩,
    hmW, hmV, hm'W, hm'V⟩


theorem mulUpper_assoc_le {L₁ U₁ L₂ U₂ L₃ U₃ p : ZFSet.{u}} (h₁ : IsLocated L₁ U₁)
    (h₂ : IsLocated L₂ U₂) (h₃ : IsLocated L₃ U₃)
    (hp : p ∈ mulUpper (mulLower L₁ U₁ L₂ U₂) (mulUpper L₁ U₁ L₂ U₂) L₃ U₃) :
    p ∈ mulUpper L₁ U₁ (mulLower L₂ U₂ L₃ U₃) (mulUpper L₂ U₂ L₃ U₃) := by
  obtain ⟨hpQ, a, ha, a', ha', c, hc, c', hc', p₁, p₂, p₃, p₄⟩ := (mem_sep_iff _ p _).mp hp
  obtain ⟨haQ, q, hq, q', hq', r, hr, r', hr', A₁, A₂, A₃, A₄⟩ := (mem_sep_iff _ a _).mp ha
  obtain ⟨ha'Q, s, hs, s', hs', t, ht, t', ht', B₁, B₂, B₃, B₄⟩ := (mem_sep_iff _ a' _).mp ha'
  obtain ⟨m, hm, hqm, hsm⟩ := lower_pair_bound h₁ hq hs
  obtain ⟨m', hm', hm'q', hm's'⟩ := upper_pair_bound h₁ hq' hs'
  obtain ⟨n, hn, hrn, htn⟩ := lower_pair_bound h₂ hr ht
  obtain ⟨n', hn', hn'r', hn't'⟩ := upper_pair_bound h₂ hr' ht'
  obtain ⟨A₁', A₂', A₃', A₄'⟩ := corners_of_refinement h₁ h₂ haQ hq hq' hr hr' hm hm' hn hn'
    hqm hm'q' hrn hn'r' A₁ A₂ A₃ A₄
  obtain ⟨B₁', B₂', B₃', B₄'⟩ := corners_of_refinement' h₁ h₂ ha'Q hs hs' ht ht' hm hm' hn hn'
    hsm hm's' htn hn't' B₁ B₂ B₃ B₄
  have hmQ := h₁.lower_subset m hm
  have hm'Q := h₁.upper_subset m' hm'
  have hnQ := h₂.lower_subset n hn
  have hn'Q := h₂.upper_subset n' hn'
  have hcQ := h₃.lower_subset c hc
  have hc'Q := h₃.upper_subset c' hc'
  -- `[a, a']` brackets every corner of `x·y`, so `p` is below `(e·f)·g` for all eight
  have eight : ∀ e f, e ∈ NumberTheory.Rat.{u} → f ∈ NumberTheory.Rat.{u} → ratLt a (ratMul e f) →
      ratLt (ratMul e f) a' → ∀ g, g ∈ NumberTheory.Rat.{u} → ratLe c g → ratLe g c' →
      ratLt (ratMul (ratMul e f) g) p :=
    fun e f heQ hfQ hlo hhi g hgQ hcg hgc' =>
      ratMul_lt_of_corners hpQ haQ ha'Q hcQ hc'Q (ratMul_mem_Rat heQ hfQ) hgQ
        hlo.left hhi.left hcg hgc' p₁ p₂ p₃ p₄
  have E₁ := eight m n hmQ hnQ A₁' B₁' c hcQ (ratLe_refl hcQ) (h₃.ordered c hc c' hc').left
  have E₂ := eight m n hmQ hnQ A₁' B₁' c' hc'Q (h₃.ordered c hc c' hc').left (ratLe_refl hc'Q)
  have E₃ := eight m n' hmQ hn'Q A₂' B₂' c hcQ (ratLe_refl hcQ) (h₃.ordered c hc c' hc').left
  have E₄ := eight m n' hmQ hn'Q A₂' B₂' c' hc'Q (h₃.ordered c hc c' hc').left (ratLe_refl hc'Q)
  have E₅ := eight m' n hm'Q hnQ A₃' B₃' c hcQ (ratLe_refl hcQ) (h₃.ordered c hc c' hc').left
  have E₆ := eight m' n hm'Q hnQ A₃' B₃' c' hc'Q (h₃.ordered c hc c' hc').left (ratLe_refl hc'Q)
  have E₇ := eight m' n' hm'Q hn'Q A₄' B₄' c hcQ (ratLe_refl hcQ) (h₃.ordered c hc c' hc').left
  have E₈ := eight m' n' hm'Q hn'Q A₄' B₄' c' hc'Q (h₃.ordered c hc c' hc').left (ratLe_refl hc'Q)
  rw [ratMul_assoc hmQ hnQ hcQ] at E₁
  rw [ratMul_assoc hmQ hnQ hc'Q] at E₂
  rw [ratMul_assoc hmQ hn'Q hcQ] at E₃
  rw [ratMul_assoc hmQ hn'Q hc'Q] at E₄
  rw [ratMul_assoc hm'Q hnQ hcQ] at E₅
  rw [ratMul_assoc hm'Q hnQ hc'Q] at E₆
  rw [ratMul_assoc hm'Q hn'Q hcQ] at E₇
  rw [ratMul_assoc hm'Q hn'Q hc'Q] at E₈
  -- the least of the four inner products, shrunk into the inner cut
  obtain ⟨w, hwQ, w₁, w₂, w₃, w₄, hwis⟩ := exists_min_four (ratMul_mem_Rat hnQ hcQ)
    (ratMul_mem_Rat hnQ hc'Q) (ratMul_mem_Rat hn'Q hcQ) (ratMul_mem_Rat hn'Q hc'Q)
  obtain ⟨v, hvQ, v₁, v₂, v₃, v₄, hvis⟩ := exists_max_four (ratMul_mem_Rat hnQ hcQ)
    (ratMul_mem_Rat hnQ hc'Q) (ratMul_mem_Rat hn'Q hcQ) (ratMul_mem_Rat hn'Q hc'Q)
  have hmw : ratLt (ratMul m w) p :=
    of_one_of_four (P := fun z => ratLt (ratMul m z) p) hwis E₁ E₂ E₃ E₄
  have hm'w : ratLt (ratMul m' w) p :=
    of_one_of_four (P := fun z => ratLt (ratMul m' z) p) hwis E₅ E₆ E₇ E₈
  have hmv : ratLt (ratMul m v) p :=
    of_one_of_four (P := fun z => ratLt (ratMul m z) p) hvis E₁ E₂ E₃ E₄
  have hm'v : ratLt (ratMul m' v) p :=
    of_one_of_four (P := fun z => ratLt (ratMul m' z) p) hvis E₅ E₆ E₇ E₈
  obtain ⟨W, hWQ, hWlt, hmW, hm'W⟩ := exists_lt_of_lt_mul₂ hpQ hmQ hm'Q hwQ hmw hm'w
  obtain ⟨V, hVQ, hVgt, hmV, hm'V⟩ := exists_gt_of_lt_mul₂ hpQ hmQ hm'Q hvQ hmv hm'v
  exact (mem_sep_iff _ p _).mpr ⟨hpQ, m, hm, m', hm',
    W, (mem_sep_iff _ W _).mpr ⟨hWQ, n, hn, n', hn', c, hc, c', hc',
      ratLt_of_lt_of_le hWQ hwQ (ratMul_mem_Rat hnQ hcQ) hWlt w₁,
      ratLt_of_lt_of_le hWQ hwQ (ratMul_mem_Rat hnQ hc'Q) hWlt w₂,
      ratLt_of_lt_of_le hWQ hwQ (ratMul_mem_Rat hn'Q hcQ) hWlt w₃,
      ratLt_of_lt_of_le hWQ hwQ (ratMul_mem_Rat hn'Q hc'Q) hWlt w₄⟩,
    V, (mem_sep_iff _ V _).mpr ⟨hVQ, n, hn, n', hn', c, hc, c', hc',
      ratLt_of_le_of_lt (ratMul_mem_Rat hnQ hcQ) hvQ hVQ v₁ hVgt,
      ratLt_of_le_of_lt (ratMul_mem_Rat hnQ hc'Q) hvQ hVQ v₂ hVgt,
      ratLt_of_le_of_lt (ratMul_mem_Rat hn'Q hcQ) hvQ hVQ v₃ hVgt,
      ratLt_of_le_of_lt (ratMul_mem_Rat hn'Q hc'Q) hvQ hVQ v₄ hVgt⟩,
    hmW, hmV, hm'W, hm'V⟩

/-- Multiplication is associative. -/
theorem realLMul_assoc {x y z : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (hz : z ∈ RealL.{u}) :
    realLMul (realLMul x y) z = realLMul x (realLMul y z) := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff y).mp hy
  obtain ⟨L₃, U₃, rfl, h₃⟩ := (mem_RealL_iff z).mp hz
  have hleft := isLocated_mul (isLocated_mul h₁ h₂) h₃
  have hright := isLocated_mul h₁ (isLocated_mul h₂ h₃)
  obtain ⟨hL, hU⟩ := located_eq_of_subset hleft hright
    (fun p hp => mulLower_assoc_le h₁ h₂ h₃ hp)
    (fun p hp => mulUpper_assoc_le h₁ h₂ h₃ hp)
  rw [realLMul, realLMul, realLMul, realLMul,
    fst_opair, snd_opair, fst_opair, snd_opair, fst_opair, snd_opair,
    fst_opair, snd_opair, fst_opair, snd_opair, hL, hU]

/-- `(p - q) + q = p`, from the abelian group laws. -/
theorem realLSub_add_cancel {p q : ZFSet.{u}} (hp : p ∈ RealL.{u}) (hq : q ∈ RealL.{u}) :
    realLAdd (realLAdd p (realLNeg q)) q = p := by
  rw [realLAdd_assoc hp (realLNeg_mem hq) hq,
    realLAdd_comm (realLNeg_mem hq) hq, realLAdd_neg hq, realLAdd_zero hp]

/-! ## The strict order, and apartness

`x < y` when some rational lies above `x` and below `y`. That witness is
positive data, so apartness is usable constructively: `x ≠ y` is a negation
and decides nothing, while `realLApart x y` hands over a rational separating
them. It is the form an inverse will need. -/

def realLLt (x y : ZFSet.{u}) : Prop := ∃ p, p ∈ snd x ∧ p ∈ fst y

def realLApart (x y : ZFSet.{u}) : Prop := realLLt x y ∨ realLLt y x

theorem realLLt_irrefl {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) : ¬ realLLt x x := by
  obtain ⟨L, U, rfl, h⟩ := (mem_RealL_iff x).mp hx
  rintro ⟨p, hpU, hpL⟩
  rw [snd_opair] at hpU
  rw [fst_opair] at hpL
  exact ratLt_irrefl (h.ordered p hpL p hpU)

theorem realLLt_trans {x y z : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (hz : z ∈ RealL.{u}) (hxy : realLLt x y) (hyz : realLLt y z) : realLLt x z := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff y).mp hy
  obtain ⟨L₃, U₃, rfl, h₃⟩ := (mem_RealL_iff z).mp hz
  obtain ⟨p, hpU, hpL⟩ := hxy
  obtain ⟨q, hqU, hqL⟩ := hyz
  rw [snd_opair] at hpU hqU
  rw [fst_opair] at hpL hqL
  -- `p` is below `y` and `q` above it, so `p < q`, and `p` is already below `z`
  refine ⟨p, ?_, ?_⟩
  · rw [snd_opair]; exact hpU
  · rw [fst_opair]
    exact h₃.lower_down q hqL p (h₂.lower_subset p hpL) (h₂.ordered p hpL q hqU)

theorem realLApart_symm {x y : ZFSet.{u}} (h : realLApart x y) : realLApart y x :=
  h.symm

theorem realLApart_irrefl {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) : ¬ realLApart x x := by
  rintro (h | h) <;> exact realLLt_irrefl hx h

/-! ## The inverse of a positive located real -/

def invLower (U : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ r, r ∈ U ∧ ratLt p (ratInv r)) NumberTheory.Rat.{u}

def invUpper (L : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ q, q ∈ L ∧ ratLt ratZero.{u} q ∧ ratLt (ratInv q) p) NumberTheory.Rat.{u}

theorem mem_invLower_iff (U p : ZFSet.{u}) :
    p ∈ invLower U ↔ p ∈ NumberTheory.Rat.{u} ∧ ∃ r, r ∈ U ∧ ratLt p (ratInv r) :=
  mem_sep_iff _ _ _

theorem mem_invUpper_iff (L p : ZFSet.{u}) :
    p ∈ invUpper L ↔ p ∈ NumberTheory.Rat.{u} ∧ ∃ q, q ∈ L ∧ ratLt ratZero.{u} q ∧ ratLt (ratInv q) p :=
  mem_sep_iff _ _ _

/-- Every member of the upper cut is above the positive witness, hence positive. -/
theorem upper_pos_of_witness {L U c : ZFSet.{u}} (h : IsLocated L U) (hc : c ∈ L)
    (hc0 : ratLt ratZero.{u} c) {r : ZFSet.{u}} (hr : r ∈ U) : ratLt ratZero.{u} r :=
  ratLt_trans ratZero_mem_Rat (h.lower_subset c hc) (h.upper_subset r hr) hc0
    (h.ordered c hc r hr)

theorem isLocated_inv {L U c : ZFSet.{u}} (h : IsLocated L U) (hc : c ∈ L)
    (hc0 : ratLt ratZero.{u} c) : IsLocated (invLower U) (invUpper L) where
  lower_subset p hp := ((mem_invLower_iff U p).mp hp).left
  upper_subset p hp := ((mem_invUpper_iff L p).mp hp).left
  lower_inhabited := by
    obtain ⟨r, hr⟩ := h.upper_inhabited
    have hr0 := upper_pos_of_witness h hc hc0 hr
    obtain ⟨s, hsQ, hs⟩ := rat_no_least (ratInv_mem_Rat (h.upper_subset r hr)
      (ratNe_zero_of_pos hr0))
    exact ⟨s, (mem_invLower_iff U s).mpr ⟨hsQ, r, hr, hs⟩⟩
  upper_inhabited := by
    obtain ⟨s, hsQ, hs⟩ := rat_no_greatest (ratInv_mem_Rat (h.lower_subset c hc)
      (ratNe_zero_of_pos hc0))
    exact ⟨s, (mem_invUpper_iff L s).mpr ⟨hsQ, c, hc, hc0, hs⟩⟩
  ordered p hp r hr := by
    obtain ⟨hpQ, s, hs, hps⟩ := (mem_invLower_iff U p).mp hp
    obtain ⟨hrQ, q, hq, hq0, hqr⟩ := (mem_invUpper_iff L r).mp hr
    have hs0 := upper_pos_of_witness h hc hc0 hs
    -- `q < s`, so `s⁻¹ < q⁻¹`, and `p < s⁻¹ < q⁻¹ < r`
    refine ratLt_trans hpQ (ratInv_mem_Rat (h.upper_subset s hs)
      (ratNe_zero_of_pos hs0)) hrQ hps ?_
    exact ratLt_trans (ratInv_mem_Rat (h.upper_subset s hs)
      (ratNe_zero_of_pos hs0))
      (ratInv_mem_Rat (h.lower_subset q hq) (ratNe_zero_of_pos hq0)) hrQ
      (ratInv_lt_ratInv (h.lower_subset q hq) (h.upper_subset s hs) hq0
        (h.ordered q hq s hs)) hqr
  lower_down q hq p hpQ hpq := by
    obtain ⟨-, r, hr, hqr⟩ := (mem_invLower_iff U q).mp hq
    exact (mem_invLower_iff U p).mpr ⟨hpQ, r, hr,
      ratLt_trans hpQ (((mem_invLower_iff U q).mp hq).left)
        (ratInv_mem_Rat (h.upper_subset r hr)
          (fun he => ratLt_irrefl (he ▸ upper_pos_of_witness h hc hc0 hr))) hpq hqr⟩
  upper_up r hr p hpQ hrp := by
    obtain ⟨-, q, hq, hq0, hqr⟩ := (mem_invUpper_iff L r).mp hr
    exact (mem_invUpper_iff L p).mpr ⟨hpQ, q, hq, hq0,
      ratLt_trans (ratInv_mem_Rat (h.lower_subset q hq) (ratNe_zero_of_pos hq0))
        (((mem_invUpper_iff L r).mp hr).left) hpQ hqr hrp⟩
  lower_open q hq := by
    obtain ⟨hqQ, r, hr, hqr⟩ := (mem_invLower_iff U q).mp hq
    have hr0 := upper_pos_of_witness h hc hc0 hr
    obtain ⟨t, htQ, hqt, htr⟩ := rat_dense hqQ (ratInv_mem_Rat (h.upper_subset r hr)
      (ratNe_zero_of_pos hr0)) hqr
    exact ⟨t, (mem_invLower_iff U t).mpr ⟨htQ, r, hr, htr⟩, hqt⟩
  upper_open r hr := by
    obtain ⟨hrQ, q, hq, hq0, hqr⟩ := (mem_invUpper_iff L r).mp hr
    obtain ⟨t, htQ, hqt, htr⟩ := rat_dense (ratInv_mem_Rat (h.lower_subset q hq)
      (ratNe_zero_of_pos hq0)) hrQ hqr
    exact ⟨t, (mem_invUpper_iff L t).mpr ⟨htQ, q, hq, hq0, hqt⟩, htr⟩
  located p hpQ r hrQ hpr := by
    obtain ⟨s, hs⟩ := h.upper_inhabited
    have hs0 := upper_pos_of_witness h hc hc0 hs
    have hsi := ratInv_mem_Rat (h.upper_subset s hs) (ratNe_zero_of_pos hs0)
    rcases ratLe_total hpQ ratZero_mem_Rat with hp0 | hp0
    · -- `p ≤ 0` is below every reciprocal
      exact Or.inl ((mem_invLower_iff U p).mpr ⟨hpQ, s, hs,
        ratLt_of_le_of_lt hpQ ratZero_mem_Rat hsi hp0 (ratInv_pos (h.upper_subset s hs) hs0)⟩)
    · -- `0 ≤ p < r`, so both reciprocals exist and `r⁻¹ < p'⁻¹` for `p < p' < r`
      obtain ⟨p', hp'Q, hpp', hp'r⟩ := rat_dense hpQ hrQ hpr
      have hp'0 : ratLt ratZero.{u} p' := ratLt_of_le_of_lt ratZero_mem_Rat hpQ hp'Q hp0 hpp'
      have hr0 : ratLt ratZero.{u} r := ratLt_trans ratZero_mem_Rat hp'Q hrQ hp'0 hp'r
      have hri := ratInv_mem_Rat hrQ (ratNe_zero_of_pos hr0)
      have hp'i := ratInv_mem_Rat hp'Q (fun he => ratLt_irrefl (he ▸ hp'0))
      rcases h.located _ hri _ hp'i (ratInv_lt_ratInv hp'Q hrQ hp'0 hp'r) with hin | hin
      · -- `r⁻¹` is in the lower cut; open it upwards to get a strict witness
        obtain ⟨t, ht, hrt⟩ := h.lower_open _ hin
        have ht0 : ratLt ratZero.{u} t :=
          ratLt_trans ratZero_mem_Rat hri (h.lower_subset t ht)
            (ratInv_pos hrQ hr0) hrt
        refine Or.inr ((mem_invUpper_iff L r).mpr ⟨hrQ, t, ht, ht0, ?_⟩)
        have := ratInv_lt_ratInv hri (h.lower_subset t ht) (ratInv_pos hrQ hr0) hrt
        rwa [ratInv_ratInv hrQ (ratNe_zero_of_pos hr0)] at this
      · -- `p'⁻¹` is in the upper cut, and `p < p' = (p'⁻¹)⁻¹`
        refine Or.inl ((mem_invLower_iff U p).mpr ⟨hpQ, _, hin, ?_⟩)
        rwa [ratInv_ratInv hp'Q (fun he => ratLt_irrefl (he ▸ hp'0))]

/-- The reciprocal, at the level of the reals. The halves swap. -/
def realLInv (z : ZFSet.{u}) : ZFSet.{u} :=
  opair (invLower (snd z)) (invUpper (fst z))

/-- `0 < z` is exactly the witness `isLocated_inv` wants: a positive rational in
the lower cut. -/
theorem realLInv_mem {z : ZFSet.{u}} (hz : z ∈ RealL.{u}) (h : realLLt realLZero.{u} z) :
    realLInv z ∈ RealL.{u} := by
  obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff z).mp hz
  obtain ⟨c, hcU0, hcL⟩ := h
  rw [realLZero, realLOf, snd_opair] at hcU0
  rw [fst_opair] at hcL
  obtain ⟨hcQ, hc0⟩ := (mem_sep_iff _ c _).mp hcU0
  refine (mem_RealL_iff _).mpr ⟨invLower U, invUpper L, ?_, ?_⟩
  · rw [realLInv, fst_opair, snd_opair]
  · exact isLocated_inv hloc hcL hc0

/-- A positive real has a positive rational strictly inside its lower cut, which
is what every use of the inverse needs to hand on. -/
theorem exists_pos_lower {z : ZFSet.{u}} (h : realLLt realLZero.{u} z) :
    ∃ c, c ∈ fst z ∧ ratLt ratZero.{u} c := by
  obtain ⟨c, hcU0, hcL⟩ := h
  rw [realLZero, realLOf, snd_opair] at hcU0
  exact ⟨c, hcL, ((mem_sep_iff _ c _).mp hcU0).right⟩

/-- The product of a positive real with its reciprocal lies below one. The
interior point is a single `t` in the upper cut and its own reciprocal, so the
corner bound closes at `t · t⁻¹ = 1`. -/
theorem mulLower_inv_le {L U c : ZFSet.{u}} (h : IsLocated L U) (hc : c ∈ L)
    (hc0 : ratLt ratZero.{u} c) {p : ZFSet.{u}}
    (hp : p ∈ mulLower L U (invLower U) (invUpper L)) : p ∈ ratCut ratOne.{u} := by
  obtain ⟨hpQ, q, hq, q', hq', r, hr, r', hr', c₁, c₂, c₃, c₄⟩ := (mem_sep_iff _ p _).mp hp
  obtain ⟨hrQ, s, hs, hrs⟩ := (mem_invLower_iff U r).mp hr
  obtain ⟨hr'Q, u, hu, hu0, hur'⟩ := (mem_invUpper_iff L r').mp hr'
  -- one point of the upper cut below both `s` and `q'`
  obtain ⟨t, ht, hts, htq'⟩ := upper_pair_bound h hs hq'
  have ht0 := upper_pos_of_witness h hc hc0 ht
  have htQ := h.upper_subset t ht
  have htne : t ≠ ratZero.{u} := ratNe_zero_of_pos ht0
  have hitQ := ratInv_mem_Rat htQ htne
  refine (mem_ratCut_iff _ _).mpr ⟨hpQ, ?_⟩
  have hcorner := ratLt_mul_of_corners hpQ (h.lower_subset q hq) (h.upper_subset q' hq')
    hrQ hr'Q htQ hitQ
    (h.ordered q hq t ht).left htq'
    -- `r ≤ t⁻¹`, since `r < s⁻¹ ≤ t⁻¹`
    (ratLt_of_lt_of_le hrQ (ratInv_mem_Rat (h.upper_subset s hs)
      (fun he => ratLt_irrefl (he ▸ upper_pos_of_witness h hc hc0 hs))) hitQ hrs
      (ratInv_le_ratInv htQ (h.upper_subset s hs) ht0 hts)).left
    -- `t⁻¹ ≤ r'`, since `t⁻¹ < u⁻¹ < r'` for `u` in the lower cut
    (ratLt_trans hitQ (ratInv_mem_Rat (h.lower_subset u hu)
      (ratNe_zero_of_pos hu0)) hr'Q
      (ratInv_lt_ratInv (h.lower_subset u hu) htQ hu0 (h.ordered u hu t ht)) hur').left
    c₁ c₂ c₃ c₄
  rwa [ratMul_inv htQ htne] at hcorner

/-- The mirror: the product of a positive real with its reciprocal lies above
one on the upper halves. -/
theorem mulUpper_inv_le {L U c : ZFSet.{u}} (h : IsLocated L U) (hc : c ∈ L)
    (hc0 : ratLt ratZero.{u} c) {p : ZFSet.{u}}
    (hp : p ∈ mulUpper L U (invLower U) (invUpper L)) :
    p ∈ sep (fun w => ratLt ratOne.{u} w) NumberTheory.Rat.{u} := by
  obtain ⟨hpQ, q, hq, q', hq', r, hr, r', hr', c₁, c₂, c₃, c₄⟩ := (mem_sep_iff _ p _).mp hp
  obtain ⟨hrQ, s, hs, hrs⟩ := (mem_invLower_iff U r).mp hr
  obtain ⟨hr'Q, u, hu, hu0, hur'⟩ := (mem_invUpper_iff L r').mp hr'
  -- one point of the upper cut below both `s` and `q'`
  obtain ⟨t, ht, hts, htq'⟩ := upper_pair_bound h hs hq'
  have ht0 := upper_pos_of_witness h hc hc0 ht
  have htQ := h.upper_subset t ht
  have htne : t ≠ ratZero.{u} := ratNe_zero_of_pos ht0
  have hitQ := ratInv_mem_Rat htQ htne
  refine (mem_sep_iff _ _ _).mpr ⟨hpQ, ?_⟩
  have hcorner := ratMul_lt_of_corners hpQ (h.lower_subset q hq) (h.upper_subset q' hq')
    hrQ hr'Q htQ hitQ
    (h.ordered q hq t ht).left htq'
    -- `r ≤ t⁻¹`, since `r < s⁻¹ ≤ t⁻¹`
    (ratLt_of_lt_of_le hrQ (ratInv_mem_Rat (h.upper_subset s hs)
      (fun he => ratLt_irrefl (he ▸ upper_pos_of_witness h hc hc0 hs))) hitQ hrs
      (ratInv_le_ratInv htQ (h.upper_subset s hs) ht0 hts)).left
    -- `t⁻¹ ≤ r'`, since `t⁻¹ < u⁻¹ < r'` for `u` in the lower cut
    (ratLt_trans hitQ (ratInv_mem_Rat (h.lower_subset u hu)
      (ratNe_zero_of_pos hu0)) hr'Q
      (ratInv_lt_ratInv (h.lower_subset u hu) htQ hu0 (h.ordered u hu t ht)) hur').left
    c₁ c₂ c₃ c₄
  rwa [ratMul_inv htQ htne] at hcorner

/-- Everything below one is in the product of a positive real with its
reciprocal. The bracket is chosen by `exists_bracket_width` so that its corner
`q/q'` already beats `p`; the reciprocal's bracket ends are then anything between
`p·q⁻¹` and `q'⁻¹`, and above `q⁻¹`. -/
theorem mulLower_inv_ge {L U c : ZFSet.{u}} (h : IsLocated L U) (hc : c ∈ L)
    (hc0 : ratLt ratZero.{u} c) {p : ZFSet.{u}} (hp : p ∈ ratCut ratOne.{u}) :
    p ∈ mulLower L U (invLower U) (invUpper L) := by
  obtain ⟨hpQ, hp1⟩ := (mem_ratCut_iff _ p).mp hp
  obtain ⟨s0, hs0⟩ := h.upper_inhabited
  have hs00 := upper_pos_of_witness h hc hc0 hs0
  rcases ratLe_total hpQ ratZero_mem_Rat with hple | hpge
  · -- `p ≤ 0` is below every product of positives
    have hs0Q := h.upper_subset s0 hs0
    have hs0ne : s0 ≠ ratZero.{u} := ratNe_zero_of_pos hs00
    obtain ⟨r, hrQ, hr0, hrs⟩ := rat_dense ratZero_mem_Rat
      (ratInv_mem_Rat hs0Q hs0ne) (ratInv_pos hs0Q hs00)
    obtain ⟨r', hr'Q, hr'⟩ := rat_no_greatest (ratInv_mem_Rat (h.lower_subset c hc)
      (ratNe_zero_of_pos hc0))
    have hr'0 : ratLt ratZero.{u} r' :=
      ratLt_trans ratZero_mem_Rat (ratInv_mem_Rat (h.lower_subset c hc)
        (ratNe_zero_of_pos hc0)) hr'Q (ratInv_pos (h.lower_subset c hc) hc0) hr'
    have pos : ∀ a b : ZFSet.{u}, a ∈ NumberTheory.Rat.{u} → b ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} a →
        ratLt ratZero.{u} b → ratLt p (ratMul a b) := by
      intro a b haQ hbQ ha0 hb0
      refine ratLt_of_le_of_lt hpQ ratZero_mem_Rat (ratMul_mem_Rat haQ hbQ) hple ?_
      have := ratMul_lt_mul_right ratZero_mem_Rat haQ hbQ
        (ratNe_zero_of_pos hb0) hb0.left ha0
      rwa [ratZero_mul hbQ] at this
    exact (mem_sep_iff _ p _).mpr ⟨hpQ, c, hc, s0, hs0,
      r, (mem_invLower_iff U r).mpr ⟨hrQ, s0, hs0, hrs⟩,
      r', (mem_invUpper_iff L r').mpr ⟨hr'Q, c, hc, hc0, hr'⟩,
      pos c r (h.lower_subset c hc) hrQ hc0 hr0,
      pos c r' (h.lower_subset c hc) hr'Q hc0 hr'0,
      pos s0 r hs0Q hrQ hs00 hr0, pos s0 r' hs0Q hr'Q hs00 hr'0⟩
  · -- `0 ≤ p < 1`: narrow the bracket until its corner beats `p`
    obtain ⟨e, heQ, he0, hwidth⟩ := exists_bracket_width hpQ (h.lower_subset c hc) hc0 hpge hp1
    obtain ⟨q0, hq0, s, hs, hqs⟩ := located_bracket h heQ he0
    obtain ⟨q, hq, hq0q, hcq⟩ := lower_pair_bound h hq0 hc
    have hqQ := h.lower_subset q hq
    have hsQ := h.upper_subset s hs
    have hq0' : ratLt ratZero.{u} q := ratLt_of_lt_of_le ratZero_mem_Rat
      (h.lower_subset c hc) hqQ hc0 hcq
    have hs0' := upper_pos_of_witness h hc hc0 hs
    have hqne : q ≠ ratZero.{u} := fun he => ratLt_irrefl (he ▸ hq0')
    have hsne : s ≠ ratZero.{u} := fun he => ratLt_irrefl (he ▸ hs0')
    have hps : ratLt (ratMul p s) q := hwidth q s hqQ hsQ hcq
      (ratLt_of_lt_of_le hsQ (ratAdd_mem_Rat (h.lower_subset q0 hq0) heQ)
        (ratAdd_mem_Rat hqQ heQ) hqs
        ((ratAdd_le_add_right_iff heQ (h.lower_subset q0 hq0) hqQ).mpr hq0q))
    -- `r` between `p·q⁻¹` and `s⁻¹`
    obtain ⟨r, hrQ, hpr, hrs⟩ := rat_dense (ratMul_mem_Rat hpQ (ratInv_mem_Rat hqQ hqne))
      (ratInv_mem_Rat hsQ hsne)
      (ratMul_inv_lt_inv hpQ hqQ hsQ hq0' hs0' hps)
    -- `r'` above `q⁻¹`
    obtain ⟨r', hr'Q, hqr'⟩ := rat_no_greatest (ratInv_mem_Rat hqQ hqne)
    have hqr : ratLt p (ratMul q r) := by
      have := ratMul_lt_mul_right (ratMul_mem_Rat hpQ (ratInv_mem_Rat hqQ hqne)) hrQ hqQ
        hqne hq0'.left hpr
      rwa [ratMul_comm (ratMul_mem_Rat hpQ (ratInv_mem_Rat hqQ hqne)) hqQ,
        ← ratMul_assoc hqQ hpQ (ratInv_mem_Rat hqQ hqne), ratMul_comm hqQ hpQ,
        ratMul_assoc hpQ hqQ (ratInv_mem_Rat hqQ hqne), ratMul_inv hqQ hqne,
        ratMul_one hpQ, ratMul_comm hrQ hqQ] at this
    have hr0 : ratLt ratZero.{u} r := by
      refine ratLt_of_le_of_lt ratZero_mem_Rat (ratMul_mem_Rat hpQ
        (ratInv_mem_Rat hqQ hqne)) hrQ ?_ hpr
      have := ratMul_le_mul_right ratZero_mem_Rat hpQ (ratInv_mem_Rat hqQ hqne) hpge
        (ratInv_pos hqQ hq0').left
      rwa [ratZero_mul (ratInv_mem_Rat hqQ hqne), ratMul_comm hpQ
        (ratInv_mem_Rat hqQ hqne), ratMul_comm (ratInv_mem_Rat hqQ hqne) hpQ] at this
    have hone : ∀ y, y ∈ NumberTheory.Rat.{u} → ratLt (ratInv q) y → ratLt p (ratMul q y) := by
      intro y hyQ hy
      refine ratLt_trans hpQ ratOne_mem_Rat (ratMul_mem_Rat hqQ hyQ) hp1 ?_
      have := ratMul_lt_mul_right (ratInv_mem_Rat hqQ hqne) hyQ hqQ hqne hq0'.left hy
      rwa [ratMul_comm (ratInv_mem_Rat hqQ hqne) hqQ, ratMul_inv hqQ hqne,
        ratMul_comm hyQ hqQ] at this
    have hmono : ∀ y, y ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} y → ratLt p (ratMul q y) →
        ratLt p (ratMul s y) := by
      intro y hyQ hy0 hqy
      refine ratLt_of_lt_of_le hpQ (ratMul_mem_Rat hqQ hyQ) (ratMul_mem_Rat hsQ hyQ) hqy ?_
      have := ratMul_le_mul_right hqQ hsQ hyQ (h.ordered q hq s hs).left hy0.left
      rwa [ratMul_comm hqQ hyQ, ratMul_comm hsQ hyQ, ratMul_comm hyQ hqQ,
        ratMul_comm hyQ hsQ] at this
    have hr'0 : ratLt ratZero.{u} r' :=
      ratLt_trans ratZero_mem_Rat (ratInv_mem_Rat hqQ hqne) hr'Q
        (ratInv_pos hqQ hq0') hqr'
    exact (mem_sep_iff _ p _).mpr ⟨hpQ, q, hq, s, hs,
      r, (mem_invLower_iff U r).mpr ⟨hrQ, s, hs, hrs⟩,
      r', (mem_invUpper_iff L r').mpr ⟨hr'Q, q, hq, hq0', hqr'⟩,
      hqr, hone r' hr'Q hqr', hmono r hrQ hr0 hqr,
      hmono r' hr'Q hr'0 (hone r' hr'Q hqr')⟩

/-- `x · x⁻¹ = 1` on the lower halves. -/
theorem mulLower_inv {L U c : ZFSet.{u}} (h : IsLocated L U) (hc : c ∈ L)
    (hc0 : ratLt ratZero.{u} c) :
    mulLower L U (invLower U) (invUpper L) = ratCut ratOne.{u} :=
  ext _ _ fun p => ⟨fun hp => mulLower_inv_le h hc hc0 hp,
    fun hp => mulLower_inv_ge h hc hc0 hp⟩

/-- Everything above one is in the upper half of the product. The bracket is
narrowed until `q' < p·q`, which is the room the reciprocal's upper end needs. -/
theorem mulUpper_inv_ge {L U c : ZFSet.{u}} (h : IsLocated L U) (hc : c ∈ L)
    (hc0 : ratLt ratZero.{u} c) {p : ZFSet.{u}}
    (hp : p ∈ sep (fun w => ratLt ratOne.{u} w) NumberTheory.Rat.{u}) :
    p ∈ mulUpper L U (invLower U) (invUpper L) := by
  obtain ⟨hpQ, hp1⟩ := (mem_sep_iff _ p _).mp hp
  obtain ⟨e, heQ, he0, hwidth⟩ := exists_bracket_width_gt hpQ (h.lower_subset c hc) hc0 hp1
  obtain ⟨q0, hq0, s, hs, hqs⟩ := located_bracket h heQ he0
  obtain ⟨q, hq, hq0q, hcq⟩ := lower_pair_bound h hq0 hc
  have hqQ := h.lower_subset q hq
  have hsQ := h.upper_subset s hs
  have hq0' : ratLt ratZero.{u} q :=
    ratLt_of_lt_of_le ratZero_mem_Rat (h.lower_subset c hc) hqQ hc0 hcq
  have hs0' := upper_pos_of_witness h hc hc0 hs
  have hqne : q ≠ ratZero.{u} := fun he => ratLt_irrefl (he ▸ hq0')
  have hsne : s ≠ ratZero.{u} := fun he => ratLt_irrefl (he ▸ hs0')
  have hps : ratLt s (ratMul p q) := hwidth q s hqQ hsQ hcq
    (ratLt_of_lt_of_le hsQ (ratAdd_mem_Rat (h.lower_subset q0 hq0) heQ)
      (ratAdd_mem_Rat hqQ heQ) hqs
      ((ratAdd_le_add_right_iff heQ (h.lower_subset q0 hq0) hqQ).mpr hq0q))
  -- `r'` between `q⁻¹` and `p·s⁻¹`
  obtain ⟨r', hr'Q, hqr', hr'p⟩ := rat_dense (ratInv_mem_Rat hqQ hqne)
    (ratMul_mem_Rat hpQ (ratInv_mem_Rat hsQ hsne))
    (ratInv_lt_mul_inv hpQ hqQ hsQ hq0' hs0' hps)
  -- `r` positive and below `s⁻¹`
  obtain ⟨r, hrQ, hr0, hrs⟩ := rat_dense ratZero_mem_Rat (ratInv_mem_Rat hsQ hsne)
    (ratInv_pos hsQ hs0')
  have hqs' : ratLe q s := (h.ordered q hq s hs).left
  -- `s·r' < p`, from `r' < p·s⁻¹`
  have hsr' : ratLt (ratMul s r') p := by
    have := ratMul_lt_mul_right hr'Q (ratMul_mem_Rat hpQ (ratInv_mem_Rat hsQ hsne)) hsQ
      hsne hs0'.left hr'p
    rwa [ratMul_comm hr'Q hsQ, ratMul_comm (ratMul_mem_Rat hpQ
      (ratInv_mem_Rat hsQ hsne)) hsQ, ← ratMul_assoc hsQ hpQ (ratInv_mem_Rat hsQ hsne),
      ratMul_comm hsQ hpQ, ratMul_assoc hpQ hsQ (ratInv_mem_Rat hsQ hsne),
      ratMul_inv hsQ hsne, ratMul_one hpQ] at this
  -- the `r` corners are below one, hence below `p`
  have hbelow : ∀ y, y ∈ NumberTheory.Rat.{u} → ratLe y s → ratLt (ratMul y r) p := by
    intro y hyQ hys
    refine ratLt_trans (ratMul_mem_Rat hyQ hrQ) ratOne_mem_Rat hpQ ?_ hp1
    refine ratLt_of_le_of_lt (ratMul_mem_Rat hyQ hrQ) (ratMul_mem_Rat hsQ hrQ)
      ratOne_mem_Rat ?_ ?_
    · have := ratMul_le_mul_right hyQ hsQ hrQ hys hr0.left
      rwa [ratMul_comm hyQ hrQ, ratMul_comm hsQ hrQ, ratMul_comm hrQ hyQ,
        ratMul_comm hrQ hsQ] at this
    · have := ratMul_lt_mul_right hrQ (ratInv_mem_Rat hsQ hsne) hsQ hsne hs0'.left hrs
      rwa [ratMul_comm hrQ hsQ, ratMul_comm (ratInv_mem_Rat hsQ hsne) hsQ,
        ratMul_inv hsQ hsne] at this
  exact (mem_sep_iff _ p _).mpr ⟨hpQ, q, hq, s, hs,
    r, (mem_invLower_iff U r).mpr ⟨hrQ, s, hs, hrs⟩,
    r', (mem_invUpper_iff L r').mpr ⟨hr'Q, q, hq, hq0', hqr'⟩,
    hbelow q hqQ hqs',
    -- `q·r' ≤ s·r' < p`
    (by
      refine ratLt_of_le_of_lt (ratMul_mem_Rat hqQ hr'Q) (ratMul_mem_Rat hsQ hr'Q) hpQ ?_ hsr'
      have hr'0 : ratLe ratZero.{u} r' :=
        (ratLt_trans ratZero_mem_Rat (ratInv_mem_Rat hqQ hqne) hr'Q
          (ratInv_pos hqQ hq0') hqr').left
      have := ratMul_le_mul_right hqQ hsQ hr'Q hqs' hr'0
      rwa [ratMul_comm hqQ hr'Q, ratMul_comm hsQ hr'Q, ratMul_comm hr'Q hqQ,
        ratMul_comm hr'Q hsQ] at this),
    hbelow s hsQ (ratLe_refl hsQ), hsr'⟩

/-- `x · x⁻¹ = 1` on the upper halves. -/
theorem mulUpper_inv {L U c : ZFSet.{u}} (h : IsLocated L U) (hc : c ∈ L)
    (hc0 : ratLt ratZero.{u} c) :
    mulUpper L U (invLower U) (invUpper L) = sep (fun w => ratLt ratOne.{u} w) NumberTheory.Rat.{u} :=
  ext _ _ fun p => ⟨fun hp => mulUpper_inv_le h hc hc0 hp,
    fun hp => mulUpper_inv_ge h hc hc0 hp⟩

/-- A positive located real times its reciprocal is one, constructively. -/
theorem realLMul_inv {z : ZFSet.{u}} (hz : z ∈ RealL.{u}) (h : realLLt realLZero.{u} z) :
    realLMul z (realLInv z) = realLOne.{u} := by
  obtain ⟨c, hcL, hc0⟩ := exists_pos_lower h
  obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff z).mp hz
  rw [fst_opair] at hcL
  rw [realLMul, realLInv, realLOne, realLOf]
  simp only [fst_opair, snd_opair]
  rw [mulLower_inv hloc hcL hc0, mulUpper_inv hloc hcL hc0]

/-- Negation reverses the order against zero: `z < 0` gives `0 < -z`. -/
theorem realLNeg_pos {z : ZFSet.{u}} (hz : z ∈ RealL.{u}) (h : realLLt z realLZero.{u}) :
    realLLt realLZero.{u} (realLNeg z) := by
  obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff z).mp hz
  obtain ⟨p, hpU, hp0⟩ := h
  rw [snd_opair] at hpU
  rw [realLZero, realLOf, fst_opair] at hp0
  obtain ⟨hpQ, hplt⟩ := (mem_ratCut_iff _ p).mp hp0
  -- `p < 0` lies in the upper cut, so `-p > 0` bounds the negation's lower cut
  have hnp0 : ratLt ratZero.{u} (ratNeg p) := by
    have := (ratNeg_lt_neg_iff ratZero_mem_Rat hpQ).mpr hplt
    rwa [ratNeg_zero] at this
  obtain ⟨q, hqQ, h0q, hqnp⟩ := rat_dense ratZero_mem_Rat (ratNeg_mem_Rat hpQ) hnp0
  refine ⟨q, ?_, ?_⟩
  · rw [realLZero, realLOf, snd_opair]
    exact (mem_sep_iff _ _ _).mpr ⟨hqQ, h0q⟩
  · rw [realLNeg, fst_opair, snd_opair]
    exact (mem_negLower_iff U q).mpr ⟨hqQ, p, hpU, hqnp⟩

/-- Zero is below one. A rational strictly between the two witnesses it,
which is `rat_dense`.

Stated here rather than as a branch of `realLApart_zero_one`: a consumer
needing the strict inequality cannot get it from the disjunction without
refuting the other side, which needs this. -/
theorem realLZero_lt_one : realLLt realLZero.{u} realLOne.{u} := by
  obtain ⟨t, htQ, h0t, ht1⟩ :=
    rat_dense ratZero_mem_Rat ratOne_mem_Rat ratZero_lt_one
  refine ⟨t, ?_, ?_⟩
  · rw [realLZero, realLOf, snd_opair]
    exact (mem_sep_iff _ _ _).mpr ⟨htQ, h0t⟩
  · rw [realLOne, realLOf, fst_opair]
    exact (mem_ratCut_iff _ _).mpr ⟨htQ, ht1⟩

#print axioms realLZero_lt_one

/-- `0` and `1` are apart, on the strict inequality above. -/
theorem realLApart_zero_one : realLApart realLZero.{u} realLOne.{u} :=
  Or.inl realLZero_lt_one

/-- Cotransitivity, and it is exactly the `located` field. Given `a < b`,
open the lower cut of `b` to get a strictly larger rational, then ask `c` which
side of the resulting gap it falls on -- which is the one question a located pair
can always answer. -/
theorem realLLt_cotrans {a b c : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (h : realLLt a b) : realLLt a c ∨ realLLt c b := by
  obtain ⟨La, Ua, rfl, hlocA⟩ := (mem_RealL_iff a).mp ha
  obtain ⟨Lb, Ub, rfl, hlocB⟩ := (mem_RealL_iff b).mp hb
  obtain ⟨Lc, Uc, rfl, hlocC⟩ := (mem_RealL_iff c).mp hc
  obtain ⟨p, hpU, hpL⟩ := h
  rw [snd_opair] at hpU
  rw [fst_opair] at hpL
  obtain ⟨p', hp'L, hpp'⟩ := hlocB.lower_open p hpL
  rcases hlocC.located p (hlocA.upper_subset p hpU) p' (hlocB.lower_subset p' hp'L) hpp'
    with hin | hin
  · exact Or.inl ⟨p, by rw [snd_opair]; exact hpU, by rw [fst_opair]; exact hin⟩
  · exact Or.inr ⟨p', by rw [snd_opair]; exact hin, by rw [fst_opair]; exact hp'L⟩

/-! ## The order against the operations

What ℂ's inverse needs: a sum of squares is positive when either summand is
apart from zero. The pieces are that a product of positives is positive, and
that a positive plus a non-negative is positive -- the second by cotransitivity,
which is where `realLApart_cotrans` earns its keep. -/

/-- A product of positives is positive. The least corner is the product of the
two lower witnesses, and everything else is larger. -/
theorem realLMul_pos {a b : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (h1 : realLLt realLZero.{u} a) (h2 : realLLt realLZero.{u} b) :
    realLLt realLZero.{u} (realLMul a b) := by
  obtain ⟨p, hpL, hp0⟩ := exists_pos_lower h1
  obtain ⟨q, hqL, hq0⟩ := exists_pos_lower h2
  obtain ⟨La, Ua, rfl, hlocA⟩ := (mem_RealL_iff a).mp ha
  obtain ⟨Lb, Ub, rfl, hlocB⟩ := (mem_RealL_iff b).mp hb
  rw [fst_opair] at hpL hqL
  obtain ⟨p', hp'⟩ := hlocA.upper_inhabited
  obtain ⟨q', hq'⟩ := hlocB.upper_inhabited
  have hpQ := hlocA.lower_subset p hpL
  have hqQ := hlocB.lower_subset q hqL
  have hp'Q := hlocA.upper_subset p' hp'
  have hq'Q := hlocB.upper_subset q' hq'
  have hp'0 := upper_pos_of_witness hlocA hpL hp0 hp'
  have hq'0 := upper_pos_of_witness hlocB hqL hq0 hq'
  have hpq0 : ratLt ratZero.{u} (ratMul p q) := by
    have := ratMul_lt_mul_right ratZero_mem_Rat hpQ hqQ
      (ratNe_zero_of_pos hq0) hq0.left hp0
    rwa [ratZero_mul hqQ] at this
  obtain ⟨t, htQ, h0t, htpq⟩ := rat_dense ratZero_mem_Rat (ratMul_mem_Rat hpQ hqQ) hpq0
  -- `p·q` is the least corner: the other factors only grow
  have grow : ∀ x y, x ∈ NumberTheory.Rat.{u} → y ∈ NumberTheory.Rat.{u} → ratLe p x → ratLe q y →
      ratLt t (ratMul x y) := by
    intro x y hxQ hyQ hpx hqy
    refine ratLt_of_lt_of_le htQ (ratMul_mem_Rat hpQ hqQ) (ratMul_mem_Rat hxQ hyQ) htpq ?_
    have s1 : ratLe (ratMul p q) (ratMul x q) := by
      have := ratMul_le_mul_right hpQ hxQ hqQ hpx hq0.left
      rwa [ratMul_comm hpQ hqQ, ratMul_comm hxQ hqQ, ratMul_comm hqQ hpQ,
        ratMul_comm hqQ hxQ] at this
    have s2 : ratLe (ratMul x q) (ratMul x y) := by
      have hx0 : ratLe ratZero.{u} x := (ratLt_of_lt_of_le ratZero_mem_Rat hpQ hxQ hp0 hpx).left
      have := ratMul_le_mul_right hqQ hyQ hxQ hqy hx0
      rwa [ratMul_comm hqQ hxQ, ratMul_comm hyQ hxQ] at this
    exact ratLe_trans (ratMul_mem_Rat hpQ hqQ) (ratMul_mem_Rat hxQ hqQ)
      (ratMul_mem_Rat hxQ hyQ) s1 s2
  refine ⟨t, ?_, ?_⟩
  · rw [realLZero, realLOf, snd_opair]
    exact (mem_sep_iff _ _ _).mpr ⟨htQ, h0t⟩
  · rw [realLMul]
    simp only [fst_opair, snd_opair]
    exact (mem_sep_iff _ t _).mpr ⟨htQ, p, hpL, p', hp', q, hqL, q', hq',
      grow p q hpQ hqQ (ratLe_refl hpQ) (ratLe_refl hqQ),
      grow p q' hpQ hq'Q (ratLe_refl hpQ) (hlocB.ordered q hqL q' hq').left,
      grow p' q hp'Q hqQ (hlocA.ordered p hpL p' hp').left (ratLe_refl hqQ),
      grow p' q' hp'Q hq'Q (hlocA.ordered p hpL p' hp').left
        (hlocB.ordered q hqL q' hq').left⟩

/-- `≤`, constructively: not strictly below. -/
def realLLe (a b : ZFSet.{u}) : Prop := ¬ realLLt b a

/-- A negative rational names a negative real. -/
theorem realLOf_lt_zero {c : ZFSet.{u}} (hc : c ∈ NumberTheory.Rat.{u}) (hc0 : ratLt c ratZero.{u}) :
    realLLt (realLOf c) realLZero.{u} := by
  obtain ⟨t, htQ, hct, ht0⟩ := rat_dense hc ratZero_mem_Rat hc0
  refine ⟨t, ?_, ?_⟩
  · rw [realLOf, snd_opair]
    exact (mem_sep_iff _ _ _).mpr ⟨htQ, hct⟩
  · rw [realLZero, realLOf, fst_opair]
    exact (mem_ratCut_iff _ _).mpr ⟨htQ, ht0⟩

/-- A negative is below anything non-negative -- by cotransitivity, not by
trichotomy, which is unavailable. -/
theorem realLLt_of_neg_of_nonneg {w y : ZFSet.{u}} (hw : w ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hw0 : realLLt w realLZero.{u})
    (hy0 : realLLe realLZero.{u} y) : realLLt w y := by
  rcases realLLt_cotrans hw realLZero_mem hy hw0 with h | h
  · exact h
  · exact absurd h hy0

/-- Shifting both sides by a real preserves the strict order. The witness for
`x < y` sits in `snd x ∩ fst y`; shifted, it needs a bracket for `z` narrower
than the room between the two, which is what `located_bracket` supplies. -/
theorem realLLt_add_right {x y z : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (hz : z ∈ RealL.{u}) (h : realLLt x y) :
    realLLt (realLAdd x z) (realLAdd y z) := by
  obtain ⟨Lx, Ux, rfl, hlx⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨Ly, Uy, rfl, hly⟩ := (mem_RealL_iff y).mp hy
  obtain ⟨Lz, Uz, rfl, hlz⟩ := (mem_RealL_iff z).mp hz
  obtain ⟨p, hpU, hpL⟩ := h
  rw [snd_opair] at hpU
  rw [fst_opair] at hpL
  obtain ⟨u, huU, hup⟩ := hlx.upper_open p hpU
  obtain ⟨l, hlL, hpl⟩ := hly.lower_open p hpL
  have huQ := hlx.upper_subset u huU
  have hlQ := hly.lower_subset l hlL
  have hpQ := hly.lower_subset p hpL
  have hul : ratLt u l := ratLt_trans huQ hpQ hlQ hup hpl
  have heQ : ratAdd l (ratNeg u) ∈ NumberTheory.Rat.{u} := ratAdd_mem_Rat hlQ (ratNeg_mem_Rat huQ)
  have he0 : ratLt ratZero.{u} (ratAdd l (ratNeg u)) := by
    have := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat huQ) huQ hlQ).mpr hul
    rwa [ratAdd_neg huQ] at this
  obtain ⟨lz, hlzL, uz, huzU, hbr⟩ := located_bracket hlz heQ he0
  have hlzQ := hlz.lower_subset lz hlzL
  have huzQ := hlz.upper_subset uz huzU
  have hkey : ratLt (ratAdd u uz) (ratAdd l lz) := by
    have hstep := (ratAdd_lt_add_left_iff huQ huzQ
      (ratAdd_mem_Rat hlzQ heQ)).mpr hbr
    have hre : ratAdd u (ratAdd lz (ratAdd l (ratNeg u))) = ratAdd l lz := by
      rw [← ratAdd_assoc hlzQ hlQ (ratNeg_mem_Rat huQ),
        ratAdd_comm (ratAdd_mem_Rat hlzQ hlQ) (ratNeg_mem_Rat huQ),
        ← ratAdd_assoc huQ (ratNeg_mem_Rat huQ) (ratAdd_mem_Rat hlzQ hlQ),
        ratAdd_neg huQ, ratZero_add (ratAdd_mem_Rat hlzQ hlQ),
        ratAdd_comm hlzQ hlQ]
    rwa [hre] at hstep
  obtain ⟨t, htQ, ht1, ht2⟩ := rat_dense (ratAdd_mem_Rat huQ huzQ)
    (ratAdd_mem_Rat hlQ hlzQ) hkey
  refine ⟨t, ?_, ?_⟩
  · rw [realLAdd, snd_opair, snd_opair, snd_opair]
    exact (mem_addUpper_iff _ _ _).mpr ⟨htQ, u, huU, uz, huzU, ht1⟩
  · rw [realLAdd, fst_opair, fst_opair, fst_opair]
    exact (mem_addLower_iff _ _ _).mpr ⟨htQ, l, hlL, lz, hlzL, ht2⟩

/-- Positive plus non-negative is positive. The lower witness `p` of `x`
gives `-p < 0 ≤ y`, so `y`'s lower cut reaches above `-p`, and the two lower
witnesses then sum to something positive. -/
theorem realLAdd_pos_of_nonneg {x y : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (hx0 : realLLt realLZero.{u} x) (hy0 : realLLe realLZero.{u} y) :
    realLLt realLZero.{u} (realLAdd x y) := by
  obtain ⟨p, hpL, hp0⟩ := exists_pos_lower hx0
  obtain ⟨Lx, Ux, rfl, hlocX⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨Ly, Uy, rfl, hlocY⟩ := (mem_RealL_iff y).mp hy
  rw [fst_opair] at hpL
  have hpQ := hlocX.lower_subset p hpL
  have hnp := ratNeg_mem_Rat hpQ
  have hnp0 : ratLt (ratNeg p) ratZero.{u} := by
    have := (ratNeg_lt_neg_iff hpQ ratZero_mem_Rat).mpr hp0
    rwa [ratNeg_zero] at this
  -- `-p < 0 ≤ y`, so some rational above `-p` sits in `y`'s lower cut
  obtain ⟨t, htU, htL⟩ := realLLt_of_neg_of_nonneg (realLOf_mem hnp)
    ((mem_RealL_iff _).mpr ⟨Ly, Uy, rfl, hlocY⟩) (realLOf_lt_zero hnp hnp0) hy0
  rw [realLOf, snd_opair] at htU
  rw [fst_opair] at htL
  obtain ⟨htQ, hnpt⟩ := (mem_sep_iff _ t _).mp htU
  -- `p + t > 0`
  have hsum0 : ratLt ratZero.{u} (ratAdd p t) := by
    have := (ratAdd_lt_add_left_iff hpQ hnp htQ).mpr hnpt
    rwa [ratAdd_neg hpQ] at this
  obtain ⟨s, hsQ, h0s, hspt⟩ := rat_dense ratZero_mem_Rat (ratAdd_mem_Rat hpQ htQ) hsum0
  refine ⟨s, ?_, ?_⟩
  · rw [realLZero, realLOf, snd_opair]
    exact (mem_sep_iff _ _ _).mpr ⟨hsQ, h0s⟩
  · rw [realLAdd]
    simp only [fst_opair, snd_opair]
    exact (mem_addLower_iff _ _ s).mpr ⟨hsQ, p, hpL, t, htL, hspt⟩

/-! ## The two reals

A located pair carries strictly more than a Dedekind cut, and the difference is
exactly `em`. Forgetting the upper half is a function `RealL → Real`, and it is
injective -- the upper half is recoverable, because `located` says a rational is
in it exactly when some smaller rational is outside the lower cut. Going back is
`cut_located`, which reverses to `em`. -/

/-- Forget the upper half. -/
def toCut (z : ZFSet.{u}) : ZFSet.{u} := fst z

/-- The upper half is determined by the lower. A rational is above the number
exactly when some smaller rational is not below it -- and it is `located` that
supplies the forward direction. -/
theorem upper_eq_of_lower {L U : ZFSet.{u}} (h : IsLocated L U) :
    U = sep (fun r => ∃ q, q ∈ NumberTheory.Rat.{u} ∧ ratLt q r ∧ q ∉ L) NumberTheory.Rat.{u} := by
  refine ext _ _ fun r => ⟨fun hr => ?_, fun hr => ?_⟩
  · obtain ⟨r', hr', hlt⟩ := h.upper_open r hr
    exact (mem_sep_iff _ _ _).mpr ⟨h.upper_subset r hr, r', h.upper_subset r' hr', hlt,
      fun hmem => ratLt_irrefl (h.ordered r' hmem r' hr')⟩
  · obtain ⟨hrQ, q, hqQ, hqr, hqL⟩ := (mem_sep_iff _ r _).mp hr
    rcases h.located q hqQ r hrQ hqr with hin | hin
    · exact absurd hin hqL
    · exact hin

/-- Forgetting the upper half is injective: the two reals agree on as much
as a cut can say, and `RealL` embeds in `Real`. -/
theorem toCut_injective {z w : ZFSet.{u}} (hz : z ∈ RealL.{u}) (hw : w ∈ RealL.{u})
    (h : toCut z = toCut w) : z = w := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff z).mp hz
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff w).mp hw
  rw [toCut, toCut, fst_opair, fst_opair] at h
  subst h
  rw [upper_eq_of_lower h₁, upper_eq_of_lower h₂]

/-- `realLOf` carries addition. Stated here, with the construction it is about,
rather than downstream where it was first needed. -/
theorem realLOf_add {a b : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u}) (hb : b ∈ NumberTheory.Rat.{u}) :
    realLOf (ratAdd a b) = realLAdd (realLOf a) (realLOf b) := by
  have hab := ratAdd_mem_Rat ha hb
  refine toCut_injective (realLOf_mem hab)
    (realLAdd_mem (realLOf_mem ha) (realLOf_mem hb)) ?_
  rw [toCut, toCut, realLOf, fst_opair, realLAdd, fst_opair, realLOf, realLOf,
    fst_opair, fst_opair]
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨hpQ, hlt⟩ := (mem_ratCut_iff _ p).mp hp
    -- a rational strictly between `p` and `a + b`, and then a split of it
    obtain ⟨t, htQ, hpt, htab⟩ := rat_dense hpQ hab hlt
    have hna := ratNeg_mem_Rat ha
    have hta : ratLt (ratAdd t (ratNeg a)) b := by
      have := (ratAdd_lt_add_right_iff hna htQ hab).mpr htab
      rwa [ratAdd_comm ha hb, ratAdd_assoc hb ha hna, ratAdd_neg ha,
        ratAdd_zero hb] at this
    obtain ⟨r, hrQ, hr1, hr2⟩ := rat_dense (ratAdd_mem_Rat htQ hna) hb hta
    have hnr := ratNeg_mem_Rat hrQ
    refine (mem_addLower_iff _ _ p).mpr ⟨hpQ, ratAdd t (ratNeg r), ?_, r, ?_, ?_⟩
    · refine (mem_ratCut_iff a _).mpr ⟨ratAdd_mem_Rat htQ hnr, ?_⟩
      -- `t - a < r` gives `t - r < a`, by adding `a - r` to both sides
      have hk := ratAdd_mem_Rat ha hnr
      have h1 := (ratAdd_lt_add_right_iff hk (ratAdd_mem_Rat htQ hna) hrQ).mpr hr1
      have hL : ratAdd (ratAdd t (ratNeg a)) (ratAdd a (ratNeg r))
          = ratAdd t (ratNeg r) := by
        rw [ratAdd_assoc htQ hna hk, ← ratAdd_assoc hna ha hnr,
          ratAdd_comm hna ha, ratAdd_neg ha, ratAdd_comm ratZero_mem_Rat hnr,
          ratAdd_zero hnr]
      have hR : ratAdd r (ratAdd a (ratNeg r)) = a := by
        rw [ratAdd_comm ha hnr, ← ratAdd_assoc hrQ hnr ha, ratAdd_neg hrQ,
          ratAdd_comm ratZero_mem_Rat ha, ratAdd_zero ha]
      rwa [hL, hR] at h1
    · exact (mem_ratCut_iff b r).mpr ⟨hrQ, hr2⟩
    · rw [ratAdd_assoc htQ hnr hrQ, ratAdd_comm hnr hrQ, ratAdd_neg hrQ,
        ratAdd_zero htQ]
      exact hpt
  · obtain ⟨hpQ, q, hq, r, hr, hlt⟩ := (mem_addLower_iff _ _ p).mp hp
    obtain ⟨hqQ, hqa⟩ := (mem_ratCut_iff a q).mp hq
    obtain ⟨hrQ, hrb⟩ := (mem_ratCut_iff b r).mp hr
    refine (mem_ratCut_iff _ p).mpr ⟨hpQ, ratLt_trans hpQ (ratAdd_mem_Rat hqQ hrQ)
      hab hlt ?_⟩
    exact ratAdd_lt_add hqQ ha hrQ hb hqa hrb

#print axioms Analysis.realLOf_add

/-! ## Audit -/


/-- Shifting is injective on the order, so the shift can be undone. -/
theorem realLLt_add_right_cancel {a b z : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hz : z ∈ RealL.{u})
    (h : realLLt (realLAdd a z) (realLAdd b z)) : realLLt a b := by
  have hn := realLNeg_mem hz
  have := realLLt_add_right (realLAdd_mem ha hz) (realLAdd_mem hb hz) hn h
  rwa [realLAdd_assoc ha hz hn, realLAdd_neg hz, realLAdd_zero ha,
    realLAdd_assoc hb hz hn, realLAdd_neg hz, realLAdd_zero hb] at this

/-- Negation reverses the order. Proved by shifting `a < b` along `-a + -b`,
which lands on `-b < -a` after the group law. -/
theorem realLNeg_lt_neg {a b : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (h : realLLt a b) : realLLt (realLNeg b) (realLNeg a) := by
  have hna := realLNeg_mem ha
  have hnb := realLNeg_mem hb
  have hs := realLAdd_mem hna hnb
  have := realLLt_add_right ha hb hs h
  rwa [← realLAdd_assoc ha hna hnb, realLAdd_neg ha, realLZero_add hnb, realLAdd_comm hna hnb, ← realLAdd_assoc hb hnb hna,
    realLAdd_neg hb, realLZero_add hna] at this

/-- `-(-a) = a`, from the group law rather than from the ring structure: the
ring instance lives in `Complex.lean`, which imports this file. -/
theorem realLNeg_realLNeg {a : ZFSet.{u}} (ha : a ∈ RealL.{u}) :
    realLNeg (realLNeg a) = a := by
  have hna := realLNeg_mem ha
  have hnna := realLNeg_mem hna
  have h : realLAdd a (realLAdd (realLNeg a) (realLNeg (realLNeg a)))
      = realLAdd a realLZero.{u} := by rw [realLAdd_neg hna]
  rw [← realLAdd_assoc ha hna hnna, realLAdd_neg ha,
    realLZero_add hnna,
    realLAdd_zero ha] at h
  exact h

/-- `≤` is transitive, and the proof is the shape every order argument here
takes: `realLLe` is a negation, so the only way to use two of them is to let
cotransitivity produce the two alternatives and refute each. -/
theorem realLLe_trans {a b c : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (hab : realLLe a b) (hbc : realLLe b c) : realLLe a c := by
  intro h
  rcases realLLt_cotrans hc ha hb h with h' | h'
  · exact hbc h'
  · exact hab h'

theorem realLLe_refl {a : ZFSet.{u}} (ha : a ∈ RealL.{u}) : realLLe a a :=
  realLLt_irrefl ha

theorem realLLe_of_lt {a b : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (h : realLLt a b) : realLLe a b :=
  fun hlt => realLLt_irrefl ha (realLLt_trans ha hb ha h hlt)

theorem realLLe_add_right {a b c : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hc : c ∈ RealL.{u}) (h : realLLe a b) :
    realLLe (realLAdd a c) (realLAdd b c) :=
  fun hlt => h (realLLt_add_right_cancel hb ha hc hlt)

/-! ### Antisymmetry

`realLLe` is a negation, so this is not a rewriting of the definition: it
descends to the cuts, and `realLLe_lower_subset` is where locatedness is spent --
the rung `(p, p')` inside the lower set has to fall one way or the other. -/

theorem realLLe_lower_subset {x y : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (h : realLLe x y) : fst x ⊆ fst y := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff y).mp hy
  intro p hp
  rw [fst_opair] at hp ⊢
  obtain ⟨p', hp', hlt⟩ := h₁.lower_open p hp
  rcases h₂.located p (h₁.lower_subset p hp) p' (h₁.lower_subset p' hp') hlt with hin | hin
  · exact hin
  · exact absurd ⟨p', by rw [snd_opair]; exact hin, by rw [fst_opair]; exact hp'⟩ h

theorem realLLe_antisymm {x y : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (hxy : realLLe x y) (hyx : realLLe y x) : x = y := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff y).mp hy
  obtain ⟨hL, hU⟩ := pairLe_antisymm h₁ h₂
    (fun w hw => by
      have := realLLe_lower_subset hx hy hxy w (by rw [fst_opair]; exact hw)
      rwa [fst_opair] at this)
    (fun w hw => by
      have := realLLe_lower_subset hy hx hyx w (by rw [fst_opair]; exact hw)
      rwa [fst_opair] at this)
  rw [hL, hU]

/-- Not apart is equal. A negative statement produces an equation, at
no principle: `realLApart` is a disjunction of strict inequalities, so denying
it denies both, and antisymmetry closes it.

Transferred from geometry, who derived it for `parallelDet_of_noMeet` and
deleted their copy once the naming rule placed it here -- the statement names
`realLApart`, `realLLe_antisymm` and `RealL`, and nothing geometric. -/
theorem realLApart_tight {x y : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (h : ¬ realLApart x y) : x = y :=
  realLLe_antisymm hx hy (fun hlt => h (Or.inr hlt)) (fun hlt => h (Or.inl hlt))

/-- Addition is cancellative on the right. -/
theorem realLAdd_right_cancel {u v a : ZFSet.{u}} (hu : u ∈ RealL.{u})
    (hv : v ∈ RealL.{u}) (ha : a ∈ RealL.{u})
    (h : realLAdd u a = realLAdd v a) : u = v := by
  have h1 : realLAdd (realLAdd u a) (realLNeg a) = u := by
    rw [realLAdd_assoc hu ha (realLNeg_mem ha), realLAdd_neg ha, realLAdd_zero hu]
  have h2 : realLAdd (realLAdd v a) (realLNeg a) = v := by
    rw [realLAdd_assoc hv ha (realLNeg_mem ha), realLAdd_neg ha, realLAdd_zero hv]
  rw [← h1, ← h2, h]

/-! ## Rationals against reals

The two orders meet here: a rational is below a located real exactly when it is
in the lower half. Both directions are one field of `IsLocated` -- `lower_down`
going in, `lower_open` coming out -- and the same for the upper half. Everything
that has to move between rational endpoints and real ones goes through these.
-/

theorem realLOf_lt_iff_mem_lower {x q : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hq : q ∈ NumberTheory.Rat.{u}) : realLLt (realLOf q) x ↔ q ∈ fst x := by
  obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff x).mp hx
  rw [fst_opair]
  constructor
  · rintro ⟨p, hpU, hpL⟩
    rw [realLOf, snd_opair] at hpU
    rw [fst_opair] at hpL
    exact hloc.lower_down p hpL q hq ((mem_sep_iff _ _ _).mp hpU).right
  · intro hqL
    obtain ⟨p, hpL, hqp⟩ := hloc.lower_open q hqL
    refine ⟨p, ?_, ?_⟩
    · rw [realLOf, snd_opair]
      exact (mem_sep_iff _ _ _).mpr ⟨hloc.lower_subset p hpL, hqp⟩
    · rw [fst_opair]
      exact hpL

theorem lt_realLOf_iff_mem_upper {x r : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hr : r ∈ NumberTheory.Rat.{u}) : realLLt x (realLOf r) ↔ r ∈ snd x := by
  obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff x).mp hx
  rw [snd_opair]
  constructor
  · rintro ⟨p, hpU, hpL⟩
    rw [snd_opair] at hpU
    rw [realLOf, fst_opair] at hpL
    exact hloc.upper_up p hpU r hr ((mem_ratCut_iff _ _).mp hpL).right
  · intro hrU
    obtain ⟨p, hpU, hpr⟩ := hloc.upper_open r hrU
    refine ⟨p, ?_, ?_⟩
    · rw [snd_opair]
      exact hpU
    · rw [realLOf, fst_opair]
      exact (mem_ratCut_iff _ _).mpr ⟨hloc.upper_subset p hpU, hpr⟩

/-- A located real is bracketed by rationals as tightly as asked: the bracket
lemma, read through the order rather than through membership. -/
theorem exists_rat_bracket {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) {ε : ZFSet.{u}}
    (hε : ε ∈ NumberTheory.Rat.{u}) (hε0 : ratLt ratZero.{u} ε) :
    ∃ p r, p ∈ NumberTheory.Rat.{u} ∧ r ∈ NumberTheory.Rat.{u} ∧ realLLt (realLOf p) x ∧
      realLLt x (realLOf r) ∧ ratLt r (ratAdd p ε) := by
  obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨p, hpL, r, hrU, hlt⟩ := located_bracket hloc hε hε0
  exact ⟨p, r, hloc.lower_subset p hpL, hloc.upper_subset r hrU,
    (realLOf_lt_iff_mem_lower (by exact (mem_RealL_iff _).mpr ⟨L, U, rfl, hloc⟩)
      (hloc.lower_subset p hpL)).mpr (by rw [fst_opair]; exact hpL),
    (lt_realLOf_iff_mem_upper (by exact (mem_RealL_iff _).mpr ⟨L, U, rfl, hloc⟩)
      (hloc.upper_subset r hrU)).mpr (by rw [snd_opair]; exact hrU),
    hlt⟩

/-! ## The smaller of two reals

`min` on located pairs is the intersection of the lower halves against the union
of the upper ones, and it is choice-free: `located` for the pair follows from the
two `located`s by cases on their disjunctions, never on a comparison of the two
numbers. Where a comparison is needed -- to inhabit the lower half, and to keep
it open -- it is a comparison of rationals, which `ratLt_trichotomy` decides.
-/

/-- The smaller of two located reals. -/
def realLMin (z w : ZFSet.{u}) : ZFSet.{u} :=
  opair (fst z ∩ fst w) (snd z ∪ snd w)

theorem realLMin_le_right {z w : ZFSet.{u}} (hw : w ∈ RealL.{u}) :
    realLLe (realLMin z w) w := by
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff w).mp hw
  rintro ⟨p, hpU, hpL⟩
  rw [snd_opair] at hpU
  rw [realLMin, fst_opair, fst_opair] at hpL
  exact ratLt_irrefl (h₂.ordered p ((mem_inter_iff _ _ _).mp hpL).right p hpU)

#print axioms isLocated_ratCut
#print axioms located_bracket        -- the point: no Classical.choice
#print axioms mem_upper_iff
#print axioms pairLe_antisymm
#print axioms isLocated_add
#print axioms isLocated_neg
#print axioms mul_located
#print axioms isLocated_mul
#print axioms realLAdd_mem
#print axioms realLNeg_mem
#print axioms realLMul_mem
#print axioms realLOf_mem
#print axioms realLZero_mem
#print axioms realLOne_mem
#print axioms realLAdd_comm
#print axioms addLower_assoc
#print axioms addUpper_assoc
#print axioms realLAdd_assoc
#print axioms addLower_zero
#print axioms addUpper_zero
#print axioms realLAdd_zero
#print axioms addLower_neg
#print axioms addUpper_neg
#print axioms realLAdd_neg

#print axioms mulLower_comm
#print axioms mulUpper_comm
#print axioms realLMul_comm
#print axioms lower_pair_bound
#print axioms upper_pair_bound
#print axioms corners_of_refinement
#print axioms mulLower_one
#print axioms mulUpper_one
#print axioms realLMul_one
#print axioms mulLower_zero
#print axioms mulUpper_zero
#print axioms realLMul_zero
#print axioms mulLower_const
#print axioms mulUpper_const
#print axioms mulLower_distrib_le
#print axioms located_eq_of_subset
#print axioms corners_of_refinement'
#print axioms mulUpper_distrib_le
#print axioms realLMul_distrib
#print axioms mulLower_assoc_le
#print axioms mulUpper_assoc_le
#print axioms realLMul_assoc
#print axioms realLSub_add_cancel
#print axioms realLLt_irrefl
#print axioms realLLt_trans
#print axioms realLLt_add_right
#print axioms realLOf_lt_iff_mem_lower
#print axioms lt_realLOf_iff_mem_upper
#print axioms exists_rat_bracket
#print axioms realLLe_trans
#print axioms realLLt_add_right_cancel
#print axioms realLNeg_lt_neg
#print axioms isLocated_inv
#print axioms realLInv_mem
#print axioms exists_pos_lower
#print axioms mulLower_inv_le
#print axioms mulLower_inv_ge
#print axioms mulLower_inv
#print axioms mulUpper_inv
#print axioms realLMul_inv
#print axioms realLNeg_pos
#print axioms realLApart_zero_one
#print axioms realLLt_cotrans
#print axioms realLMul_pos
#print axioms upper_eq_of_lower
#print axioms toCut_injective
/-- The larger of two located reals, dual to `realLMin`. -/
def realLMax (z w : ZFSet.{u}) : ZFSet.{u} :=
  opair (fst z ∪ fst w) (snd z ∩ snd w)

/-- The maximum of a finite list of located reals, above a seed. -/
def realLMaxList (seed : ZFSet.{u}) : List ZFSet.{u} → ZFSet.{u}
  | [] => seed
  | a :: as => realLMax a (realLMaxList seed as)

/-- The minimum of a finite list of located reals, below a seed. The mirror of
`realLMaxList`, and the shape a DISTANCE to a finite set of points takes. -/
def realLMinList (seed : ZFSet.{u}) : List ZFSet.{u} → ZFSet.{u}
  | [] => seed
  | a :: as => realLMin a (realLMinList seed as)

#print axioms Analysis.realLMinList
/-! ## Negation against multiplication, and the field structure's raw material

Proved from the group and distributive laws here, not transported from the
ring instance -- that instance lives in `Complex.lean`, which imports this
file. -/

/-- `a·(-b) = -(a·b)`. -/
theorem realLMul_neg {a b : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u}) :
    realLMul a (realLNeg b) = realLNeg (realLMul a b) := by
  have hnb := realLNeg_mem hb
  have hab := realLMul_mem ha hb
  refine realLAdd_right_cancel (realLMul_mem ha hnb) (realLNeg_mem hab) hab ?_
  rw [← realLMul_distrib ha hnb hb, realLAdd_comm hnb hb, realLAdd_neg hb,
    realLMul_zero ha, realLAdd_comm (realLNeg_mem hab) hab, realLAdd_neg hab]

/-- `(-a)·(-b) = a·b`. -/
theorem realLMul_neg_neg {a b : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u}) :
    realLMul (realLNeg a) (realLNeg b) = realLMul a b := by
  have hna := realLNeg_mem ha
  rw [realLMul_neg hna hb, realLMul_comm hna hb, realLMul_neg hb ha,
    realLNeg_realLNeg (realLMul_mem hb ha), realLMul_comm hb ha]

/-- Every real apart from zero has an inverse. The inverse cannot be a
single function of the apartness proof -- `realLApart` is a `Prop`-level
disjunction, and reading it as data is the move that costs choice.
Stated existentially it is fine: the goal is a `Prop`, so the
disjunction eliminates into it and each side supplies its own witness. -/
theorem realL_inverses {a : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (h : realLApart realLZero.{u} a) :
    ∃ b, b ∈ RealL.{u} ∧ realLMul a b = realLOne.{u} := by
  rcases h with hpos | hneg
  · exact ⟨realLInv a, realLInv_mem ha hpos, realLMul_inv ha hpos⟩
  · have hna := realLNeg_mem ha
    have hnpos := realLNeg_pos ha hneg
    refine ⟨realLNeg (realLInv (realLNeg a)),
      realLNeg_mem (realLInv_mem hna hnpos), ?_⟩
    have hstep := realLMul_neg_neg hna (realLInv (realLNeg a) |> fun _ =>
      realLInv_mem hna hnpos)
    rw [realLNeg_realLNeg ha] at hstep
    rw [hstep, realLMul_inv hna hnpos]

/-- A square is positive when its root is apart from zero. -/
theorem realLSq_pos {a : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (h : realLApart realLZero.{u} a) : realLLt realLZero.{u} (realLMul a a) := by
  rcases h with hpos | hneg
  · exact realLMul_pos ha ha hpos hpos
  · have hnpos := realLNeg_pos ha hneg
    have := realLMul_pos (realLNeg_mem ha) (realLNeg_mem ha) hnpos hnpos
    rwa [realLMul_neg_neg ha ha] at this

#print axioms realLMul_neg
#print axioms realLMul_neg_neg
#print axioms realL_inverses
#print axioms realLSq_pos

/-! ### The reciprocal, uniform in the sign

`realL_inverses` says a real apart from zero has an inverse. Nothing stronger
is available while the inverse is read off the apartness proof: `realLApart` is
a `Prop`-level disjunction, so a function of it would be a definition by cases
on an undecided alternative.

There is no need to read it. `x⁻¹ = x·(x²)⁻¹`, and `x²` is positive whenever
`x` is apart from zero, so the positive-witness inverse already built does the
work and the sign never has to be known. The construction is a term in `x` alone;
the apartness proof appears only in the membership lemma, where it is a `Prop`
hypothesis and eliminates freely. -/

/-- The reciprocal of a real apart from zero, as data rather than as an
existential: `x · (x·x)⁻¹`. -/
def realLInvApart (x : ZFSet.{u}) : ZFSet.{u} :=
  realLMul x (realLInv (realLMul x x))

theorem realLInvApart_mem {a : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (h : realLApart realLZero.{u} a) : realLInvApart a ∈ RealL.{u} :=
  realLMul_mem ha (realLInv_mem (realLMul_mem ha ha) (realLSq_pos ha h))

/-- And it is the reciprocal. One associativity: `a·(a·(a·a)⁻¹)` is
`(a·a)·(a·a)⁻¹`. -/
theorem realLMul_invApart {a : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (h : realLApart realLZero.{u} a) :
    realLMul a (realLInvApart a) = realLOne.{u} := by
  have hsq := realLMul_mem ha ha
  rw [realLInvApart, ← realLMul_assoc ha ha (realLInv_mem hsq (realLSq_pos ha h))]
  exact realLMul_inv hsq (realLSq_pos ha h)


#print axioms realLInvApart_mem
#print axioms realLMul_invApart
/-- The four-factor shuffle: `(x*y)*(z*w) = (x*z)*(y*w)`, from
associativity and commutativity. Stated directly on `realLMul` rather than
reached through `IsRing`, because the ring interface speaks in `opAt` over a
function graph and every consumer here holds Lean-level reals -- the same
reason `Integer.lean` carries `intMul_mul_comm` beside the generic
`ringMul_shuffle_pair`. Added after the geometry track wrote a local copy
for want of it. -/
theorem realLMul_shuffle_pair {x y z w : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hz : z ∈ RealL.{u}) (hw : w ∈ RealL.{u}) :
    realLMul (realLMul x y) (realLMul z w)
      = realLMul (realLMul x z) (realLMul y w) :=
  calc realLMul (realLMul x y) (realLMul z w)
      = realLMul x (realLMul y (realLMul z w)) :=
        realLMul_assoc hx hy (realLMul_mem hz hw)
    _ = realLMul x (realLMul (realLMul y z) w) := by
        rw [realLMul_assoc hy hz hw]
    _ = realLMul x (realLMul (realLMul z y) w) := by
        rw [realLMul_comm hy hz]
    _ = realLMul x (realLMul z (realLMul y w)) := by
        rw [realLMul_assoc hz hy hw]
    _ = realLMul (realLMul x z) (realLMul y w) :=
        (realLMul_assoc hx hz (realLMul_mem hy hw)).symm


#print axioms realLMul_shuffle_pair
/-! ## Rearrangements

Cancellations in the ring `RealL` rather than facts about cuts, and they belong
beside the laws they rearrange. They lived beside the derivative because that is where they were
first needed, which is the worst reason for a lemma to live anywhere: a track
that could not import that file could not use them, and two were rediscovered
from outside before the misfiling was visible from within. -/

theorem realLNeg_realLAdd {x y : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u}) :
    realLNeg (realLAdd x y) = realLAdd (realLNeg x) (realLNeg y) := by
  have hnx := realLNeg_mem hx
  have hny := realLNeg_mem hy
  refine realLAdd_right_cancel (realLNeg_mem (realLAdd_mem hx hy))
    (realLAdd_mem hnx hny) (realLAdd_mem hx hy) ?_
  rw [realLAdd_comm (realLNeg_mem (realLAdd_mem hx hy)) (realLAdd_mem hx hy),
    realLAdd_neg (realLAdd_mem hx hy), realLAdd_assoc hnx hny (realLAdd_mem hx hy),
    ← realLAdd_assoc hny hx hy, realLAdd_comm hny hx, realLAdd_assoc hx hny hy,
    realLAdd_comm hny hy, realLAdd_neg hy, realLAdd_zero hx,
    realLAdd_comm hnx hx, realLAdd_neg hx]
theorem realLAdd_mul {x y z : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (hz : z ∈ RealL.{u}) :
    realLMul (realLAdd x y) z = realLAdd (realLMul x z) (realLMul y z) := by
  rw [realLMul_comm (realLAdd_mem hx hy) hz, realLMul_distrib hz hx hy,
    realLMul_comm hz hx, realLMul_comm hz hy]
theorem realLNeg_realLMul {x y : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u}) :
    realLMul (realLNeg x) y = realLNeg (realLMul x y) := by
  have hnx := realLNeg_mem hx
  have hxy := realLMul_mem hx hy
  refine realLAdd_right_cancel (realLMul_mem hnx hy) (realLNeg_mem hxy) hxy ?_
  rw [realLAdd_comm (realLMul_mem hnx hy) hxy, ← realLAdd_mul hx hnx hy,
    realLAdd_neg hx, realLZero_mul hy,
    realLAdd_comm (realLNeg_mem hxy) hxy, realLAdd_neg hxy]
/-- The four-term additive shuffle -- `(A+B)+(C+D) = (A+C)+(B+D)`, the
additive partner of `realLMul_shuffle_pair`. Named for the algebraic
convention rather than the family convention; the word SHUFFLE is here so a search on the family's usual name finds
it too. -/
theorem realLAdd_interchange {A B C D : ZFSet.{u}} (hA : A ∈ RealL.{u})
    (hB : B ∈ RealL.{u}) (hC : C ∈ RealL.{u}) (hD : D ∈ RealL.{u}) :
    realLAdd (realLAdd A B) (realLAdd C D) = realLAdd (realLAdd A C) (realLAdd B D) := by
  rw [realLAdd_assoc hA hB (realLAdd_mem hC hD), ← realLAdd_assoc hB hC hD,
    realLAdd_comm hB hC, realLAdd_assoc hC hB hD,
    ← realLAdd_assoc hA hC (realLAdd_mem hB hD)]
/-! ## More rearrangements

The rest of the block whose first six moved earlier. `misfiled.py` names each
of these: none references anything from the file it sat in, so each belongs
here and each move typechecks by construction. -/

/-- `-(A - B) = B - A`. -/
theorem realLNeg_sub {A B : ZFSet.{u}} (hA : A ∈ RealL.{u}) (hB : B ∈ RealL.{u}) :
    realLNeg (realLAdd A (realLNeg B)) = realLAdd B (realLNeg A) := by
  rw [realLNeg_realLAdd hA (realLNeg_mem hB), realLNeg_realLNeg hB,
    realLAdd_comm (realLNeg_mem hA) hB]

/-- Strict order adds. -/
theorem realLLt_add {a b c d : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (hd : d ∈ RealL.{u}) (h₁ : realLLt a b) (h₂ : realLLt c d) :
    realLLt (realLAdd a c) (realLAdd b d) := by
  refine realLLt_trans (realLAdd_mem ha hc) (realLAdd_mem hb hc) (realLAdd_mem hb hd)
    (realLLt_add_right ha hb hc h₁) ?_
  have := realLLt_add_right hc hd hb h₂
  rwa [realLAdd_comm hc hb, realLAdd_comm hd hb] at this

/-- Doubling preserves apartness from zero -- the direction tightness needs. -/
theorem apart_add_self_of_apart {y : ZFSet.{u}} (hy : y ∈ RealL.{u})
    (h : realLApart realLZero.{u} y) :
    realLApart realLZero.{u} (realLAdd y y) := by
  have h0 : realLAdd realLZero.{u} realLZero.{u} = realLZero.{u} :=
    realLAdd_zero realLZero_mem
  rcases h with hlt | hlt
  · exact Or.inl (by
      have := realLLt_add realLZero_mem hy realLZero_mem hy hlt hlt
      rwa [h0] at this)
  · exact Or.inr (by
      have := realLLt_add hy realLZero_mem hy realLZero_mem hlt hlt
      rwa [h0] at this)

/-- A doubled real that vanishes was already zero. Apartness is tight, so
refuting the apartness IS the equality. -/
theorem eq_zero_of_add_self_eq_zero {y : ZFSet.{u}} (hy : y ∈ RealL.{u})
    (h : realLAdd y y = realLZero.{u}) : y = realLZero.{u} := by
  have hnap : ¬ realLApart realLZero.{u} y := fun hz =>
    realLApart_irrefl realLZero_mem (h ▸ apart_add_self_of_apart hy hz)
  exact realLLe_antisymm hy realLZero_mem
    (fun hlt => hnap (Or.inl hlt)) (fun hlt => hnap (Or.inr hlt))

/-- Mixed transitivity, one way. `realLLe` carries no witness, so this is not a
rearrangement of the definitions: cotransitivity supplies the witness and the
weak hypothesis refutes the wrong branch. -/
theorem realLLt_of_le_of_lt {a b c : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (hab : realLLe a b) (hbc : realLLt b c) : realLLt a c := by
  rcases realLLt_cotrans hb hc ha hbc with h | h
  · exact absurd h hab
  · exact h

/-- Mixed transitivity, the other way. -/
theorem realLLt_of_lt_of_le {a b c : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (hab : realLLt a b) (hbc : realLLe b c) : realLLt a c := by
  rcases realLLt_cotrans ha hb hc hab with h | h
  · exact h
  · exact absurd h hbc

/-! ### Located-reals algebra placed from the geometry files

Eight lemmas that mention no geometry, moved here under geometry's 3164/3200.
They sat in the geometry files because that is
where they were first needed; `misfiled.py` scored the first five at +13 toward
this file, and `realLApart` is defined here, so the apartness three belong here
by dependency and not merely by vocabulary. -/

/-- `0 < r` turns into `-r < 0` by shifting the whole inequality, which is what
`realLLt_add_right` is for. -/
theorem realLNeg_neg_of_pos {r : ZFSet.{u}} (hr : r ∈ RealL.{u})
    (h : realLLt realLZero.{u} r) : realLLt (realLNeg r) realLZero.{u} := by
  have := realLLt_add_right realLZero_mem hr (realLNeg_mem hr) h
  rwa [realLAdd_comm realLZero_mem (realLNeg_mem hr),
    realLAdd_zero (realLNeg_mem hr), realLAdd_neg hr] at this

/-- A product of two reals apart from zero is apart from zero, by the four
sign cases. Each case is `realLMul_pos` on suitably negated arguments, so
nothing is decided that the two apartnesses did not already supply. -/
theorem apart_mul_apart {x y : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hxa : realLApart realLZero.{u} x)
    (hya : realLApart realLZero.{u} y) :
    realLApart realLZero.{u} (realLMul x y) := by
  have hnx := realLNeg_mem hx
  have hny := realLNeg_mem hy
  rcases hxa with hxp | hxn
  · rcases hya with hyp | hyn
    · exact Or.inl (realLMul_pos hx hy hxp hyp)
    · refine Or.inr ?_
      have h := realLMul_pos hx hny hxp (realLNeg_pos hy hyn)
      rw [realLMul_neg hx hy] at h
      have := realLNeg_neg_of_pos (realLNeg_mem (realLMul_mem hx hy)) h
      rwa [realLNeg_realLNeg (realLMul_mem hx hy)] at this
  · rcases hya with hyp | hyn
    · refine Or.inr ?_
      have h := realLMul_pos hnx hy (realLNeg_pos hx hxn) hyp
      rw [realLNeg_realLMul hx hy] at h
      have := realLNeg_neg_of_pos (realLNeg_mem (realLMul_mem hx hy)) h
      rwa [realLNeg_realLNeg (realLMul_mem hx hy)] at this
    · refine Or.inl ?_
      have h := realLMul_pos hnx hny (realLNeg_pos hx hxn) (realLNeg_pos hy hyn)
      rwa [realLMul_neg_neg hx hy] at h

#print axioms Analysis.realLLe_antisymm
#print axioms Analysis.realLApart_tight
#print axioms Analysis.LocatedReadout
#print axioms Analysis.realLNeg_realLAdd
#print axioms Analysis.realLAdd_mul
#print axioms Analysis.realLNeg_realLMul
#print axioms Analysis.realLAdd_interchange
#print axioms Analysis.realLNeg_sub
#print axioms Analysis.realLLt_of_lt_of_le
#print axioms Analysis.realLLt_of_le_of_lt
#print axioms Analysis.realLLt_add
#print axioms Analysis.apart_add_self_of_apart
#print axioms Analysis.eq_zero_of_add_self_eq_zero
#print axioms Analysis.realLLe_refl
#print axioms Analysis.realLLe_of_lt
#print axioms Analysis.realLLe_add_right
/-- The weak order adds.

Supersedes `realLAdd_le_add`, which stated the same thing; do not add new uses
of that name. A branch that has not merged the supersession still defines both,
and a use written there is correct on that branch and breaks at the merge -- so
the marker belongs here, where a proof is being written, rather than only in
`lost-allow.txt`. -/
theorem realLLe_add {a b c d : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (hd : d ∈ RealL.{u}) (h₁ : realLLe a b) (h₂ : realLLe c d) :
    realLLe (realLAdd a c) (realLAdd b d) := by
  refine realLLe_trans (realLAdd_mem ha hc) (realLAdd_mem hb hc) (realLAdd_mem hb hd)
    (realLLe_add_right ha hb hc h₁) ?_
  have := realLLe_add_right hc hd hb h₂
  rwa [realLAdd_comm hc hb, realLAdd_comm hd hb] at this

/-- Moving a summand across `≤`, in the one direction the bracket needs. -/
theorem realLLe_neg_of_le_add {a e : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (he : e ∈ RealL.{u}) (h : realLLe realLZero.{u} (realLAdd a e)) :
    realLLe (realLNeg e) a := by
  have hne := realLNeg_mem he
  have := realLLe_add_right realLZero_mem (realLAdd_mem ha he) hne h
  rwa [realLZero_add hne,
    realLAdd_assoc ha he hne, realLAdd_neg he, realLAdd_zero ha] at this


/-! ## The interval, and a modulus

`Metric.lean` has the open interval; the intermediate value theorem wants the
closed one, because the endpoints are where the sign change lives. -/
/-- Reading `-a < -b` forwards, which `realLNeg_lt_neg` and double negation
together allow. -/
theorem realLLt_of_neg_lt_neg {a b : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (h : realLLt (realLNeg a) (realLNeg b)) :
    realLLt b a := by
  have := realLNeg_lt_neg (realLNeg_mem ha) (realLNeg_mem hb) h
  rwa [realLNeg_realLNeg ha, realLNeg_realLNeg hb] at this
/-- The embedding is an order embedding. -/
theorem realLOf_lt_realLOf {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) :
    realLLt (realLOf p) (realLOf q) ↔ ratLt p q := by
  refine Iff.trans (realLOf_lt_iff_mem_lower (realLOf_mem hq) hp) ?_
  rw [realLOf, fst_opair]
  exact Iff.trans (mem_ratCut_iff q p) ⟨And.right, fun h => ⟨hp, h⟩⟩
/-- The order on rationals, read through the embedding. -/
theorem realLOf_le_realLOf {a b : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u}) (hb : b ∈ NumberTheory.Rat.{u}) :
    realLLe (realLOf a) (realLOf b) ↔ ratLe a b := by
  constructor
  · intro h
    rcases ratLt_trichotomy ha hb with hlt | he | hgt
    · exact hlt.left
    · exact he ▸ ratLe_refl ha
    · exact absurd ((realLOf_lt_realLOf hb ha).mpr hgt) h
  · intro h hlt
    exact ratLt_irrefl (ratLt_of_le_of_lt ha hb ha h ((realLOf_lt_realLOf hb ha).mp hlt))


/-! ## Differentiability on an interval

Nothing about the slope function is asked for in the definition. Where a bound
on it is needed the bound is a hypothesis, because a supremum over an interval
is exactly the thing a constructive development cannot help itself to. -/
theorem realLNeg_le_neg {a b : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (h : realLLe a b) : realLLe (realLNeg b) (realLNeg a) :=
  fun hlt => h (realLLt_of_neg_lt_neg ha hb hlt)
/-- `|z| ≤ ε`, spelled as the bracket it is. -/
def WithinOf (z ε : ZFSet.{u}) : Prop :=
  realLLe (realLNeg ε) z ∧ realLLe z ε

/-- `x` and `y` are within `δ` of each other. -/
def Close (x y δ : ZFSet.{u}) : Prop := WithinOf (realLAdd x (realLNeg y)) δ

theorem sq_sum {u v : ZFSet.{u}} (hu : u ∈ RealL.{u}) (hv : v ∈ RealL.{u}) :
    realLMul (realLAdd u v) (realLAdd u v)
      = realLAdd (realLAdd (realLMul u u) (realLMul v v))
          (realLAdd (realLMul u v) (realLMul u v)) := by
  have huv := realLMul_mem hu hv
  rw [realLAdd_mul hu hv (realLAdd_mem hu hv), realLMul_distrib hu hu hv,
    realLMul_distrib hv hu hv, realLMul_comm hv hu,
    realLAdd_comm huv (realLMul_mem hv hv)]
  exact realLAdd_interchange (realLMul_mem hu hu) huv (realLMul_mem hv hv) huv

/-- `(z + m) - z = m`. -/
theorem shift_sub {z m : ZFSet.{u}} (hz : z ∈ RealL.{u}) (hm : m ∈ RealL.{u}) :
    realLAdd (realLAdd z m) (realLNeg z) = m := by
  rw [realLAdd_comm hz hm, realLAdd_assoc hm hz (realLNeg_mem hz), realLAdd_neg hz,
    realLAdd_zero hm]

#print axioms sq_sum
#print axioms shift_sub
#print axioms Analysis.realLNeg_neg_of_pos
#print axioms Analysis.apart_mul_apart

#print axioms Analysis.realLLe_add
#print axioms Analysis.realLLe_neg_of_le_add
#print axioms Analysis.realLLt_of_neg_lt_neg
#print axioms Analysis.realLZero_add
#print axioms Analysis.realLOne_mul
#print axioms Analysis.realLZero_mul
#print axioms Analysis.realLOf_lt_realLOf
#print axioms Analysis.realLOf_le_realLOf
#print axioms Analysis.realLNeg_le_neg
#print axioms Analysis.WithinOf
#print axioms Analysis.Close
#print axioms Analysis.BoundedLocated
end Analysis





namespace ZFSet
export Analysis (BoundedLocated Close IsLocated LocatedReadout RealL WithinOf addLower addLower_assoc addLower_comm addLower_neg addLower_zero addUpper addUpper_assoc addUpper_comm addUpper_neg addUpper_zero apart_add_self_of_apart apart_mul_apart corners_of_refinement corners_of_refinement' eq_zero_of_add_self_eq_zero exists_pos_lower exists_rat_bracket invLower invScale invScale_mem invUpper isLocated_add isLocated_inv isLocated_mul isLocated_mul_of_located isLocated_neg isLocated_ratCut located_bracket located_eq_of_subset lower_pair_bound lt_realLOf_iff_mem_upper mem_RealL_iff mem_addLower_iff mem_addUpper_iff mem_invLower_iff mem_invUpper_iff mem_mulLower_iff mem_mulUpper_iff mem_negLower_iff mem_negUpper_iff mem_upper_iff mulLower mulLower_assoc_le mulLower_comm mulLower_const mulLower_distrib_le mulLower_inv mulLower_inv_ge mulLower_inv_le mulLower_one mulLower_zero mulUpper mulUpper_assoc_le mulUpper_comm mulUpper_const mulUpper_distrib_le mulUpper_inv mulUpper_inv_ge mulUpper_inv_le mulUpper_one mulUpper_zero mul_located negLower negUpper pairLe pairLe_antisymm realLAdd realLAdd_assoc realLAdd_comm realLAdd_interchange realLAdd_mem realLAdd_mul realLAdd_neg realLAdd_pos_of_nonneg realLAdd_right_cancel realLAdd_zero realLApart realLApart_irrefl realLApart_symm realLApart_tight realLApart_zero_one realLInv realLInvApart realLInvApart_mem realLInv_mem realLLe realLLe_add realLLe_add_right realLLe_antisymm realLLe_lower_subset realLLe_neg_of_le_add realLLe_of_lt realLLe_refl realLLe_trans realLLt realLLt_add realLLt_add_right realLLt_add_right_cancel realLLt_cotrans realLLt_irrefl realLLt_of_le_of_lt realLLt_of_lt_of_le realLLt_of_neg_lt_neg realLLt_of_neg_of_nonneg realLLt_trans realLMax realLMaxList realLMin realLMinList realLMin_le_right realLMul realLMul_assoc realLMul_comm realLMul_distrib realLMul_inv realLMul_invApart realLMul_mem realLMul_neg realLMul_neg_neg realLMul_one realLMul_pos realLMul_shuffle_pair realLMul_zero realLNeg realLNeg_le_neg realLNeg_lt_neg realLNeg_mem realLNeg_neg_of_pos realLNeg_pos realLNeg_realLAdd realLNeg_realLMul realLNeg_realLNeg realLNeg_sub realLOf realLOf_add realLOf_le_realLOf realLOf_lt_iff_mem_lower realLOf_lt_realLOf realLOf_lt_zero realLOf_mem realLOne realLOne_mem realLOne_mul realLSq_pos realLSub_add_cancel realLZero realLZero_add realLZero_lt_one realLZero_mem realLZero_mul realL_inverses shift_sub sq_sum toCut toCut_injective upper_eq_of_lower upper_eq_of_lower_eq upper_pair_bound upper_pos_of_witness)
end ZFSet
