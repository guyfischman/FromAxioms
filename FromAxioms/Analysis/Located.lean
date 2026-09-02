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
#print axioms Analysis.LocatedReadout
#print axioms Analysis.realLZero_add
#print axioms Analysis.realLOne_mul
#print axioms Analysis.realLZero_mul
#print axioms Analysis.BoundedLocated
end Analysis





namespace ZFSet
export Analysis (BoundedLocated IsLocated LocatedReadout RealL addLower addLower_assoc addLower_comm addLower_neg addLower_zero addUpper addUpper_assoc addUpper_comm addUpper_neg addUpper_zero corners_of_refinement corners_of_refinement' invScale invScale_mem isLocated_add isLocated_mul isLocated_mul_of_located isLocated_neg isLocated_ratCut located_bracket located_eq_of_subset lower_pair_bound mem_RealL_iff mem_addLower_iff mem_addUpper_iff mem_mulLower_iff mem_mulUpper_iff mem_negLower_iff mem_negUpper_iff mem_upper_iff mulLower mulLower_assoc_le mulLower_comm mulLower_const mulLower_distrib_le mulLower_one mulLower_zero mulUpper mulUpper_comm mulUpper_const mulUpper_distrib_le mulUpper_one mulUpper_zero mul_located negLower negUpper pairLe pairLe_antisymm realLAdd realLAdd_assoc realLAdd_comm realLAdd_mem realLAdd_neg realLAdd_zero realLMul realLMul_comm realLMul_distrib realLMul_mem realLMul_one realLMul_zero realLNeg realLNeg_mem realLOf realLOf_mem realLOne realLOne_mem realLOne_mul realLZero realLZero_add realLZero_mem realLZero_mul upper_eq_of_lower_eq upper_pair_bound)
end ZFSet
