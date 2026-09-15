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

/-! ## Locatedness, constructively

The same ladder as `cut_located`, and the same walk up it. The difference is the
step: there, `by_cases` on whether the rung is still inside the cut; here, the
`located` field applied to two consecutive rungs. The bracket it produces spans
two rungs rather than one, so the ladder is built over `2b` and a
bracket of `2/(2b) = 1/b` still fits inside `ε`. -/

/-- The grid from `q` in steps of `d`. A plain `Nat` recursion: no choice,
and no decision at any step. -/
def gridPt (q d : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => q
  | k + 1 => ratAdd (gridPt q d k) d

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


/-- The bracket in width form: `r < q + ε` restated as `r - q < ε`.

Named because a cover's total is compared in that shape. -/
theorem located_bracket_width {L U ε : ZFSet.{u}} (h : IsLocated L U)
    (hεQ : ε ∈ NumberTheory.Rat.{u}) (hε : ratLt ratZero.{u} ε) :
    ∃ q r, q ∈ L ∧ r ∈ U ∧ ratLt (ratAdd r (ratNeg q)) ε := by
  obtain ⟨q, hq, r, hr, hlt⟩ := located_bracket h hεQ hε
  have hqQ := h.lower_subset _ hq
  have hrQ := h.upper_subset _ hr
  refine ⟨q, r, hq, hr, ?_⟩
  have hstep := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat hqQ) hrQ
    (ratAdd_mem_Rat hqQ hεQ)).mpr hlt
  rwa [ratAdd_comm hqQ hεQ, ratAdd_assoc hεQ hqQ (ratNeg_mem_Rat hqQ),
    ratAdd_neg hqQ, ratAdd_zero hεQ] at hstep

/-! ## The payoff -/

theorem lower_mem_Real {L U : ZFSet.{u}} (h : IsLocated L U) : L ∈ Real.{u} := by
  obtain ⟨r, hr⟩ := h.upper_inhabited
  exact (mem_Real_iff L).mpr
    ⟨h.lower_subset, h.lower_inhabited,
     ⟨r, h.upper_subset r hr, fun hmem => ratLt_irrefl (h.ordered r hmem r hr)⟩,
     h.lower_down, h.lower_open⟩

theorem located_of_isLocated {L U : ZFSet.{u}} (h : IsLocated L U) : Located L := by
  intro ε hεQ hε
  obtain ⟨q, hq, r, hr, hlt⟩ := located_bracket h hεQ hε
  exact ⟨q, hq, r, h.upper_subset r hr,
    fun hmem => ratLt_irrefl (h.ordered r hmem r hr), hlt⟩

/-! ## Completeness, for located families

`em_of_sup_located` showed that suprema of arbitrary bounded families cannot
be located: the family `{0} ∪ {1 | p}` is not itself located, and asking for its
supremum is asking to decide `p`. The constructive statement puts that condition
where it belongs -- on the family:

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

theorem isLocated_of_mem_RealL {z L U : ZFSet.{u}} (hz : z ∈ RealL.{u})
    (he : z = opair L U) : IsLocated L U := by
  obtain ⟨L', U', he', hloc⟩ := (mem_RealL_iff z).mp hz
  obtain ⟨rfl, rfl⟩ := opair_injective (he.symm.trans he')
  exact hloc

def supLower (S : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ z, z ∈ S ∧ ∃ L U, z = opair L U ∧ p ∈ L) NumberTheory.Rat.{u}

def supUpper (S : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun r => ∃ p, p ∈ NumberTheory.Rat.{u} ∧ ratLt p r ∧
        ∀ z, z ∈ S → ∀ L U, z = opair L U → p ∈ U) NumberTheory.Rat.{u}

theorem mem_supLower_iff (S p : ZFSet.{u}) :
    p ∈ supLower S ↔ p ∈ NumberTheory.Rat.{u} ∧ ∃ z, z ∈ S ∧ ∃ L U, z = opair L U ∧ p ∈ L :=
  mem_sep_iff _ _ _

theorem mem_supUpper_iff (S r : ZFSet.{u}) :
    r ∈ supUpper S ↔ r ∈ NumberTheory.Rat.{u} ∧ ∃ p, p ∈ NumberTheory.Rat.{u} ∧ ratLt p r ∧
      ∀ z, z ∈ S → ∀ L U, z = opair L U → p ∈ U :=
  mem_sep_iff _ _ _

/-- A family is located when every rational interval is decided: some member
reaches above the left end, or all of them stay below the right end. -/
def FamilyLocated (S : ZFSet.{u}) : Prop :=
  ∀ p, p ∈ NumberTheory.Rat.{u} → ∀ q, q ∈ NumberTheory.Rat.{u} → ratLt p q →
    (∃ z, z ∈ S ∧ ∃ L U, z = opair L U ∧ p ∈ L) ∨
    (∀ z, z ∈ S → ∀ L U, z = opair L U → q ∈ U)

theorem isLocated_sup_of_familyLocated {S : ZFSet.{u}} (hS : S ⊆ RealL.{u}) (hne : ∃ z, z ∈ S)
    (hbd : ∃ r, r ∈ NumberTheory.Rat.{u} ∧ ∀ z, z ∈ S → ∀ L U, z = opair L U → r ∈ U)
    (hfam : FamilyLocated S) : IsLocated (supLower S) (supUpper S) where
  lower_subset p hp := ((mem_supLower_iff S p).mp hp).left
  upper_subset r hr := ((mem_supUpper_iff S r).mp hr).left
  lower_inhabited := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff z).mp (hS z hz)
    obtain ⟨q, hq⟩ := hloc.lower_inhabited
    exact ⟨q, (mem_supLower_iff S q).mpr
      ⟨hloc.lower_subset q hq, _, hz, L, U, rfl, hq⟩⟩
  upper_inhabited := by
    obtain ⟨r₀, hr₀Q, hall⟩ := hbd
    obtain ⟨r, hrQ, hlt⟩ := rat_no_greatest hr₀Q
    exact ⟨r, (mem_supUpper_iff S r).mpr ⟨hrQ, r₀, hr₀Q, hlt, hall⟩⟩
  ordered q hq r hr := by
    obtain ⟨hqQ, z, hz, L, U, he, hqL⟩ := (mem_supLower_iff S q).mp hq
    obtain ⟨hrQ, p, hpQ, hpr, hall⟩ := (mem_supUpper_iff S r).mp hr
    have hloc := isLocated_of_mem_RealL (hS z hz) he
    exact ratLt_trans hqQ hpQ hrQ (hloc.ordered q hqL p (hall z hz L U he)) hpr
  lower_down q hq p hpQ hlt := by
    obtain ⟨-, z, hz, L, U, he, hqL⟩ := (mem_supLower_iff S q).mp hq
    have hloc := isLocated_of_mem_RealL (hS z hz) he
    exact (mem_supLower_iff S p).mpr ⟨hpQ, z, hz, L, U, he, hloc.lower_down q hqL p hpQ hlt⟩
  upper_up r hr p hpQ hlt := by
    obtain ⟨hrQ, t, htQ, htr, hall⟩ := (mem_supUpper_iff S r).mp hr
    exact (mem_supUpper_iff S p).mpr ⟨hpQ, t, htQ, ratLt_trans htQ hrQ hpQ htr hlt, hall⟩
  lower_open q hq := by
    obtain ⟨-, z, hz, L, U, he, hqL⟩ := (mem_supLower_iff S q).mp hq
    have hloc := isLocated_of_mem_RealL (hS z hz) he
    obtain ⟨q', hq'L, hlt⟩ := hloc.lower_open q hqL
    exact ⟨q', (mem_supLower_iff S q').mpr
      ⟨hloc.lower_subset q' hq'L, z, hz, L, U, he, hq'L⟩, hlt⟩
  upper_open r hr := by
    obtain ⟨hrQ, p, hpQ, hpr, hall⟩ := (mem_supUpper_iff S r).mp hr
    obtain ⟨t, htQ, h₁, h₂⟩ := rat_dense hpQ hrQ hpr
    exact ⟨t, (mem_supUpper_iff S t).mpr ⟨htQ, p, hpQ, h₁, hall⟩, h₂⟩
  located p hpQ q hqQ hlt := by
    obtain ⟨t, htQ, h₁, h₂⟩ := rat_dense hpQ hqQ hlt
    -- the family's locatedness is used exactly here, and nowhere else
    rcases hfam p hpQ t htQ h₁ with hleft | hright
    · exact Or.inl ((mem_supLower_iff S p).mpr ⟨hpQ, hleft⟩)
    · exact Or.inr ((mem_supUpper_iff S q).mpr ⟨hqQ, t, htQ, h₂, hright⟩)

/-- The supremum is an upper bound, and the least one: both halves are the
membership condition of `supLower` read in the two directions. -/
theorem le_sup {S z L U : ZFSet.{u}} (hS : S ⊆ RealL.{u}) (hz : z ∈ S)
    (he : z = opair L U) : L ⊆ supLower S := fun p hp =>
  (mem_supLower_iff S p).mpr
    ⟨(isLocated_of_mem_RealL (hS z hz) he).lower_subset p hp, z, hz, L, U, he, hp⟩

theorem sup_le {S B : ZFSet.{u}}
    (h : ∀ z, z ∈ S → ∀ L U, z = opair L U → L ⊆ B) : supLower S ⊆ B := by
  intro p hp
  obtain ⟨-, z, hz, L, U, he, hpL⟩ := (mem_supLower_iff S p).mp hp
  exact h z hz L U he p hpL

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

/-! ## The operations, at the level of the reals

Everything above works on a pair of sets `L`, `U` and a proof they are located.
`RealL` is the set of such pairs, and a construction built on top of it -- `ℂ`,
or a polynomial ring -- wants operations on its elements, not on the two
halves. These package them, and `mem` lemmas say they land back in `RealL`. -/

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

/-- Swap the last two summands. Named with the `realLAdd` prefix rather than
bare, so it is not mistaken for core's additive right-commutativity, which is
in a different namespace. -/
theorem realLAdd_right_comm {a b c : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hc : c ∈ RealL.{u}) :
    realLAdd (realLAdd a b) c = realLAdd (realLAdd a c) b := by
  rw [realLAdd_assoc ha hb hc, realLAdd_comm hb hc, ← realLAdd_assoc ha hc hb]

#print axioms Analysis.realLAdd_right_comm
/-! ## Zero

`x + 0 = x` is where openness earns its place in `IsLocated`: the sum's lower
half holds the rationals strictly below `q + r` with `r < 0`, and recovering all
of `L` needs a member of `L` strictly above the one in hand. -/

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

/-- Membership in the lower cut is witnessed by arbitrarily tight brackets.
A witnessing bracket exists by definition; `located_bracket` supplies a tight
one, and the common refinement of the two is tight and witnessing, because
refinement preserves the corner condition. This is the form associativity and
the unit law both need: it lets a proof assume its brackets are as narrow as it
likes. -/
theorem mulLower_tight {L₁ U₁ L₂ U₂ p ε : ZFSet.{u}} (h₁ : IsLocated L₁ U₁)
    (h₂ : IsLocated L₂ U₂) (hεQ : ε ∈ NumberTheory.Rat.{u}) (hε : ratLt ratZero.{u} ε)
    (hp : p ∈ mulLower L₁ U₁ L₂ U₂) :
    ∃ q, q ∈ L₁ ∧ ∃ q', q' ∈ U₁ ∧ ∃ r, r ∈ L₂ ∧ ∃ r', r' ∈ U₂ ∧
      ratLt q' (ratAdd q ε) ∧ ratLt r' (ratAdd r ε) ∧
      ratLt p (ratMul q r) ∧ ratLt p (ratMul q r') ∧
        ratLt p (ratMul q' r) ∧ ratLt p (ratMul q' r') := by
  obtain ⟨hpQ, a, ha, a', ha', b, hb, b', hb', c₁, c₂, c₃, c₄⟩ := (mem_sep_iff _ p _).mp hp
  obtain ⟨s, hs, s', hs', hss'⟩ := located_bracket h₁ hεQ hε
  obtain ⟨t, ht, t', ht', htt'⟩ := located_bracket h₂ hεQ hε
  -- the common refinement of the witnessing bracket and the tight one
  obtain ⟨q, hq, haq, hsq⟩ := lower_pair_bound h₁ ha hs
  obtain ⟨q', hq', hq'a', hq's'⟩ := upper_pair_bound h₁ ha' hs'
  obtain ⟨r, hr, hbr, htr⟩ := lower_pair_bound h₂ hb ht
  obtain ⟨r', hr', hr'b', hr't'⟩ := upper_pair_bound h₂ hb' ht'
  obtain ⟨d₁, d₂, d₃, d₄⟩ :=
    corners_of_refinement h₁ h₂ hpQ ha ha' hb hb' hq hq' hr hr'
      haq hq'a' hbr hr'b' c₁ c₂ c₃ c₄
  refine ⟨q, hq, q', hq', r, hr, r', hr', ?_, ?_, d₁, d₂, d₃, d₄⟩
  · -- `q' ≤ s' < s + ε ≤ q + ε`
    refine ratLt_of_le_of_lt (h₁.upper_subset q' hq') (h₁.upper_subset s' hs')
      (ratAdd_mem_Rat (h₁.lower_subset q hq) hεQ) hq's' ?_
    exact ratLt_of_lt_of_le (h₁.upper_subset s' hs')
      (ratAdd_mem_Rat (h₁.lower_subset s hs) hεQ)
      (ratAdd_mem_Rat (h₁.lower_subset q hq) hεQ) hss'
      ((ratAdd_le_add_right_iff hεQ (h₁.lower_subset s hs) (h₁.lower_subset q hq)).mpr hsq)
  · refine ratLt_of_le_of_lt (h₂.upper_subset r' hr') (h₂.upper_subset t' ht')
      (ratAdd_mem_Rat (h₂.lower_subset r hr) hεQ) hr't' ?_
    exact ratLt_of_lt_of_le (h₂.upper_subset t' ht')
      (ratAdd_mem_Rat (h₂.lower_subset t ht) hεQ)
      (ratAdd_mem_Rat (h₂.lower_subset r hr) hεQ) htt'
      ((ratAdd_le_add_right_iff hεQ (h₂.lower_subset t ht) (h₂.lower_subset r hr)).mpr htr)

/-- The mirror of `mulLower_tight` for the upper half: a witnessing bracket can
be taken as narrow as asked, refined against a tight one exactly as before. -/
theorem mulUpper_tight {L₁ U₁ L₂ U₂ p ε : ZFSet.{u}} (h₁ : IsLocated L₁ U₁)
    (h₂ : IsLocated L₂ U₂) (hεQ : ε ∈ NumberTheory.Rat.{u}) (hε : ratLt ratZero.{u} ε)
    (hp : p ∈ mulUpper L₁ U₁ L₂ U₂) :
    ∃ q, q ∈ L₁ ∧ ∃ q', q' ∈ U₁ ∧ ∃ r, r ∈ L₂ ∧ ∃ r', r' ∈ U₂ ∧
      ratLt q' (ratAdd q ε) ∧ ratLt r' (ratAdd r ε) ∧
      ratLt (ratMul q r) p ∧ ratLt (ratMul q r') p ∧
        ratLt (ratMul q' r) p ∧ ratLt (ratMul q' r') p := by
  obtain ⟨hpQ, a, ha, a', ha', b, hb, b', hb', c₁, c₂, c₃, c₄⟩ := (mem_sep_iff _ p _).mp hp
  obtain ⟨s, hs, s', hs', hss'⟩ := located_bracket h₁ hεQ hε
  obtain ⟨t, ht, t', ht', htt'⟩ := located_bracket h₂ hεQ hε
  obtain ⟨q, hq, haq, hsq⟩ := lower_pair_bound h₁ ha hs
  obtain ⟨q', hq', hq'a', hq's'⟩ := upper_pair_bound h₁ ha' hs'
  obtain ⟨r, hr, hbr, htr⟩ := lower_pair_bound h₂ hb ht
  obtain ⟨r', hr', hr'b', hr't'⟩ := upper_pair_bound h₂ hb' ht'
  obtain ⟨d₁, d₂, d₃, d₄⟩ :=
    corners_of_refinement' h₁ h₂ hpQ ha ha' hb hb' hq hq' hr hr'
      haq hq'a' hbr hr'b' c₁ c₂ c₃ c₄
  refine ⟨q, hq, q', hq', r, hr, r', hr', ?_, ?_, d₁, d₂, d₃, d₄⟩
  · refine ratLt_of_le_of_lt (h₁.upper_subset q' hq') (h₁.upper_subset s' hs')
      (ratAdd_mem_Rat (h₁.lower_subset q hq) hεQ) hq's' ?_
    exact ratLt_of_lt_of_le (h₁.upper_subset s' hs')
      (ratAdd_mem_Rat (h₁.lower_subset s hs) hεQ)
      (ratAdd_mem_Rat (h₁.lower_subset q hq) hεQ) hss'
      ((ratAdd_le_add_right_iff hεQ (h₁.lower_subset s hs) (h₁.lower_subset q hq)).mpr hsq)
  · refine ratLt_of_le_of_lt (h₂.upper_subset r' hr') (h₂.upper_subset t' ht')
      (ratAdd_mem_Rat (h₂.lower_subset r hr) hεQ) hr't' ?_
    exact ratLt_of_lt_of_le (h₂.upper_subset t' ht')
      (ratAdd_mem_Rat (h₂.lower_subset t ht) hεQ)
      (ratAdd_mem_Rat (h₂.lower_subset r hr) hεQ) htt'
      ((ratAdd_le_add_right_iff hεQ (h₂.lower_subset t ht) (h₂.lower_subset r hr)).mpr htr)

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

/-- `-0 = 0`. Each half is a density argument: a rational below zero has a
positive rational whose negation still exceeds it. -/
theorem realLNeg_zero : realLNeg realLZero.{u} = realLZero.{u} := by
  have hlow : negLower (sep (fun p => ratLt ratZero.{u} p) NumberTheory.Rat.{u}) = ratCut ratZero.{u} := by
    refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
    · obtain ⟨hpQ, r, hr, hpr⟩ := (mem_negLower_iff _ p).mp hp
      obtain ⟨hrQ, h0r⟩ := (mem_sep_iff _ r _).mp hr
      refine (mem_ratCut_iff _ _).mpr ⟨hpQ, ratLt_trans hpQ (ratNeg_mem_Rat hrQ)
        ratZero_mem_Rat hpr ?_⟩
      have := (ratNeg_lt_neg_iff hrQ ratZero_mem_Rat).mpr h0r
      rwa [ratNeg_zero] at this
    · obtain ⟨hpQ, hp0⟩ := (mem_ratCut_iff _ p).mp hp
      have hnp0 : ratLt ratZero.{u} (ratNeg p) := by
        have := (ratNeg_lt_neg_iff ratZero_mem_Rat hpQ).mpr hp0
        rwa [ratNeg_zero] at this
      obtain ⟨r, hrQ, h0r, hrn⟩ := rat_dense ratZero_mem_Rat (ratNeg_mem_Rat hpQ) hnp0
      refine (mem_negLower_iff _ _).mpr ⟨hpQ, r, (mem_sep_iff _ _ _).mpr ⟨hrQ, h0r⟩, ?_⟩
      have := (ratNeg_lt_neg_iff (ratNeg_mem_Rat hpQ) hrQ).mpr hrn
      rwa [ratNeg_ratNeg hpQ] at this
  have hupp : negUpper (ratCut ratZero.{u}) = sep (fun p => ratLt ratZero.{u} p) NumberTheory.Rat.{u} := by
    refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
    · obtain ⟨hpQ, q, hq, hqp⟩ := (mem_negUpper_iff _ p).mp hp
      obtain ⟨hqQ, hq0⟩ := (mem_ratCut_iff _ q).mp hq
      refine (mem_sep_iff _ _ _).mpr ⟨hpQ, ratLt_trans ratZero_mem_Rat
        (ratNeg_mem_Rat hqQ) hpQ ?_ hqp⟩
      have := (ratNeg_lt_neg_iff ratZero_mem_Rat hqQ).mpr hq0
      rwa [ratNeg_zero] at this
    · obtain ⟨hpQ, h0p⟩ := (mem_sep_iff _ p _).mp hp
      have hnp0 : ratLt (ratNeg p) ratZero.{u} := by
        have := (ratNeg_lt_neg_iff hpQ ratZero_mem_Rat).mpr h0p
        rwa [ratNeg_zero] at this
      obtain ⟨q, hqQ, hnq, hq0⟩ := rat_dense (ratNeg_mem_Rat hpQ) ratZero_mem_Rat hnp0
      refine (mem_negUpper_iff _ _).mpr ⟨hpQ, q, (mem_ratCut_iff _ _).mpr ⟨hqQ, hq0⟩, ?_⟩
      have := (ratNeg_lt_neg_iff hqQ (ratNeg_mem_Rat hpQ)).mpr hnq
      rwa [ratNeg_ratNeg hpQ] at this
  rw [realLNeg, realLZero, realLOf, fst_opair, snd_opair, hlow, hupp]

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

/-- `x·(y·z) = y·(x·z)`: the left factor moves past the middle one. -/
theorem realLMul_left_comm {x y z : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hz : z ∈ RealL.{u}) :
    realLMul x (realLMul y z) = realLMul y (realLMul x z) := by
  rw [← realLMul_assoc hx hy hz, realLMul_comm hx hy, realLMul_assoc hy hx hz]

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

/-- The strict order is ASYMMETRIC: `x < y` rules out `y < x`.

The two-line composition of the two theorems above.

Both memberships are taken because `realLLt_trans` needs them, and the consumers
on that chain have them to hand. -/
theorem realLLt_asymm {x y : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (h : realLLt x y) : ¬ realLLt y x :=
  fun h' => realLLt_irrefl hx (realLLt_trans hx hy hx h h')

theorem realLApart_symm {x y : ZFSet.{u}} (h : realLApart x y) : realLApart y x :=
  h.symm

theorem realLApart_irrefl {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) : ¬ realLApart x x := by
  rintro (h | h) <;> exact realLLt_irrefl hx h

/-- Apartness gives a rational strictly between, on whichever side it holds. -/
theorem exists_between_of_realLApart {x y : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (h : realLApart x y) :
    ∃ p, p ∈ NumberTheory.Rat.{u} ∧ ((p ∈ snd x ∧ p ∈ fst y) ∨ (p ∈ snd y ∧ p ∈ fst x)) := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff y).mp hy
  rcases h with ⟨p, hpU, hpL⟩ | ⟨p, hpU, hpL⟩
  · rw [snd_opair] at hpU
    exact ⟨p, h₁.upper_subset p hpU, Or.inl ⟨by rw [snd_opair]; exact hpU, hpL⟩⟩
  · rw [snd_opair] at hpU
    exact ⟨p, h₂.upper_subset p hpU, Or.inr ⟨by rw [snd_opair]; exact hpU, hpL⟩⟩

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

/-- The reciprocal of a positive real is positive. A rational strictly
between zero and `1/r`, for any `r` in the upper cut, is the witness -- and `r`
is positive because the real is. -/
theorem realLInv_pos {z : ZFSet.{u}} (hz : z ∈ RealL.{u})
    (h : realLLt realLZero.{u} z) : realLLt realLZero.{u} (realLInv z) := by
  obtain ⟨c, hcL, hc0⟩ := exists_pos_lower h
  obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff z).mp hz
  rw [fst_opair] at hcL
  obtain ⟨r, hrU⟩ := hloc.upper_inhabited
  have hr0 := upper_pos_of_witness hloc hcL hc0 hrU
  have hrQ := hloc.upper_subset r hrU
  obtain ⟨q, hqQ, h0q, hqinv⟩ := rat_dense ratZero_mem_Rat
    (ratInv_mem_Rat hrQ (ratNe_zero_of_pos hr0)) (ratInv_pos hrQ hr0)
  refine ⟨q, ?_, ?_⟩
  · rw [realLZero, realLOf, snd_opair]
    exact (mem_sep_iff _ _ _).mpr ⟨hqQ, h0q⟩
  · rw [realLInv, fst_opair, snd_opair]
    exact (mem_invLower_iff U q).mpr ⟨hqQ, r, hrU, hqinv⟩

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

/-- A square is never negative. A rational above `a·a` would dominate every
product from inside the two brackets -- including `t·t` for a `t` lying in both,
and a rational square is not negative. -/
theorem realLSq_nonneg {a : ZFSet.{u}} (ha : a ∈ RealL.{u}) :
    realLLe realLZero.{u} (realLMul a a) := by
  obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff a).mp ha
  rintro ⟨p, hpU, hpL⟩
  rw [realLMul] at hpU
  simp only [fst_opair, snd_opair] at hpU
  rw [realLZero, realLOf, fst_opair] at hpL
  obtain ⟨hpQ, hp0⟩ := (mem_ratCut_iff _ p).mp hpL
  obtain ⟨-, q, hq, q', hq', r, hr, r', hr', c₁, c₂, c₃, c₄⟩ := (mem_sep_iff _ p _).mp hpU
  obtain ⟨t, ht, hqt, hrt⟩ := lower_pair_bound hloc hq hr
  have htQ := hloc.lower_subset t ht
  have hsq := ratMul_lt_of_corners hpQ (hloc.lower_subset q hq) (hloc.upper_subset q' hq')
    (hloc.lower_subset r hr) (hloc.upper_subset r' hr') htQ htQ
    hqt (hloc.ordered t ht q' hq').left hrt (hloc.ordered t ht r' hr').left c₁ c₂ c₃ c₄
  exact ratLt_irrefl (ratLt_of_le_of_lt ratZero_mem_Rat (ratMul_mem_Rat htQ htQ)
    ratZero_mem_Rat (ratMul_self_nonneg htQ)
    (ratLt_trans (ratMul_mem_Rat htQ htQ) hpQ ratZero_mem_Rat hsq hp0))

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

/-- TWO IS A REAL. -/
theorem realLTwo_mem : realLAdd realLOne.{u} realLOne.{u} ∈ RealL.{u} :=
  realLAdd_mem realLOne_mem realLOne_mem

/-- TWO IS POSITIVE.

The field axioms alone do not give `2 ≠ 0`, since `1 + 1 = 0` in characteristic
two, so `realLOne_ne_zero` does not reach it. The ORDER rules it out.
-/
theorem realLTwo_pos : realLLt realLZero.{u} (realLAdd realLOne.{u} realLOne.{u}) := by
  have h := realLLt_add_right realLZero_mem realLOne_mem realLOne_mem realLZero_lt_one
  rw [realLAdd_comm realLZero_mem realLOne_mem, realLAdd_zero realLOne_mem] at h
  exact realLLt_trans realLZero_mem realLOne_mem realLTwo_mem realLZero_lt_one h

#print axioms realLTwo_mem
#print axioms realLTwo_pos

/-! ## The two reals

A located pair carries strictly more than a Dedekind cut, and the difference is
exactly `em`. Forgetting the upper half is a function `RealL → Real`, and it is
injective -- the upper half is recoverable, because `located` says a rational is
in it exactly when some smaller rational is outside the lower cut. Going back is
`cut_located`, which reverses to `em`. -/

theorem isCut_lower {L U : ZFSet.{u}} (h : IsLocated L U) : IsCut L where
  subset := h.lower_subset
  nonempty := h.lower_inhabited
  proper := by
    obtain ⟨r, hr⟩ := h.upper_inhabited
    exact ⟨r, h.upper_subset r hr, fun hmem => ratLt_irrefl (h.ordered r hmem r hr)⟩
  down := h.lower_down
  no_greatest := h.lower_open

/-- Forget the upper half. -/
def toCut (z : ZFSet.{u}) : ZFSet.{u} := fst z

theorem toCut_mem {z : ZFSet.{u}} (hz : z ∈ RealL.{u}) : toCut z ∈ Real.{u} := by
  obtain ⟨L, U, rfl, h⟩ := (mem_RealL_iff z).mp hz
  rw [toCut, fst_opair]
  exact (mem_sep_iff _ _ _).mpr ⟨(mem_powerset_iff _ _).mpr h.lower_subset, isCut_lower h⟩

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

/-- `Nat` addition embeds into `RealL` addition, at denominator one.

`ratNat_add_same_denom` does the rational half and `realLOf_add` the located
half; neither is about `Nat`, and together they are. Stated because the bound
this rung carries is an inequality between NATURALS and the content's values
are located reals. -/
theorem realLOf_ratNat_add (a b : Nat) :
    realLOf (ratNat.{u} (a + b) 1)
      = realLAdd (realLOf (ratNat.{u} a 1)) (realLOf (ratNat.{u} b 1)) := by
  rw [← ratNat_add_same_denom (q := 1) (by omega),
    realLOf_add (ratNat_mem_Rat (by omega)) (ratNat_mem_Rat (by omega))]

#print axioms Analysis.realLOf_ratNat_add


/-- The bridge carries the order, and carries it free.

`realLLe a b` is `¬ realLLt b a`, a negation; `realLe` is `⊆`, a
membership. Turning one into the other looks like double-negation
elimination on `p ∈ L`, and it is not: locatedness supplies the missing
positive information, and the negation is spent only against the hypothesis.

Given `p ∈ L_a`, `lower_open` gives `p < p'` with `p' ∈ L_a`, and `located`
decides `b` at that gap. `p ∈ L_b` is the conclusion; `p' ∈ U_b` would put
`p'` in `b`'s upper and `a`'s lower, which is exactly `realLLt b a`. So the
second branch closes against the hypothesis rather than producing anything,
and no instance of `¬¬X → X` is used. -/
theorem toCut_le {z w : ZFSet.{u}} (hz : z ∈ RealL.{u}) (hw : w ∈ RealL.{u})
    (h : realLLe z w) : realLe (toCut z) (toCut w) := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff z).mp hz
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff w).mp hw
  rw [toCut, toCut, fst_opair, fst_opair]
  intro p hp
  obtain ⟨p', hp'L, hlt⟩ := h₁.lower_open p hp
  rcases h₂.located p (h₁.lower_subset p hp) p' (h₁.lower_subset p' hp'L) hlt with
    hin | hin
  · exact hin
  · exact absurd ⟨p', by rw [snd_opair]; exact hin, by rw [fst_opair]; exact hp'L⟩ h

/-- The two additions agree on cuts. `realAdd` is the sumset `{q + r}` and
`addLower` its downward closure; they coincide because a cut is already
downward closed -- given `p < q + r`, the summand `p - r` is below `q` and so
still in the lower cut. -/
theorem addLower_eq_realAdd {L₁ U₁ L₂ U₂ : ZFSet.{u}} (h₁ : IsLocated L₁ U₁)
    (h₂ : IsLocated L₂ U₂) : addLower L₁ L₂ = realAdd L₁ L₂ := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨hpQ, q, hq, r, hr, hlt⟩ := (mem_addLower_iff _ _ p).mp hp
    have hqQ := h₁.lower_subset q hq
    have hrQ := h₂.lower_subset r hr
    have hd := ratAdd_mem_Rat hpQ (ratNeg_mem_Rat hrQ)
    -- `p - r < q`, so it is still in the lower cut, and `(p - r) + r = p`
    refine (mem_realAdd_iff _ _ p).mpr ⟨hpQ, ratAdd p (ratNeg r),
      h₁.lower_down q hq _ hd ?_, r, hr, ?_⟩
    · have := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat hrQ) hpQ
        (ratAdd_mem_Rat hqQ hrQ)).mpr hlt
      rwa [ratAdd_assoc hqQ hrQ (ratNeg_mem_Rat hrQ), ratAdd_neg hrQ,
        ratAdd_zero hqQ] at this
    · rw [ratAdd_assoc hpQ (ratNeg_mem_Rat hrQ) hrQ,
        ratAdd_comm (ratNeg_mem_Rat hrQ) hrQ, ratAdd_neg hrQ, ratAdd_zero hpQ]
  · obtain ⟨hpQ, q, hq, r, hr, rfl⟩ := (mem_realAdd_iff _ _ p).mp hp
    obtain ⟨q', hq', hqq'⟩ := h₁.lower_open q hq
    refine (mem_addLower_iff _ _ _).mpr ⟨hpQ, q', hq', r, hr, ?_⟩
    exact (ratAdd_lt_add_right_iff (h₂.lower_subset r hr) (h₁.lower_subset q hq)
      (h₁.lower_subset q' hq')).mpr hqq'

/-- Where both factors are non-negative the four corners collapse to one.
Not because three are dominated -- because the two MIXED corners are what make
the sign hypothesis bite. If `q < 0` then `r' ≥ 0` (else `hn₂` puts `r'` in
`L₂` and `ordered` gives `r' < r'`), so `q·r' ≤ 0` and `p < q·r'` forces
`p < 0`. On the branch where `p` is not negative the witnesses `mulLower` hands
over are ALREADY non-negative, and `p < q·r` is the corner `realMulNonneg`
asks for. -/
theorem mulLower_nonneg_witnesses {L₁ U₁ L₂ U₂ q r' p : ZFSet.{u}}
    (h₁ : IsLocated L₁ U₁) (h₂ : IsLocated L₂ U₂) (hn₂ : realNonneg L₂)
    (hq : q ∈ L₁) (hr' : r' ∈ U₂) (hpQ : p ∈ NumberTheory.Rat.{u})
    (hp0 : ¬ ratLt p ratZero.{u}) (hcorner : ratLt p (ratMul q r')) :
    ratLe ratZero.{u} q := by
  have hqQ := h₁.lower_subset q hq
  have hr'Q := h₂.upper_subset r' hr'
  rcases ratLt_trichotomy hqQ ratZero_mem_Rat with hneg | heq | hpos
  · exfalso
    have hr'nn : ¬ ratLt r' ratZero.{u} := fun hc =>
      ratLt_irrefl (h₂.ordered r' (hn₂ r' ((mem_ratCut_iff ratZero.{u} r').mpr
        ⟨hr'Q, hc⟩)) r' hr')
    exact hp0 (ratLt_of_lt_of_le hpQ (ratMul_mem_Rat hqQ hr'Q) ratZero_mem_Rat
      hcorner (ratLe_of_not_lt (ratMul_mem_Rat hqQ hr'Q) ratZero_mem_Rat
        (ratMul_nonpos_of_neg_of_nonneg hqQ hr'Q hneg hr'nn)))
  · exact heq ▸ ratLe_refl hqQ
  · exact hpos.left

/-- The four-corner product agrees with the one-sided one, where both factors
are non-negative. The witnesses `mulLower` supplies are already non-negative
on the branch that needs them (`mulLower_nonneg_witnesses`), so the corner
`p < q·r` it already carries is exactly what `realMulNonneg` asks for. -/
theorem mulLower_sub_realMulNonneg {L₁ U₁ L₂ U₂ : ZFSet.{u}}
    (h₁ : IsLocated L₁ U₁) (h₂ : IsLocated L₂ U₂)
    (hn₁ : realNonneg L₁) (hn₂ : realNonneg L₂) :
    mulLower L₁ U₁ L₂ U₂ ⊆ realMulNonneg L₁ L₂ := by
  intro p hp
  obtain ⟨hpQ, q, hq, q', hq', r, hr, r', hr', h1, h2, h3, h4⟩ :=
    (mem_mulLower_iff _ _ _ _ p).mp hp
  refine (mem_realMulNonneg_iff _ _ p).mpr ⟨hpQ, ?_⟩
  -- `by_cases` here would route through `Classical.em`; trichotomy is free.
  rcases ratLt_trichotomy hpQ ratZero_mem_Rat with hlt | heq | hgt
  · exact Or.inl hlt
  all_goals
    have hneg : ¬ ratLt p ratZero.{u} := by
      first
        | exact fun hc => ratLt_irrefl (heq ▸ hc)
        | exact fun hc => ratLt_irrefl (ratLt_trans hpQ ratZero_mem_Rat hpQ hc hgt)
    exact Or.inr ⟨q, hq, r, hr,
      mulLower_nonneg_witnesses h₁ h₂ hn₂ hq hr' hpQ hneg h2,
      mulLower_nonneg_witnesses h₂ h₁ hn₁ hr hq' hpQ hneg
        (by rwa [ratMul_comm (h₂.lower_subset r hr) (h₁.upper_subset q' hq')]),
      h1⟩

/-- One corner lifts to all four, when both factors are non-negative.
The reverse inclusion needs this at two different pairs, and the sign
bookkeeping is the whole content: `ratMul_le_mul_right` varies the left factor,
so the corners with `r` varying are reached by commuting first. -/
private theorem four_corners_of_nonneg {p q q' r r' : ZFSet.{u}}
    (hpQ : p ∈ NumberTheory.Rat.{u}) (hqQ : q ∈ NumberTheory.Rat.{u}) (hq'Q : q' ∈ NumberTheory.Rat.{u})
    (hrQ : r ∈ NumberTheory.Rat.{u}) (hr'Q : r' ∈ NumberTheory.Rat.{u})
    (hq0 : ratLe ratZero.{u} q) (hr0 : ratLe ratZero.{u} r)
    (hqq' : ratLt q q') (hrr' : ratLt r r') (hp : ratLt p (ratMul q r)) :
    ratLt p (ratMul q r) ∧ ratLt p (ratMul q r') ∧
      ratLt p (ratMul q' r) ∧ ratLt p (ratMul q' r') := by
  have hle_q : ratLe q q' := ratLe_of_lt hqQ hq'Q hqq'
  have hle_r : ratLe r r' := ratLe_of_lt hrQ hr'Q hrr'
  have hq'0 : ratLe ratZero.{u} q' := ratLe_trans ratZero_mem_Rat hqQ hq'Q hq0 hle_q
  have h_q' : ratLe (ratMul q r) (ratMul q' r) :=
    ratMul_le_mul_right hqQ hq'Q hrQ hle_q hr0
  have h_r' : ratLe (ratMul q r) (ratMul q r') := by
    rw [ratMul_comm hqQ hrQ, ratMul_comm hqQ hr'Q]
    exact ratMul_le_mul_right hrQ hr'Q hqQ hle_r hq0
  have h_far : ratLe (ratMul q r) (ratMul q' r') :=
    ratLe_trans (ratMul_mem_Rat hqQ hrQ) (ratMul_mem_Rat hq'Q hrQ)
      (ratMul_mem_Rat hq'Q hr'Q) h_q'
      (by rw [ratMul_comm hq'Q hrQ, ratMul_comm hq'Q hr'Q]
          exact ratMul_le_mul_right hrQ hr'Q hq'Q hle_r hq'0)
  exact ⟨hp,
    ratLt_of_lt_of_le hpQ (ratMul_mem_Rat hqQ hrQ) (ratMul_mem_Rat hqQ hr'Q) hp h_r',
    ratLt_of_lt_of_le hpQ (ratMul_mem_Rat hqQ hrQ) (ratMul_mem_Rat hq'Q hrQ) hp h_q',
    ratLt_of_lt_of_le hpQ (ratMul_mem_Rat hqQ hrQ) (ratMul_mem_Rat hq'Q hr'Q) hp h_far⟩

/-- A negative rational lies in the lower set of a non-negative real. -/
private theorem neg_mem_lower {L d : ZFSet.{u}} (hn : realNonneg L)
    (hdQ : d ∈ NumberTheory.Rat.{u}) (hd : ratLt d ratZero.{u}) : d ∈ L :=
  hn d ((mem_ratCut_iff ratZero.{u} d).mpr ⟨hdQ, hd⟩)

/-- An upper witness of a non-negative real is non-negative. Zero is not
excluded: that is the real-is-zero case, where the upper set is closed at its
infimum, so this is `ratLe`. -/
private theorem upper_nonneg {L U q' : ZFSet.{u}} (h : IsLocated L U)
    (hn : realNonneg L) (hq' : q' ∈ U) : ratLe ratZero.{u} q' := by
  have hq'Q := h.upper_subset q' hq'
  refine ratLe_of_not_lt ratZero_mem_Rat hq'Q (fun hc => ?_)
  exact ratLt_irrefl (h.ordered q' (neg_mem_lower hn hq'Q hc) q' hq')

/-- Below zero, the negatives reach every corner. The upper witnesses are
fixed FIRST, so each mixed corner imposes one inequality on its own variable
and `small_of_pos` discharges it. The like-signed corners are free: a product
of two negatives is positive, and `q'·r'` is non-negative, both above `p`. -/
private theorem mem_mulLower_of_neg {L₁ U₁ L₂ U₂ p : ZFSet.{u}}
    (h₁ : IsLocated L₁ U₁) (h₂ : IsLocated L₂ U₂)
    (hn₁ : realNonneg L₁) (hn₂ : realNonneg L₂)
    (hpQ : p ∈ NumberTheory.Rat.{u}) (hp : ratLt p ratZero.{u}) :
    p ∈ mulLower L₁ U₁ L₂ U₂ := by
  obtain ⟨q', hq'⟩ := h₁.upper_inhabited
  obtain ⟨r', hr'⟩ := h₂.upper_inhabited
  have hq'Q := h₁.upper_subset q' hq'
  have hr'Q := h₂.upper_subset r' hr'
  have hq'0 := upper_nonneg h₁ hn₁ hq'
  have hr'0 := upper_nonneg h₂ hn₂ hr'
  have hnpQ := ratNeg_mem_Rat hpQ
  have hnp : ratLt ratZero.{u} (ratNeg p) := by
    have h := (ratNeg_lt_neg_iff ratZero_mem_Rat hpQ).mpr hp
    rwa [ratNeg_zero] at h
  obtain ⟨d, hdQ, hd0, hdr'⟩ := small_of_pos hr'Q hnpQ hr'0 hnp
  obtain ⟨e, heQ, he0, heq'⟩ := small_of_pos hq'Q hnpQ hq'0 hnp
  have hndQ := ratNeg_mem_Rat hdQ
  have hneQ := ratNeg_mem_Rat heQ
  -- -d < 0 and -e < 0, so both lie in the lower sets
  have hdneg : ratLt (ratNeg d) ratZero.{u} := by
    have h := (ratNeg_lt_neg_iff hdQ ratZero_mem_Rat).mpr hd0
    rwa [ratNeg_zero] at h
  have hEneg : ratLt (ratNeg e) ratZero.{u} := by
    have h := (ratNeg_lt_neg_iff heQ ratZero_mem_Rat).mpr he0
    rwa [ratNeg_zero] at h
  refine (mem_mulLower_iff _ _ _ _ p).mpr
    ⟨hpQ, ratNeg d, neg_mem_lower hn₁ hndQ hdneg, q', hq',
     ratNeg e, neg_mem_lower hn₂ hneQ hEneg, r', hr', ?_, ?_, ?_, ?_⟩
  · -- (-d)·(-e) = d·e > 0 > p
    rw [ratNeg_mul hdQ hneQ, ratMul_neg hdQ heQ, ratNeg_ratNeg (ratMul_mem_Rat hdQ heQ)]
    exact ratLt_trans hpQ ratZero_mem_Rat (ratMul_mem_Rat hdQ heQ) hp
      (ratMul_pos hdQ heQ hd0 he0)
  · -- (-d)·r' = -(d·r'), and d·r' < -p gives p < -(d·r')
    rw [ratNeg_mul hdQ hr'Q]
    have h := (ratNeg_lt_neg_iff hnpQ (ratMul_mem_Rat hdQ hr'Q)).mpr hdr'
    rwa [ratNeg_ratNeg hpQ] at h
  · -- q'·(-e) = -(q'·e); heq' is about e·q', so commute
    rw [ratMul_neg hq'Q heQ, ratMul_comm hq'Q heQ]
    have h := (ratNeg_lt_neg_iff hnpQ (ratMul_mem_Rat heQ hq'Q)).mpr heq'
    rwa [ratNeg_ratNeg hpQ] at h
  · -- q'·r' ≥ 0 > p
    exact ratLt_of_lt_of_le hpQ ratZero_mem_Rat (ratMul_mem_Rat hq'Q hr'Q) hp
      (ratZero_le_mul hq'Q hr'Q hq'0 hr'0)

/-- The sign-free half of the product: where both factors are non-negative,
the four-corner lower set IS the one-sided one. Both inclusions are proved
separately and neither is a triviality: the forward one needs the sign
hypothesis to KILL the two mixed corners (`mulLower_nonneg_witnesses`), and the
reverse one needs them to SURVIVE, small (`mem_mulLower_of_neg`). Same two
corners, opposite role -- so the four-corner definition is not
redundant under `realNonneg`. -/
theorem mulLower_eq_realMulNonneg {L₁ U₁ L₂ U₂ : ZFSet.{u}}
    (h₁ : IsLocated L₁ U₁) (h₂ : IsLocated L₂ U₂)
    (hn₁ : realNonneg L₁) (hn₂ : realNonneg L₂) :
    mulLower L₁ U₁ L₂ U₂ = realMulNonneg L₁ L₂ := by
  refine ext _ _ fun p => ⟨fun hp => mulLower_sub_realMulNonneg h₁ h₂ hn₁ hn₂ p hp,
    fun hp => ?_⟩
  obtain ⟨hpQ, hcase⟩ := (mem_realMulNonneg_iff _ _ p).mp hp
  rcases hcase with hneg | ⟨q, hq, r, hr, hq0, hr0, hlt⟩
  · exact mem_mulLower_of_neg h₁ h₂ hn₁ hn₂ hpQ hneg
  · obtain ⟨q', hq'⟩ := h₁.upper_inhabited
    obtain ⟨r', hr'⟩ := h₂.upper_inhabited
    obtain ⟨c1, c2, c3, c4⟩ := four_corners_of_nonneg hpQ
      (h₁.lower_subset q hq) (h₁.upper_subset q' hq')
      (h₂.lower_subset r hr) (h₂.upper_subset r' hr')
      hq0 hr0 (h₁.ordered q hq q' hq') (h₂.ordered r hr r' hr') hlt
    exact (mem_mulLower_iff _ _ _ _ p).mpr
      ⟨hpQ, q, hq, q', hq', r, hr, r', hr', c1, c2, c3, c4⟩

/-- The embedding carries addition. -/
theorem toCut_add {x y : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u}) :
    toCut (realLAdd x y) = realAdd (toCut x) (toCut y) := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff y).mp hy
  rw [toCut, toCut, toCut, realLAdd]
  simp only [fst_opair, snd_opair]
  exact addLower_eq_realAdd h₁ h₂

/-- The embedding carries multiplication, where both factors are
non-negative. -/
theorem toCut_mul {x y : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (hn₁ : realNonneg (toCut x)) (hn₂ : realNonneg (toCut y)) :
    toCut (realLMul x y) = realMulNonneg (toCut x) (toCut y) := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff y).mp hy
  -- The sign hypotheses arrive about `toCut (opair L₁ U₁)` and the set lemma
  -- wants them about `L₁`; reduce them before the goal moves.
  simp only [toCut, fst_opair] at hn₁ hn₂
  rw [toCut, toCut, toCut, realLMul]
  simp only [fst_opair, snd_opair]
  exact mulLower_eq_realMulNonneg h₁ h₂ hn₁ hn₂

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

/-- Negation takes a nonnegative real to a nonpositive one. -/
theorem realLNeg_le_zero {e : ZFSet.{u}} (he : e ∈ RealL.{u})
    (h : realLLe realLZero.{u} e) : realLLe (realLNeg e) realLZero.{u} := by
  intro hlt
  have := realLNeg_lt_neg realLZero_mem (realLNeg_mem he) hlt
  rw [realLNeg_realLNeg he, realLNeg_zero] at this
  exact h this

/-- `0 <= -e` from `e <= 0`. The companion of `realLNeg_le_zero`. -/
theorem realLZero_le_realLNeg {e : ZFSet.{u}} (he : e ∈ RealL.{u})
    (h : realLLe e realLZero.{u}) : realLLe realLZero.{u} (realLNeg e) := by
  intro hlt
  have hstep := realLNeg_lt_neg (realLNeg_mem he) realLZero_mem hlt
  rw [realLNeg_realLNeg he, realLNeg_zero] at hstep
  exact h hstep

#print axioms realLZero_le_realLNeg

theorem realLLe_add_right {a b c : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hc : c ∈ RealL.{u}) (h : realLLe a b) :
    realLLe (realLAdd a c) (realLAdd b c) :=
  fun hlt => h (realLLt_add_right_cancel hb ha hc hlt)

/-- And the converse, undoing the shift. `realLLe` is a negation, so this is the
`<` version read backwards rather than a rewriting of the definition -- the same
one-line shape as the law above, in the other direction. -/
theorem realLLe_add_right_cancel {a b z : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hz : z ∈ RealL.{u})
    (h : realLLe (realLAdd a z) (realLAdd b z)) : realLLe a b :=
  fun hlt => h (realLLt_add_right hb ha hz hlt)

#print axioms realLLe_add_right_cancel

/-! ### Antisymmetry

`realLLe` is a negation, so antisymmetry descends to the cuts, and
`realLLe_lower_subset` is where locatedness is spent -- the rung `(p, p')`
inside the lower set has to fall one way or the other. -/

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

/-- APARTNESS FROM ZERO SURVIVES DOUBLING.

`realLApart` is a disjunction of strict inequalities, so this is two symmetric
branches and each is one `realLLt_add_right` plus transitivity.

Written for the cubic group law's VERTICAL clause, whose comaximality condition
is `-y - y # 0` --- this, with `realLApart_neg` on top. -/
theorem realLApart_add_self {y : ZFSet.{u}} (hy : y ∈ RealL.{u})
    (hap : realLApart realLZero.{u} y) :
    realLApart realLZero.{u} (realLAdd y y) := by
  rcases hap with hlt | hlt
  · refine Or.inl ?_
    have h := realLLt_add_right realLZero_mem hy hy hlt
    rw [realLZero_add hy] at h
    exact realLLt_trans realLZero_mem hy (realLAdd_mem hy hy) hlt h
  · refine Or.inr ?_
    have h := realLLt_add_right hy realLZero_mem hy hlt
    rw [realLZero_add hy] at h
    exact realLLt_trans (realLAdd_mem hy hy) hy realLZero_mem h hlt

-- Its companion `realLApart_neg` sits AFTER `realLNeg_neg_of_pos` (line ~5290),
-- which it needs and which is defined below this point.

#print axioms Analysis.realLApart_add_self

/-- A non-zero located real is not-not apart from zero.

The contrapositive of `realLApart_tight`, which already says that denying an
apartness produces an equation -- `realLApart` is a disjunction of strict
inequalities, so denying it denies both, and `realLLe` IS a negated `realLLt`.

The converse is `NeApartZero` and is floored at `MP`; the asymmetry is the
content. -/
theorem not_not_apart_of_ne {a : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (h : a ≠ realLZero.{u}) : ¬ ¬ realLApart realLZero.{u} a :=
  fun hnap => h (realLApart_tight realLZero_mem ha hnap).symm

#print axioms Analysis.not_not_apart_of_ne

/-- Addition is cancellative on the right. -/
theorem realLAdd_right_cancel {u v a : ZFSet.{u}} (hu : u ∈ RealL.{u})
    (hv : v ∈ RealL.{u}) (ha : a ∈ RealL.{u})
    (h : realLAdd u a = realLAdd v a) : u = v := by
  have h1 : realLAdd (realLAdd u a) (realLNeg a) = u := by
    rw [realLAdd_assoc hu ha (realLNeg_mem ha), realLAdd_neg ha, realLAdd_zero hu]
  have h2 : realLAdd (realLAdd v a) (realLNeg a) = v := by
    rw [realLAdd_assoc hv ha (realLNeg_mem ha), realLAdd_neg ha, realLAdd_zero hv]
  rw [← h1, ← h2, h]

/-- `x - (x - c) = c`. -/
theorem realLSub_sub_cancel {x c : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) :
    realLAdd x (realLNeg (realLAdd x (realLNeg c))) = c := by
  have ha := realLAdd_mem hx (realLNeg_mem hc)
  refine realLAdd_right_cancel (realLAdd_mem hx (realLNeg_mem ha)) hc ha ?_
  rw [realLSub_add_cancel hx ha, realLAdd_comm hc ha,
    realLAdd_assoc hx (realLNeg_mem hc) hc,
    realLAdd_comm (realLNeg_mem hc) hc, realLAdd_neg hc, realLAdd_zero hx]

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
-/

theorem isLocated_min {L₁ U₁ L₂ U₂ : ZFSet.{u}} (h₁ : IsLocated L₁ U₁)
    (h₂ : IsLocated L₂ U₂) : IsLocated (L₁ ∩ L₂) (U₁ ∪ U₂) where
  lower_subset := fun q hq => h₁.lower_subset q ((mem_inter_iff _ _ _).mp hq).left
  upper_subset := fun r hr => by
    rcases (mem_union_iff _ _ _).mp hr with h | h
    · exact h₁.upper_subset r h
    · exact h₂.upper_subset r h
  lower_inhabited := by
    obtain ⟨a, ha⟩ := h₁.lower_inhabited
    obtain ⟨b, hb⟩ := h₂.lower_inhabited
    rcases ratLt_trichotomy (h₁.lower_subset a ha) (h₂.lower_subset b hb) with
      hlt | rfl | hgt
    · exact ⟨a, (mem_inter_iff _ _ _).mpr
        ⟨ha, h₂.lower_down b hb a (h₁.lower_subset a ha) hlt⟩⟩
    · exact ⟨a, (mem_inter_iff _ _ _).mpr ⟨ha, hb⟩⟩
    · exact ⟨b, (mem_inter_iff _ _ _).mpr
        ⟨h₁.lower_down a ha b (h₂.lower_subset b hb) hgt, hb⟩⟩
  upper_inhabited := by
    obtain ⟨r, hr⟩ := h₁.upper_inhabited
    exact ⟨r, (mem_union_iff _ _ _).mpr (Or.inl hr)⟩
  ordered := fun q hq r hr => by
    obtain ⟨hq1, hq2⟩ := (mem_inter_iff _ _ _).mp hq
    rcases (mem_union_iff _ _ _).mp hr with h | h
    · exact h₁.ordered q hq1 r h
    · exact h₂.ordered q hq2 r h
  lower_down := fun q hq p hp hlt => by
    obtain ⟨hq1, hq2⟩ := (mem_inter_iff _ _ _).mp hq
    exact (mem_inter_iff _ _ _).mpr
      ⟨h₁.lower_down q hq1 p hp hlt, h₂.lower_down q hq2 p hp hlt⟩
  upper_up := fun r hr p hp hlt => by
    rcases (mem_union_iff _ _ _).mp hr with h | h
    · exact (mem_union_iff _ _ _).mpr (Or.inl (h₁.upper_up r h p hp hlt))
    · exact (mem_union_iff _ _ _).mpr (Or.inr (h₂.upper_up r h p hp hlt))
  lower_open := fun q hq => by
    obtain ⟨hq1, hq2⟩ := (mem_inter_iff _ _ _).mp hq
    obtain ⟨a, ha, hqa⟩ := h₁.lower_open q hq1
    obtain ⟨b, hb, hqb⟩ := h₂.lower_open q hq2
    rcases ratLt_trichotomy (h₁.lower_subset a ha) (h₂.lower_subset b hb) with
      hlt | rfl | hgt
    · exact ⟨a, (mem_inter_iff _ _ _).mpr
        ⟨ha, h₂.lower_down b hb a (h₁.lower_subset a ha) hlt⟩, hqa⟩
    · exact ⟨a, (mem_inter_iff _ _ _).mpr ⟨ha, hb⟩, hqa⟩
    · exact ⟨b, (mem_inter_iff _ _ _).mpr
        ⟨h₁.lower_down a ha b (h₂.lower_subset b hb) hgt, hb⟩, hqb⟩
  upper_open := fun r hr => by
    rcases (mem_union_iff _ _ _).mp hr with h | h
    · obtain ⟨r', hr', hlt⟩ := h₁.upper_open r h
      exact ⟨r', (mem_union_iff _ _ _).mpr (Or.inl hr'), hlt⟩
    · obtain ⟨r', hr', hlt⟩ := h₂.upper_open r h
      exact ⟨r', (mem_union_iff _ _ _).mpr (Or.inr hr'), hlt⟩
  located := fun p hp q hq hlt => by
    rcases h₁.located p hp q hq hlt with h | h
    · rcases h₂.located p hp q hq hlt with h' | h'
      · exact Or.inl ((mem_inter_iff _ _ _).mpr ⟨h, h'⟩)
      · exact Or.inr ((mem_union_iff _ _ _).mpr (Or.inr h'))
    · exact Or.inr ((mem_union_iff _ _ _).mpr (Or.inl h))

/-- The smaller of two located reals. -/
def realLMin (z w : ZFSet.{u}) : ZFSet.{u} :=
  opair (fst z ∩ fst w) (snd z ∪ snd w)

theorem realLMin_mem {z w : ZFSet.{u}} (hz : z ∈ RealL.{u}) (hw : w ∈ RealL.{u}) :
    realLMin z w ∈ RealL.{u} := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff z).mp hz
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff w).mp hw
  refine (mem_RealL_iff _).mpr ⟨_, _, ?_, isLocated_min h₁ h₂⟩
  rw [realLMin, fst_opair, fst_opair, snd_opair, snd_opair]

/-- `min` is below each argument, in the sense the order gives: nothing sits
strictly above the argument and below the minimum. -/
theorem realLMin_le_left {z w : ZFSet.{u}} (hz : z ∈ RealL.{u}) :
    realLLe (realLMin z w) z := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff z).mp hz
  rintro ⟨p, hpU, hpL⟩
  rw [snd_opair] at hpU
  rw [realLMin, fst_opair, fst_opair] at hpL
  exact ratLt_irrefl (h₁.ordered p ((mem_inter_iff _ _ _).mp hpL).left p hpU)

theorem realLMin_le_right {z w : ZFSet.{u}} (hw : w ∈ RealL.{u}) :
    realLLe (realLMin z w) w := by
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff w).mp hw
  rintro ⟨p, hpU, hpL⟩
  rw [snd_opair] at hpU
  rw [realLMin, fst_opair, fst_opair] at hpL
  exact ratLt_irrefl (h₂.ordered p ((mem_inter_iff _ _ _).mp hpL).right p hpU)

/-- Positivity survives `min`, and `located` never had to decide which of the
two reals is smaller -- only which of two rationals is, which is decidable. -/
theorem realLMin_pos {z w : ZFSet.{u}} (hzm : z ∈ RealL.{u}) (hwm : w ∈ RealL.{u})
    (hz : realLLt realLZero.{u} z) (hw : realLLt realLZero.{u} w) :
    realLLt realLZero.{u} (realLMin z w) := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff z).mp hzm
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff w).mp hwm
  obtain ⟨p, hpU, hpL⟩ := hz
  obtain ⟨q, hqU, hqL⟩ := hw
  rw [fst_opair] at hpL hqL
  have hpQ := h₁.lower_subset p hpL
  have hqQ := h₂.lower_subset q hqL
  -- the smaller of the two rational witnesses lies in both lower halves
  have hboth : ∃ t, t ∈ snd realLZero.{u} ∧ t ∈ L₁ ∧ t ∈ L₂ := by
    rcases ratLt_trichotomy hpQ hqQ with hlt | rfl | hgt
    · exact ⟨p, hpU, hpL, h₂.lower_down q hqL p hpQ hlt⟩
    · exact ⟨p, hpU, hpL, hqL⟩
    · exact ⟨q, hqU, h₁.lower_down p hpL q hqQ hgt, hqL⟩
  obtain ⟨t, htU, ht1, ht2⟩ := hboth
  refine ⟨t, htU, ?_⟩
  rw [realLMin, fst_opair, fst_opair, fst_opair]
  exact (mem_inter_iff _ _ _).mpr ⟨ht1, ht2⟩


#print axioms isLocated_ratCut
#print axioms located_bracket        -- the point: no Classical.choice
#print axioms located_bracket_width
#print axioms located_of_isLocated
#print axioms isLocated_sup_of_familyLocated  -- completeness, for located families
#print axioms mem_upper_iff
#print axioms pairLe_antisymm
#print axioms isLocated_add
#print axioms isLocated_neg
#print axioms mul_located
#print axioms isLocated_mul
#print axioms sup_le
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
#print axioms mulLower_tight
#print axioms mulUpper_tight
#print axioms mulLower_one
#print axioms mulUpper_one
#print axioms realLMul_one
#print axioms mulLower_zero
#print axioms mulUpper_zero
#print axioms realLMul_zero
#print axioms mulLower_const
#print axioms mulUpper_const
#print axioms realLNeg_zero
#print axioms mulLower_distrib_le
#print axioms located_eq_of_subset
#print axioms corners_of_refinement'
#print axioms mulUpper_distrib_le
#print axioms realLMul_distrib
#print axioms mulLower_assoc_le
#print axioms mulUpper_assoc_le
#print axioms realLMul_assoc
#print axioms realLMul_left_comm
#print axioms realLSub_add_cancel
#print axioms realLLt_irrefl
#print axioms realLLt_trans
#print axioms realLLt_add_right
#print axioms realLSub_sub_cancel
#print axioms realLOf_lt_iff_mem_lower
#print axioms lt_realLOf_iff_mem_upper
#print axioms exists_rat_bracket
#print axioms realLLe_trans
#print axioms realLLt_add_right_cancel
#print axioms realLNeg_lt_neg
#print axioms isLocated_min
#print axioms realLMin_mem
#print axioms realLMin_pos
#print axioms exists_between_of_realLApart
#print axioms isLocated_inv
#print axioms realLInv_mem
#print axioms exists_pos_lower
#print axioms realLInv_pos
#print axioms mulLower_inv_le
#print axioms mulLower_inv_ge
#print axioms mulLower_inv
#print axioms mulUpper_inv
#print axioms realLMul_inv
#print axioms realLNeg_pos
#print axioms realLApart_zero_one
#print axioms realLLt_cotrans
#print axioms realLMul_pos
#print axioms realLSq_nonneg
#print axioms toCut_mem
#print axioms upper_eq_of_lower
#print axioms toCut_injective
#print axioms addLower_eq_realAdd
#print axioms toCut_add
#print axioms toCut_mul

/-- The mirror of `isLocated_min`: lowers union, uppers intersect. -/
theorem isLocated_max {L₁ U₁ L₂ U₂ : ZFSet.{u}} (h₁ : IsLocated L₁ U₁)
    (h₂ : IsLocated L₂ U₂) : IsLocated (L₁ ∪ L₂) (U₁ ∩ U₂) where
  lower_subset := fun q hq => by
    rcases (mem_union_iff _ _ _).mp hq with h | h
    · exact h₁.lower_subset q h
    · exact h₂.lower_subset q h
  upper_subset := fun r hr => h₁.upper_subset r ((mem_inter_iff _ _ _).mp hr).left
  lower_inhabited := by
    obtain ⟨a, ha⟩ := h₁.lower_inhabited
    exact ⟨a, (mem_union_iff _ _ _).mpr (Or.inl ha)⟩
  upper_inhabited := by
    obtain ⟨r, hr⟩ := h₁.upper_inhabited
    obtain ⟨s, hs⟩ := h₂.upper_inhabited
    rcases ratLt_trichotomy (h₁.upper_subset r hr) (h₂.upper_subset s hs) with
      hlt | rfl | hgt
    · exact ⟨s, (mem_inter_iff _ _ _).mpr
        ⟨h₁.upper_up r hr s (h₂.upper_subset s hs) hlt, hs⟩⟩
    · exact ⟨r, (mem_inter_iff _ _ _).mpr ⟨hr, hs⟩⟩
    · exact ⟨r, (mem_inter_iff _ _ _).mpr
        ⟨hr, h₂.upper_up s hs r (h₁.upper_subset r hr) hgt⟩⟩
  ordered := fun q hq r hr => by
    obtain ⟨hr1, hr2⟩ := (mem_inter_iff _ _ _).mp hr
    rcases (mem_union_iff _ _ _).mp hq with h | h
    · exact h₁.ordered q h r hr1
    · exact h₂.ordered q h r hr2
  lower_down := fun q hq p hp hlt => by
    rcases (mem_union_iff _ _ _).mp hq with h | h
    · exact (mem_union_iff _ _ _).mpr (Or.inl (h₁.lower_down q h p hp hlt))
    · exact (mem_union_iff _ _ _).mpr (Or.inr (h₂.lower_down q h p hp hlt))
  upper_up := fun r hr p hp hlt => by
    obtain ⟨hr1, hr2⟩ := (mem_inter_iff _ _ _).mp hr
    exact (mem_inter_iff _ _ _).mpr
      ⟨h₁.upper_up r hr1 p hp hlt, h₂.upper_up r hr2 p hp hlt⟩
  lower_open := fun q hq => by
    rcases (mem_union_iff _ _ _).mp hq with h | h
    · obtain ⟨q', hq', hlt⟩ := h₁.lower_open q h
      exact ⟨q', (mem_union_iff _ _ _).mpr (Or.inl hq'), hlt⟩
    · obtain ⟨q', hq', hlt⟩ := h₂.lower_open q h
      exact ⟨q', (mem_union_iff _ _ _).mpr (Or.inr hq'), hlt⟩
  upper_open := fun r hr => by
    obtain ⟨hr1, hr2⟩ := (mem_inter_iff _ _ _).mp hr
    obtain ⟨a, ha, hra⟩ := h₁.upper_open r hr1
    obtain ⟨b, hb, hrb⟩ := h₂.upper_open r hr2
    rcases ratLt_trichotomy (h₁.upper_subset a ha) (h₂.upper_subset b hb) with
      hlt | rfl | hgt
    · exact ⟨b, (mem_inter_iff _ _ _).mpr
        ⟨h₁.upper_up a ha b (h₂.upper_subset b hb) hlt, hb⟩, hrb⟩
    · exact ⟨a, (mem_inter_iff _ _ _).mpr ⟨ha, hb⟩, hra⟩
    · exact ⟨a, (mem_inter_iff _ _ _).mpr
        ⟨ha, h₂.upper_up b hb a (h₁.upper_subset a ha) hgt⟩, hra⟩
  located := fun p hp q hq hlt => by
    rcases h₁.located p hp q hq hlt with h | h
    · exact Or.inl ((mem_union_iff _ _ _).mpr (Or.inl h))
    · rcases h₂.located p hp q hq hlt with h' | h'
      · exact Or.inl ((mem_union_iff _ _ _).mpr (Or.inr h'))
      · exact Or.inr ((mem_inter_iff _ _ _).mpr ⟨h, h'⟩)

/-- The larger of two located reals, dual to `realLMin`. -/
def realLMax (z w : ZFSet.{u}) : ZFSet.{u} :=
  opair (fst z ∪ fst w) (snd z ∩ snd w)

theorem realLMax_mem {z w : ZFSet.{u}} (hz : z ∈ RealL.{u}) (hw : w ∈ RealL.{u}) :
    realLMax z w ∈ RealL.{u} := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff z).mp hz
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff w).mp hw
  refine (mem_RealL_iff _).mpr ⟨_, _, ?_, isLocated_max h₁ h₂⟩
  rw [realLMax, fst_opair, fst_opair, snd_opair, snd_opair]

/-- Each argument is below `max`. -/
theorem realLLe_max_left {z w : ZFSet.{u}} (hz : z ∈ RealL.{u}) :
    realLLe z (realLMax z w) := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff z).mp hz
  rintro ⟨p, hpU, hpL⟩
  rw [fst_opair] at hpL
  rw [realLMax, snd_opair, snd_opair] at hpU
  exact ratLt_irrefl (h₁.ordered p hpL p ((mem_inter_iff _ _ _).mp hpU).left)

theorem realLLe_max_right {z w : ZFSet.{u}} (hw : w ∈ RealL.{u}) :
    realLLe w (realLMax z w) := by
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff w).mp hw
  rintro ⟨p, hpU, hpL⟩
  rw [fst_opair] at hpL
  rw [realLMax, snd_opair, snd_opair] at hpU
  exact ratLt_irrefl (h₂.ordered p hpL p ((mem_inter_iff _ _ _).mp hpU).right)

/-- A witness below the max lands in one lower half or the other. -/
theorem realLLt_max_cases {a b x : ZFSet.{u}}
    (h : realLLt x (realLMax a b)) : Or (realLLt x a) (realLLt x b) := by
  obtain ⟨p, hpU, hpL⟩ := h
  rw [realLMax, fst_opair] at hpL
  rcases (mem_union_iff _ _ _).mp hpL with h' | h'
  · exact Or.inl ⟨p, hpU, h'⟩
  · exact Or.inr ⟨p, hpU, h'⟩

theorem realLLt_max_of_right {a b x : ZFSet.{u}} (h : realLLt x b) :
    realLLt x (realLMax a b) := by
  obtain ⟨p, hpU, hpL⟩ := h
  refine ⟨p, hpU, ?_⟩
  rw [realLMax, fst_opair]
  exact (mem_union_iff _ _ _).mpr (Or.inr hpL)

/-- `max` is the least upper bound: below anything above both. -/
theorem realLMax_le {a b x : ZFSet.{u}} (h₁ : realLLe a x) (h₂ : realLLe b x) :
    realLLe (realLMax a b) x := fun h =>
  match realLLt_max_cases h with
  | Or.inl h' => h₁ h'
  | Or.inr h' => h₂ h'

/-- The maximum of a finite list of located reals, above a seed. -/
def realLMaxList (seed : ZFSet.{u}) : List ZFSet.{u} → ZFSet.{u}
  | [] => seed
  | a :: as => realLMax a (realLMaxList seed as)

/-- A witness above the min lands in one upper half or the other. -/
theorem realLLt_min_cases {a b x : ZFSet.{u}}
    (h : realLLt (realLMin a b) x) : Or (realLLt a x) (realLLt b x) := by
  obtain ⟨p, hpU, hpL⟩ := h
  rw [realLMin, snd_opair] at hpU
  rcases (mem_union_iff _ _ _).mp hpU with h' | h'
  · exact Or.inl ⟨p, h', hpL⟩
  · exact Or.inr ⟨p, h', hpL⟩

theorem realLMin_lt_of_left {a b x : ZFSet.{u}} (h : realLLt a x) :
    realLLt (realLMin a b) x := by
  obtain ⟨p, hpU, hpL⟩ := h
  refine ⟨p, ?_, hpL⟩
  rw [realLMin, snd_opair]
  exact (mem_union_iff _ _ _).mpr (Or.inl hpU)

/-- `min` is the greatest lower bound: above anything below both. -/
theorem le_realLMin {a b x : ZFSet.{u}} (h₁ : realLLe x a) (h₂ : realLLe x b) :
    realLLe x (realLMin a b) := fun h =>
  match realLLt_min_cases h with
  | Or.inl h' => h₁ h'
  | Or.inr h' => h₂ h'

/-- Strictly below `x` on both sides puts the max strictly below `x`: only
two rationals are ever compared. -/
theorem realLMax_lt {a b x : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (h₁ : realLLt a x) (h₂ : realLLt b x) :
    realLLt (realLMax a b) x := by
  obtain ⟨L₁, U₁, rfl, hA⟩ := (mem_RealL_iff a).mp ha
  obtain ⟨L₂, U₂, rfl, hB⟩ := (mem_RealL_iff b).mp hb
  obtain ⟨p, hpU, hpL⟩ := h₁
  obtain ⟨q, hqU, hqL⟩ := h₂
  rw [snd_opair] at hpU hqU
  have hmax : ∀ r, r ∈ U₁ → r ∈ U₂ → r ∈ fst x →
      realLLt (realLMax (opair L₁ U₁) (opair L₂ U₂)) x := by
    intro r hr1 hr2 hrL
    refine ⟨r, ?_, hrL⟩
    rw [realLMax, snd_opair, snd_opair, snd_opair]
    exact (mem_inter_iff _ _ _).mpr ⟨hr1, hr2⟩
  rcases ratLt_trichotomy (hA.upper_subset p hpU) (hB.upper_subset q hqU) with
    hlt | rfl | hgt
  · exact hmax q (hA.upper_up p hpU q (hB.upper_subset q hqU) hlt) hqU hqL
  · exact hmax p hpU hqU hpL
  · exact hmax p hpU (hB.upper_up q hqU p (hA.upper_subset p hpU) hgt) hpL

/-- The minimum of a finite list of located reals, below a seed. The mirror of
`realLMaxList`, and the shape a DISTANCE to a finite set of points takes. -/
def realLMinList (seed : ZFSet.{u}) : List ZFSet.{u} → ZFSet.{u}
  | [] => seed
  | a :: as => realLMin a (realLMinList seed as)

#print axioms Analysis.realLMinList
/-- Strictly above `x` on both sides keeps the min strictly above `x`:
`realLMin_pos` is the `x = 0` case, generalised. -/
theorem realLLt_min {a b x : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (h₁ : realLLt x a) (h₂ : realLLt x b) :
    realLLt x (realLMin a b) := by
  obtain ⟨L₁, U₁, rfl, hA⟩ := (mem_RealL_iff a).mp ha
  obtain ⟨L₂, U₂, rfl, hB⟩ := (mem_RealL_iff b).mp hb
  obtain ⟨p, hpU, hpL⟩ := h₁
  obtain ⟨q, hqU, hqL⟩ := h₂
  rw [fst_opair] at hpL hqL
  have hmin : ∀ r, r ∈ L₁ → r ∈ L₂ → r ∈ snd x →
      realLLt x (realLMin (opair L₁ U₁) (opair L₂ U₂)) := by
    intro r hr1 hr2 hrU
    refine ⟨r, hrU, ?_⟩
    rw [realLMin, fst_opair, fst_opair, fst_opair]
    exact (mem_inter_iff _ _ _).mpr ⟨hr1, hr2⟩
  rcases ratLt_trichotomy (hA.lower_subset p hpL) (hB.lower_subset q hqL) with
    hlt | rfl | hgt
  · exact hmin p hpL (hB.lower_down q hqL p (hA.lower_subset p hpL) hlt) hpU
  · exact hmin p hpL hqL hpU
  · exact hmin q (hA.lower_down p hpL q (hB.lower_subset q hqL) hgt) hqL hqU

/-- Below the min is below both: the witness lies in the intersected lower. -/
theorem realLLt_min_pair {a b x : ZFSet.{u}}
    (h : realLLt x (realLMin a b)) : And (realLLt x a) (realLLt x b) := by
  obtain ⟨p, hpU, hpL⟩ := h
  rw [realLMin, fst_opair] at hpL
  obtain ⟨h1, h2⟩ := (mem_inter_iff _ _ _).mp hpL
  exact ⟨⟨p, hpU, h1⟩, ⟨p, hpU, h2⟩⟩

/-- Above the max is above both: the witness lies in the intersected upper. -/
theorem realLMax_lt_pair {a b x : ZFSet.{u}}
    (h : realLLt (realLMax a b) x) : And (realLLt a x) (realLLt b x) := by
  obtain ⟨p, hpU, hpL⟩ := h
  rw [realLMax, snd_opair] at hpU
  obtain ⟨h1, h2⟩ := (mem_inter_iff _ _ _).mp hpU
  exact ⟨⟨p, h1, hpL⟩, ⟨p, h2, hpL⟩⟩

/-- The min is not strictly below both arguments: whichever upper half the
first witness came from closes against one of the two lowers. -/
theorem not_min_lt_both {b d : ZFSet.{u}} (hb : b ∈ RealL.{u})
    (hd : d ∈ RealL.{u}) (h1 : realLLt (realLMin b d) b)
    (h2 : realLLt (realLMin b d) d) : False := by
  obtain ⟨L₁, U₁, rfl, hB⟩ := (mem_RealL_iff b).mp hb
  obtain ⟨L₂, U₂, rfl, hD⟩ := (mem_RealL_iff d).mp hd
  obtain ⟨p, hpU, hpL⟩ := h1
  obtain ⟨q, hqU, hqL⟩ := h2
  rw [realLMin, snd_opair, snd_opair, snd_opair] at hpU hqU
  rw [fst_opair] at hpL hqL
  rcases (mem_union_iff _ _ _).mp hpU with hp | hp
  · exact ratLt_irrefl (hB.ordered p hpL p hp)
  · rcases (mem_union_iff _ _ _).mp hqU with hq | hq
    · exact ratLt_irrefl (ratLt_trans (hB.lower_subset p hpL)
        (hB.upper_subset q hq) (hB.lower_subset p hpL)
        (hB.ordered p hpL q hq) (hD.ordered q hqL p hp))
    · exact ratLt_irrefl (hD.ordered q hqL q hq)

/-- Shifting both arguments distributes out of the min, as an inequality:
the direction `le_realLMin` does not give. -/
theorem realLMin_add_le {v w z : ZFSet.{u}} (hv : v ∈ RealL.{u})
    (hw : w ∈ RealL.{u}) (hz : z ∈ RealL.{u}) :
    realLLe (realLMin (realLAdd v z) (realLAdd w z))
      (realLAdd (realLMin v w) z) := by
  intro hlt
  obtain ⟨hlt1, hlt2⟩ := realLLt_min_pair hlt
  exact not_min_lt_both hv hw
    (realLLt_add_right_cancel (realLMin_mem hv hw) hv hz hlt1)
    (realLLt_add_right_cancel (realLMin_mem hv hw) hw hz hlt2)

#print axioms isLocated_max
#print axioms realLMax_mem
#print axioms realLLe_max_left
#print axioms realLLe_max_right
#print axioms realLMax_le
#print axioms le_realLMin
#print axioms realLMax_lt
#print axioms realLLt_min
#print axioms realLLt_min_pair
#print axioms realLMax_lt_pair

/-- A maximum against something below it is itself. -/
theorem realLMax_eq_left_of_le {a b : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (h : realLLe b a) : realLMax a b = a :=
  realLLe_antisymm (realLMax_mem ha hb) ha
    (realLMax_le (realLLe_refl ha) h) (realLLe_max_left ha)

#print axioms realLMax_eq_left_of_le
#print axioms not_min_lt_both
#print axioms realLMin_add_le

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

/-- A factor apart from zero cannot annihilate a non-zero partner.

Invert the apart factor and the product equation gives `b = 0`. The second
factor is asked only for `≠ 0`, which is what refutes it -- an apartness there
would be over-asking. -/
theorem mul_eq_zero_absurd_of_apart {a b : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hap : realLApart realLZero.{u} a)
    (hbne : b ≠ realLZero.{u}) (hab : realLMul a b = realLZero.{u}) : False := by
  obtain ⟨c, hc, hac⟩ := realL_inverses ha hap
  apply hbne
  have h := congrArg (fun z => realLMul c z) hab
  simp only [] at h
  rwa [← realLMul_assoc hc ha hb, realLMul_comm hc ha, hac,
    realLOne_mul hb, realLMul_zero hc] at h

/-- A product of non-zero located reals is non-zero, and no principle is
spent. Getting `0 # a` from `a ≠ 0` is `NeApartZero`, floored at `MP` -- but the
GOAL here is itself a negation, so `not_not_apart_of_ne`'s double negation is
consumed rather than eliminated. The apartness route is sufficient, not
necessary. -/
theorem realL_mul_ne_zero {a b : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hane : a ≠ realLZero.{u}) (hbne : b ≠ realLZero.{u}) :
    realLMul a b ≠ realLZero.{u} :=
  fun hab => not_not_apart_of_ne ha hane
    (fun hap => mul_eq_zero_absurd_of_apart ha hb hap hbne hab)

#print axioms Analysis.mul_eq_zero_absurd_of_apart
#print axioms Analysis.realL_mul_ne_zero

/-! The regularity form of `realL_mul_ne_zero` --- `IsRegularElt RealL …` ---
CANNOT LIVE HERE: `IsRegularElt` is `Algebra/Ring.lean`'s and this file imports
only `Analysis.Real`, so the two cones are parallel. It is landed in
`Analysis/Complex.lean` beside `isConstructiveField_realL`, which is the lowest
file holding both. -/

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

/-- A positive `max x (-x)` is apartness from zero -- the converse
direction of the sign split, and the step every quantitative route to
apartness ends at. `realLLt_max_cases` does the work: a witness below the
max lands below one half or the other, and those two halves are the two
disjuncts of `realLApart`.

Stated on `realLMax x (realLNeg x)` rather than on `realLAbs`, which is the
same term but is defined in `Deriv.lean`, downstream of everything here. -/
theorem realLApart_zero_of_max_pos {x : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (h : realLLt realLZero.{u} (realLMax x (realLNeg x))) :
    realLApart x realLZero.{u} := by
  rcases realLLt_max_cases h with h' | h'
  · exact Or.inr h'
  · have hstep := realLNeg_lt_neg realLZero_mem (realLNeg_mem hx) h'
    rw [realLNeg_realLNeg hx, realLNeg_zero] at hstep
    exact Or.inl hstep

/-- And it is the reciprocal. One associativity: `a·(a·(a·a)⁻¹)` is
`(a·a)·(a·a)⁻¹`. -/
theorem realLMul_invApart {a : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (h : realLApart realLZero.{u} a) :
    realLMul a (realLInvApart a) = realLOne.{u} := by
  have hsq := realLMul_mem ha ha
  rw [realLInvApart, ← realLMul_assoc ha ha (realLInv_mem hsq (realLSq_pos ha h))]
  exact realLMul_inv hsq (realLSq_pos ha h)


#print axioms realLApart_zero_of_max_pos
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
/-- A factor apart from zero cancels. -/
theorem realLMul_left_cancel_apart {c x y : ZFSet.{u}} (hc : c ∈ RealL.{u})
    (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (h0 : realLApart realLZero.{u} c) (h : realLMul c x = realLMul c y) : x = y := by
  have hinv := realLInvApart_mem hc h0
  have hcx : realLMul (realLInvApart c) (realLMul c x)
      = realLMul (realLInvApart c) (realLMul c y) := congrArg _ h
  rw [← realLMul_assoc hinv hc hx, ← realLMul_assoc hinv hc hy,
    realLMul_comm hinv hc, realLMul_invApart hc h0,
    realLOne_mul hx, realLOne_mul hy] at hcx
  exact hcx

#print axioms realLMul_left_cancel_apart

/-- `(ac)(ac) = (aa)(cc)`. -/
theorem realLMul_sq_swap {a c : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hc : c ∈ RealL.{u}) :
    realLMul (realLMul a c) (realLMul a c)
      = realLMul (realLMul a a) (realLMul c c) :=
  realLMul_shuffle_pair ha hc ha hc

#print axioms realLMul_sq_swap



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
/-- `x·z - y·z = (x - y)·z`. -/
theorem realLSub_mul {x y z : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (hz : z ∈ RealL.{u}) :
    realLAdd (realLMul x z) (realLNeg (realLMul y z))
      = realLMul (realLAdd x (realLNeg y)) z := by
  rw [realLAdd_mul hx (realLNeg_mem hy) hz, realLNeg_realLMul hy hz]

/-- Doubling, as a scalar multiple. -/
theorem realLDouble {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    realLMul (realLOf (ratNat.{u} 2 1)) x = realLAdd x x := by
  rw [show ratNat.{u} 2 1 = ratAdd ratOne.{u} ratOne.{u} from by
        rw [← ratNat_one_one, ratNat_add_same_denom (by omega : 0 < 1)],
    realLOf_add ratOne_mem_Rat ratOne_mem_Rat,
    show realLOf ratOne.{u} = realLOne.{u} from rfl,
    realLAdd_mul realLOne_mem realLOne_mem hx, realLOne_mul hx]

/-- The product's error, split. `x*y - L*M = (x - L)y + L(y - M)` -- the
identity every product-limit argument runs on, with each factor carrying one
error. -/
theorem realLMul_sub_mul {x y L M : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hL : L ∈ RealL.{u}) (hM : M ∈ RealL.{u}) :
    realLAdd (realLMul x y) (realLNeg (realLMul L M))
      = realLAdd (realLMul (realLAdd x (realLNeg L)) y)
          (realLMul L (realLAdd y (realLNeg M))) := by
  have hxy := realLMul_mem hx hy
  have hLy := realLMul_mem hL hy
  have hLM := realLMul_mem hL hM
  rw [← realLSub_mul hx hL hy, realLMul_distrib hL hy (realLNeg_mem hM),
    realLMul_neg hL hM,
    realLAdd_assoc hxy (realLNeg_mem hLy) (realLAdd_mem hLy (realLNeg_mem hLM)),
    ← realLAdd_assoc (realLNeg_mem hLy) hLy (realLNeg_mem hLM),
    realLAdd_comm (realLNeg_mem hLy) hLy, realLAdd_neg hLy,
    realLAdd_comm realLZero_mem (realLNeg_mem hLM),
    realLAdd_zero (realLNeg_mem hLM)]
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
/-- The Cauchy-Schwarz inequality over the located reals, in the Euclidean
plane: `(ac + bd)² ≤ (a² + b²)(c² + d²)`.

Free, and Lagrange's identity is why: the difference between the two sides is
`(ad - bc)²`, so the whole inequality is one square being non-negative. Nothing
is decided, no case is split, no apartness is needed, no principle is spent.

The reciprocal estimates below are conditional on an apartness and the spike's
continuity is priced at `WLPO`: the cost lives in the operations that must
divide, not in the order on `RealL`.

Geometry's `tangent_cs` is the MINKOWSKI form on the hyperboloid: a different
statement in a different signature, not a duplication of this one. -/
theorem cauchySchwarz_realL {a b c d : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hc : c ∈ RealL.{u}) (hd : d ∈ RealL.{u}) :
    realLLe (realLMul (realLAdd (realLMul a c) (realLMul b d))
        (realLAdd (realLMul a c) (realLMul b d)))
      (realLMul (realLAdd (realLMul a a) (realLMul b b))
        (realLAdd (realLMul c c) (realLMul d d))) := by
  have hac := realLMul_mem ha hc
  have hbd := realLMul_mem hb hd
  have had := realLMul_mem ha hd
  have hbc := realLMul_mem hb hc
  have hnbc := realLNeg_mem hbc
  have hP := realLAdd_mem hac hbd
  have hQ := realLAdd_mem had hnbc
  have hPP := realLMul_mem hP hP
  have hQQ := realLMul_mem hQ hQ
  have haa := realLMul_mem ha ha
  have hbb := realLMul_mem hb hb
  have hcc := realLMul_mem hc hc
  have hdd := realLMul_mem hd hd
  -- the four squares, each collapsed by one interchange
  have e1 : realLMul (realLMul a c) (realLMul a c)
      = realLMul (realLMul a a) (realLMul c c) := realLMul_shuffle_pair ha hc ha hc
  have e2 : realLMul (realLMul b d) (realLMul b d)
      = realLMul (realLMul b b) (realLMul d d) := realLMul_shuffle_pair hb hd hb hd
  have e3 : realLMul (realLMul a d) (realLMul a d)
      = realLMul (realLMul a a) (realLMul d d) := realLMul_shuffle_pair ha hd ha hd
  have e4 : realLMul (realLNeg (realLMul b c)) (realLNeg (realLMul b c))
      = realLMul (realLMul b b) (realLMul c c) := by
    rw [realLMul_neg_neg hbc hbc]
    exact realLMul_shuffle_pair hb hc hb hc
  -- the cross terms are the same product with opposite signs
  have e5 : realLMul (realLMul a c) (realLMul b d)
      = realLMul (realLMul a d) (realLMul b c) := by
    rw [realLMul_shuffle_pair ha hc hb hd, realLMul_shuffle_pair ha hd hb hc,
      realLMul_comm hc hd]
  -- Lagrange: expand both sides and the cross terms cancel
  have hlag : realLMul (realLAdd (realLMul a a) (realLMul b b))
      (realLAdd (realLMul c c) (realLMul d d))
      = realLAdd (realLMul (realLAdd (realLMul a c) (realLMul b d))
            (realLAdd (realLMul a c) (realLMul b d)))
        (realLMul (realLAdd (realLMul a d) (realLNeg (realLMul b c)))
          (realLAdd (realLMul a d) (realLNeg (realLMul b c)))) := by
    rw [realLAdd_mul haa hbb (realLAdd_mem hcc hdd),
      realLMul_distrib haa hcc hdd, realLMul_distrib hbb hcc hdd,
      realLAdd_mul hac hbd hP, realLMul_distrib hac hac hbd,
      realLMul_distrib hbd hac hbd,
      realLAdd_mul had hnbc hQ, realLMul_distrib had had hnbc,
      realLMul_distrib hnbc had hnbc,
      e1, e2, e3, e4, e5,
      realLMul_comm hbd hac, e5,
      realLNeg_realLMul hbc had, realLMul_comm hbc had,
      realLMul_neg had hbc]
    -- five atoms left: a²c², a²d², b²c², b²d², and the cross term (ad)(bc),
    -- which appears twice with each sign and cancels
    have hA := realLMul_mem haa hcc
    have hB := realLMul_mem haa hdd
    have hC := realLMul_mem hbb hcc
    have hD := realLMul_mem hbb hdd
    have hX := realLMul_mem had hbc
    have hnX := realLNeg_mem hX
    rw [realLAdd_interchange (realLAdd_mem hA hX) (realLAdd_mem hX hD)
        (realLAdd_mem hB hnX) (realLAdd_mem hnX hC),
      realLAdd_interchange hA hX hB hnX,
      realLAdd_interchange hX hD hnX hC,
      realLAdd_neg hX,
      realLAdd_zero (realLAdd_mem hA hB),
      realLAdd_comm realLZero_mem (realLAdd_mem hD hC),
      realLAdd_zero (realLAdd_mem hD hC),
      realLAdd_comm hD hC]
  rw [hlag]
  have hstep := realLLe_add_right realLZero_mem hQQ hPP (realLSq_nonneg hQ)
  rwa [realLZero_add hPP,
    realLAdd_comm hQQ hPP] at hstep

/-- `(P + T) + (T + Q) = (P + Q) + (T + T)`.

The regroup that every modulus expansion here ends at: two outer terms and a
doubled middle one. -/
theorem realLAdd_middle_pair {P Q T : ZFSet.{u}} (hP : P ∈ RealL.{u})
    (hQ : Q ∈ RealL.{u}) (hT : T ∈ RealL.{u}) :
    realLAdd (realLAdd P T) (realLAdd T Q)
      = realLAdd (realLAdd P Q) (realLAdd T T) := by
  -- One step, because `interchange hP hT hQ hT` is this statement up to one
  -- commutation.
  rw [realLAdd_comm hT hQ, realLAdd_interchange hP hT hQ hT]

#print axioms realLDouble
#print axioms realLAdd_middle_pair
/-- Two opposite pairs cancel.

    ((P - T) + (-T + Q)) + ((R + T) + (T + S))  =  (P + Q) + (R + S)

The shape the modulus expansion leaves: four cross terms, two of each sign. -/
theorem realLAdd_cancel_two {P Q R S T : ZFSet.{u}} (hP : P ∈ RealL.{u})
    (hQ : Q ∈ RealL.{u}) (hR : R ∈ RealL.{u}) (hS : S ∈ RealL.{u})
    (hT : T ∈ RealL.{u}) :
    realLAdd (realLAdd (realLAdd P (realLNeg T)) (realLAdd (realLNeg T) Q))
        (realLAdd (realLAdd R T) (realLAdd T S))
      = realLAdd (realLAdd P Q) (realLAdd R S) := by
  have hnT := realLNeg_mem hT
  rw [realLAdd_middle_pair hP hQ hnT, realLAdd_middle_pair hR hS hT,
    realLAdd_interchange (realLAdd_mem hP hQ) (realLAdd_mem hnT hnT)
      (realLAdd_mem hR hS) (realLAdd_mem hT hT),
    realLAdd_interchange hnT hnT hT hT,
    realLAdd_comm hnT hT, realLAdd_neg hT,
    realLAdd_zero realLZero_mem,
    realLAdd_zero (realLAdd_mem (realLAdd_mem hP hQ) (realLAdd_mem hR hS))]

#print axioms realLAdd_cancel_two


/-- The difference of squares: `a² - b² = (a-b)(a+b)`, as located reals. -/
theorem realLSub_sq {a b : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) :
    realLAdd (realLMul a a) (realLNeg (realLMul b b))
      = realLMul (realLAdd a (realLNeg b)) (realLAdd a b) := by
  rw [← realLSub_mul ha hb (realLAdd_mem ha hb),
    realLMul_distrib ha ha hb, realLMul_distrib hb ha hb,
    realLNeg_realLAdd (realLMul_mem hb ha) (realLMul_mem hb hb),
    realLMul_comm hb ha,
    ← realLAdd_assoc (realLAdd_mem (realLMul_mem ha ha) (realLMul_mem ha hb))
      (realLNeg_mem (realLMul_mem ha hb)) (realLNeg_mem (realLMul_mem hb hb)),
    realLAdd_assoc (realLMul_mem ha ha) (realLMul_mem ha hb)
      (realLNeg_mem (realLMul_mem ha hb)),
    realLAdd_neg (realLMul_mem ha hb),
    realLAdd_zero (realLMul_mem ha ha)]

/-! ## More rearrangements

-/

/-- `-(A - B) = B - A`. -/
theorem realLNeg_sub {A B : ZFSet.{u}} (hA : A ∈ RealL.{u}) (hB : B ∈ RealL.{u}) :
    realLNeg (realLAdd A (realLNeg B)) = realLAdd B (realLNeg A) := by
  rw [realLNeg_realLAdd hA (realLNeg_mem hB), realLNeg_realLNeg hB,
    realLAdd_comm (realLNeg_mem hA) hB]

/-- `(B - A) + (A - C) = B - C`: the triangle, as an identity. -/
theorem realLSub_add_sub {A B C : ZFSet.{u}} (hA : A ∈ RealL.{u}) (hB : B ∈ RealL.{u})
    (hC : C ∈ RealL.{u}) :
    realLAdd (realLAdd B (realLNeg A)) (realLAdd A (realLNeg C))
      = realLAdd B (realLNeg C) := by
  have hnA := realLNeg_mem hA
  have hnC := realLNeg_mem hC
  rw [realLAdd_assoc hB hnA (realLAdd_mem hA hnC), ← realLAdd_assoc hnA hA hnC,
    realLAdd_comm hnA hA, realLAdd_neg hA, realLZero_add hnC]

/-- Two linear approximations at the same base point differ by the difference of
their slopes, times the step. -/
theorem approx_diff {A L L' W : ZFSet.{u}} (hA : A ∈ RealL.{u}) (hL : L ∈ RealL.{u})
    (hL' : L' ∈ RealL.{u}) (hW : W ∈ RealL.{u}) :
    realLAdd (realLAdd A (realLMul L W)) (realLNeg (realLAdd A (realLMul L' W)))
      = realLMul (realLAdd L (realLNeg L')) W := by
  have hP := realLMul_mem hL hW
  have hQ := realLMul_mem hL' hW
  have hnA := realLNeg_mem hA
  have hnQ := realLNeg_mem hQ
  rw [realLNeg_realLAdd hA hQ, realLAdd_assoc hA hP (realLAdd_mem hnA hnQ),
    ← realLAdd_assoc hP hnA hnQ, realLAdd_comm hP hnA, realLAdd_assoc hnA hP hnQ,
    ← realLAdd_assoc hA hnA (realLAdd_mem hP hnQ), realLAdd_neg hA,
    realLAdd_comm realLZero_mem (realLAdd_mem hP hnQ),
    realLAdd_zero (realLAdd_mem hP hnQ), realLSub_mul hL hL' hW]

/-- `(A + B) - (C + D) = (A - C) + (B - D)`: the sum rule, before any analysis. -/
theorem realLAdd_sub_add {A B C D : ZFSet.{u}} (hA : A ∈ RealL.{u}) (hB : B ∈ RealL.{u})
    (hC : C ∈ RealL.{u}) (hD : D ∈ RealL.{u}) :
    realLAdd (realLAdd A B) (realLNeg (realLAdd C D))
      = realLAdd (realLAdd A (realLNeg C)) (realLAdd B (realLNeg D)) := by
  rw [realLNeg_realLAdd hC hD,
    realLAdd_interchange hA hB (realLNeg_mem hC) (realLNeg_mem hD)]

/-- `(Z + X) - (Z + Y) = X - Y`. -/
theorem realLAdd_sub_cancel_left {Z X Y : ZFSet.{u}} (hZ : Z ∈ RealL.{u})
    (hX : X ∈ RealL.{u}) (hY : Y ∈ RealL.{u}) :
    realLAdd (realLAdd Z X) (realLNeg (realLAdd Z Y)) = realLAdd X (realLNeg Y) := by
  rw [realLAdd_sub_add hZ hX hZ hY, realLAdd_neg hZ,
    realLAdd_comm realLZero_mem (realLAdd_mem hX (realLNeg_mem hY)),
    realLAdd_zero (realLAdd_mem hX (realLNeg_mem hY))]

/-- Adding the linear part back to the slack recovers the increment:
`(A - (B + P)) + P = A - B`. -/
theorem slack_add_lin {A B P : ZFSet.{u}} (hA : A ∈ RealL.{u}) (hB : B ∈ RealL.{u})
    (hP : P ∈ RealL.{u}) :
    realLAdd (realLAdd A (realLNeg (realLAdd B P))) P = realLAdd A (realLNeg B) := by
  have hnB := realLNeg_mem hB
  have hnP := realLNeg_mem hP
  rw [realLNeg_realLAdd hB hP, realLAdd_assoc hA (realLAdd_mem hnB hnP) hP,
    realLAdd_assoc hnB hnP hP, realLAdd_comm hnP hP, realLAdd_neg hP,
    realLAdd_zero hnB]

/-- `(X - Y) - P = X - (Y + P)`. -/
theorem realLSub_sub {X Y P : ZFSet.{u}} (hX : X ∈ RealL.{u}) (hY : Y ∈ RealL.{u})
    (hP : P ∈ RealL.{u}) :
    realLAdd (realLAdd X (realLNeg Y)) (realLNeg P)
      = realLAdd X (realLNeg (realLAdd Y P)) := by
  rw [realLNeg_realLAdd hY hP,
    ← realLAdd_assoc hX (realLNeg_mem hY) (realLNeg_mem hP)]


theorem realLLe_sub_nonneg {a b : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u}) :
    realLLe a b ↔ realLLe realLZero.{u} (realLAdd b (realLNeg a)) := by
  have hna := realLNeg_mem ha
  constructor
  · intro h hlt
    have hstep := realLLt_add_right (realLAdd_mem hb hna) realLZero_mem ha hlt
    rw [realLAdd_assoc hb hna ha, realLAdd_comm hna ha, realLAdd_neg ha,
      realLAdd_zero hb, realLZero_add ha] at hstep
    exact h hstep
  · intro h hlt
    refine h ?_
    have := realLLt_add_right hb ha hna hlt
    rwa [realLAdd_neg ha] at this

theorem realLLt_sub_pos {a b : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u}) :
    realLLt a b ↔ realLLt realLZero.{u} (realLAdd b (realLNeg a)) := by
  have hna := realLNeg_mem ha
  constructor
  · intro h
    have := realLLt_add_right ha hb hna h
    rwa [realLAdd_neg ha] at this
  · intro h
    have := realLLt_add_right realLZero_mem (realLAdd_mem hb hna) ha h
    rwa [realLZero_add ha, realLAdd_assoc hb hna ha,
      realLAdd_comm hna ha, realLAdd_neg ha, realLAdd_zero hb] at this

/-- Strict order adds. -/
theorem realLLt_add {a b c d : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (hd : d ∈ RealL.{u}) (h₁ : realLLt a b) (h₂ : realLLt c d) :
    realLLt (realLAdd a c) (realLAdd b d) := by
  refine realLLt_trans (realLAdd_mem ha hc) (realLAdd_mem hb hc) (realLAdd_mem hb hd)
    (realLLt_add_right ha hb hc h₁) ?_
  have := realLLt_add_right hc hd hb h₂
  rwa [realLAdd_comm hc hb, realLAdd_comm hd hb] at this

-- `apart_add_self_of_apart` stood here: the same statement as
-- `realLApart_add_self` (line ~3692), reached by `realLLt_add` on both
-- summands rather than `realLLt_add_right` plus transitivity. Same file, so the
-- two were visible to each other throughout; deleted rather than allowed,
-- because a same-file pair is the cheapest kind to resolve and the survivor is
-- the one its `realLApart_` siblings are named after.

/-- A doubled real that vanishes was already zero. Apartness is tight, so
refuting the apartness IS the equality. -/
theorem eq_zero_of_add_self_eq_zero {y : ZFSet.{u}} (hy : y ∈ RealL.{u})
    (h : realLAdd y y = realLZero.{u}) : y = realLZero.{u} := by
  have hnap : ¬ realLApart realLZero.{u} y := fun hz =>
    realLApart_irrefl realLZero_mem (h ▸ realLApart_add_self hy hz)
  exact realLLe_antisymm hy realLZero_mem
    (fun hlt => hnap (Or.inl hlt)) (fun hlt => hnap (Or.inr hlt))

/-- Mixed transitivity, one way. `realLLe` carries no witness, so cotransitivity
supplies it and the weak hypothesis refutes the wrong branch. -/
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

/-- `max` is symmetric: the halves are a union and an intersection. -/
theorem realLMax_comm (a b : ZFSet.{u}) : realLMax a b = realLMax b a := by
  rw [realLMax, realLMax, union_comm, inter_comm]

/-- Swap the inner terms of a double sum: `(a+b)+(c+e) = (a+e)+(c+b)`. -/
theorem realLAdd_swap_inner {a b c e : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hc : c ∈ RealL.{u}) (he : e ∈ RealL.{u}) :
    realLAdd (realLAdd a b) (realLAdd c e)
      = realLAdd (realLAdd a e) (realLAdd c b) := by
  rw [realLAdd_assoc ha hb (realLAdd_mem hc he),
    realLAdd_comm hc he,
    ← realLAdd_assoc hb he hc,
    realLAdd_comm hb he,
    realLAdd_assoc he hb hc,
    realLAdd_comm hb hc,
    ← realLAdd_assoc he hc hb,
    realLAdd_comm he hc,
    ← realLAdd_assoc ha (realLAdd_mem hc he) hb,
    realLAdd_comm hc he,
    ← realLAdd_assoc ha he hc,
    realLAdd_assoc (realLAdd_mem ha he) hc hb]


/-! ### Located-reals algebra placed from the geometry files

Eight lemmas that mention no geometry, moved here under geometry's 3164/3200.
They sat in the geometry files because that is where they were first needed,
and `realLApart` is defined here, so the apartness three belong here by
dependency and not merely by vocabulary. -/

/-- A product of two sums, expanded. With this, every quadratic identity
the Minkowski form needs is a rearrangement rather than a fresh distributivity
chain -- including the boost's, whose cross terms cancel between the two
squares before the unit relation is used at all. -/
theorem realL_add_mul_add {a b c d : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hc : c ∈ RealL.{u}) (hd : d ∈ RealL.{u}) :
    realLMul (realLAdd a b) (realLAdd c d)
      = realLAdd (realLAdd (realLMul a c) (realLMul a d))
          (realLAdd (realLMul b c) (realLMul b d)) := by
  rw [realLMul_comm (realLAdd_mem ha hb) (realLAdd_mem hc hd),
    realLMul_distrib (realLAdd_mem hc hd) ha hb,
    realLMul_comm (realLAdd_mem hc hd) ha,
    realLMul_distrib ha hc hd,
    realLMul_comm (realLAdd_mem hc hd) hb,
    realLMul_distrib hb hc hd]

/-- Apartness is a statement about the difference: `x # y` exactly when
`x - y # 0`, so an apartness hypothesis can be moved onto a norm. -/
theorem realLApart_iff_sub {x y : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) :
    realLApart x y ↔ realLApart realLZero.{u} (realLAdd x (realLNeg y)) := by
  have hny := realLNeg_mem hy
  have h0 : realLAdd y (realLNeg y) = realLZero.{u} := realLAdd_neg hy
  constructor
  · rintro (h | h)
    · refine Or.inr ?_
      have := realLLt_add_right hx hy hny h
      rwa [h0] at this
    · refine Or.inl ?_
      have := realLLt_add_right hy hx hny h
      rwa [h0] at this
  · rintro (h | h)
    · refine Or.inr ?_
      refine realLLt_add_right_cancel hy hx hny ?_
      rwa [h0]
    · refine Or.inl ?_
      refine realLLt_add_right_cancel hx hy hny ?_
      rwa [h0]


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

/-- Scaling preserves apartness, given the scalar is apart from zero. The
multiplicative companion of `realLLt_add_right`, and what carries an
independence hypothesis onto a norm. -/
theorem realLApart_mul_left {c x y : ZFSet.{u}} (hc : c ∈ RealL.{u})
    (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (hcap : realLApart realLZero.{u} c) (h : realLApart x y) :
    realLApart (realLMul c x) (realLMul c y) := by
  have hd := realLAdd_mem hx (realLNeg_mem hy)
  have hsub : realLApart realLZero.{u} (realLAdd x (realLNeg y)) :=
    (realLApart_iff_sub hx hy).mp h
  have hprod : realLApart realLZero.{u} (realLMul c (realLAdd x (realLNeg y))) :=
    apart_mul_apart hc hd hcap hsub
  refine (realLApart_iff_sub (realLMul_mem hc hx) (realLMul_mem hc hy)).mpr ?_
  rwa [realLMul_distrib hc hx (realLNeg_mem hy), realLMul_neg hc hy] at hprod
#print axioms Analysis.realLLe_antisymm
#print axioms Analysis.realLApart_tight
#print axioms Analysis.gridPt
#print axioms Analysis.LocatedReadout
#print axioms Analysis.realLNeg_realLAdd
#print axioms Analysis.realLAdd_mul
#print axioms Analysis.realLNeg_realLMul
#print axioms Analysis.realLSub_mul
#print axioms Analysis.realLAdd_interchange
#print axioms Analysis.realLSub_sq
#print axioms Analysis.realLNeg_sub
#print axioms Analysis.realLSub_add_sub
#print axioms Analysis.realLAdd_sub_add
#print axioms Analysis.realLAdd_sub_cancel_left
#print axioms Analysis.realLSub_sub
#print axioms Analysis.realLLt_sub_pos
#print axioms Analysis.realLLt_of_lt_of_le
#print axioms Analysis.realLLt_of_le_of_lt
#print axioms Analysis.realLLt_add
#print axioms Analysis.mulLower_nonneg_witnesses
#print axioms Analysis.mulLower_sub_realMulNonneg
#print axioms Analysis.eq_zero_of_add_self_eq_zero
#print axioms Analysis.realLLe_sub_nonneg
#print axioms Analysis.realLAdd_swap_inner
#print axioms Analysis.approx_diff
#print axioms Analysis.slack_add_lin
#print axioms Analysis.realLLe_refl
#print axioms Analysis.realLLe_of_lt
#print axioms Analysis.realLNeg_le_zero
#print axioms Analysis.realLLe_add_right
#print axioms Analysis.toCut_le
#print axioms Analysis.mulLower_eq_realMulNonneg
#print axioms Analysis.cauchySchwarz_realL

/-- The composite decomposition:
`(X - (A + M·U)) + M·(U - L·h) = X - (A + M·(L·h))`. -/
theorem chain_slack {X A Mv U L h : ZFSet.{u}} (hX : X ∈ RealL.{u}) (hA : A ∈ RealL.{u})
    (hMv : Mv ∈ RealL.{u}) (hU : U ∈ RealL.{u}) (hL : L ∈ RealL.{u})
    (hh : h ∈ RealL.{u}) :
    realLAdd (realLAdd X (realLNeg (realLAdd A (realLMul Mv U))))
        (realLMul Mv (realLAdd U (realLNeg (realLMul L h))))
      = realLAdd X (realLNeg (realLAdd A (realLMul Mv (realLMul L h)))) := by
  have hLh := realLMul_mem hL hh
  have hP := realLMul_mem hMv hU
  have hQ := realLMul_mem hMv hLh
  have hXA := realLAdd_mem hX (realLNeg_mem hA)
  rw [realLMul_distrib hMv hU (realLNeg_mem hLh),
    realLMul_comm hMv (realLNeg_mem hLh), realLNeg_realLMul hLh hMv,
    realLMul_comm hLh hMv,
    ← realLSub_sub hX hA hP, ← realLSub_sub hX hA hQ,
    realLAdd_assoc hXA (realLNeg_mem hP) (realLAdd_mem hP (realLNeg_mem hQ)),
    ← realLAdd_assoc (realLNeg_mem hP) hP (realLNeg_mem hQ),
    realLAdd_comm (realLNeg_mem hP) hP, realLAdd_neg hP,
    realLAdd_comm realLZero_mem (realLNeg_mem hQ), realLAdd_zero (realLNeg_mem hQ)]
/-- Multiplication by a positive real is strictly monotone. -/
theorem realLMul_lt_right {u v c : ZFSet.{u}} (hu : u ∈ RealL.{u}) (hv : v ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (huv : realLLt u v) (hc0 : realLLt realLZero.{u} c) :
    realLLt (realLMul u c) (realLMul v c) := by
  refine (realLLt_sub_pos (realLMul_mem hu hc) (realLMul_mem hv hc)).mpr ?_
  rw [realLSub_mul hv hu hc]
  exact realLMul_pos (realLAdd_mem hv (realLNeg_mem hu)) hc
    ((realLLt_sub_pos hu hv).mp huv) hc0
/-- The weak order adds. -/
theorem realLLe_add {a b c d : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (hd : d ∈ RealL.{u}) (h₁ : realLLe a b) (h₂ : realLLe c d) :
    realLLe (realLAdd a c) (realLAdd b d) := by
  refine realLLe_trans (realLAdd_mem ha hc) (realLAdd_mem hb hc) (realLAdd_mem hb hd)
    (realLLe_add_right ha hb hc h₁) ?_
  have := realLLe_add_right hc hd hb h₂
  rwa [realLAdd_comm hc hb, realLAdd_comm hd hb] at this

/-- Two half-epsilon bounds compose into one whole-epsilon bound.

    a ≤ b + ε/2   and   b + c ≤ M + ε/2   ⊢   a + c ≤ M + ε

`b` is the intermediate quantity: the first bound overshoots it by `ε/2`, the
second places it with `c` under `M` up to another `ε/2`, and the two halves fold
by `ratMid_add_self`.

`hh` IS A HYPOTHESIS RATHER THAN A DERIVATION: every call site already holds
it, so taking it costs no caller anything.
-/
theorem realLLe_add_of_halves {a b c M e : ZFSet.{u}}
    (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u}) (hc : c ∈ RealL.{u})
    (hM : M ∈ RealL.{u}) (he : e ∈ NumberTheory.Rat.{u})
    (hh : NumberTheory.ratMid NumberTheory.ratZero.{u} e ∈ NumberTheory.Rat.{u})
    (h₁ : realLLe a (realLAdd b (realLOf (NumberTheory.ratMid NumberTheory.ratZero.{u} e))))
    (h₂ : realLLe (realLAdd b c)
      (realLAdd M (realLOf (NumberTheory.ratMid NumberTheory.ratZero.{u} e)))) :
    realLLe (realLAdd a c) (realLAdd M (realLOf e)) := by
  have hhm : realLOf (NumberTheory.ratMid NumberTheory.ratZero.{u} e) ∈ RealL.{u} :=
    realLOf_mem hh
  have step1 : realLLe (realLAdd a c)
      (realLAdd (realLAdd b (realLOf (NumberTheory.ratMid NumberTheory.ratZero.{u} e))) c) :=
    realLLe_add ha (realLAdd_mem hb hhm) hc hc h₁ (realLLe_refl hc)
  have swap : realLAdd (realLAdd b
        (realLOf (NumberTheory.ratMid NumberTheory.ratZero.{u} e))) c
      = realLAdd (realLAdd b c)
        (realLOf (NumberTheory.ratMid NumberTheory.ratZero.{u} e)) := by
    rw [realLAdd_assoc hb hhm hc, realLAdd_comm hhm hc,
      ← realLAdd_assoc hb hc hhm]
  have step2 : realLLe (realLAdd (realLAdd b c)
        (realLOf (NumberTheory.ratMid NumberTheory.ratZero.{u} e)))
      (realLAdd (realLAdd M (realLOf (NumberTheory.ratMid NumberTheory.ratZero.{u} e)))
        (realLOf (NumberTheory.ratMid NumberTheory.ratZero.{u} e))) :=
    realLLe_add (realLAdd_mem hb hc) (realLAdd_mem hM hhm) hhm hhm h₂
      (realLLe_refl hhm)
  have fold : realLAdd (realLAdd M
        (realLOf (NumberTheory.ratMid NumberTheory.ratZero.{u} e)))
      (realLOf (NumberTheory.ratMid NumberTheory.ratZero.{u} e))
      = realLAdd M (realLOf e) := by
    rw [realLAdd_assoc hM hhm hhm, ← realLOf_add hh hh,
      NumberTheory.ratMid_add_self he]
  rw [← fold]
  exact realLLe_trans (realLAdd_mem ha hc)
    (realLAdd_mem (realLAdd_mem hb hc) hhm)
    (realLAdd_mem (realLAdd_mem hM hhm) hhm) (swap ▸ step1) step2

#print axioms realLLe_add_of_halves

/-- Two non-negatives summing to zero are each zero, by antisymmetry alone:
adding a non-negative can only increase, so `a` is at most the sum, and the sum
is zero. Nothing is decided, and `eq_zero_of_add_self_eq_zero` reaches the
doubled case a different way -- through apartness rather than the order -- so
neither subsumes the other. -/
theorem eq_zero_of_add_eq_zero {a b : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (ha0 : realLLe realLZero.{u} a)
    (hb0 : realLLe realLZero.{u} b) (h : realLAdd a b = realLZero.{u}) :
    a = realLZero.{u} := by
  refine realLLe_antisymm ha realLZero_mem ?_ ha0
  have hstep : realLLe (realLAdd a realLZero.{u}) (realLAdd a b) :=
    realLLe_add ha ha realLZero_mem hb (realLLe_refl ha) hb0
  rwa [realLAdd_zero ha, h] at hstep

/-- Adding something non-negative does not decrease. -/
theorem realLLe_self_add_nonneg {a b : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (h0 : realLLe realLZero.{u} b) :
    realLLe a (realLAdd a b) := by
  have h := realLLe_add ha ha realLZero_mem hb (realLLe_refl ha) h0
  rwa [realLAdd_zero ha] at h

#print axioms realLLe_self_add_nonneg

/-- `x ≤ y` read as `x - y ≤ 0`. -/
theorem realLSub_nonpos_of_le {x y : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (h : realLLe x y) : realLLe (realLAdd x (realLNeg y)) realLZero.{u} :=
  fun hlt => h ((realLLt_sub_pos hy hx).mpr hlt)
/-- `a - b ≤ d` exactly when `a ≤ b + d`, as reals. -/
theorem realLSub_le_iff {a b d : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hd : d ∈ RealL.{u}) :
    Iff (realLLe (realLAdd a (realLNeg b)) d) (realLLe a (realLAdd b d)) := by
  constructor
  · intro h
    have := realLLe_add_right (realLAdd_mem ha (realLNeg_mem hb)) hd hb h
    rwa [realLSub_add_cancel ha hb, realLAdd_comm hd hb] at this
  · intro h
    have := realLLe_add_right ha (realLAdd_mem hb hd) (realLNeg_mem hb) h
    rwa [realLAdd_comm hb hd,
      realLAdd_assoc hd hb (realLNeg_mem hb),
      realLAdd_neg hb, realLAdd_zero hd] at this
/-- A common shift distributes out of the max, one direction. -/
theorem realLMax_shift_le {a b c : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hc : c ∈ RealL.{u}) :
    realLLe (realLMax (realLAdd a c) (realLAdd b c))
      (realLAdd (realLMax a b) c) := by
  refine realLMax_le ?_ ?_
  · exact realLLe_add_right ha (realLMax_mem ha hb) hc (realLLe_max_left ha)
  · exact realLLe_add_right hb (realLMax_mem ha hb) hc (realLLe_max_right hb)
/-- The rearrangement the induction turns on: the new discrepancy is the old one
plus the cell's. -/
theorem riemann_step_eq {A P X Y C : ZFSet.{u}} (hA : A ∈ RealL.{u}) (hP : P ∈ RealL.{u})
    (hX : X ∈ RealL.{u}) (hY : Y ∈ RealL.{u}) (hC : C ∈ RealL.{u}) :
    realLAdd (realLAdd A (realLNeg (realLAdd X (realLNeg C))))
        (realLAdd P (realLNeg (realLAdd Y (realLNeg X))))
      = realLAdd (realLAdd A P) (realLNeg (realLAdd Y (realLNeg C))) := by
  rw [realLAdd_interchange hA (realLNeg_mem (realLAdd_mem hX (realLNeg_mem hC))) hP
      (realLNeg_mem (realLAdd_mem hY (realLNeg_mem hX))),
    ← realLNeg_realLAdd (realLAdd_mem hX (realLNeg_mem hC))
      (realLAdd_mem hY (realLNeg_mem hX)),
    realLAdd_comm (realLAdd_mem hX (realLNeg_mem hC))
      (realLAdd_mem hY (realLNeg_mem hX)),
    realLSub_add_sub hX hY hC]

/-- Shifting both sides by the same real cancels: `(x - L) - (y - L) = x - y`. -/
theorem sub_shift_cancel {x y L : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hL : L ∈ RealL.{u}) :
    realLAdd (realLAdd x (realLNeg L)) (realLNeg (realLAdd y (realLNeg L)))
      = realLAdd x (realLNeg y) := by
  have hnL := realLNeg_mem hL
  have hny := realLNeg_mem hy
  rw [realLNeg_realLAdd hy hnL, realLNeg_realLNeg hL,
    realLAdd_assoc hx hnL (realLAdd_mem hny hL),
    ← realLAdd_assoc hnL hny hL, realLAdd_comm hnL hny,
    realLAdd_assoc hny hnL hL, realLAdd_comm hnL hL, realLAdd_neg hL,
    realLAdd_zero hny]
theorem realLSub_eq_zero_iff {x y : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u}) :
    realLAdd x (realLNeg y) = realLZero.{u} ↔ x = y := by
  constructor
  · intro h
    have := congrArg (fun z => realLAdd z y) h
    simp only at this
    rwa [realLSub_add_cancel hx hy, realLZero_add hy] at this
  · rintro rfl
    exact realLAdd_neg hx
/-- The square of a difference, expanded to the four products the sums
recognise. -/
theorem sq_sub_expand {a x : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hx : x ∈ RealL.{u}) :
    realLMul (realLAdd a (realLNeg x)) (realLAdd a (realLNeg x))
    = realLAdd (realLMul a a) (realLAdd (realLMul (realLNeg x) a)
        (realLAdd (realLMul (realLNeg x) a)
          (realLMul (realLNeg x) (realLNeg x)))) := by
  have hnx := realLNeg_mem hx
  have hs := realLAdd_mem ha hnx
  rw [realLAdd_mul ha hnx hs, realLMul_distrib ha ha hnx,
    realLMul_distrib hnx ha hnx,
    realLMul_comm ha hnx,
    realLAdd_assoc (realLMul_mem ha ha) (realLMul_mem hnx ha)
      (realLAdd_mem (realLMul_mem hnx ha) (realLMul_mem hnx hnx))]

set_option maxHeartbeats 1000000 in
/-- Squares of negations agree. -/
theorem realLNeg_sq {a : ZFSet.{u}} (ha : a ∈ RealL.{u}) :
    realLMul (realLNeg a) (realLNeg a) = realLMul a a := by
  rw [realLNeg_realLMul ha (realLNeg_mem ha), realLMul_comm ha
    (realLNeg_mem ha), realLNeg_realLMul ha ha,
    realLNeg_realLNeg (realLMul_mem ha ha)]
/-- The rearrangement the reflection induction turns on:
`(A + ((B + C) - T)) + (D - C) = (A + D) + (B - T)`. -/
theorem reflect_step_eq {A B C T D : ZFSet.{u}} (hA : A ∈ RealL.{u})
    (hB : B ∈ RealL.{u}) (hC : C ∈ RealL.{u}) (hT : T ∈ RealL.{u})
    (hD : D ∈ RealL.{u}) :
    realLAdd (realLAdd A (realLAdd (realLAdd B C) (realLNeg T)))
      (realLAdd D (realLNeg C))
    = realLAdd (realLAdd A D) (realLAdd B (realLNeg T)) := by
  have hBC := realLAdd_mem hB hC
  have hnT := realLNeg_mem hT
  have hnC := realLNeg_mem hC
  rw [realLAdd_assoc hA (realLAdd_mem hBC hnT) (realLAdd_mem hD hnC),
    realLAdd_interchange hBC hnT hD hnC,
    realLAdd_comm hnT hnC,
    realLAdd_interchange hBC hD hnC hnT,
    realLAdd_assoc hB hC hnC, realLAdd_neg hC, realLAdd_zero hB,
    ← realLAdd_assoc hB hD hnT, realLAdd_comm hB hD,
    realLAdd_assoc hD hB hnT,
    ← realLAdd_assoc hA hD (realLAdd_mem hB hnT)]
/-- What splitting a cell costs. The coarse cell contributes `P·(w₁+w₂)`
and the two fine cells `P·w₁ + Q·w₂`, so the sums drift apart by exactly
`(Q - P)·w₂` -- the difference of the two sample values, times the second
half-width. That is why uniform continuity is enough: `P` and `Q` are values at
points inside one coarse cell. -/
theorem cell_split {A B P Q w₁ w₂ : ZFSet.{u}} (hA : A ∈ RealL.{u})
    (hB : B ∈ RealL.{u}) (hP : P ∈ RealL.{u}) (hQ : Q ∈ RealL.{u})
    (hw₁ : w₁ ∈ RealL.{u}) (hw₂ : w₂ ∈ RealL.{u}) :
    realLAdd (realLAdd (realLAdd A (realLMul P w₁)) (realLMul Q w₂))
        (realLNeg (realLAdd B (realLMul P (realLAdd w₁ w₂))))
      = realLAdd (realLAdd A (realLNeg B))
        (realLMul (realLAdd Q (realLNeg P)) w₂) := by
  have hPw₁ := realLMul_mem hP hw₁
  have hPw₂ := realLMul_mem hP hw₂
  have hQw₂ := realLMul_mem hQ hw₂
  -- put the shared `P·w₁` first on both sides and cancel it
  rw [realLMul_distrib hP hw₁ hw₂,
    realLAdd_assoc hA hPw₁ hQw₂, realLAdd_comm hPw₁ hQw₂,
    ← realLAdd_assoc hA hQw₂ hPw₁,
    realLAdd_comm hPw₁ hPw₂, ← realLAdd_assoc hB hPw₂ hPw₁,
    realLAdd_comm (realLAdd_mem hA hQw₂) hPw₁,
    realLAdd_comm (realLAdd_mem hB hPw₂) hPw₁,
    realLAdd_sub_cancel_left hPw₁ (realLAdd_mem hA hQw₂) (realLAdd_mem hB hPw₂),
    realLAdd_sub_add hA hQw₂ hB hPw₂, realLSub_mul hQ hP hw₂]
/-- `(S + Q·w₂) - P·(w₁ + w₂) = (S - P·w₁) + (Q - P)·w₂`. The running
discrepancy is against a single sample value `P`, so unlike `cell_split` there
is no second sum to carry: each new cell costs the gap between its own sample
and `P`. -/
theorem block_split {S P Q w₁ w₂ : ZFSet.{u}} (hS : S ∈ RealL.{u}) (hP : P ∈ RealL.{u})
    (hQ : Q ∈ RealL.{u}) (hw₁ : w₁ ∈ RealL.{u}) (hw₂ : w₂ ∈ RealL.{u}) :
    realLAdd (realLAdd S (realLMul Q w₂)) (realLNeg (realLMul P (realLAdd w₁ w₂)))
      = realLAdd (realLAdd S (realLNeg (realLMul P w₁)))
        (realLMul (realLAdd Q (realLNeg P)) w₂) := by
  rw [realLMul_distrib hP hw₁ hw₂,
    realLAdd_sub_add hS (realLMul_mem hQ hw₂) (realLMul_mem hP hw₁)
      (realLMul_mem hP hw₂),
    realLSub_mul hQ hP hw₂]
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
/-- A sum of non-negative reals is non-negative -- the additive companion
of `realLMul_nonneg`. Nothing decides which summand carries the weight: the
bound moves along the order, so neither side is examined. -/
theorem realLAdd_nonneg {x y : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (h0x : realLLe realLZero.{u} x) (h0y : realLLe realLZero.{u} y) :
    realLLe realLZero.{u} (realLAdd x y) := by
  have step := realLLe_add_right realLZero_mem hx hy h0x
  rw [realLZero_add hy] at step
  exact realLLe_trans realLZero_mem hy (realLAdd_mem hx hy) h0y step
/-- From `a - b ≤ ε`, the value `a` is no more than `ε` above `b`. -/
theorem le_add_of_sub_le {a b e : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (he : e ∈ RealL.{u}) (h : realLLe (realLAdd a (realLNeg b)) e) :
    realLLe a (realLAdd b e) := by
  have hnb := realLNeg_mem hb
  have h1 := realLLe_add_right (realLAdd_mem ha hnb) he hb h
  rwa [realLAdd_assoc ha hnb hb, realLAdd_comm hnb hb, realLAdd_neg hb,
    realLAdd_zero ha, realLAdd_comm he hb] at h1
/-- From `-ε ≤ a - b`, the value `b` is no more than `ε` above `a`.

The mirror of `realLLe_sub_of_sub_le`: together the two are the two sides of
`WithinOf` read as bounds on `b`. -/
theorem le_add_of_neg_le_sub'  {a b e : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (he : e ∈ RealL.{u})
    (h : realLLe (realLNeg e) (realLAdd a (realLNeg b))) :
    realLLe b (realLAdd a e) := by
  have hnb := realLNeg_mem hb
  have hne := realLNeg_mem he
  have h1 := realLLe_add_right hne (realLAdd_mem ha hnb) hb h
  rw [realLAdd_assoc ha hnb hb, realLAdd_comm hnb hb, realLAdd_neg hb,
    realLAdd_zero ha] at h1
  have h2 := realLLe_add_right (realLAdd_mem hne hb) ha he h1
  rwa [realLAdd_assoc hne hb he, realLAdd_comm hb he,
    ← realLAdd_assoc hne he hb, realLAdd_comm hne he, realLAdd_neg he,
    realLZero_add hb] at h2
/-- Reading `-a < -b` forwards, which `realLNeg_lt_neg` and double negation
together allow. -/
theorem realLLt_of_neg_lt_neg {a b : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (h : realLLt (realLNeg a) (realLNeg b)) :
    realLLt b a := by
  have := realLNeg_lt_neg (realLNeg_mem ha) (realLNeg_mem hb) h
  rwa [realLNeg_realLNeg ha, realLNeg_realLNeg hb] at this
/-- The two orientations of a difference are negatives of each other. -/
theorem sub_add_sub_eq_zero {x y : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) :
    realLAdd (realLAdd y (realLNeg x)) (realLAdd x (realLNeg y))
      = realLZero.{u} := by
  have hnx := realLNeg_mem hx
  have hny := realLNeg_mem hy
  rw [realLAdd_assoc hy hnx (realLAdd_mem hx hny),
    ← realLAdd_assoc hnx hx hny, realLAdd_comm hnx hx, realLAdd_neg hx,
    realLZero_add hny, realLAdd_neg hy]
/-- Every located real IS its pair of cuts, so the locator hypotheses are
stated with `fst`/`snd` rather than with an equation. -/
theorem realL_eq_opair {w : ZFSet.{u}} (hw : w ∈ RealL.{u}) :
    w = opair (fst w) (snd w) := by
  obtain ⟨L, U, rfl, -⟩ := (mem_RealL_iff w).mp hw
  rw [fst_opair, snd_opair]
/-- An inverse is unique. `realLInvApart` is a CONSTRUCTION, so two proofs
arriving at "the inverse" by different routes cannot be identified without this. -/
theorem realL_inv_unique {a e e' : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (he : e ∈ RealL.{u}) (he' : e' ∈ RealL.{u})
    (h : realLMul a e = realLOne.{u}) (h' : realLMul a e' = realLOne.{u}) :
    e = e' := by
  have step : realLMul e (realLMul a e') = realLMul e realLOne.{u} := by rw [h']
  rw [← realLMul_assoc he ha he', realLMul_comm he ha, h,
    realLOne_mul he', realLMul_one he] at step
  exact step.symm
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


/-- A located real is dominated by a natural. Every `x` has an `n : Nat`
with `x < n`.

The two clauses that give it: `upper_inhabited` produces a rational in the
upper set, which `lt_realLOf_iff_mem_upper` turns into a bound with no search,
and `exists_ratNatMul_gt` at `d = 1` passes it with a natural.

`rat_archimedean` is the other Archimedean statement here and is the wrong
SHAPE: it lands in `ratOf (intOfNat n) b`, so every later step would carry an
`intOfNat 1` against `intOne`. `exists_ratNatMul_gt` lands in `ratNat`, which is
the vocabulary the exponential's terms are written in. -/
theorem exists_natBound_realL {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    ∃ n : Nat, realLLt x (realLOf (ratNat.{u} n 1)) := by
  obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨r, hrU⟩ := hloc.upper_inhabited
  have hrQ : r ∈ NumberTheory.Rat.{u} := hloc.upper_subset r hrU
  have hxr : realLLt (opair L U) (realLOf r) :=
    (lt_realLOf_iff_mem_upper hx hrQ).mpr (by rw [snd_opair]; exact hrU)
  have hone : ratLt ratZero.{u} (ratNat.{u} 1 1) :=
    ratNat_one_pos (Nat.succ_pos 0)
  obtain ⟨n, hn⟩ := exists_ratNatMul_gt (ratNat_mem_Rat (Nat.succ_pos 0)) hrQ hone
  rw [ratNatMul_ratNat (Nat.succ_pos 0) n, Nat.mul_one] at hn
  exact ⟨n, realLLt_trans hx (realLOf_mem hrQ)
    (realLOf_mem (ratNat_mem_Rat (Nat.succ_pos 0))) hxr
    ((realLOf_lt_realLOf hrQ (ratNat_mem_Rat (Nat.succ_pos 0))).mpr hn)⟩

/-- And a natural below it, the mirror of the bound above: a located real
carries a lower rational as well as an upper one, so both halves come from
`IsLocated` and neither decides anything about the sign of `x`. -/
theorem exists_natBound_below {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    ∃ n : Nat, realLLt (realLOf (ratNeg (ratNat.{u} n 1))) x := by
  obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨q, hqL⟩ := hloc.lower_inhabited
  have hqQ : q ∈ NumberTheory.Rat.{u} := hloc.lower_subset q hqL
  have hqx : realLLt (realLOf q) (opair L U) :=
    (realLOf_lt_iff_mem_lower hx hqQ).mpr (by rw [fst_opair]; exact hqL)
  have hone : ratLt ratZero.{u} (ratNat.{u} 1 1) :=
    ratNat_one_pos (Nat.succ_pos 0)
  obtain ⟨n, hn⟩ := exists_ratNatMul_gt (ratNat_mem_Rat (Nat.succ_pos 0))
    (ratNeg_mem_Rat hqQ) hone
  rw [ratNatMul_ratNat (Nat.succ_pos 0) n, Nat.mul_one] at hn
  have hnq : ratLt (ratNeg (ratNat.{u} n 1)) q := by
    have := (ratNeg_lt_neg_iff (ratNat_mem_Rat (Nat.succ_pos 0))
      (ratNeg_mem_Rat hqQ)).mpr hn
    rwa [ratNeg_ratNeg hqQ] at this
  exact ⟨n, realLLt_trans (realLOf_mem (ratNeg_mem_Rat
      (ratNat_mem_Rat (Nat.succ_pos 0)))) (realLOf_mem hqQ) hx
    ((realLOf_lt_realLOf (ratNeg_mem_Rat (ratNat_mem_Rat (Nat.succ_pos 0)))
      hqQ).mpr hnq) hqx⟩

/-- A finer scale is a smaller real, so the bundle takes its mesh to be
`m + modulus m` rather than `modulus m`: `approx` asks for closeness
at `invScale (modulus m)`, and closeness at the finer `invScale (m + modulus m)`
implies it. Without a mesh at least `m` the grid never refines and `limit`
cannot be met, since `UniformOn.modulus` may be constant. -/
theorem invScale_antitone {a b : Nat} (hab : a ≤ b) :
    realLLe (invScale.{u} b) (invScale.{u} a) :=
  (realLOf_le_realLOf (invWidth_mem_Rat (ofNat_mem_omega b))
      (invWidth_mem_Rat (ofNat_mem_omega a))).mpr
    (invWidth_antitone (ofNat_mem_omega a) (ofNat_mem_omega b)
      ((ofNat_subset_iff a b).mpr hab))
/-- Adding a positive rational strictly increases a located real.

The step every epsilon argument opens with. `realLZero` is `realLOf ratZero` by
definition, so the positivity transfers through `realLOf_lt_realLOf` with
nothing to prove. -/
theorem realLLt_self_add_pos {L e : ZFSet.{u}} (hL : L ∈ RealL.{u}) (he : e ∈ NumberTheory.Rat.{u})
    (he0 : ratLt ratZero.{u} e) : realLLt L (realLAdd L (realLOf e)) := by
  have h0 : realLLt realLZero.{u} (realLOf e) :=
    (realLOf_lt_realLOf ratZero_mem_Rat he).mpr he0
  have hstep : realLLt (realLAdd realLZero.{u} L) (realLAdd (realLOf e) L) :=
    realLLt_add_right realLZero_mem (realLOf_mem he) hL h0
  rw [realLZero_add hL,
    realLAdd_comm (realLOf_mem he) hL] at hstep
  exact hstep

/-- Subtracting a positive rational strictly decreases a located real.

The mirror of `realLLt_self_add_pos`, and the other half of what an
`(x - e, x + e)` neighbourhood claim needs: an epsilon-ball hypothesis about a
real is two strict inequalities, and this is the lower one.

THE NEGATION STAYS ON THE REAL, and it has to: pushing it onto the rational by
`realLOf_neg` is the obvious route and that lemma lives in `IVT.lean`,
DOWNSTREAM of this file, so it is not in scope here at all.
`realLNeg_neg_of_pos` does the same step with no rational arithmetic at all. -/
theorem realLLt_sub_pos_self {L e : ZFSet.{u}} (hL : L ∈ RealL.{u})
    (he : e ∈ NumberTheory.Rat.{u}) (he0 : ratLt ratZero.{u} e) :
    realLLt (realLAdd L (realLNeg (realLOf e))) L := by
  have h0 : realLLt realLZero.{u} (realLOf e) :=
    (realLOf_lt_realLOf ratZero_mem_Rat he).mpr he0
  have hneg := realLNeg_neg_of_pos (realLOf_mem he) h0
  have h := realLLt_add_right (realLNeg_mem (realLOf_mem he)) realLZero_mem hL hneg
  rwa [realLAdd_comm (realLNeg_mem (realLOf_mem he)) hL, realLZero_add hL] at h

/-- A product of non-negatives is non-negative. -/
theorem realLMul_nonneg {x y : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (hx0 : realLLe realLZero.{u} x) (hy0 : realLLe realLZero.{u} y) :
    realLLe realLZero.{u} (realLMul x y) := by
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff y).mp hy
  have hupper : ∀ (U : ZFSet.{u}) (z : ZFSet.{u}),
      ¬ realLLt z realLZero.{u} → snd z = U → ∀ t, t ∈ U → t ∈ NumberTheory.Rat.{u} →
      ratLe ratZero.{u} t := by
    intro U z hz hsnd t ht htQ
    refine ratLe_of_not_lt ratZero_mem_Rat htQ (fun hlt => hz ⟨t, ?_, ?_⟩)
    · rw [hsnd]; exact ht
    · rw [realLZero, realLOf, fst_opair]
      exact (mem_ratCut_iff _ t).mpr ⟨htQ, hlt⟩
  rintro ⟨p, hpU, hpL⟩
  rw [realLZero, realLOf, fst_opair] at hpL
  obtain ⟨hpQ, hp0⟩ := (mem_ratCut_iff _ p).mp hpL
  rw [realLMul, fst_opair, snd_opair, fst_opair, snd_opair, snd_opair] at hpU
  obtain ⟨-, q, hq, q', hq', r, hr, r', hr', -, -, -, c₄⟩ :=
    (mem_mulUpper_iff _ _ _ _ p).mp hpU
  have hq'0 := hupper U₁ _ hx0 (snd_opair L₁ U₁) q' hq' (h₁.upper_subset q' hq')
  have hr'0 := hupper U₂ _ hy0 (snd_opair L₂ U₂) r' hr' (h₂.upper_subset r' hr')
  exact ratLt_irrefl (ratLt_of_le_of_lt ratZero_mem_Rat
    (ratMul_mem_Rat (h₁.upper_subset q' hq') (h₂.upper_subset r' hr')) ratZero_mem_Rat
    (ratZero_le_mul (h₁.upper_subset q' hq') (h₂.upper_subset r' hr') hq'0 hr'0)
    (ratLt_trans (ratMul_mem_Rat (h₁.upper_subset q' hq') (h₂.upper_subset r' hr'))
      hpQ ratZero_mem_Rat c₄ hp0))
/-- Multiplication by a non-negative real is monotone. -/
theorem realLMul_le_right {u v c : ZFSet.{u}} (hu : u ∈ RealL.{u}) (hv : v ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (huv : realLLe u v) (hc0 : realLLe realLZero.{u} c) :
    realLLe (realLMul u c) (realLMul v c) := by
  refine (realLLe_sub_nonneg (realLMul_mem hu hc) (realLMul_mem hv hc)).mpr ?_
  rw [realLSub_mul hv hu hc]
  exact realLMul_nonneg (realLAdd_mem hv (realLNeg_mem hu)) hc
    ((realLLe_sub_nonneg hu hv).mp huv) hc0

/-- Multiplication on the left by a non-negative real is monotone. -/
theorem realLMul_le_left {u v c : ZFSet.{u}} (hu : u ∈ RealL.{u}) (hv : v ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (huv : realLLe u v) (hc0 : realLLe realLZero.{u} c) :
    realLLe (realLMul c u) (realLMul c v) := by
  rw [realLMul_comm hc hu, realLMul_comm hc hv]
  exact realLMul_le_right hu hv hc huv hc0


/-! ## Differentiability on an interval

Nothing about the slope function is asked for in the definition. Where a bound
on it is needed the bound is a hypothesis, because a supremum over an interval
is exactly the thing a constructive development cannot help itself to. -/
/-- The embedding carries multiplication. Both inclusions are one corner
lemma: a rational above the product beats every corner of a bracket around
`(a, b)`, and a rational below it is beaten by every one. -/
theorem realLOf_mul {a b : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u}) (hb : b ∈ NumberTheory.Rat.{u}) :
    realLOf (ratMul a b) = realLMul (realLOf a) (realLOf b) := by
  have hab := ratMul_mem_Rat ha hb
  have hprod : realLMul (realLOf a) (realLOf b)
      = opair (mulLower (ratCut a) (sep (fun p => ratLt a p) NumberTheory.Rat.{u})
          (ratCut b) (sep (fun p => ratLt b p) NumberTheory.Rat.{u}))
        (mulUpper (ratCut a) (sep (fun p => ratLt a p) NumberTheory.Rat.{u})
          (ratCut b) (sep (fun p => ratLt b p) NumberTheory.Rat.{u})) := by
    rw [realLMul, realLOf, realLOf, fst_opair, snd_opair, fst_opair, snd_opair]
  refine realLLe_antisymm (realLOf_mem hab)
    (realLMul_mem (realLOf_mem ha) (realLOf_mem hb)) ?_ ?_
  · rintro ⟨p, hpU, hpL⟩
    rw [hprod, snd_opair] at hpU
    rw [realLOf, fst_opair] at hpL
    obtain ⟨hpQ, hplt⟩ := (mem_ratCut_iff _ p).mp hpL
    obtain ⟨-, q, hq, q', hq', r, hr, r', hr', c₁, c₂, c₃, c₄⟩ :=
      (mem_mulUpper_iff _ _ _ _ p).mp hpU
    obtain ⟨hqQ, hqa⟩ := (mem_ratCut_iff a q).mp hq
    obtain ⟨hq'Q, haq'⟩ := (mem_sep_iff _ q' _).mp hq'
    obtain ⟨hrQ, hrb⟩ := (mem_ratCut_iff b r).mp hr
    obtain ⟨hr'Q, hbr'⟩ := (mem_sep_iff _ r' _).mp hr'
    exact ratLt_irrefl (ratLt_trans hab hpQ hab
      (ratMul_lt_of_corners hpQ hqQ hq'Q hrQ hr'Q ha hb hqa.left haq'.left hrb.left
        hbr'.left c₁ c₂ c₃ c₄) hplt)
  · rintro ⟨p, hpU, hpL⟩
    rw [realLOf, snd_opair] at hpU
    rw [hprod, fst_opair] at hpL
    obtain ⟨hpQ, habp⟩ := (mem_sep_iff _ p _).mp hpU
    obtain ⟨-, q, hq, q', hq', r, hr, r', hr', c₁, c₂, c₃, c₄⟩ :=
      (mem_mulLower_iff _ _ _ _ p).mp hpL
    obtain ⟨hqQ, hqa⟩ := (mem_ratCut_iff a q).mp hq
    obtain ⟨hq'Q, haq'⟩ := (mem_sep_iff _ q' _).mp hq'
    obtain ⟨hrQ, hrb⟩ := (mem_ratCut_iff b r).mp hr
    obtain ⟨hr'Q, hbr'⟩ := (mem_sep_iff _ r' _).mp hr'
    exact ratLt_irrefl (ratLt_trans hab hpQ hab habp
      (ratLt_mul_of_corners hpQ hqQ hq'Q hrQ hr'Q ha hb hqa.left haq'.left hrb.left
        hbr'.left c₁ c₂ c₃ c₄))
/-- Inversion reverses the order: `0 < a <= b` gives `1/b <= 1/a`.

`realLInv_le_of_le` below compares `1/z` against `realLOf (ratInv c)` for a
RATIONAL `c`, which is what the cut arguments needed. This is the two-real
statement, and the difference matters: a comparison between two constructed
reals --- two powers `r^s` and `r^t`, say --- has no rational in hand to route
through.

The proof multiplies the hypothesis by the positive `(1/a)(1/b)` and lets
`realLMul_inv` collapse each side: `a * (1/a) * (1/b)` is `1/b`, and
`b * (1/b) * (1/a)` is `1/a`. No cut is opened and nothing is decided. -/
theorem realLInv_antitone {a b : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (ha0 : realLLt realLZero.{u} a)
    (hab : realLLe a b) :
    realLLe (realLInv b) (realLInv a) := by
  have hb0 : realLLt realLZero.{u} b :=
    realLLt_of_lt_of_le realLZero_mem ha hb ha0 hab
  have hia := realLInv_mem ha ha0
  have hib := realLInv_mem hb hb0
  have hprod := realLMul_mem hia hib
  have hprod0 : realLLe realLZero.{u} (realLMul (realLInv a) (realLInv b)) :=
    realLLe_of_lt realLZero_mem hprod
      (realLMul_pos hia hib (realLInv_pos ha ha0) (realLInv_pos hb hb0))
  have h := realLMul_le_right ha hb hprod hab hprod0
  -- `a * ((1/a)(1/b))` collapses to `1/b`, and `b * ((1/a)(1/b))` to `1/a`
  rwa [← realLMul_assoc ha hia hib, realLMul_inv ha ha0, realLOne_mul hib,
    realLMul_comm hia hib, ← realLMul_assoc hb hib hia,
    realLMul_inv hb hb0, realLOne_mul hia] at h

#print axioms realLInv_antitone

/-- The inverse is unique: anything multiplying `z` to one IS `1/z`.

`realLMul_ratInv_cancel` shows that `realLOf (ratInv d)` cancels `realLOf d`
without saying that such a witness must BE `realLInv`. This identifies a
rational reciprocal with the constructed one.

One line of associativity: `w = w * (z * (1/z)) = (w * z) * (1/z) = 1/z`. -/
theorem realLInv_eq_of_mul_one {z w : ZFSet.{u}} (hz : z ∈ RealL.{u})
    (hw : w ∈ RealL.{u}) (hz0 : realLLt realLZero.{u} z)
    (h : realLMul z w = realLOne.{u}) :
    w = realLInv z := by
  have hiz := realLInv_mem hz hz0
  have hstep : realLMul (realLMul w z) (realLInv z)
      = realLMul w (realLMul z (realLInv z)) := realLMul_assoc hw hz hiz
  rw [realLMul_inv hz hz0, realLMul_one hw, realLMul_comm hw hz, h,
    realLOne_mul hiz] at hstep
  -- the chain lands on `1/z = w`; the statement is the other way round
  exact hstep.symm

#print axioms realLInv_eq_of_mul_one

/-- And so `realLInv` of a rational IS the rational inverse.

This is the bridge a Dirichlet term needs: `1/(n+1)` written as `invScale` and
`1/(n+1)` written as `realLInv` of a real are the same object, which until now
could only be shown by reopening the cut. -/
theorem realLInv_realLOf {d : ZFSet.{u}} (hd : d ∈ NumberTheory.Rat.{u})
    (hne : d ≠ ratZero.{u}) (hpos : realLLt realLZero.{u} (realLOf d)) :
    realLInv (realLOf d) = realLOf (ratInv d) := by
  refine (realLInv_eq_of_mul_one (realLOf_mem hd)
    (realLOf_mem (ratInv_mem_Rat hd hne)) hpos ?_).symm
  rw [← realLOf_mul hd (ratInv_mem_Rat hd hne), ratMul_inv hd hne]
  rfl

#print axioms realLInv_realLOf


/-- The reciprocal of a positive real is bounded by the reciprocal of a
rational below it. Proved by multiplying rather than by comparing cuts: if
the bound failed, multiplying the strict inequality by `z` would put `1`
strictly below itself. The converse of Carathéodory needs it to divide the
derivative's error by the increment, and so needs a lower bound on the
increment supplied. -/
theorem realLInv_le_of_le {z c : ZFSet.{u}} (hz : z ∈ RealL.{u})
    (hzpos : realLLt realLZero.{u} z) (hc : c ∈ NumberTheory.Rat.{u}) (hc0 : ratLt ratZero.{u} c)
    (hcz : realLLe (realLOf c) z) :
    realLLe (realLInv z) (realLOf (ratInv c)) := by
  have hcne : c ≠ ratZero.{u} := ratNe_zero_of_pos hc0
  have hi := ratInv_mem_Rat hc hcne
  have hiR := realLOf_mem hi
  have hcR := realLOf_mem hc
  have hinv := realLInv_mem hz hzpos
  -- `realLZero` is `realLOf ratZero`, so the rational bound is the real one
  have hi0 : realLLe realLZero.{u} (realLOf (ratInv c)) :=
    (realLOf_le_realLOf ratZero_mem_Rat hi).mpr (ratInv_pos hc hc0).left
  -- `1 = c·c⁻¹ ≤ z·c⁻¹`
  have hone : realLLe realLOne.{u} (realLMul z (realLOf (ratInv c))) := by
    have h := realLMul_le_right hcR hz hiR hcz hi0
    rw [← realLOf_mul hc hi, ratMul_inv hc hcne] at h
    exact h
  intro hlt
  -- and multiplying `c⁻¹ < z⁻¹` by `z` puts `z·c⁻¹` strictly below `1`
  have h := realLMul_lt_right hiR hinv hz hlt hzpos
  rw [realLMul_comm hiR hz, realLMul_comm hinv hz, realLMul_inv hz hzpos] at h
  exact hone h
theorem realLNeg_le_neg {a b : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (h : realLLe a b) : realLLe (realLNeg b) (realLNeg a) :=
  fun hlt => h (realLLt_of_neg_lt_neg ha hb hlt)
/-- A negative real times a positive one is negative. -/
theorem realLMul_neg_of_neg_of_pos {a b : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (ha0 : realLLt a realLZero.{u})
    (hb0 : realLLt realLZero.{u} b) : realLLt (realLMul a b) realLZero.{u} := by
  have := realLMul_lt_right ha realLZero_mem hb ha0 hb0
  rwa [realLZero_mul hb] at this
/-- Multiplication by a positive real cancels on the right. -/
theorem realLLe_of_mul_le_mul_right {X Y w : ZFSet.{u}} (hX : X ∈ RealL.{u})
    (hY : Y ∈ RealL.{u}) (hw : w ∈ RealL.{u}) (hw0 : realLLt realLZero.{u} w)
    (h : realLLe (realLMul X w) (realLMul Y w)) : realLLe X Y :=
  fun hlt => h (realLMul_lt_right hY hX hw hlt hw0)
/-- A common shift distributes out of the max, as an equality: the reverse
inequality is the forward one read at the shifted arguments. -/
theorem realLMax_add_dist {a b c : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hc : c ∈ RealL.{u}) :
    realLMax (realLAdd a c) (realLAdd b c) = realLAdd (realLMax a b) c := by
  have hac := realLAdd_mem ha hc
  have hbc := realLAdd_mem hb hc
  have hmax := realLMax_mem ha hb
  have hmaxs := realLMax_mem hac hbc
  refine realLLe_antisymm hmaxs (realLAdd_mem hmax hc)
    (realLMax_shift_le ha hb hc) ?_
  have hrev := realLMax_shift_le hac hbc (realLNeg_mem hc)
  have hcanc : ∀ z, z ∈ RealL.{u} →
      realLAdd (realLAdd z c) (realLNeg c) = z := by
    intro z hz
    rw [realLAdd_assoc hz hc (realLNeg_mem hc), realLAdd_neg hc,
      realLAdd_zero hz]
  rw [hcanc a ha, hcanc b hb] at hrev
  have hstep := realLLe_add_right hmax
    (realLAdd_mem hmaxs (realLNeg_mem hc)) hc hrev
  rwa [realLAdd_assoc hmaxs (realLNeg_mem hc) hc,
    realLAdd_comm (realLNeg_mem hc) hc, realLAdd_neg hc,
    realLAdd_zero hmaxs] at hstep
/-- A bracketed real has a bracketed square: `w² - d² = (w-d)(w+d)` is a
product of nonnegatives, and no case ever asks for `d`'s sign. -/
theorem sq_le_sq_of_bracket {d W : ZFSet.{u}} (hd : d ∈ RealL.{u})
    (hW : W ∈ RealL.{u}) (h1 : realLLe (realLNeg W) d) (h2 : realLLe d W) :
    realLLe (realLMul d d) (realLMul W W) := by
  have hWd : realLLe realLZero.{u} (realLAdd W (realLNeg d)) :=
    (realLLe_sub_nonneg hd hW).mp h2
  have hWd2 : realLLe realLZero.{u} (realLAdd W d) := by
    have hstep := (realLLe_sub_nonneg (realLNeg_mem hW) hd).mp h1
    rwa [realLNeg_realLNeg hW, realLAdd_comm hd hW] at hstep
  have hprod := realLMul_nonneg (realLAdd_mem hW (realLNeg_mem hd))
    (realLAdd_mem hW hd) hWd hWd2
  have hid := (realLSub_sq hW hd).symm
  rw [hid] at hprod
  exact (realLLe_sub_nonneg (realLMul_mem hd hd) (realLMul_mem hW hW)).mpr hprod
/-- Squaring is monotone from a nonnegative base. -/
theorem sq_le_sq_of_le {a c : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (hc0 : realLLe realLZero.{u} c)
    (h : realLLe c a) : realLLe (realLMul c c) (realLMul a a) := by
  have ha0 : realLLe realLZero.{u} a :=
    realLLe_trans realLZero_mem hc ha hc0 h
  refine realLLe_trans (realLMul_mem hc hc) (realLMul_mem ha hc)
    (realLMul_mem ha ha) (realLMul_le_right hc ha hc h hc0) ?_
  rw [realLMul_comm ha hc]
  exact realLMul_le_right hc ha ha h ha0

/-- `-d ≤ a - b` exactly when `b ≤ a + d`, as reals. -/
theorem realLNeg_le_sub_iff {a b d : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hd : d ∈ RealL.{u}) :
    Iff (realLLe (realLNeg d) (realLAdd a (realLNeg b)))
      (realLLe b (realLAdd a d)) := by
  constructor
  · intro h
    have hstep := realLNeg_le_neg (realLNeg_mem hd)
      (realLAdd_mem ha (realLNeg_mem hb)) h
    rw [realLNeg_sub ha hb, realLNeg_realLNeg hd] at hstep
    exact (realLSub_le_iff hb ha hd).mp hstep
  · intro h
    have hstep := realLNeg_le_neg
      (realLAdd_mem hb (realLNeg_mem ha)) hd
      ((realLSub_le_iff hb ha hd).mpr h)
    rwa [realLNeg_sub hb ha] at hstep

/-- `|z| ≤ ε`, spelled as the bracket it is. -/
def WithinOf (z ε : ZFSet.{u}) : Prop :=
  realLLe (realLNeg ε) z ∧ realLLe z ε

/-- Squaring is monotone on a symmetric window: `|y| <= c` gives
`y*y <= c*c`, with no case on the sign of `y`.

`realLMul_le_right` needs a non-negative multiplier and so cannot be pointed at
`y` directly. The factorisation does it instead: `c*c - y*y` is
`(c - y) * (c + y)`, and BOTH factors are non-negative precisely because the
window is two-sided --- the right half gives `c - y >= 0`, the left half gives
`c + y >= 0`. Neither says which side of zero `y` is on, and the product does
not care.

A located real forces this. `y` typically arrives as a difference whose sign is
not decidable, so a bound on `y*y` cannot be routed through `|y|` without first
deciding something the reals do not decide. -/
theorem realLSq_le_of_within {y c : ZFSet.{u}} (hy : y ∈ RealL.{u})
    (hc : c ∈ RealL.{u}) (h : WithinOf y c) :
    realLLe (realLMul y y) (realLMul c c) := by
  obtain ⟨hlo, hhi⟩ := h
  have hnc := realLNeg_mem hc
  have hny := realLNeg_mem hy
  have hsub := realLAdd_mem hc hny
  have hsum := realLAdd_mem hc hy
  have h1 : realLLe realLZero.{u} (realLAdd c (realLNeg y)) :=
    (realLLe_sub_nonneg hy hc).mp hhi
  have h2 : realLLe realLZero.{u} (realLAdd c y) := by
    have hstep := (realLLe_sub_nonneg hnc hy).mp hlo
    rwa [realLNeg_realLNeg hc, realLAdd_comm hy hc] at hstep
  have hid : realLMul (realLAdd c (realLNeg y)) (realLAdd c y)
      = realLAdd (realLMul c c) (realLNeg (realLMul y y)) := by
    rw [realLAdd_mul hc hny hsum,
      realLMul_comm hc hsum, realLAdd_mul hc hy hc,
      realLMul_comm hny hsum, realLAdd_mul hc hy hny,
      realLMul_neg hc hy, realLMul_neg hy hy,
      realLMul_comm hy hc,
      realLAdd_assoc (realLMul_mem hc hc) (realLMul_mem hc hy)
        (realLAdd_mem (realLNeg_mem (realLMul_mem hc hy))
          (realLNeg_mem (realLMul_mem hy hy))),
      ← realLAdd_assoc (realLMul_mem hc hy)
        (realLNeg_mem (realLMul_mem hc hy))
        (realLNeg_mem (realLMul_mem hy hy)),
      realLAdd_neg (realLMul_mem hc hy),
      realLAdd_comm realLZero_mem (realLNeg_mem (realLMul_mem hy hy)),
      realLAdd_zero (realLNeg_mem (realLMul_mem hy hy))]
  refine (realLLe_sub_nonneg (realLMul_mem hy hy) (realLMul_mem hc hc)).mpr ?_
  rw [← hid]
  exact realLMul_nonneg hsub hsum h1 h2

#print axioms realLSq_le_of_within

/-- `x` and `y` are within `δ` of each other. -/
def Close (x y δ : ZFSet.{u}) : Prop := WithinOf (realLAdd x (realLNeg y)) δ

/-- `WithinOf` is stable under double negation, by its shape rather than
anything about reals: `realLLe a b` IS `¬ realLLt b a`, so
`WithinOf` is a conjunction of two negations and a negation absorbs `¬¬`.

That separates a bar phrased with `Close` from a DECIDABLE one. The fan
theorem's premise is `B s ∨ ¬ B s`, which such a bar does not satisfy --
`realLLt` is an existential over rationals and nothing decides it. But
stability it does satisfy, for free. -/
theorem withinOf_stable {z ε : ZFSet.{u}} (h : ¬¬ WithinOf z ε) : WithinOf z ε :=
  ⟨fun hlt => h (fun hw => hw.left hlt), fun hlt => h (fun hw => hw.right hlt)⟩


/-- The half-open interval, closed below and open above. -/
def realLIco (p q : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun x => realLLe (realLOf p) x ∧ realLLt x (realLOf q)) RealL.{u}

/-- The dyadic left endpoint at `i`: `1 - (1/2)^i`, so `0` at `i = 0` and rising to
`1`. -/
def dyadicLeft (i : Nat) : ZFSet.{u} :=
  ratAdd ratOne.{u} (ratNeg (ratPow (ratNat.{u} 1 2) i))

/-- The lower endpoint of the subinterval a bit string names. -/
def dyadicLo (p q : ZFSet.{u}) : List Bool → ZFSet.{u}
  | [] => p
  | false :: s => dyadicLo p (ratMid p q) s
  | true :: s => dyadicLo (ratMid p q) q s

/-- And the upper. -/
def dyadicHi (p q : ZFSet.{u}) : List Bool → ZFSet.{u}
  | [] => q
  | false :: s => dyadicHi p (ratMid p q) s
  | true :: s => dyadicHi (ratMid p q) q s

/-! ### The endpoints are rational

Both definitions above had NO lemmas: `dyadicLo_*` and `dyadicHi_*` were empty
tree-wide, so a predicate over a dyadic cell could not state its own
decidability --- which is where this was noticed, pricing a fan route to Cousin's
lemma.

THE INDUCTION GENERALISES `p` AND `q`, which is the only thing to get right here:
each step replaces one endpoint by the midpoint, so an induction that fixed them
does not close.
-/

/-- Scaling a real by `d` and then by `1/d` returns it. The inverse is taken on
the RATIONAL, so this is `ratMul_inv` carried across `realLOf_mul` -- no real is
inverted anywhere. -/
theorem realLMul_ratInv_cancel {d y : ZFSet.{u}} (hd : d ∈ NumberTheory.Rat.{u})
    (hne : d ≠ ratZero.{u}) (hy : y ∈ RealL.{u}) :
    realLMul (realLMul (realLOf d) y) (realLOf (ratInv d)) = y := by
  have hinv := ratInv_mem_Rat hd hne
  rw [realLMul_comm (realLOf_mem hd) hy,
    realLMul_assoc hy (realLOf_mem hd) (realLOf_mem hinv),
    ← realLOf_mul hd hinv, ratMul_inv hd hne]
  exact realLMul_one hy

/-- Scaling a margin by a non-negative real. `|z| ≤ e` gives `|cz| ≤ ce`,
which is `realLMul_le_right` on each side with `realLMul_neg` to move the
negation across. -/
theorem withinOf_realLMul {z e c : ZFSet.{u}} (hz : z ∈ RealL.{u})
    (he : e ∈ RealL.{u}) (hc : c ∈ RealL.{u})
    (hc0 : realLLe realLZero.{u} c) (h : WithinOf z e) :
    WithinOf (realLMul c z) (realLMul c e) := by
  have hlo := realLMul_le_right (realLNeg_mem he) hz hc h.left hc0
  have hhi := realLMul_le_right hz he hc h.right hc0
  rw [realLMul_comm (realLNeg_mem he) hc, realLMul_comm hz hc,
    realLMul_neg hc he] at hlo
  rw [realLMul_comm hz hc, realLMul_comm he hc] at hhi
  exact ⟨hlo, hhi⟩

/-- A stable goal may be proved by cases on an UNDECIDED proposition.

If `A` proves the goal and `¬ A` proves the goal, the goal follows -- not
because `A ∨ ¬ A` is available, but because `WithinOf` is a negation and so
absorbs the double negation the two branches generate:

    ¬ G → ¬ A   (from the first branch)
    ¬ G → A     is not needed; the SECOND branch turns `¬ A` into `G`

so `¬ G` refutes itself. Nothing is decided and no principle is spent.

`FANstable`'s premise uses this mechanism in a special case. It lets a
measure-theoretic argument split on this piece is inhabited without paying
for the witness a regularity argument pays `Classical.choice` for. -/
theorem withinOf_of_cases {z e : ZFSet.{u}} {A : Prop}
    (hA : A → WithinOf z e) (hnA : ¬ A → WithinOf z e) : WithinOf z e :=
  withinOf_stable (fun hn => hn (hnA (fun a => hn (hA a))))
/-- The same for `Close`, which is `WithinOf` of a difference. -/
theorem close_stable {x y δ : ZFSet.{u}} (h : ¬¬ Close x y δ) : Close x y δ :=
  withinOf_stable h

/-- A bound is non-negative as soon as anything is within it. Both halves of
`WithinOf` are used and neither alone suffices: `-ε ≤ z` and `z ≤ ε` give
`-ε ≤ ε`, and a negative `ε` would put `ε` strictly below `-ε`.

Needed wherever an estimate is transported through an operation that must also
be applied to the bound -- `realLMax` is the case that wanted it -- since such a
step asks that adding `ε` be monotone, which is false for a negative one. -/
theorem nonneg_of_withinOf {z ε : ZFSet.{u}} (hz : z ∈ RealL.{u})
    (hε : ε ∈ RealL.{u}) (h : WithinOf z ε) : realLLe realLZero.{u} ε := by
  intro hlt
  have hpos : realLLt realLZero.{u} (realLNeg ε) := by
    have := realLNeg_lt_neg hε realLZero_mem hlt
    rwa [realLNeg_zero] at this
  exact realLLe_trans (realLNeg_mem hε) hz hε h.left h.right
    (realLLt_trans hε realLZero_mem (realLNeg_mem hε) hlt hpos)

/-- Negating what is estimated, at a bound that is any real.

`withinOf_neg` (`Deriv.lean`) is this at a RATIONAL bound, and the general form
is the fourth member of the family whose other three -- `withinOf_add_real`,
`close_trans_real`, `close_add_real` -- are already here. The rational versions
cannot serve a caller whose bound is `invScale n` composed with anything. -/
theorem withinOf_neg_real {z ε : ZFSet.{u}} (hz : z ∈ RealL.{u})
    (hε : ε ∈ RealL.{u}) (h : WithinOf z ε) : WithinOf (realLNeg z) ε := by
  refine ⟨?_, ?_⟩
  · have := realLNeg_le_neg hz hε h.right
    exact this
  · have := realLNeg_le_neg (realLNeg_mem hε) hz h.left
    rwa [realLNeg_realLNeg hε] at this

/-- Closeness is symmetric, at a bound that is any real. -/
theorem close_symm_real {x y ε : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hε : ε ∈ RealL.{u}) (h : Close x y ε) : Close y x ε := by
  have hstep := withinOf_neg_real (realLAdd_mem hx (realLNeg_mem hy)) hε h
  rwa [realLNeg_sub hx hy] at hstep

/-- `realLMax` is NON-EXPANSIVE: clamping two nearby reals from below by the
same thing leaves them just as near.

One direction is the whole content and the other is it applied to the symmetric
hypothesis. The direction runs `max a c ≤ max b c + ε` by `realLMax_le` on two
cases: `a ≤ b + ε` is the estimate weakened along `b ≤ max b c`, and
`c ≤ max b c` is weakened by adding a NON-NEGATIVE `ε` -- which is what
`nonneg_of_withinOf` is for, and the step that fails if the bound is allowed to
be negative.

`realLSub_le_iff` moves the estimate between `x - y ≤ ε` and `x ≤ y + ε`,
putting the goal into the shape `realLMax_le` consumes: two separate bounds
against one right-hand side. -/
theorem close_realLMax {a b c ε : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hc : c ∈ RealL.{u}) (hε : ε ∈ RealL.{u})
    (h : Close a b ε) : Close (realLMax a c) (realLMax b c) ε := by
  have hε0 : realLLe realLZero.{u} ε :=
    nonneg_of_withinOf (realLAdd_mem ha (realLNeg_mem hb)) hε h
  have step : ∀ x y : ZFSet.{u}, x ∈ RealL.{u} → y ∈ RealL.{u} →
      Close x y ε → realLLe (realLMax x c) (realLAdd (realLMax y c) ε) := by
    intro x y hx hy hxy
    have hmy := realLMax_mem hy hc
    refine realLMax_le ?_ ?_
    · refine realLLe_trans hx (realLAdd_mem hy hε) (realLAdd_mem hmy hε)
        ((realLSub_le_iff hx hy hε).mp hxy.right) ?_
      exact realLLe_add_right hy hmy hε (realLLe_max_left hy)
    · refine realLLe_trans hc hmy (realLAdd_mem hmy hε) (realLLe_max_right hc) ?_
      have := realLLe_add_right realLZero_mem hε hmy hε0
      rwa [realLZero_add hmy,
        realLAdd_comm hε hmy] at this
  refine ⟨?_, ?_⟩
  · have hrev := (realLSub_le_iff (realLMax_mem hb hc) (realLMax_mem ha hc) hε).mpr
      (step b a hb ha (close_symm_real ha hb hε h))
    have hneg := realLNeg_le_neg
      (realLAdd_mem (realLMax_mem hb hc) (realLNeg_mem (realLMax_mem ha hc))) hε hrev
    rwa [realLNeg_sub (realLMax_mem hb hc) (realLMax_mem ha hc)] at hneg
  · exact (realLSub_le_iff (realLMax_mem ha hc) (realLMax_mem hb hc) hε).mpr
      (step a b ha hb h)

/-- Two-sided bounds add, over arbitrary located bounds. `Deriv.lean`'s
`withinOf_add` is the RATIONAL case of this and is now a corollary of it: its
bounds are `realLOf c` for rationals, which is what a grid supplies and not what
a modulus does. The general form is what `Close`'s arithmetic needs.

Between them these were the only two facts `WithinOf` had beyond stability, and
the specialised one existed while the general one did not -- so nothing could
combine two estimates whose bounds were reals.

Both halves are `realLLe_add`; the lower one needs `-(ε₁ + ε₂) = -ε₁ + -ε₂`
first, which is the only step that is not symmetric between them. -/
theorem withinOf_add_real {z₁ z₂ ε₁ ε₂ : ZFSet.{u}} (hz₁ : z₁ ∈ RealL.{u})
    (hz₂ : z₂ ∈ RealL.{u}) (hε₁ : ε₁ ∈ RealL.{u}) (hε₂ : ε₂ ∈ RealL.{u})
    (h₁ : WithinOf z₁ ε₁) (h₂ : WithinOf z₂ ε₂) :
    WithinOf (realLAdd z₁ z₂) (realLAdd ε₁ ε₂) := by
  refine ⟨?_, realLLe_add hz₁ hε₁ hz₂ hε₂ h₁.right h₂.right⟩
  rw [realLNeg_realLAdd hε₁ hε₂]
  exact realLLe_add (realLNeg_mem hε₁) hz₁ (realLNeg_mem hε₂) hz₂ h₁.left h₂.left

/-- Chaining, over arbitrary located bounds. `close_trans` in Banach.lean and
`close_of_close_close` in Deriv.lean are the RATIONAL cases; this is the general
one, following the general-bound suffix those files already use for
`withinOf_le_real`/`close_le_real`. The telescoping `(x - y) + (y - z) = x - z`
is `realLSub_add_cancel` under one re-association. -/
theorem close_trans_real {x y z δ₁ δ₂ : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hz : z ∈ RealL.{u}) (hδ₁ : δ₁ ∈ RealL.{u})
    (hδ₂ : δ₂ ∈ RealL.{u}) (h₁ : Close x y δ₁) (h₂ : Close y z δ₂) :
    Close x z (realLAdd δ₁ δ₂) := by
  have hxy := realLAdd_mem hx (realLNeg_mem hy)
  have hyz := realLAdd_mem hy (realLNeg_mem hz)
  have key : realLAdd (realLAdd x (realLNeg y)) (realLAdd y (realLNeg z))
      = realLAdd x (realLNeg z) := by
    rw [← realLAdd_assoc hxy hy (realLNeg_mem hz), realLSub_add_cancel hx hy]
  have hsum := withinOf_add_real hxy hyz hδ₁ hδ₂ h₁ h₂
  rwa [key] at hsum


/-- Estimates add across a sum, over arbitrary located bounds:
`(x₁+x₂) - (y₁+y₂) = (x₁-y₁) + (x₂-y₂)` is `realLAdd_sub_add`, then
`withinOf_add_real`. What a sum of uniformly continuous functions needs, and
the general case of the rational `withinOf_add` in `Deriv.lean`. -/
theorem close_add_real {x₁ y₁ x₂ y₂ δ₁ δ₂ : ZFSet.{u}} (hx₁ : x₁ ∈ RealL.{u})
    (hy₁ : y₁ ∈ RealL.{u}) (hx₂ : x₂ ∈ RealL.{u}) (hy₂ : y₂ ∈ RealL.{u})
    (hδ₁ : δ₁ ∈ RealL.{u}) (hδ₂ : δ₂ ∈ RealL.{u})
    (h₁ : Close x₁ y₁ δ₁) (h₂ : Close x₂ y₂ δ₂) :
    Close (realLAdd x₁ x₂) (realLAdd y₁ y₂) (realLAdd δ₁ δ₂) := by
  have hsum := withinOf_add_real (realLAdd_mem hx₁ (realLNeg_mem hy₁))
    (realLAdd_mem hx₂ (realLNeg_mem hy₂)) hδ₁ hδ₂ h₁ h₂
  rwa [← realLAdd_sub_add hx₁ hx₂ hy₁ hy₂] at hsum

#print axioms withinOf_add_real
#print axioms close_trans_real
#print axioms close_add_real

/-- A positive sum of two non-negatives has a positive summand -- by
cotransitivity, not by deciding which. -/
theorem pos_or_pos_of_add_pos {s t : ZFSet.{u}} (hs : s ∈ RealL.{u})
    (ht : t ∈ RealL.{u}) (h : realLLt realLZero.{u} (realLAdd s t)) :
    realLLt realLZero.{u} s ∨ realLLt realLZero.{u} t := by
  rcases realLLt_cotrans realLZero_mem (realLAdd_mem hs ht) hs h with hleft | hright
  · exact Or.inl hleft
  · refine Or.inr ?_
    have hstep := (realLLt_sub_pos hs (realLAdd_mem hs ht)).mp hright
    rwa [realLAdd_comm hs ht, realLAdd_assoc ht hs (realLNeg_mem hs), realLAdd_neg hs,
      realLAdd_zero ht] at hstep

/-- A vanishing square has a vanishing root, choice-free. `realLSq_pos`
says an apart-from-zero root gives a positive square, so a zero square leaves
nothing apart from zero, and antisymmetry of `realLLe` -- which is a negation on
both sides -- closes it. -/
theorem eq_zero_of_sq_zero {x : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (h : realLMul x x = realLZero.{u}) : x = realLZero.{u} :=
  have hnap : ¬ realLApart realLZero.{u} x := fun hap =>
    realLLt_irrefl realLZero_mem (h ▸ realLSq_pos hx hap)
  realLLe_antisymm hx realLZero_mem (fun hlt => hnap (Or.inl hlt))
    (fun hlt => hnap (Or.inr hlt))

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

theorem realLSq_lt_sq {a b : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (hb0 : realLLe realLZero.{u} b) (hlt : realLLt b a) :
    realLLt (realLMul b b) (realLMul a a) := by
  have ha0 : realLLt realLZero.{u} a := realLLt_of_le_of_lt realLZero_mem hb ha hb0 hlt
  have h₁ : realLLe (realLMul b b) (realLMul a b) :=
    realLMul_le_right hb ha hb (realLLe_of_lt hb ha hlt) hb0
  have h₂ : realLLt (realLMul b a) (realLMul a a) :=
    realLMul_lt_right hb ha ha hlt ha0
  rw [realLMul_comm hb ha] at h₂
  exact realLLt_of_le_of_lt (realLMul_mem hb hb) (realLMul_mem ha hb)
    (realLMul_mem ha ha) h₁ h₂

/-- A difference is negative exactly when the other orientation is positive. -/
theorem realLLt_sub_neg {x y : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) :
    realLLt realLZero.{u} (realLAdd y (realLNeg x)) ↔
      realLLt (realLAdd x (realLNeg y)) realLZero.{u} := by
  have hd : realLAdd x (realLNeg y) ∈ RealL.{u} := realLAdd_mem hx (realLNeg_mem hy)
  have hd' : realLAdd y (realLNeg x) ∈ RealL.{u} := realLAdd_mem hy (realLNeg_mem hx)
  constructor
  · intro h
    have hstep := realLLt_add_right realLZero_mem hd' hd h
    rw [realLZero_add hd,
      sub_add_sub_eq_zero hx hy] at hstep
    exact hstep
  · intro h
    have hstep := realLLt_add_right hd realLZero_mem hd' h
    rw [realLAdd_comm realLZero_mem hd', realLAdd_zero hd',
      realLAdd_comm hd hd', sub_add_sub_eq_zero hx hy] at hstep
    exact hstep

theorem sub_pos_of_lt {a b : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (h : realLLt a b) :
    realLLt realLZero.{u} (realLAdd b (realLNeg a)) := by
  have := realLLt_add_right ha hb (realLNeg_mem ha) h
  rwa [realLAdd_neg ha] at this

/-- Cancelling a positive factor keeps positivity: `0 < w` and `0 < w·z`
give `0 < z`. Not by the cut-level argument -- `w` positive has an inverse, that
inverse is positive, and `z = w⁻¹·(w·z)` is a product of two positives.

Sits here beside `realLInv_pos`, which it needs. Both are generic `RealL`
algebra with no geometry in them and belong in `Located.lean`; they move
together when analysis takes them. -/
theorem pos_of_mul_pos_left {w z : ZFSet.{u}} (hw : w ∈ RealL.{u})
    (hz : z ∈ RealL.{u}) (hwpos : realLLt realLZero.{u} w)
    (hprod : realLLt realLZero.{u} (realLMul w z)) :
    realLLt realLZero.{u} z := by
  have hiv := realLInv_mem hw hwpos
  have hrecover : realLMul (realLInv w) (realLMul w z) = z := by
    rw [← realLMul_assoc hiv hw hz, realLMul_comm hiv hw,
      realLMul_inv hw hwpos, realLOne_mul hz]
  rw [← hrecover]
  exact realLMul_pos hiv (realLMul_mem hw hz) (realLInv_pos hw hwpos) hprod

/-- A negative product with a positive factor gives a negative cofactor, via
the inverse of a positive real rather than by deciding a sign.
-/
theorem neg_of_mul_neg_left {w z : ZFSet.{u}} (hw : w ∈ RealL.{u})
    (hz : z ∈ RealL.{u}) (hwpos : realLLt realLZero.{u} w)
    (hprod : realLLt (realLMul w z) realLZero.{u}) :
    realLLt z realLZero.{u} := by
  have hnz := realLNeg_mem hz
  have hpos : realLLt realLZero.{u} (realLMul w (realLNeg z)) := by
    rw [realLMul_comm hw hnz, realLNeg_realLMul hz hw, realLMul_comm hz hw]
    exact realLNeg_pos (realLMul_mem hw hz) hprod
  have hnzpos := pos_of_mul_pos_left hw hnz hwpos hpos
  have hback := realLNeg_neg_of_pos hnz hnzpos
  rwa [realLNeg_realLNeg hz] at hback

theorem lt_of_sub_pos {a b : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (h : realLLt realLZero.{u} (realLAdd b (realLNeg a))) :
    realLLt a b := by
  have := realLLt_add_right realLZero_mem (realLAdd_mem hb (realLNeg_mem ha)) ha h
  rwa [realLSub_add_cancel hb ha, realLZero_add ha] at this

/-- `w < x - a` and `a < x - w` are the same statement.

Both say `a + w < x`, but the tower has no lemma moving a term across a strict
inequality, so the swap has to be done by hand. The whole content is that
`(x - a) - w` and `(x - w) - a` are the same real --- one associativity and one
commutation --- after which `realLLt_sub_pos` reads the inequality both ways.
-/
theorem realLLt_sub_swap {x a w : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (ha : a ∈ RealL.{u}) (hw : w ∈ RealL.{u})
    (h : realLLt w (realLAdd x (realLNeg a))) :
    realLLt a (realLAdd x (realLNeg w)) := by
  have hna := realLNeg_mem ha
  have hnw := realLNeg_mem hw
  have hkey : realLAdd (realLAdd x (realLNeg a)) (realLNeg w)
      = realLAdd (realLAdd x (realLNeg w)) (realLNeg a) := by
    rw [realLAdd_assoc hx hna hnw, realLAdd_comm hna hnw,
      ← realLAdd_assoc hx hnw hna]
  refine (realLLt_sub_pos ha (realLAdd_mem hx hnw)).mpr ?_
  rw [← hkey]
  exact (realLLt_sub_pos hw (realLAdd_mem hx hna)).mp h

#print axioms Analysis.realLLt_sub_swap

/-- `(C - A) - (B - A) = C - B`: two displacements from a common base differ by
the displacement between their tips. Used by the betweenness parameter here and
by SAS over points in `GeomCongruence.lean`. -/
theorem disp_sub {a b c : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hc : c ∈ RealL.{u}) :
    realLAdd (realLAdd c (realLNeg a)) (realLNeg (realLAdd b (realLNeg a)))
      = realLAdd c (realLNeg b) := by
  rw [realLNeg_sub hb ha, realLSub_add_sub ha hc hb]

#print axioms pos_or_pos_of_add_pos
#print axioms eq_zero_of_sq_zero
#print axioms sq_sum
#print axioms shift_sub
#print axioms realLSq_lt_sq
#print axioms realLLt_sub_neg
#print axioms sub_pos_of_lt
#print axioms pos_of_mul_pos_left
#print axioms neg_of_mul_neg_left
#print axioms lt_of_sub_pos
#print axioms disp_sub
/-- The Hahn-Banach gap rearrangement.  `a + b ≤ p + q` says exactly that
`a - p` sits below `q - b`, which is the well-posedness of the separating value
in the one-dimensional extension step: every candidate lower bound lies below
every candidate upper bound. -/
theorem realLLe_sub_sub_of_add_le {a b p q : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hp : p ∈ RealL.{u}) (hq : q ∈ RealL.{u})
    (h : realLLe (realLAdd a b) (realLAdd p q)) :
    realLLe (realLAdd a (realLNeg p)) (realLAdd q (realLNeg b)) := by
  have hnb : realLNeg b ∈ RealL.{u} := realLNeg_mem hb
  have hnp : realLNeg p ∈ RealL.{u} := realLNeg_mem hp
  have hqb : realLAdd q (realLNeg b) ∈ RealL.{u} := realLAdd_mem hq hnb
  refine (realLSub_le_iff ha hp hqb).mpr ?_
  refine realLLe_add_right_cancel ha (realLAdd_mem hp hqb) hb ?_
  have hkey : realLAdd (realLAdd p (realLAdd q (realLNeg b))) b
      = realLAdd p q := by
    rw [realLAdd_assoc hp hqb hb, realLAdd_assoc hq hnb hb,
      realLAdd_comm hnb hb, realLAdd_neg hb, realLAdd_zero hq]
  rw [hkey]
  exact h

/-- Inclusion of lower cuts gives the order.  `realLLe` is a negation, so a
witness for the strict inequality would put one rational in both halves of a
located pair, which `ordered` refutes.

This is the bridge the supremum lemmas need.  `le_sup` and `sup_le`
(`le_sup` and `sup_le`) are stated as inclusions of LOWER CUTS, and every
consumer wants `realLLe`. -/
theorem realLLe_of_lower_subset {L U L' U' : ZFSet.{u}}
    (h' : IsLocated L' U') (hsub : L ⊆ L') :
    realLLe (opair L U) (opair L' U') := by
  rintro ⟨p, hpU, hpL⟩
  rw [snd_opair] at hpU
  rw [fst_opair] at hpL
  exact ratLt_irrefl (h'.ordered p (hsub p hpL) p hpU)

/-- The supremum is the LEAST upper bound, at the order rather than the cut.
`sup_le` says the lower cut is contained; the bridge turns that into `realLLe`,
which is what a consumer states its bounds in.

Together with `isLocated_sup_of_familyLocated` this is the whole supremum API a
Hahn-Banach extension needs: `FamilyLocated` gives the value, this gives that it
does not overshoot any bound the family respects. -/
theorem sup_realLLe_of_forall {S b L' U' : ZFSet.{u}}
    (hb : b = opair L' U') (h' : IsLocated L' U')
    (h : ∀ z, z ∈ S → ∀ L U, z = opair L U → L ⊆ L') :
    realLLe (opair (supLower S) (supUpper S)) b := by
  rw [hb]
  exact realLLe_of_lower_subset h' (sup_le h)

/-- The supremum is the least upper bound, with the hypothesis at the ORDER
level.  The companion of `sup_realLLe_of_forall`, and the one that composes:
consumers produce `realLLe` bounds, not cut inclusions, and the converse bridge
is not available.

`rangeSup_le` (`Extreme.lean`) is this argument inlined for one particular
set.  Stated here for an arbitrary `S`, which is what a family indexed by
something other than an interval needs. -/
theorem sup_realLLe_of_forall_le {S w : ZFSet.{u}}
    (h : ∀ z, z ∈ S → realLLe z w) :
    realLLe (opair (supLower S) (supUpper S)) w := by
  rintro ⟨p, hpU, hpL⟩
  rw [fst_opair] at hpL
  obtain ⟨hpQ, z, hz, L, U, heq, hpLz⟩ := (mem_supLower_iff _ p).mp hpL
  refine h z hz ⟨p, hpU, ?_⟩
  rw [heq, fst_opair]
  exact hpLz


/-- Every member sits below the supremum, at the ORDER rather than the cut.

`le_sup` gives the LOWER-CUT inclusion and has no consumer
in the tree -- `rangeSup_le` inlines its own argument instead. This is the form a
consumer states its bounds in, and it is the companion of
`sup_realLLe_of_forall_le`.

A witness for the strict inequality would put one rational above EVERY member --
`supUpper`'s own condition -- and simultaneously in this member's lower half,
which its `ordered` clause refutes. -/
theorem le_sup_realLLe {S z L U : ZFSet.{u}} (hz : z ∈ S) (he : z = opair L U)
    (hloc : IsLocated L U) :
    realLLe z (opair (supLower S) (supUpper S)) := by
  rintro ⟨r, hrU, hrL⟩
  rw [snd_opair] at hrU
  obtain ⟨-, p, hpQ, hpr, hall⟩ := (mem_supUpper_iff S r).mp hrU
  rw [he, fst_opair] at hrL
  have hrp : ratLt r p := hloc.ordered r hrL p (hall z hz L U he)
  have hrQ : r ∈ NumberTheory.Rat.{u} := hloc.lower_subset r hrL
  exact ratLt_irrefl (ratLt_trans hpQ hrQ hpQ hpr hrp)

/-- The lower cut of an INFIMUM: a rational below every member, with a strict
buffer -- the mirror of `supUpper`. -/
def infLower (S : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ q, q ∈ NumberTheory.Rat.{u} ∧ ratLt p q ∧
        ∀ z, z ∈ S → ∀ L U, z = opair L U → q ∈ L) NumberTheory.Rat.{u}

/-- The upper cut of an INFIMUM: a rational above SOME member -- the mirror of
`supLower`. -/
def infUpper (S : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun r => ∃ z, z ∈ S ∧ ∃ L U, z = opair L U ∧ r ∈ U) NumberTheory.Rat.{u}

theorem mem_infLower_iff (S p : ZFSet.{u}) :
    p ∈ infLower S ↔ p ∈ NumberTheory.Rat.{u} ∧ ∃ q, q ∈ NumberTheory.Rat.{u} ∧ ratLt p q ∧
      ∀ z, z ∈ S → ∀ L U, z = opair L U → q ∈ L :=
  mem_sep_iff _ _ _

theorem mem_infUpper_iff (S r : ZFSet.{u}) :
    r ∈ infUpper S ↔ r ∈ NumberTheory.Rat.{u} ∧ ∃ z, z ∈ S ∧ ∃ L U, z = opair L U ∧ r ∈ U :=
  mem_sep_iff _ _ _

/-- The dual of `FamilyLocated`, and it is a genuinely different condition:
`FamilyLocated` asks whether SOME member exceeds `p`, this asks whether EVERY
member does. Neither follows from the other -- each member's own `located`
clause gives a pointwise disjunction, and the two ways of collapsing it over the
family are independent. -/
def FamilyLocatedInf (S : ZFSet.{u}) : Prop :=
  ∀ p, p ∈ NumberTheory.Rat.{u} → ∀ q, q ∈ NumberTheory.Rat.{u} → ratLt p q →
    (∀ z, z ∈ S → ∀ L U, z = opair L U → p ∈ L) ∨
    (∃ z, z ∈ S ∧ ∃ L U, z = opair L U ∧ q ∈ U)

/-- The infimum of a family is a located real, dual to
`isLocated_sup_of_familyLocated` -- and the tree had no infimum construction at
all before this. Every outer measure is a greatest LOWER bound, so
`LebesgueOuter` could only be stated as a characterisation. -/
theorem isLocated_inf_of_familyLocatedInf {S : ZFSet.{u}} (hS : S ⊆ RealL.{u})
    (hne : ∃ z, z ∈ S)
    (hbd : ∃ p, p ∈ NumberTheory.Rat.{u} ∧ ∀ z, z ∈ S → ∀ L U, z = opair L U → p ∈ L)
    (hfam : FamilyLocatedInf S) : IsLocated (infLower S) (infUpper S) where
  lower_subset p hp := ((mem_infLower_iff S p).mp hp).left
  upper_subset r hr := ((mem_infUpper_iff S r).mp hr).left
  lower_inhabited := by
    obtain ⟨p₀, hp₀Q, hall⟩ := hbd
    obtain ⟨p, hpQ, hlt⟩ := rat_no_least hp₀Q
    exact ⟨p, (mem_infLower_iff S p).mpr ⟨hpQ, p₀, hp₀Q, hlt, hall⟩⟩
  upper_inhabited := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff z).mp (hS z hz)
    obtain ⟨r, hr⟩ := hloc.upper_inhabited
    exact ⟨r, (mem_infUpper_iff S r).mpr
      ⟨hloc.upper_subset r hr, _, hz, L, U, rfl, hr⟩⟩
  ordered q hq r hr := by
    obtain ⟨hqQ, q', hq'Q, hqq', hall⟩ := (mem_infLower_iff S q).mp hq
    obtain ⟨hrQ, z, hz, L, U, he, hrU⟩ := (mem_infUpper_iff S r).mp hr
    have hloc := isLocated_of_mem_RealL (hS z hz) he
    exact ratLt_trans hqQ hq'Q hrQ hqq' (hloc.ordered q' (hall z hz L U he) r hrU)
  lower_down q hq p hpQ hlt := by
    obtain ⟨hqQ, q', hq'Q, hqq', hall⟩ := (mem_infLower_iff S q).mp hq
    exact (mem_infLower_iff S p).mpr
      ⟨hpQ, q', hq'Q, ratLt_trans hpQ hqQ hq'Q hlt hqq', hall⟩
  upper_up r hr p hpQ hlt := by
    obtain ⟨hrQ, z, hz, L, U, he, hrU⟩ := (mem_infUpper_iff S r).mp hr
    have hloc := isLocated_of_mem_RealL (hS z hz) he
    exact (mem_infUpper_iff S p).mpr
      ⟨hpQ, z, hz, L, U, he, hloc.upper_up r hrU p hpQ hlt⟩
  lower_open q hq := by
    obtain ⟨hqQ, q', hq'Q, hqq', hall⟩ := (mem_infLower_iff S q).mp hq
    obtain ⟨t, htQ, h₁, h₂⟩ := rat_dense hqQ hq'Q hqq'
    exact ⟨t, (mem_infLower_iff S t).mpr ⟨htQ, q', hq'Q, h₂, hall⟩, h₁⟩
  upper_open r hr := by
    obtain ⟨hrQ, z, hz, L, U, he, hrU⟩ := (mem_infUpper_iff S r).mp hr
    have hloc := isLocated_of_mem_RealL (hS z hz) he
    obtain ⟨r', hr'U, hlt⟩ := hloc.upper_open r hrU
    exact ⟨r', (mem_infUpper_iff S r').mpr
      ⟨hloc.upper_subset r' hr'U, z, hz, L, U, he, hr'U⟩, hlt⟩
  located p hpQ q hqQ hlt := by
    obtain ⟨t, htQ, h₁, h₂⟩ := rat_dense hpQ hqQ hlt
    rcases hfam t htQ q hqQ h₂ with hleft | hright
    · exact Or.inl ((mem_infLower_iff S p).mpr ⟨hpQ, t, htQ, h₁, hleft⟩)
    · exact Or.inr ((mem_infUpper_iff S q).mpr ⟨hqQ, hright⟩)

/-- A constructed infimum is APPROACHED, free.  Anything strictly above the
infimum has a member of the family at or below it.

This is `OuterApproached`'s conclusion (`Caratheodory.lean`) for an infimum
that has been BUILT rather than characterised, and it costs nothing: `infUpper`
is by definition above some member, so a witness for `inf < U` names the member
directly.

With only the glb characterisation the same statement refutes a universal
instead of producing a witness -- classically identical, constructively the
whole difficulty. -/
theorem approached_of_inf {S U : ZFSet.{u}} (hS : S ⊆ RealL.{u})
    (hU : U ∈ RealL.{u})
    (h : realLLt (opair (infLower S) (infUpper S)) U) :
    ∃ z, z ∈ S ∧ realLLe z U := by
  obtain ⟨p, hpU, hpL⟩ := h
  rw [snd_opair] at hpU
  obtain ⟨hpQ, z, hz, L', U', he, hpU'⟩ := (mem_infUpper_iff S p).mp hpU
  obtain ⟨Lu, Uu, heU, hlocU⟩ := (mem_RealL_iff U).mp hU
  refine ⟨z, hz, ?_⟩
  rintro ⟨r, hrU, hrL⟩
  have hlocz := isLocated_of_mem_RealL (hS z hz) he
  rw [he, fst_opair] at hrL
  rw [heU, snd_opair] at hrU
  rw [heU, fst_opair] at hpL
  have hrp : ratLt r p := hlocz.ordered r hrL p hpU'
  have hpr : ratLt p r := hlocU.ordered p hpL r hrU
  have hrQ : r ∈ NumberTheory.Rat.{u} := hlocz.lower_subset r hrL
  exact ratLt_irrefl (ratLt_trans hrQ hpQ hrQ hrp hpr)


/-- The infimum is a LOWER bound.  Dual to `le_sup_realLLe`. -/
theorem inf_realLLe_of_mem {S z L U : ZFSet.{u}} (hz : z ∈ S) (he : z = opair L U)
    (hloc : IsLocated L U) :
    realLLe (opair (infLower S) (infUpper S)) z := by
  rintro ⟨r, hrU, hrL⟩
  rw [he, snd_opair] at hrU
  rw [fst_opair] at hrL
  obtain ⟨hrQ, q, hqQ, hrq, hall⟩ := (mem_infLower_iff S r).mp hrL
  exact ratLt_irrefl (ratLt_trans hrQ hqQ hrQ hrq
    (hloc.ordered q (hall z hz L U he) r hrU))

/-- And it is the GREATEST lower bound.  Dual to `sup_realLLe_of_forall_le`,
with the hypothesis at the ORDER level, which is the form that composes. -/
theorem realLLe_inf_of_forall {S K : ZFSet.{u}}
    (h : ∀ z, z ∈ S → realLLe K z) :
    realLLe K (opair (infLower S) (infUpper S)) := by
  rintro ⟨r, hrU, hrL⟩
  rw [snd_opair] at hrU
  obtain ⟨hrQ, z, hz, L, U, he, hrU'⟩ := (mem_infUpper_iff S r).mp hrU
  refine h z hz ⟨r, ?_, hrL⟩
  rw [he, snd_opair]
  exact hrU'


/-- Below one real is below any real above it -- and no family is involved.
If `L <= M` and a rational `t` sits in `L`'s lower cut, every rational strictly
below `t` is in `M`'s lower cut.

This is the LEFT case of the converse sketch, and writing it revealed the family
hypothesis was never used: the statement is about two located reals.

The step that matters: `realLLe L M` forbids `t` from `M`'s UPPER cut, and `M`'s
own `located` clause at `(p, t)` then has only one branch left. Being below is
not enough on its own -- the dichotomy is what converts it. -/
theorem lower_of_le_of_lower {L M Ll Lu Ml Mu p t : ZFSet.{u}}
    (hLeq : L = opair Ll Lu) (hMeq : M = opair Ml Mu)
    (hlocM : IsLocated Ml Mu)
    (hle : realLLe L M) (htL : t ∈ Ll)
    (hpQ : p ∈ NumberTheory.Rat.{u}) (htQ : t ∈ NumberTheory.Rat.{u}) (hpt : ratLt p t) :
    p ∈ Ml := by
  rcases hlocM.located p hpQ t htQ hpt with hp | ht
  · exact hp
  · exact absurd ⟨t, by rw [hMeq, snd_opair]; exact ht,
      by rw [hLeq, fst_opair]; exact htL⟩ hle

/-- The RIGHT case: an approximant below a rational puts that rational in its
upper cut.  If `M <= realLOf t'` and `t' < q`, then `q ∈ U_M`.

As the left case predicted, this does NOT go by transitivity. `M`'s own `located`
clause at `(t', q)` leaves two branches, and the wrong one is killed by
`lower_open`: a rational in `M`'s lower cut has a strictly larger companion
there, which is exactly the witness `M <= realLOf t'` forbids. -/
theorem upper_of_le_ratOf {M Ml Mu t q : ZFSet.{u}} (hMeq : M = opair Ml Mu)
    (hlocM : IsLocated Ml Mu) (hle : realLLe M (realLOf t))
    (htQ : t ∈ NumberTheory.Rat.{u}) (hqQ : q ∈ NumberTheory.Rat.{u}) (htq : ratLt t q) :
    q ∈ Mu := by
  rcases hlocM.located t htQ q hqQ htq with ht | hq
  · exfalso
    obtain ⟨t', ht'L, htt'⟩ := hlocM.lower_open t ht
    refine hle ⟨t', ?_, ?_⟩
    · rw [realLOf, snd_opair]
      exact (mem_sep_iff _ _ _).mpr ⟨hlocM.lower_subset t' ht'L, htt'⟩
    · rw [hMeq, fst_opair]; exact ht'L
  · exact hq

/-- THE CONVERSE: a lower bound that is APPROACHED makes the family
inf-located.  So `FamilyLocatedInf` is not strictly stronger than
`OuterApproached` -- given a glb that exists as a located real, the two are
interderivable. What that buys is not an upgrade to the characterisations, which
were always correct as conditionals on a supplied `L`: it is the ANTECEDENT.
With the bound family inf-located, `L` can be produced rather than assumed.

The proof is one case split on `L`'s OWN `located` clause, with a proved lemma
per branch. Neither branch is transitivity: both convert an order fact into cut
membership through a dichotomy, which is what the order/cut gap forces. -/
theorem familyLocatedInf_of_lowerBound_of_approx {S L Ll Lu : ZFSet.{u}}
    (hS : S ⊆ RealL.{u}) (hLeq : L = opair Ll Lu) (hlocL : IsLocated Ll Lu)
    (hlb : ∀ M, M ∈ S → realLLe L M)
    (happ : ∀ v, v ∈ NumberTheory.Rat.{u} → v ∈ Lu → ∃ M, M ∈ S ∧ realLLe M (realLOf v)) :
    FamilyLocatedInf S := by
  intro p hp q hq hpq
  obtain ⟨t, htQ, hpt, htq⟩ := rat_dense hp hq hpq
  rcases hlocL.located t htQ q hq htq with htL | hqU
  · refine Or.inl (fun z hz L' U' heq => ?_)
    exact lower_of_le_of_lower hLeq heq
      (isLocated_of_mem_RealL (hS z hz) heq) (hlb z hz) htL hp htQ hpt
  · obtain ⟨r, hrU, hrq⟩ := hlocL.upper_open q hqU
    obtain ⟨M, hM, hMle⟩ := happ r (hlocL.upper_subset r hrU) hrU
    obtain ⟨Ml, Mu, hMeq, hlocM⟩ := (mem_RealL_iff M).mp (hS M hM)
    exact Or.inr ⟨M, hM, Ml, Mu, hMeq,
      upper_of_le_ratOf hMeq hlocM hMle (hlocL.upper_subset r hrU) hq hrq⟩

/-- At or above zero, every negative rational is already in the lower cut. The
crossing goes through `located` at `(p, 0)`, with the wrong branch refuted by
`upper_open` -- `realLLe` is a negation, so transitivity is not available and
the cut's own structure has to supply the step. -/
theorem mem_lower_of_neg_of_nonneg {M Ml Mu p : ZFSet.{u}} (hMeq : M = opair Ml Mu)
    (hlocM : IsLocated Ml Mu) (hnn : realLLe realLZero.{u} M)
    (hpQ : p ∈ NumberTheory.Rat.{u}) (hp0 : ratLt p ratZero.{u}) : p ∈ Ml := by
  rcases hlocM.located p hpQ ratZero.{u} ratZero_mem_Rat hp0 with hl | hu
  · exact hl
  · exfalso
    obtain ⟨r, hrU, hr0⟩ := hlocM.upper_open ratZero.{u} hu
    refine hnn ⟨r, ?_, ?_⟩
    · rw [hMeq, snd_opair]; exact hrU
    · rw [realLZero, realLOf, fst_opair]
      exact (mem_ratCut_iff ratZero.{u} r).mpr ⟨hlocM.upper_subset r hrU, hr0⟩

/-- A member of the UPPER cut names a rational the real is strictly below.
`upper_open` supplies the witness `realLLt` asks for; the rationality of `v`
is not needed, since the witness comes from the cut rather than from `v`. -/
theorem realLLt_realLOf_of_mem_upper {L Ll Lu v : ZFSet.{u}} (hLeq : L = opair Ll Lu)
    (hloc : IsLocated Ll Lu) (hv : v ∈ Lu) :
    realLLt L (realLOf v) := by
  obtain ⟨r, hrU, hrlt⟩ := hloc.upper_open v hv
  refine ⟨r, ?_, ?_⟩
  · rw [hLeq, snd_opair]; exact hrU
  · rw [realLOf, fst_opair]
    exact (mem_ratCut_iff v r).mpr ⟨hloc.upper_subset r hrU, hrlt⟩

/-- The reals satisfying `P`, as a set.

The infimum machinery below takes the bound predicate as a parameter rather than
naming `IsOuterBound`, which is the one-dimensional notion and would tie these
results to a single dimension. All the proofs require of `P` is that its bounds
are reals and that they are nonnegative. -/
def boundsOf (P : ZFSet.{u} → Prop) : ZFSet.{u} := sep P RealL.{u}

theorem mem_boundsOf_iff {P : ZFSet.{u} → Prop} {M : ZFSet.{u}}
    (hmem : ∀ N, P N → N ∈ RealL.{u}) : M ∈ boundsOf P ↔ P M :=
  Iff.trans (mem_sep_iff _ _ _) ⟨And.right, fun h => ⟨hmem M h, h⟩⟩

theorem boundsOf_subset {P : ZFSet.{u} → Prop}
    (hmem : ∀ N, P N → N ∈ RealL.{u}) : boundsOf P ⊆ RealL.{u} :=
  fun _ h => hmem _ ((mem_boundsOf_iff hmem).mp h)

theorem lowerBound_boundsOf {P : ZFSet.{u} → Prop}
    (hmem : ∀ N, P N → N ∈ RealL.{u})
    (hnn : ∀ N, P N → realLLe realLZero.{u} N) :
    ∃ p, p ∈ NumberTheory.Rat.{u} ∧ ∀ z, z ∈ boundsOf P → ∀ L U, z = opair L U → p ∈ L := by
  obtain ⟨s, hsQ, hs0⟩ := rat_no_least ratZero_mem_Rat
  refine ⟨s, hsQ, fun z hz L U heq => ?_⟩
  have hb := (mem_boundsOf_iff hmem).mp hz
  exact mem_lower_of_neg_of_nonneg heq
    (isLocated_of_mem_RealL (hmem _ hb) heq) (hnn _ hb) hsQ hs0

/-- The greatest lower bound of ANY nonnegative family of reals exists once the
family is inf-located -- `LebesgueOuter`'s three clauses, with the bound
predicate abstracted. -/
theorem glb_of_familyLocatedInf {P : ZFSet.{u} → Prop}
    (hmem : ∀ N, P N → N ∈ RealL.{u})
    (hnn : ∀ N, P N → realLLe realLZero.{u} N)
    (hne : ∃ M, P M) (hfam : FamilyLocatedInf (boundsOf P)) :
    And (opair (infLower (boundsOf P)) (infUpper (boundsOf P)) ∈ RealL.{u})
      (And (∀ M, P M → realLLe (opair (infLower (boundsOf P)) (infUpper (boundsOf P))) M)
        (∀ K, K ∈ RealL.{u} → (∀ M, P M → realLLe K M) →
          realLLe K (opair (infLower (boundsOf P)) (infUpper (boundsOf P))))) := by
  obtain ⟨M₀, hM₀⟩ := hne
  have hloc := isLocated_inf_of_familyLocatedInf (boundsOf_subset hmem)
    ⟨M₀, (mem_boundsOf_iff hmem).mpr hM₀⟩ (lowerBound_boundsOf hmem hnn) hfam
  refine ⟨(mem_RealL_iff _).mpr ⟨_, _, rfl, hloc⟩, ?_, ?_⟩
  · intro M hM
    obtain ⟨Ml, Mu, hMeq, hlocM⟩ := (mem_RealL_iff M).mp (hmem M hM)
    exact inf_realLLe_of_mem ((mem_boundsOf_iff hmem).mpr hM) hMeq hlocM
  · intro K hK hKlb
    exact realLLe_inf_of_forall (fun z hz => hKlb z ((mem_boundsOf_iff hmem).mp hz))


/-- The infimum of a set of located reals is its greatest lower bound.

Stated over a SET rather than a carving predicate, which is the form
`isLocated_sup_of_familyLocated` already takes on the dual side and the form
every consumer holding a family actually has.

What it asks for is a rational LOWER BOUND, not nonnegativity:
`glb_of_familyLocatedInf` takes the latter only to derive the former through
`lowerBound_boundsOf`, so nonnegativity is one way of meeting the hypothesis
rather than the hypothesis itself. A finite family of located reals has a lower
bound with no sign condition at all, and could not use the stronger form.

The third clause does not restrict `K` to `RealL`, because
`realLLe_inf_of_forall` does not. `glb_of_familyLocatedInf` does restrict it,
and must: its conclusion has to stay definitionally equal to `LebesgueOuter`. -/
theorem glb_of_familyLocatedInf_set {S : ZFSet.{u}}
    (hS : S ⊆ RealL.{u})
    (hbd : ∃ p, p ∈ NumberTheory.Rat.{u} ∧ ∀ z, z ∈ S → ∀ L U, z = opair L U → p ∈ L)
    (hne : ∃ M, M ∈ S) (hfam : FamilyLocatedInf S) :
    And (opair (infLower S) (infUpper S) ∈ RealL.{u})
      (And (∀ M, M ∈ S → realLLe (opair (infLower S) (infUpper S)) M)
        (∀ K, (∀ M, M ∈ S → realLLe K M) →
          realLLe K (opair (infLower S) (infUpper S)))) := by
  have hloc := isLocated_inf_of_familyLocatedInf hS hne hbd hfam
  refine ⟨(mem_RealL_iff _).mpr ⟨_, _, rfl, hloc⟩, ?_, ?_⟩
  · intro M hM
    obtain ⟨Ml, Mu, hMeq, hlocM⟩ := (mem_RealL_iff M).mp (hS M hM)
    exact inf_realLLe_of_mem hM hMeq hlocM
  · intro K hKlb
    exact realLLe_inf_of_forall hKlb

/-- The supremum of a located family is its least upper bound, the dual of
`glb_of_familyLocatedInf_set`.

The three components were already here separately -- `isLocated_sup_of_familyLocated`,
`le_sup_realLLe`, `sup_realLLe_of_forall_le`. What was missing is the statement
that they compose, so a caller wanting the least upper bound had to know three
names and that they fit together. -/
theorem lub_of_familyLocated {S : ZFSet.{u}}
    (hS : S ⊆ RealL.{u}) (hne : ∃ z, z ∈ S)
    (hbd : ∃ r, r ∈ NumberTheory.Rat.{u} ∧ ∀ z, z ∈ S → ∀ L U, z = opair L U → r ∈ U)
    (hfam : FamilyLocated S) :
    And (opair (supLower S) (supUpper S) ∈ RealL.{u})
      (And (∀ M, M ∈ S → realLLe M (opair (supLower S) (supUpper S)))
        (∀ K, (∀ M, M ∈ S → realLLe M K) →
          realLLe (opair (supLower S) (supUpper S)) K)) := by
  have hloc := isLocated_sup_of_familyLocated hS hne hbd hfam
  refine ⟨(mem_RealL_iff _).mpr ⟨_, _, rfl, hloc⟩, ?_, ?_⟩
  · intro M hM
    obtain ⟨Ml, Mu, hMeq, hlocM⟩ := (mem_RealL_iff M).mp (hS M hM)
    exact le_sup_realLLe hM hMeq hlocM
  · intro K hub
    exact sup_realLLe_of_forall_le hub

/-- `1/1 = 1`. Nothing in the tree states it; it is one application of
`realLInv_eq_of_mul_one` to `1 * 1 = 1`. -/
theorem realLInv_one : realLInv realLOne.{u} = realLOne.{u} :=
  (realLInv_eq_of_mul_one realLOne_mem realLOne_mem realLZero_lt_one.{u}
    (realLMul_one realLOne_mem)).symm

/-- The reciprocal of something in `(0,1]` is at least one.

Applied to the Euler factor `(1 - X^f)^g`, whose base lies in `[0,1)`: its
reciprocal is the factor of `prod over j of L(s, chi_j)` at the prime, and this
is why that product is at least one without any coefficient being named. -/
theorem realLOne_le_realLInv_of_le_one {y : ZFSet.{u}} (hy : y ∈ RealL.{u})
    (hy0 : realLLt realLZero.{u} y) (hy1 : realLLe y realLOne.{u}) :
    realLLe realLOne.{u} (realLInv y) := by
  have h := realLInv_antitone hy realLOne_mem hy0 hy1
  rwa [realLInv_one] at h


#print axioms Analysis.realL_add_mul_add
#print axioms Analysis.realLApart_iff_sub
#print axioms Analysis.realLApart_mul_left
#print axioms Analysis.realLNeg_neg_of_pos
#print axioms Analysis.apart_mul_apart

#print axioms Analysis.chain_slack
#print axioms Analysis.realLMul_lt_right
#print axioms Analysis.realLLe_add
#print axioms Analysis.realLSub_nonpos_of_le
#print axioms Analysis.realLSub_le_iff
#print axioms Analysis.realLMax_shift_le
#print axioms Analysis.riemann_step_eq

#print axioms Analysis.sub_shift_cancel
#print axioms Analysis.realLSub_eq_zero_iff
#print axioms Analysis.sq_sub_expand
#print axioms Analysis.reflect_step_eq
#print axioms Analysis.cell_split
#print axioms Analysis.block_split
#print axioms Analysis.realLLe_neg_of_le_add
#print axioms Analysis.realLAdd_nonneg
#print axioms Analysis.le_add_of_sub_le
#print axioms Analysis.le_add_of_neg_le_sub'
#print axioms Analysis.realLLt_of_neg_lt_neg
#print axioms Analysis.realLZero_add
#print axioms Analysis.realLOne_mul
#print axioms Analysis.realLZero_mul
#print axioms Analysis.sub_add_sub_eq_zero
#print axioms Analysis.realL_eq_opair
#print axioms Analysis.realL_inv_unique

#print axioms Analysis.realLOf_lt_realLOf
#print axioms Analysis.realLLt_self_add_pos
#print axioms Analysis.realLLt_sub_pos_self
#print axioms Analysis.realLOf_le_realLOf
#print axioms Analysis.realLMul_nonneg
#print axioms Analysis.realLMul_le_right

#print axioms Analysis.realLOf_mul
#print axioms Analysis.realLInv_le_of_le
#print axioms Analysis.realLNeg_le_neg
#print axioms Analysis.realLMul_neg_of_neg_of_pos
#print axioms Analysis.realLLe_of_mul_le_mul_right
#print axioms Analysis.realLMax_add_dist
#print axioms Analysis.sq_le_sq_of_bracket
#print axioms Analysis.sq_le_sq_of_le

#print axioms Analysis.realLNeg_le_sub_iff

#print axioms Analysis.WithinOf
#print axioms Analysis.Close
#print axioms Analysis.withinOf_stable
#print axioms Analysis.close_stable
#print axioms Analysis.nonneg_of_withinOf
#print axioms Analysis.withinOf_neg_real
#print axioms Analysis.close_symm_real
#print axioms Analysis.close_realLMax
#print axioms Analysis.eq_zero_of_add_eq_zero
#print axioms Analysis.invScale_antitone
#print axioms Analysis.realLIco
#print axioms Analysis.dyadicLeft
#print axioms Analysis.dyadicLo
#print axioms Analysis.dyadicHi
#print axioms Analysis.realLMul_ratInv_cancel
#print axioms Analysis.withinOf_realLMul
#print axioms Analysis.withinOf_of_cases
#print axioms Analysis.realLLe_sub_sub_of_add_le
#print axioms Analysis.realLLe_of_lower_subset
#print axioms Analysis.sup_realLLe_of_forall
#print axioms Analysis.sup_realLLe_of_forall_le
#print axioms Analysis.le_sup_realLLe
#print axioms Analysis.infLower
#print axioms Analysis.infUpper
#print axioms Analysis.mem_infLower_iff
#print axioms Analysis.mem_infUpper_iff
#print axioms Analysis.FamilyLocatedInf
#print axioms Analysis.isLocated_inf_of_familyLocatedInf
#print axioms Analysis.approached_of_inf
#print axioms Analysis.inf_realLLe_of_mem
#print axioms Analysis.realLLe_inf_of_forall
#print axioms Analysis.lower_of_le_of_lower
#print axioms Analysis.upper_of_le_ratOf
#print axioms Analysis.familyLocatedInf_of_lowerBound_of_approx
#print axioms Analysis.mem_lower_of_neg_of_nonneg
#print axioms Analysis.realLLt_realLOf_of_mem_upper
#print axioms Analysis.boundsOf
#print axioms Analysis.mem_boundsOf_iff
#print axioms Analysis.boundsOf_subset
#print axioms Analysis.lowerBound_boundsOf

#print axioms Analysis.glb_of_familyLocatedInf
#print axioms Analysis.glb_of_familyLocatedInf_set
#print axioms Analysis.lub_of_familyLocated

#print axioms Analysis.BoundedLocated
#print axioms Analysis.realLMul_le_left
#print axioms Analysis.realLMul_sub_mul
#print axioms Analysis.realLInv_one
#print axioms Analysis.realLOne_le_realLInv_of_le_one

/-- And `Nat` order embeds too, at denominator one.

`realLOf_ratNat_add` carries the arithmetic; this carries the COMPARISON, and
the pair is what lets a `Nat` inequality be read as one between contents.
`lawOfLargeNumbers_tail` is stated as `q * binomTail ... <= (a+b)^(n+2)` with
both denominators cleared, so it needs exactly this and no division. -/
theorem realLOf_ratNat_le {p r : Nat} (h : p ≤ r) :
    realLLe (realLOf (ratNat.{u} p 1)) (realLOf (ratNat.{u} r 1)) :=
  (realLOf_le_realLOf (ratNat_mem_Rat (by omega)) (ratNat_mem_Rat (by omega))).mpr
    ((ratNat_le_iff (by omega) (by omega)).mpr (by omega))


/-- A nonnegative rational names a nonnegative real. The idiom
`realLThreeQuarters_nonneg` spelled once for every numerator and denominator,
since the descent's rational ratio needs it too and that one is not a
reciprocal. -/
theorem realLOf_ratNat_nonneg (a : Nat) {d : Nat} (hd : 0 < d) :
    realLLe realLZero.{u} (realLOf (ratNat.{u} a d)) := by
  rw [show realLZero.{u} = realLOf (ratNat.{u} 0 d) from
    congrArg realLOf (ratNat_zero hd).symm]
  exact (realLOf_le_realLOf (ratNat_mem_Rat hd) (ratNat_mem_Rat hd)).mpr
    ((ratNat_le_iff hd hd).mpr (by omega))


/-- A positive natural embeds as a positive real.

The family already has `realLOf_ratNat_nonneg`, `realLOf_ratNat_le` and
`ratNat_pos`, and not this composition of them --- so the four-line
form

    show realLLt (realLOf ratZero) _
    exact (realLOf_lt_realLOf ratZero_mem_Rat (ratNat_mem_Rat h1)).mpr
      (ratNat_pos hk)

is otherwise written inline wherever a denominator or a `realLInv` needs its
argument positive. `Topology/Metric.lean` has `realLOf_pos` at the same shape
over a general rational; this one sits beside `_nonneg`, where a reader of the
family looks, and needs no `open` line changed to be named. -/
theorem realLOf_ratNat_pos {k : Nat} (hk : 0 < k) :
    realLLt realLZero.{u} (realLOf (ratNat.{u} k 1)) := by
  show realLLt (realLOf ratZero.{u}) _
  exact (realLOf_lt_realLOf ratZero_mem_Rat
    (ratNat_mem_Rat (by omega : (0:Nat) < 1))).mpr (ratNat_pos hk)

/-- `realLOf` carries a product of naturals.

Proved twice, in `Combinatorics/Stirling.lean` and in
`Analysis/DirichletChar.lean`, by modules that cannot see one another,
under two spellings whose statements were identical binder for binder. -/
theorem realLOf_ratNat_mul (a b : Nat) :
    realLOf (ratNat.{u} (a * b) 1)
      = realLMul (realLOf (ratNat.{u} a 1)) (realLOf (ratNat.{u} b 1)) := by
  rw [← realLOf_mul (ratNat_mem_Rat (Nat.succ_pos 0)) (ratNat_mem_Rat (Nat.succ_pos 0)),
    ratNat_mul (Nat.succ_pos 0) (Nat.succ_pos 0)]

#print axioms Analysis.realLOf_ratNat_mul

/-- `k / 1` is a real. The membership half of the `realLOf_ratNat_*` family.

Every use is at denominator `1`, where `ratNat_mem_Rat`'s hypothesis is the
constant `0 < 1`. Stating it here removes that `have h1 : (0:Nat) < 1` from the
call sites, which is the only thing the inline form was ever carrying. -/
theorem realLOf_ratNat_mem (k : Nat) : realLOf (ratNat.{u} k 1) ∈ RealL.{u} :=
  realLOf_mem (ratNat_mem_Rat (by omega : (0:Nat) < 1))

#print axioms realLOf_ratNat_mem

/-- `k / 1` is nonnegative, as a function of `k`.

`realLOf_ratNat_nonneg` takes the denominator's positivity as a hypothesis, so
every call site carried a `have h1 : (0:Nat) < 1`. At denominator `1` that
hypothesis is constant and `omega` closes it here instead. -/
theorem realLOf_ratNat_one_nonneg (k : Nat) :
    realLLe realLZero.{u} (realLOf (ratNat.{u} k 1)) :=
  realLOf_ratNat_nonneg k (by omega : (0:Nat) < 1)

#print axioms realLOf_ratNat_one_nonneg

/-- `(k+1) / 1` is positive, as a function of `k`.

The successor form, where positivity of the numerator is a fact about `k + 1`
rather than a hypothesis. The call sites use this shape --- they index sums
from `1` --- so a bare name replaces the local `have`. -/
theorem realLOf_ratNat_succ_pos (k : Nat) :
    realLLt realLZero.{u} (realLOf (ratNat.{u} (k + 1) 1)) :=
  realLOf_ratNat_pos (by omega : 0 < k + 1)

#print axioms realLOf_ratNat_succ_pos

/-- And a rational strictly above it.

WHY IT WAS BUILT: the other side of the same bracket. Stated separately rather
than as a conjunction because the two halves are used at different points of a
reduction --- the lower one bounds the round from below, the upper one bounds
the remainder. -/
theorem exists_realLLt_ratOf {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    ∃ r : ZFSet.{u}, r ∈ NumberTheory.Rat.{u} ∧ realLLt x (realLOf r) := by
  obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨r, hr⟩ := hloc.upper_inhabited
  refine ⟨r, hloc.upper_subset r hr, ?_⟩
  exact (lt_realLOf_iff_mem_upper hx (hloc.upper_subset r hr)).mpr
    (by rw [snd_opair]; exact hr)

#print axioms Analysis.exists_realLLt_ratOf

/-- Deciding the strict order between LOCATED REALS, as a Prop.

Named because the seven bisection rows' residue is exactly this and a principle
named in prose cannot be reversed to. Those rows spend
`SignDisjunction + BinaryDCOn`; `NumberTheory.binaryDCOnAt_of_decided` replaces
the second summand by a decision about the branch, and the branch is a
comparison of one located real against another.

THE `RealL` GUARDS MUST NOT BE DROPPED. `Constructive.DecidableRealLLe` has
none, and `Constructive.wem_of_decidableRealLLe` exploits that: its witness is
built from `opair`s of separation sets, points that are NOT located reals, so
`decidableRealLLe_iff_wem` prices the UNRESTRICTED decision by the `sep` gadget
and says nothing about this one. Restricting to `RealL` changes the question,
and `Analysis.lpo_of_decidableRealLLt` shows it changes the answer.
-/
def DecidableRealLLt : Prop :=
  ∀ x y : ZFSet.{u}, x ∈ RealL.{u} → y ∈ RealL.{u} →
    realLLt x y ∨ ¬ realLLt x y

#print axioms Analysis.DecidableRealLLt


#print axioms add_window
#print axioms larger_mem
#print axioms smaller_mem
#print axioms mul_located_of_brackets
#print axioms addLower_assoc_le
#print axioms addUpper_assoc_le
#print axioms mulCorners_comm
#print axioms four_corners_of_nonneg
#print axioms neg_mem_lower
#print axioms upper_nonneg
#print axioms mem_mulLower_of_neg

#print axioms lower_mem_Real
#print axioms mem_RealL_iff
#print axioms isLocated_of_mem_RealL
#print axioms mem_supLower_iff
#print axioms mem_supUpper_iff
#print axioms le_sup
#print axioms upper_eq_of_lower_eq
#print axioms mem_addLower_iff
#print axioms mem_addUpper_iff
#print axioms mem_negLower_iff
#print axioms mem_negUpper_iff
#print axioms mem_mulLower_iff
#print axioms mem_mulUpper_iff
#print axioms isLocated_mul_of_located
#print axioms addLower_comm
#print axioms addUpper_comm
#print axioms realLLt_asymm
#print axioms realLApart_symm
#print axioms realLApart_irrefl
#print axioms mem_invLower_iff
#print axioms mem_invUpper_iff
#print axioms upper_pos_of_witness
#print axioms mulUpper_inv_le
#print axioms mulUpper_inv_ge
#print axioms realLOf_lt_zero
#print axioms realLLt_of_neg_of_nonneg
#print axioms realLAdd_pos_of_nonneg
#print axioms isCut_lower
#print axioms realLNeg_realLNeg
#print axioms realLLe_lower_subset
#print axioms realLAdd_right_cancel
#print axioms realLMin_le_left
#print axioms realLMin_le_right
#print axioms realLLt_max_cases
#print axioms realLLt_max_of_right
#print axioms realLLt_min_cases
#print axioms realLMin_lt_of_left
#print axioms realLMax_comm
end Analysis





#print axioms Analysis.realLOf_ratNat_nonneg
#print axioms Analysis.realLOf_ratNat_le








#print axioms Analysis.exists_natBound_realL
#print axioms Analysis.exists_natBound_below
#print axioms Analysis.realLOf_ratNat_pos

namespace ZFSet
export Analysis (BoundedLocated Close DecidableRealLLt FamilyLocated FamilyLocatedInf IsLocated LocatedReadout RealL WithinOf addLower addLower_assoc addLower_comm addLower_eq_realAdd addLower_neg addLower_zero addUpper addUpper_assoc addUpper_comm addUpper_neg addUpper_zero apart_mul_apart approached_of_inf approx_diff block_split boundsOf boundsOf_subset cauchySchwarz_realL cell_split chain_slack close_add_real close_realLMax close_stable close_symm_real close_trans_real corners_of_refinement corners_of_refinement' disp_sub dyadicHi dyadicLeft dyadicLo eq_zero_of_add_eq_zero eq_zero_of_add_self_eq_zero eq_zero_of_sq_zero exists_between_of_realLApart exists_natBound_below exists_natBound_realL exists_pos_lower exists_rat_bracket exists_realLLt_ratOf familyLocatedInf_of_lowerBound_of_approx glb_of_familyLocatedInf glb_of_familyLocatedInf_set gridPt infLower infUpper inf_realLLe_of_mem invLower invScale invScale_antitone invScale_mem invUpper isCut_lower isLocated_add isLocated_inf_of_familyLocatedInf isLocated_inv isLocated_max isLocated_min isLocated_mul isLocated_mul_of_located isLocated_neg isLocated_of_mem_RealL isLocated_ratCut isLocated_sup_of_familyLocated le_add_of_neg_le_sub' le_add_of_sub_le le_realLMin le_sup le_sup_realLLe located_bracket located_bracket_width located_eq_of_subset located_of_isLocated lowerBound_boundsOf lower_mem_Real lower_of_le_of_lower lower_pair_bound lt_of_sub_pos lt_realLOf_iff_mem_upper lub_of_familyLocated mem_RealL_iff mem_addLower_iff mem_addUpper_iff mem_boundsOf_iff mem_infLower_iff mem_infUpper_iff mem_invLower_iff mem_invUpper_iff mem_lower_of_neg_of_nonneg mem_mulLower_iff mem_mulUpper_iff mem_negLower_iff mem_negUpper_iff mem_supLower_iff mem_supUpper_iff mem_upper_iff mulLower mulLower_assoc_le mulLower_comm mulLower_const mulLower_distrib_le mulLower_eq_realMulNonneg mulLower_inv mulLower_inv_ge mulLower_inv_le mulLower_nonneg_witnesses mulLower_one mulLower_sub_realMulNonneg mulLower_tight mulLower_zero mulUpper mulUpper_assoc_le mulUpper_comm mulUpper_const mulUpper_distrib_le mulUpper_inv mulUpper_inv_ge mulUpper_inv_le mulUpper_one mulUpper_tight mulUpper_zero mul_eq_zero_absurd_of_apart mul_located negLower negUpper nonneg_of_withinOf not_min_lt_both not_not_apart_of_ne pairLe neg_of_mul_neg_left pairLe_antisymm pos_of_mul_pos_left pos_or_pos_of_add_pos realLAdd realLAdd_assoc realLAdd_cancel_two realLAdd_comm realLAdd_interchange realLAdd_mem realLAdd_middle_pair realLAdd_mul realLAdd_neg realLAdd_nonneg realLAdd_pos_of_nonneg realLAdd_right_cancel realLAdd_right_comm realLAdd_sub_add realLAdd_sub_cancel_left realLAdd_swap_inner realLAdd_zero realLApart realLApart_add_self realLApart_iff_sub realLApart_irrefl realLApart_mul_left realLApart_symm realLApart_tight realLApart_zero_of_max_pos realLApart_zero_one realLDouble realLIco realLInv realLInvApart realLInvApart_mem realLInv_antitone realLInv_eq_of_mul_one realLInv_le_of_le realLInv_mem realLInv_one realLInv_pos realLInv_realLOf realLLe realLLe_add realLLe_add_right realLLe_add_right_cancel realLLe_antisymm realLLe_inf_of_forall realLLe_lower_subset realLLe_max_left realLLe_max_right realLLe_neg_of_le_add realLLe_of_lower_subset realLLe_of_lt realLLe_of_mul_le_mul_right realLLe_refl realLLe_self_add_nonneg realLLe_sub_nonneg realLLe_sub_sub_of_add_le realLLe_trans realLLt realLLt_add realLLt_add_right realLLt_add_right_cancel realLLt_cotrans realLLt_irrefl realLLt_max_cases realLLt_max_of_right realLLt_min realLLt_min_cases realLLt_min_pair realLLt_of_le_of_lt realLLt_of_lt_of_le realLLt_of_neg_lt_neg realLLt_of_neg_of_nonneg realLLt_realLOf_of_mem_upper realLLt_self_add_pos realLLt_sub_neg realLLt_sub_pos realLLt_sub_pos_self realLLt_trans realLMax realLMaxList realLMax_add_dist realLMax_comm realLMax_eq_left_of_le realLMax_le realLMax_lt realLMax_lt_pair realLMax_mem realLMax_shift_le realLMin realLMinList realLMin_add_le realLMin_le_left realLMin_le_right realLMin_lt_of_left realLMin_mem realLMin_pos realLMul realLMul_assoc realLMul_comm realLMul_distrib realLMul_inv realLMul_invApart realLMul_le_left realLMul_le_right realLMul_left_cancel_apart realLMul_left_comm realLMul_lt_right realLMul_mem realLMul_neg realLMul_neg_neg realLMul_neg_of_neg_of_pos realLMul_nonneg realLMul_one realLMul_pos realLMul_ratInv_cancel realLMul_shuffle_pair realLMul_sq_swap realLMul_sub_mul realLMul_zero realLNeg realLNeg_le_neg realLNeg_le_sub_iff realLNeg_le_zero realLNeg_lt_neg realLNeg_mem realLNeg_neg_of_pos realLNeg_pos realLNeg_realLAdd realLNeg_realLMul realLNeg_realLNeg realLNeg_sub realLNeg_zero realLOf realLOf_add realLOf_le_realLOf realLOf_lt_iff_mem_lower realLOf_lt_realLOf realLOf_lt_zero realLOf_mem realLOf_mul realLOf_ratNat_add realLOf_ratNat_le realLOf_ratNat_mem realLOf_ratNat_nonneg realLOf_ratNat_one_nonneg realLOf_ratNat_pos realLOf_ratNat_succ_pos realLOne realLOne_le_realLInv_of_le_one realLOne_mem realLOne_mul realLSq_le_of_within realLSq_lt_sq realLSq_nonneg realLSq_pos realLSub_add_cancel realLSub_add_sub realLSub_eq_zero_iff realLSub_le_iff realLSub_mul realLSub_nonpos_of_le realLSub_sq realLSub_sub realLSub_sub_cancel realLTwo_mem realLTwo_pos realLZero realLZero_add realLZero_le_realLNeg realLZero_lt_one realLZero_mem realLZero_mul realL_add_mul_add realL_eq_opair realL_inv_unique realL_inverses realL_mul_ne_zero reflect_step_eq riemann_step_eq shift_sub slack_add_lin sq_le_sq_of_bracket sq_le_sq_of_le sq_sub_expand sq_sum sub_add_sub_eq_zero sub_pos_of_lt sub_shift_cancel supLower supUpper sup_le sup_realLLe_of_forall sup_realLLe_of_forall_le toCut toCut_add toCut_injective toCut_le toCut_mem toCut_mul upper_eq_of_lower upper_eq_of_lower_eq upper_of_le_ratOf upper_pair_bound upper_pos_of_witness withinOf_add_real withinOf_neg_real withinOf_of_cases withinOf_realLMul withinOf_stable)
end ZFSet
