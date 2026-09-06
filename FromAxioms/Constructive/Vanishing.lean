/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# What it costs to decide that a real is zero

`DecidableVanishing R zero` is the hypothesis every degree argument in
`PolyRing.lean` carries: that a coefficient can be told apart from zero. Over a
finite ring it is free, and over `ℚ` it is arithmetic. Over `ℝ` it is not, and
this file measures it.

The measurement is a transport. `Ternary.lean` walks a binary sequence down the
thirds and lands on nested intervals; `Nested.lean` turns those into a located
pair, which is a member of `RealL`; and `toCut` is injective on `RealL`, so the
located real is zero exactly when its lower cut is. That last equivalence is
`Omniscience.lean`'s `TernaryZeroDecidable`, which is `WLPO`.

So the bridge the reduction needed is `toCut_injective`, and the chain is

    DecidableVanishing RealL realLZero  →  TernaryZeroDecidable  →  WLPO

The converse holds on the walk-built family -- `ternary_vanishing_of_wlpo` --
so `WLPO` is exactly the price there. For an arbitrary located real it is a
lower bound only, and the gap is the familiar one: `located` returns a
disjunction, and turning one into a bit is defining data by cases.
-/

import FromAxioms.Algebra.Field
import FromAxioms.Analysis.IVT
import FromAxioms.SetTheory.Uncountable

set_option autoImplicit false

universe u

open Analysis NumberTheory SetTheory
namespace Constructive

/-- The ternary walk, as a located real rather than a bare cut. -/
def ternaryReal (α : Nat → Bool) : ZFSet.{u} :=
  opair (nestLower (tlowSeq.{u} (boolDigit α))) (nestUpper (thighSeq.{u} (boolDigit α)))

theorem ternaryReal_mem (α : Nat → Bool) : ternaryReal.{u} α ∈ RealL.{u} :=
  (mem_RealL_iff _).mpr ⟨_, _, rfl, isLocated_nest (isNested_ternary (boolDigit_le_one α))⟩


/-- The walk never goes below zero: every rational above it is above one of
the walk's upper endpoints, and those are positive. -/
theorem ternaryReal_nonneg (α : Nat → Bool) :
    realLLe realLZero.{u} (ternaryReal.{u} α) := by
  rintro ⟨p, hpU, hp0⟩
  rw [ternaryReal, snd_opair] at hpU
  rw [realLZero, realLOf, fst_opair] at hp0
  obtain ⟨hpQ, hpneg⟩ := (mem_ratCut_iff _ p).mp hp0
  obtain ⟨-, m, hm, hlt⟩ := (mem_nestUpper_iff _ p).mp hpU
  obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
  rw [app_thighSeq, thigh] at hlt
  have hpos : ratLt ratZero.{u} (ratNat.{u} (tnum (boolDigit α) i + 1) (pow3 i)) := by
    rw [ratZero_eq_ratNat, ratNat_lt_iff (by omega) (pow3_pos i)]
    omega
  exact ratLt_irrefl (ratLt_trans ratZero_mem_Rat hpQ ratZero_mem_Rat
    (ratLt_trans ratZero_mem_Rat (ratNat_mem_Rat (pow3_pos i)) hpQ hpos hlt) hpneg)

/-- And it lands in `[0,1]`, with the upper end ATTAINED. The lower cut
holds nothing above `1`, because every approximant is `tnum c n / 3^n` and
`tnum_lt_pow3` keeps that strictly below one. The companion to
`ternaryReal_nonneg`, and what lets a product be compared against a single
factor.

THE BOUND IS TIGHT AND THE STRICT FORM IS FALSE. `tnum c (n+1)` is
`3 * tnum c n + 2 * c n`, which DOUBLES each digit, so the walk is the Cantor
embedding whose supremum is exactly `1` --- attained at the all-true sequence.
A caller needing `<` must constrain the SEQUENCE rather than sharpen this
proof; `ternaryReal_lt_one_of_head_false` does it with a single digit. -/
theorem ternaryReal_le_one (a : Nat → Bool) :
    realLLe (ternaryReal.{u} a) realLOne.{u} := by
  rintro ⟨p, hpU, hplow⟩
  rw [realLOne, realLOf, snd_opair] at hpU
  rw [ternaryReal, fst_opair] at hplow
  obtain ⟨hpQ, hp1⟩ := (mem_sep_iff _ _ _).mp hpU
  obtain ⟨-, m, hm, hlt⟩ := (mem_nestLower_iff _ p).mp hplow
  obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
  rw [app_tlowSeq, tlow] at hlt
  have hb := tnum_lt_pow3 (boolDigit_le_one a) i
  have hlt1 : ratLt.{u} (ratNat.{u} (tnum (boolDigit a) i) (pow3 i)) ratOne.{u} := by
    -- `intOfNat 1` and `intOne` are the same term
    have : ratOne.{u} = ratNat.{u} 1 1 := rfl
    rw [this, ratNat_lt_iff (pow3_pos i) (by omega)]
    omega
  exact ratLt_irrefl (ratLt_trans (ratNat_mem_Rat (pow3_pos i)) ratOne_mem_Rat
    (ratNat_mem_Rat (pow3_pos i)) hlt1 (ratLt_trans ratOne_mem_Rat hpQ
      (ratNat_mem_Rat (pow3_pos i)) hp1 hlt))

/-- A walk whose first digit is `false` is STRICTLY below one.

`ternaryReal_le_one` cannot be sharpened as it stands, because its bound is
attained, so the strictness has to be bought from the SEQUENCE. One digit pays
for it: with `a 0 = false` the walk is confined to the first third, and `1/2` is
then a rational lying in its upper cut and under one, which is exactly the
witness `realLLt` asks for.

THE INDEX IS ONE, NOT ZERO, and that is the whole content. `thigh` at zero is
`1` itself and says nothing; at one it is `(2 * d_0 + 1)/3`, which the
hypothesis pins at `1/3`. -/
theorem ternaryReal_lt_one_of_head_false {a : Nat → Bool} (h : a 0 = false) :
    realLLt (ternaryReal.{u} a) realLOne.{u} := by
  have hd : boolDigit a 0 = 0 := by rw [boolDigit, h]; decide
  have ht : tnum (boolDigit a) 1 = 0 := by
    show 3 * 0 + 2 * boolDigit a 0 = 0
    rw [hd]
  have hp3 : pow3 1 = 3 := rfl
  refine ⟨ratNat.{u} 1 2, ?_, ?_⟩
  · rw [ternaryReal, snd_opair]
    refine (mem_nestUpper_iff _ _).mpr ⟨ratNat_mem_Rat (by omega), ofNat.{u} 1,
      ofNat_mem_omega 1, ?_⟩
    rw [app_thighSeq, thigh, ht, hp3]
    exact (ratNat_lt_iff (by omega) (by omega)).mpr (by omega)
  · rw [realLOne, realLOf, fst_opair]
    refine (mem_ratCut_iff _ _).mpr ⟨ratNat_mem_Rat (by omega), ?_⟩
    have hone : ratOne.{u} = ratNat.{u} 1 1 := rfl
    rw [hone]
    exact (ratNat_lt_iff (by omega) (by omega)).mpr (by omega)

#print axioms Constructive.ternaryReal_lt_one_of_head_false

/-! ## From vanishing to equality
-/


/-- Dependent choice. The value at each step is constrained by the value
already taken, which is exactly what `BinaryDC` turned out not to require:
its hypothesis asked for a decision at every numerator, so the decisions could
all precede the recursion and it collapsed to countable choice.
Here `R` is only total, so nothing about step `n+1` is available until step `n`
has been chosen.

Stated but not used. Like `ACOmega` in `Cauchy.lean` it is here so implications
can be measured against it. `ACOmega` from it is DONE -- `acOmega_of_dc`, below
in this file. What is still wanted is the Baire category theorem REVERSED to it:
`baireL_of_dc` and `baire_of_dc` are the forward direction, and the Baire node
is a SINK in `lattice.json`, with incoming edges only. -/
def DC : Prop :=
  ∀ S R : ZFSet.{u}, R ⊆ prod S S →
    (∀ a, a ∈ S → ∃ b, b ∈ S ∧ opair a b ∈ R) →
    ∀ a₀, a₀ ∈ S →
    ∃ g, IsFunction g ∧ domain g = omega.{u} ∧ app g empty.{u} = a₀ ∧
      ∀ n, n ∈ omega.{u} → opair (app g n) (app g (succ n)) ∈ R

/-- Dependent choice on one set. `DC` is this quantified over every `S`,
and no consumer in this development needs that quantifier: each spends its
hypothesis on a set it has already built. `baire_of_dc` uses `baireState`,
a separation of `prod omega (prod NumberTheory.Rat NumberTheory.Rat)`; `acOmega_of_dc` uses
`acState F`. Naming the restriction lets a theorem state which set it needs
rather than asking for all of them.

`Baire.lean` already makes this argument for the target of a reversal --
"`DC` quantifies over every set; Baire knows only about the reals; no
argument from the second can reach the first" -- and `DCOmega` is that
restriction. The same argument applies to the hypothesis, which is what
this is. -/
def DCOn (S : ZFSet.{u}) : Prop :=
  ∀ R : ZFSet.{u}, R ⊆ prod S S →
    (∀ a, a ∈ S → ∃ b, b ∈ S ∧ opair a b ∈ R) →
    ∀ a₀, a₀ ∈ S →
    ∃ g, IsFunction g ∧ domain g = omega.{u} ∧ app g empty.{u} = a₀ ∧
      ∀ n, n ∈ omega.{u} → opair (app g n) (app g (succ n)) ∈ R

/-- `DC` is `DCOn` at every set, so it gives one at any particular set. The
converse is exactly the quantifier, and nothing here proves it. -/
theorem dcOn_of_dc (hdc : DC.{u}) (S : ZFSet.{u}) : DCOn.{u} S :=
  fun R hR htotal a₀ ha₀ => hdc S R hR htotal a₀ ha₀

/-! ## Countable choice from dependent choice

`ACOmega` chooses from an `ω`-indexed family; `DC` steps along a relation. The
bridge is the usual one: make the index part of the state, so stepping the
relation advances the index, and the sequence `DC` returns becomes a choice
function once its first component is discarded.
-/

/-- The states: an index paired with a member of that index's set. -/
private def acState (F : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => ∃ n, n ∈ omega.{u} ∧ ∃ y, y ∈ app F n ∧ z = opair n y)
    (prod omega.{u} (sUnion (range F)))

private theorem mem_acState_iff (F z : ZFSet.{u}) :
    z ∈ acState F ↔ z ∈ prod omega.{u} (sUnion (range F)) ∧
      ∃ n, n ∈ omega.{u} ∧ ∃ y, y ∈ app F n ∧ z = opair n y :=
  mem_sep_iff _ _ _

/-- The step: advance the index by one, choosing anew. -/
private def acStep (F : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ a, a ∈ acState F ∧ ∃ b, b ∈ acState F ∧
        p = opair a b ∧ fst b = succ (fst a))
    (prod (acState F) (acState F))

/-- Countable choice from dependent choice on the state sets. The
hypothesis is `DCOn` at each `acState F` rather than `DC`, because that is
all the proof reaches for. -/
theorem acOmega_of_dcOn (hdc : ∀ F : ZFSet.{u}, DCOn.{u} (acState F)) :
    ACOmega.{u} := by
  intro F hF hdom hinh
  have hmemS : ∀ n y, n ∈ omega.{u} → y ∈ app F n → opair n y ∈ acState F := by
    intro n y hn hy
    refine (mem_acState_iff F _).mpr ⟨?_, n, hn, y, hy, rfl⟩
    exact opair_mem_prod hn ((mem_sUnion_iff _ _).mpr
      ⟨app F n, app_mem_range hF (hdom ▸ hn), hy⟩)
  -- the relation is total: every state has a successor at the next index
  have htotal : ∀ a, a ∈ acState F → ∃ b, b ∈ acState F ∧ opair a b ∈ acStep F := by
    intro a ha
    obtain ⟨-, n, hn, y, hy, rfl⟩ := (mem_acState_iff F a).mp ha
    obtain ⟨y', hy'⟩ := hinh (succ n) (succ_mem_omega _ hn)
    refine ⟨opair (succ n) y', hmemS _ _ (succ_mem_omega _ hn) hy', ?_⟩
    refine (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod ha (hmemS _ _ (succ_mem_omega _ hn) hy'),
      _, ha, _, hmemS _ _ (succ_mem_omega _ hn) hy', rfl, ?_⟩
    rw [fst_opair, fst_opair]
  obtain ⟨y₀, hy₀⟩ := hinh empty.{u} empty_mem_omega
  obtain ⟨h, hfun, hdomh, hzero, hstep⟩ :=
    hdc F (acStep F) (fun z hz => ((mem_sep_iff _ _ _).mp hz).left) htotal _ (hmemS _ _ empty_mem_omega hy₀)
  -- the index really is the position
  have hwalk : ∀ n, n ∈ omega.{u} → app h n ∈ acState F ∧ fst (app h n) = n := by
    refine omega_induction ?_ ?_
    · rw [hzero, fst_opair]
      exact ⟨hmemS _ _ empty_mem_omega hy₀, rfl⟩
    · intro k hk ih
      obtain ⟨-, a, ha, b, hb, he, hfb⟩ := (mem_sep_iff _ _ _).mp (hstep k hk)
      obtain ⟨rfl, rfl⟩ := opair_injective he
      exact ⟨hb, by rw [hfb, ih.right]⟩
  have hval : ∀ n, n ∈ omega.{u} → snd (app h n) ∈ app F n := by
    intro n hn
    obtain ⟨hS, hfstn⟩ := hwalk n hn
    obtain ⟨-, m, -, y, hy, he⟩ := (mem_acState_iff F _).mp hS
    rw [he] at hfstn ⊢
    rw [fst_opair] at hfstn
    rw [snd_opair, ← hfstn]
    exact hy
  have hinto : ∀ n, n ∈ omega.{u} → snd (app h n) ∈ sUnion (range F) := by
    intro n hn
    exact (mem_sUnion_iff _ _).mpr ⟨app F n, app_mem_range hF (hdom ▸ hn), hval n hn⟩
  refine ⟨graphOn omega.{u} (sUnion (range F)) (fun n => snd (app h n)),
    graphOn_isFunction _ _ _, graphOn_domain hinto, fun n hn => ?_⟩
  rw [app_graphOn hinto hn]
  exact hval n hn

/-- `DC` gives the sharper hypothesis at every set, so the original
statement is a corollary. Kept because it is the lattice edge's
witness. -/
theorem acOmega_of_dc (hdc : DC.{u}) : ACOmega.{u} :=
  acOmega_of_dcOn fun F => dcOn_of_dc hdc (acState F)

/-! ## The sign disjunction is `LLPO`

`IVT.lean` states a `SignReadout` -- data deciding whether a value is at most or
at least zero -- and notes that unlike the Baire selector's readout, the
disjunction it reads is not free. This is that claim, proved: a universal sign
disjunction gives `LLPO`.

The two ternary reals are both non-negative and cannot both be positive; the
difference's sign says which of them is at most zero. So the principle that
every real has a sign is exactly the principle that of two sequences at most one
of which fires, one can be named. -/

def SignDisjunction : Prop :=
  ∀ z, z ∈ RealL.{u} → realLLe z realLZero.{u} ∨ realLLe realLZero.{u} z

/-- Being above zero is having zero in the lower cut. -/
theorem realLZero_lt_iff_mem_lower {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    realLLt realLZero.{u} x ↔ ratZero.{u} ∈ fst x := by
  obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff x).mp hx
  rw [fst_opair]
  constructor
  · rintro ⟨p, hpU, hpL⟩
    rw [realLZero, realLOf, snd_opair] at hpU
    rw [fst_opair] at hpL
    exact hloc.lower_down p hpL ratZero.{u} ratZero_mem_Rat
      ((mem_sep_iff _ _ _).mp hpU).right
  · intro h
    obtain ⟨p, hpL, hlt⟩ := hloc.lower_open ratZero.{u} h
    refine ⟨p, ?_, ?_⟩
    · rw [realLZero, realLOf, snd_opair]
      exact (mem_sep_iff _ _ _).mpr ⟨hloc.lower_subset p hpL, hlt⟩
    · rw [fst_opair]
      exact hpL

/-- Rearrangement: a difference at most zero is an inequality. -/
private theorem le_of_sub_le_zero {a b : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (h : realLLe (realLAdd a (realLNeg b)) realLZero.{u}) :
    realLLe a b := by
  intro hlt
  refine h ?_
  exact sub_pos_of_lt hb ha hlt

/-- `LLPO` from comparing ternary reals ALONE, which is all
`llpo_of_signDisjunction` ever used.

A REFINEMENT OF AN EXISTING THEOREM, not a new route. `llpo_of_signDisjunction`
takes `SignDisjunction` --- every real has a sign --- and spends it in one place:
`rcases h _ (realLAdd_mem hα (realLNeg_mem hβ))`, on the DIFFERENCE of two
ternary reals, immediately converting the answer into `a <= b` or `b <= a`. The
`key` helper, which is the substance, never sees the principle at all.

So the hypothesis is stronger than the proof needs. This takes the comparison
of two ternary reals only --- a statement about a bounded family rather than
about every located real --- and `signDisjunction` still reaches it, so nothing
is lost.

WHY IT MATTERS HERE: `ternary_dichotomy` derives that comparison from
`DyadicApprox`, so the one-cell readout reaches `LLPO` through this and would not
through the unrefined form, which would demand a sign for reals the readout says
nothing about. -/
theorem llpo_of_ternaryComparison
    (hcmp : ∀ α β : Nat → Bool, realLLe (ternaryReal.{u} α) (ternaryReal.{u} β) ∨
      realLLe (ternaryReal.{u} β) (ternaryReal.{u} α)) : LLPO := by
  refine llpo_of_ternary_llpo.{u} fun α β hdisj => ?_
  have key : ∀ x y : Nat → Bool, realLLe (ternaryReal.{u} x) (ternaryReal.{u} y) →
      ¬ ((∃ n, x n = true) ∧ (∃ n, y n = true)) →
      ratZero.{u} ∉ nestLower (tlowSeq.{u} (boolDigit x)) := by
    intro x y hle hno hin
    have hxm := ternaryReal_mem.{u} x
    have hym := ternaryReal_mem.{u} y
    have hxpos : realLLt realLZero.{u} (ternaryReal.{u} x) :=
      (realLZero_lt_iff_mem_lower hxm).mpr (by rw [ternaryReal, fst_opair]; exact hin)
    have hypos : realLLt realLZero.{u} (ternaryReal.{u} y) := by
      rcases realLLt_cotrans realLZero_mem hxm hym hxpos with hgt | hlt
      · exact hgt
      · exact absurd hlt hle
    refine hno ⟨(zero_mem_ternary_iff x).mp hin, (zero_mem_ternary_iff y).mp ?_⟩
    have := (realLZero_lt_iff_mem_lower hym).mp hypos
    rwa [ternaryReal, fst_opair] at this
  rcases hcmp α β with hle | hge
  · exact Or.inl (key α β hle hdisj)
  · exact Or.inr (key β α hge (fun hc => hdisj ⟨hc.right, hc.left⟩))

#print axioms Constructive.llpo_of_ternaryComparison

/-- A sign for every real is `LLPO`. -/
theorem llpo_of_signDisjunction (h : SignDisjunction.{u}) : LLPO :=
  -- ROUTED THROUGH `llpo_of_ternaryComparison`, which carries the comparison
  -- block. The principle is spent in ONE place: on the DIFFERENCE of the two
  -- ternary reals, read back as a comparison.
  llpo_of_ternaryComparison fun α β => by
    have hα := ternaryReal_mem.{u} α
    have hβ := ternaryReal_mem.{u} β
    rcases h _ (realLAdd_mem hα (realLNeg_mem hβ)) with hle | hge
    · exact Or.inl (le_of_sub_le_zero hα hβ hle)
    · refine Or.inr (fun hlt => hge ?_)
      have := realLLt_add_right hα hβ (realLNeg_mem hβ) hlt
      rwa [realLAdd_neg hβ] at this

/-! ## The harmonic jump, and where a zero locator comes from -/

/-- Dependent choice for relations on `ω`. -/
def DCOmega : Prop :=
  ∀ R : ZFSet.{u}, R ⊆ prod omega.{u} omega.{u} →
    (∀ a, a ∈ omega.{u} → ∃ b, b ∈ omega.{u} ∧ opair a b ∈ R) →
    ∀ a₀, a₀ ∈ omega.{u} →
    ∃ g, IsFunction g ∧ domain g = omega.{u} ∧ app g empty.{u} = a₀ ∧
      ∀ n, n ∈ omega.{u} → opair (app g n) (app g (succ n)) ∈ R

/-- The ONE-cell readout at DEPTH ONE decides which side of `1` a real lies on.

Why the two-cell form is a necessity and not a convenience. At depth one the
one-cell window is `2 * (1/2)^1 = 1` and the grid is `{0, 1}` --- the two strings
of length one --- so a one-cell answer at that depth IS a dichotomy: `[false]`
says `x <= 1` and `[true]` says `1 <= x`.

THE `∃` IS ALREADY THE DISJUNCTION. This needs no map form and no choice to
extract: a list of length one is `[false]` or `[true]`, so the existential
unfolds to a two-way case split on its own. So the one-cell form is expensive
where the two-cell form is free --- a locator answers about a PAIR and never
places a real relative to a single point.

`SignDisjunction` is this dichotomy at zero, and `llpo_of_signDisjunction`
prices it at `LLPO`. This is the same shape at `1` on `[0,2]`, which is where a
route from the one-cell readout to that principle would start. -/
theorem dichotomy_of_depthOne
    (h : ∀ x : ZFSet.{u}, x ∈ RealL.{u} →
      realLLe (realLOf ratZero.{u}) x →
      realLLe x (realLOf (ratNat.{u} 2 1)) →
      ∃ s : List Bool, s.length = 1 ∧
        realLLe (realLOf (dyadicOf.{u} s)) x ∧
        realLLe x (realLOf (ratAdd (dyadicOf.{u} s)
          (ratMul (ratNat.{u} 2 1) (ratPow (ratNat.{u} 1 2) 1)))))
    {x : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (h0 : realLLe (realLOf ratZero.{u}) x)
    (h2 : realLLe x (realLOf (ratNat.{u} 2 1))) :
    realLLe x (realLOf ratOne.{u}) ∨ realLLe (realLOf ratOne.{u}) x := by
  obtain ⟨s, hlen, hlo, hhi⟩ := h x hx h0 h2
  have hw : ratMul (ratNat.{u} 2 1) (ratPow (ratNat.{u} 1 2) 1) = ratOne.{u} := by
    show ratMul (ratNat.{u} 2 1) (ratMul ratOne.{u} (ratNat.{u} 1 2)) = ratOne.{u}
    rw [ratOne_mul (ratNat_mem_Rat (by omega)), ratNat_mul (by omega) (by omega),
      ← ratNat_one_one]
    exact (ratNat_eq_iff (by omega) (by omega)).mpr (by omega)
  match s, hlen with
  | [false], _ =>
      refine Or.inl ?_
      rw [hw, SetTheory.dyadicOf_false, ratZero_add ratOne_mem_Rat] at hhi
      exact hhi
  | [true], _ =>
      refine Or.inr ?_
      rw [SetTheory.dyadicOf_true] at hlo
      exact hlo

#print axioms Constructive.dichotomy_of_depthOne

/-- The same dichotomy from the full principle, which is the form a caller
holding `DyadicApprox` wants. The content is `dichotomy_of_depthOne`; this only
instantiates the depth, choosing the `1`. -/
theorem dichotomy_of_dyadicApprox (h : SetTheory.DyadicApprox.{u})
    {x : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (h0 : realLLe (realLOf ratZero.{u}) x)
    (h2 : realLLe x (realLOf (ratNat.{u} 2 1))) :
    realLLe x (realLOf ratOne.{u}) ∨ realLLe (realLOf ratOne.{u}) x :=
  dichotomy_of_depthOne (fun y hy hy0 hy2 => h y hy hy0 hy2 1) hx h0 h2
#print axioms Constructive.dichotomy_of_dyadicApprox

/-- The depth-one readout gives a SIGN for every real in `[-1,1]`.

`SignDisjunction` with the range restricted, stated in that principle's own
shape so the two are directly comparable. The record's line that the one-cell
readout "yields a sign disjunction for bounded reals" was prose; this is it.

THE SHIFT IS THE WHOLE PROOF. `z + 1` lies in `[0,2]` exactly when `z` lies in
`[-1,1]`, and `dichotomy_of_depthOne` decides that against the midpoint `1` ---
which is `z` against `0`. Every step adds or subtracts `1` and cancels.

WHAT SEPARATES THIS FROM `SignDisjunction` IS THE RANGE HYPOTHESES. So the
distance between the one-cell readout and that principle is exactly the offset
--- reaching an arbitrary real --- which is the same forall-exists gap in its
third appearance, and NOT anything about deciding signs. -/
theorem boundedSign_of_depthOne
    (h : ∀ x : ZFSet.{u}, x ∈ RealL.{u} →
      realLLe (realLOf ratZero.{u}) x →
      realLLe x (realLOf (ratNat.{u} 2 1)) →
      ∃ s : List Bool, s.length = 1 ∧
        realLLe (realLOf (dyadicOf.{u} s)) x ∧
        realLLe x (realLOf (ratAdd (dyadicOf.{u} s)
          (ratMul (ratNat.{u} 2 1) (ratPow (ratNat.{u} 1 2) 1)))))
    {z : ZFSet.{u}} (hz : z ∈ RealL.{u})
    (hlo : realLLe (realLNeg (realLOf ratOne.{u})) z)
    (hhi : realLLe z (realLOf ratOne.{u})) :
    realLLe z realLZero.{u} ∨ realLLe realLZero.{u} z := by
  have h1 : realLOf ratOne.{u} ∈ RealL.{u} := realLOf_mem ratOne_mem_Rat
  have hn1 : realLNeg (realLOf ratOne.{u}) ∈ RealL.{u} := realLNeg_mem h1
  have hx : realLAdd z (realLOf ratOne.{u}) ∈ RealL.{u} := realLAdd_mem hz h1
  have htwo : realLAdd (realLOf ratOne.{u}) (realLOf ratOne.{u})
      = realLOf (ratNat.{u} 2 1) := by
    rw [← realLOf_add ratOne_mem_Rat ratOne_mem_Rat, ← ratNat_one_one,
      ratNat_add_same_denom (by omega : (0:Nat) < 1)]
  -- `0 <= z + 1`, from `-1 <= z`
  have h0 : realLLe (realLOf ratZero.{u}) (realLAdd z (realLOf ratOne.{u})) := by
    have hstep := realLLe_add_right hn1 hz h1 hlo
    rwa [realLAdd_comm hn1 h1, realLAdd_neg h1,
      show realLZero.{u} = realLOf ratZero.{u} from rfl] at hstep
  -- `z + 1 <= 2`, from `z <= 1`
  have h2 : realLLe (realLAdd z (realLOf ratOne.{u})) (realLOf (ratNat.{u} 2 1)) := by
    have hstep := realLLe_add_right hz h1 h1 hhi
    rwa [htwo] at hstep
  rcases dichotomy_of_depthOne h hx h0 h2 with hle | hge
  · -- `z + 1 <= 1` is `z <= 0`
    refine Or.inl ?_
    have hstep := realLLe_add_right hx h1 hn1 hle
    -- `rw` rewrites EVERY occurrence, so the second `realLAdd_neg` has nothing
    -- left; the chain is already at the goal. Trailing step trimmed.
    rwa [realLAdd_assoc hz h1 hn1, realLAdd_neg h1, realLAdd_zero hz] at hstep
  · -- `1 <= z + 1` is `0 <= z`
    refine Or.inr ?_
    have hstep := realLLe_add_right h1 hx hn1 hge
    -- `rw` rewrites EVERY occurrence, so the second `realLAdd_neg` has nothing
    -- left; the chain is already at the goal. Trailing step trimmed.
    rwa [realLAdd_assoc hz h1 hn1, realLAdd_neg h1, realLAdd_zero hz] at hstep

#print axioms Constructive.boundedSign_of_depthOne

/-- The comparison is the SIGN of the difference, so one of the two bounded
results derives the other.

`boundedDichotomy` and `boundedSign_of_depthOne` were proved separately from the
same depth-one dichotomy, each carrying its own forty lines of shifting. They are
one result: `a <= b` is `0 <= b - a`, and `b - a` lies in `[-1,1]` exactly when
`a` and `b` lie in `[0,1]`. So the comparison follows from the sign, and the
parallel development can go.

`realLLe_sub_nonneg` does the forward reading directly; the backward one adds `a`
to both sides, where `realLSub_add_cancel` collapses the left. -/
theorem boundedDichotomy
    (h : ∀ x : ZFSet.{u}, x ∈ RealL.{u} →
      realLLe (realLOf ratZero.{u}) x →
      realLLe x (realLOf (ratNat.{u} 2 1)) →
      ∃ s : List Bool, s.length = 1 ∧
        realLLe (realLOf (dyadicOf.{u} s)) x ∧
        realLLe x (realLOf (ratAdd (dyadicOf.{u} s)
          (ratMul (ratNat.{u} 2 1) (ratPow (ratNat.{u} 1 2) 1)))))
    {a b : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (ha0 : realLLe realLZero.{u} a) (ha1 : realLLe a (realLOf ratOne.{u}))
    (hb0 : realLLe realLZero.{u} b) (hb1 : realLLe b (realLOf ratOne.{u})) :
    realLLe a b ∨ realLLe b a := by
  have h1 : realLOf ratOne.{u} ∈ RealL.{u} := realLOf_mem ratOne_mem_Rat
  have hna : realLNeg a ∈ RealL.{u} := realLNeg_mem ha
  have hd : realLAdd b (realLNeg a) ∈ RealL.{u} := realLAdd_mem hb hna
  -- `b - a <= 1`, from `b <= 1` and `-a <= 0`
  -- `realLNeg_le_zero` IS this; the four lines it replaces were a hand-rolled
  -- derivation of a lemma sitting in `Located.lean`.
  have hna0 : realLLe (realLNeg a) realLZero.{u} := realLNeg_le_zero ha ha0
  have hhi : realLLe (realLAdd b (realLNeg a)) (realLOf ratOne.{u}) := by
    -- `realLLe_add_right` adds on the RIGHT, so this is `(-a) + b <= 0 + b`
    have hstep := realLLe_add_right hna realLZero_mem hb hna0
    rw [realLZero_add hb, realLAdd_comm hna hb] at hstep
    exact realLLe_trans hd hb h1 hstep hb1
  -- `-1 <= b - a`, from `0 <= b` and `-1 <= -a`
  have hlo : realLLe (realLNeg (realLOf ratOne.{u})) (realLAdd b (realLNeg a)) := by
    have hna1 : realLLe (realLNeg (realLOf ratOne.{u})) (realLNeg a) :=
      realLNeg_le_neg ha h1 ha1
    have hstep := realLLe_add_right realLZero_mem hb hna hb0
    rw [realLZero_add hna] at hstep      -- already `-a <= b + (-a)`
    exact realLLe_trans (realLNeg_mem h1) hna hd hna1 hstep
  rcases boundedSign_of_depthOne h hd hlo hhi with hle | hge
  · -- `b - a <= 0` is `b <= a`
    refine Or.inr ?_
    have hstep := realLLe_add_right hd realLZero_mem ha hle
    rwa [realLSub_add_cancel hb ha, realLZero_add ha] at hstep
  · exact Or.inl ((realLLe_sub_nonneg ha hb).mpr hge)

/-- The one-cell readout compares any two ternary reals.

The step that carries `dichotomy_of_dyadicApprox` toward a named principle.
`llpo_of_signDisjunction` consumes its hypothesis only at DIFFERENCES of ternary
reals, which lie in `[-1,1]`, so a dichotomy on `[0,2]` is enough: shift by one
and "which side of the midpoint" IS "which of the two is smaller".

NO NEGATION OF A SUM ANYWHERE, so this stays short. Every step adds `b` to both
sides and cancels: `x + b = 1 + a` by `realLSub_add_cancel`, so `x <= 1`
becomes `1 + a <= 1 + b` and then `a <= b` by cancelling on the right after a
commutation. The range bounds go the same way.

`1 + a` AND `2 + b` ARE THE ONLY TERMS THAT APPEAR, so the whole argument stays
inside the abelian-group laws the tree already has. -/
theorem ternary_dichotomy
    (h : ∀ x : ZFSet.{u}, x ∈ RealL.{u} →
      realLLe (realLOf ratZero.{u}) x →
      realLLe x (realLOf (ratNat.{u} 2 1)) →
      ∃ s : List Bool, s.length = 1 ∧
        realLLe (realLOf (dyadicOf.{u} s)) x ∧
        realLLe x (realLOf (ratAdd (dyadicOf.{u} s)
          (ratMul (ratNat.{u} 2 1) (ratPow (ratNat.{u} 1 2) 1))))) (α β : Nat → Bool) :
    realLLe (ternaryReal.{u} α) (ternaryReal.{u} β) ∨
      realLLe (ternaryReal.{u} β) (ternaryReal.{u} α) :=
  boundedDichotomy h (ternaryReal_mem α) (ternaryReal_mem β)
    (ternaryReal_nonneg α) (ternaryReal_le_one α)
    (ternaryReal_nonneg β) (ternaryReal_le_one β)

#print axioms Constructive.boundedDichotomy
#print axioms Constructive.ternary_dichotomy
end Constructive

#print axioms Constructive.ternaryReal_mem
#print axioms Constructive.DC
#print axioms Constructive.ternaryReal_nonneg
#print axioms Constructive.ternaryReal_le_one
#print axioms Constructive.DCOn
#print axioms Constructive.dcOn_of_dc
#print axioms Constructive.acOmega_of_dcOn      -- the premise the proof spends
#print axioms Constructive.acOmega_of_dc
#print axioms Constructive.realLZero_lt_iff_mem_lower
#print axioms Constructive.llpo_of_signDisjunction
#print axioms Constructive.DCOmega

namespace ZFSet
export Constructive (DC DCOmega DCOn SignDisjunction acOmega_of_dc acOmega_of_dcOn dcOn_of_dc llpo_of_signDisjunction realLZero_lt_iff_mem_lower ternaryReal ternaryReal_le_one ternaryReal_mem ternaryReal_nonneg)
end ZFSet
