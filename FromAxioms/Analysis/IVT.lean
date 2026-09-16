/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Towards the intermediate value theorem, constructively

The classical statement is false here, and not for a technical reason: a
function that crosses zero somewhere in an interval need not tell you where,
and a proof that produced the crossing point would decide which side of zero a
real lies on. What holds constructively is the approximate form -- a point where
the value is within `ε` of zero, for every `ε` -- and the exact form under a
hypothesis that supplies the missing decision.

This file builds towards that. `WithinOf` is the vocabulary: a two-sided bracket standing in for `|·| ≤ ε`.

No absolute value in the statements here: everything is a conjunction of
two order facts. (`realLAbs` now exists case-free in `Deriv.lean`, as
`max(x, -x)`; these brackets predate it and are the same content.)
-/

import FromAxioms.Analysis.Ternary
import FromAxioms.NumberTheory.SqrtTwo
import FromAxioms.Topology.Metric

universe u

open NumberTheory SetTheory Topology
namespace Analysis


/-- The closed interval, as a set of located reals. -/
def realLIcc (p q : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun x => realLLe (realLOf p) x ∧ realLLe x (realLOf q)) RealL.{u}

theorem mem_realLIcc_iff (p q x : ZFSet.{u}) :
    x ∈ realLIcc p q ↔ x ∈ RealL.{u} ∧ realLLe (realLOf p) x ∧ realLLe x (realLOf q) :=
  mem_sep_iff _ _ _

/-- The closed interval with REAL endpoints.

`realLIcc` above applies `realLOf` to both endpoints, so the NOTION takes
rationals and every consumer of it --- `UniformlyContinuousOn`, `bernOp`, the
whole Weierstrass chain --- inherits that restriction. It is not a constructive
obstruction: `p < q` gives the apartness, and `realLInv_mem` takes exactly a
positivity hypothesis. The restriction comes from the interval rather than from
the analysis.

The compatibility is `rfl`, so this is a widening rather than a fork:
`realLIcc p q` IS `realLIccR (realLOf p) (realLOf q)` by definition, so every
existing consumer is a consumer of this at the embedded endpoints and nothing
has to move.
-/
def realLIccR (p q : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun x => realLLe p x ∧ realLLe x q) RealL.{u}

/-- Its membership law, the same separation `realLIcc` uses. -/
theorem mem_realLIccR_iff (p q x : ZFSet.{u}) :
    x ∈ realLIccR p q ↔ x ∈ RealL.{u} ∧ realLLe p x ∧ realLLe x q :=
  mem_sep_iff _ _ _

/-- The rational-ended interval IS this one at `realLOf` of its endpoints. -/
theorem realLIcc_eq_realLIccR (p q : ZFSet.{u}) :
    realLIcc p q = realLIccR (realLOf p) (realLOf q) := rfl

/-- A member is bracketed by the endpoints, the clause a consumer opens
with. -/
theorem realLIccR_bounds {p q x : ZFSet.{u}} (hx : x ∈ realLIccR p q) :
    x ∈ RealL.{u} ∧ realLLe p x ∧ realLLe x q :=
  (mem_realLIccR_iff p q x).mp hx

#print axioms realLIccR
#print axioms mem_realLIccR_iff
#print axioms realLIcc_eq_realLIccR
#print axioms realLIccR_bounds

/-- AT TWO NON-RATIONAL ENDPOINTS THE CLOSED INTERVAL IS THE WHOLE LINE.

`realLIcc` is total in its endpoints and every consumer of it quantifies over
all of them, so what it means off the rationals is what those quantifiers are
actually saying. `realLOf empty` is `opair empty empty` by `ratCut_empty` and
`ratUpper_empty`, and `realLLe a b` is `¬ realLLt b a` with `realLLt x y` an
existential over `snd x ∩ fst y` --- so both order clauses hold VACUOUSLY of
every real and the separation keeps everything.

WHY IT IS WORTH A NAME. `CutAt p q r` quantifies over `realLIcc p r`, and its
docstring contrasts it with `UniversalCutAt` as *the form that can be
BRACKETED*, the interval being what bounds it. At junk endpoints there is no
bound: `CutAtRat` instantiated here is the cut of the WHOLE line at a rational,
which `forall_cut_of_cutAtRat` (Caratheodory.lean) states outright. The
restriction that is really doing work is the rationality of `q`, not the
interval. -/
theorem realLIcc_empty_empty : realLIcc.{u} empty.{u} empty.{u} = RealL.{u} := by
  refine ext _ _ (fun z => ⟨fun hz => ((mem_realLIcc_iff _ _ z).mp hz).left,
    fun hz => (mem_realLIcc_iff _ _ z).mpr ⟨hz, ?_, ?_⟩⟩)
  · rintro ⟨t, -, ht⟩
    rw [show fst (realLOf.{u} empty.{u}) = ratCut empty.{u} from by
      rw [realLOf, fst_opair], ratCut_empty] at ht
    exact not_mem_empty _ ht
  · rintro ⟨t, ht, -⟩
    rw [show snd (realLOf.{u} empty.{u})
        = sep (fun p => ratLt empty.{u} p) NumberTheory.Rat.{u} from by
      rw [realLOf, snd_opair], NumberTheory.ratUpper_empty] at ht
    exact not_mem_empty _ ht

#print axioms realLIcc_empty_empty

/-- Reflection keeps a point in the unit interval. -/
theorem refl_mem_Icc01 {z : ZFSet.{u}}
    (hz : z ∈ realLIcc ratZero.{u} ratOne.{u}) :
    realLAdd realLOne.{u} (realLNeg z) ∈ realLIcc ratZero.{u} ratOne.{u} := by
  obtain ⟨hzR, hz0, hz1⟩ := (mem_realLIcc_iff ratZero.{u} ratOne.{u} z).mp hz
  have hs := realLAdd_mem realLOne_mem (realLNeg_mem hzR)
  refine (mem_realLIcc_iff ratZero.{u} ratOne.{u} _).mpr ⟨hs, ?_, ?_⟩
  · exact (realLLe_sub_nonneg hzR realLOne_mem).mp hz1
  · have hnz0 : realLLe (realLNeg z) realLZero.{u} := realLNeg_le_zero hzR hz0
    have := realLLe_add realLOne_mem realLOne_mem (realLNeg_mem hzR)
      realLZero_mem (realLLe_refl realLOne_mem) hnz0
    rwa [realLAdd_zero realLOne_mem] at this

/-- Every located real sits in SOME rational interval: its cuts are inhabited,
which is a field of `IsLocated` and not a search. -/
theorem mem_some_realLIcc {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    ∃ p r : ZFSet.{u}, p ∈ NumberTheory.Rat.{u} ∧ r ∈ NumberTheory.Rat.{u} ∧ x ∈ realLIcc p r := by
  obtain ⟨L, U, hxe, hloc⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨p, hp⟩ := hloc.lower_inhabited
  obtain ⟨r, hr⟩ := hloc.upper_inhabited
  have hpQ := hloc.lower_subset _ hp
  have hrQ := hloc.upper_subset _ hr
  refine ⟨p, r, hpQ, hrQ, (mem_realLIcc_iff p r x).mpr ⟨hx, ?_, ?_⟩⟩
  · exact realLLe_of_lt (realLOf_mem hpQ) hx
      ((realLOf_lt_iff_mem_lower hx hpQ).mpr (by rw [hxe, fst_opair]; exact hp))
  · exact realLLe_of_lt hx (realLOf_mem hrQ)
      ((lt_realLOf_iff_mem_upper hx hrQ).mpr (by rw [hxe, snd_opair]; exact hr))

#print axioms mem_some_realLIcc

theorem left_mem_realLIcc {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (h : ratLe p q) : realLOf p ∈ realLIcc p q :=
  (mem_realLIcc_iff p q _).mpr ⟨realLOf_mem hp, realLLe_refl (realLOf_mem hp),
    fun hlt => absurd ((realLOf_lt_realLOf hq hp).mp hlt).left
      (fun hle => ((realLOf_lt_realLOf hq hp).mp hlt).right
        (ratLe_antisymm hq hp hle h))⟩

theorem right_mem_realLIcc {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (h : ratLe p q) : realLOf q ∈ realLIcc p q :=
  (mem_realLIcc_iff p q _).mpr ⟨realLOf_mem hq,
    fun hlt => absurd ((realLOf_lt_realLOf hq hp).mp hlt).left
      (fun hle => ((realLOf_lt_realLOf hq hp).mp hlt).right
        (ratLe_antisymm hq hp hle h)),
    realLLe_refl (realLOf_mem hq)⟩

/-- A function on `[p,q]` together with a modulus of uniform continuity: at
scale `n`, inputs within `1/(modulus n + 1)` have values within `1/(n+1)`. -/
structure UniformOn (F : ZFSet.{u} → ZFSet.{u}) (p q : ZFSet.{u}) : Type (u + 1) where
  maps : ∀ x, x ∈ realLIcc p q → F x ∈ RealL.{u}
  modulus : Nat → Nat
  spec : ∀ (n : Nat) (x y : ZFSet.{u}), x ∈ realLIcc p q → y ∈ realLIcc p q →
    Close x y (invScale.{u} (modulus n)) →
    Close (F x) (F y) (invScale.{u} n)

/-! ## The embedding is additive

`realLOf` was built to place a rational among the located reals and nothing
more was asked of it: no file needed `realLOf (a + b) = realLOf a + realLOf b`
until a grid did, which is the same pattern the degenerate set-algebra cases
turned up.

The forward direction carries the work. A rational `p` below `a + b` has to be
split as `q + r` with `q < a` and `r < b`, and the split is explicit: put the
whole slack on one side, `q = a + (p - a - b)` and `r = b`, then push `r` down
by density. -/

theorem realLOf_neg {a : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u}) :
    realLNeg (realLOf a) = realLOf (ratNeg a) := by
  refine toCut_injective (realLNeg_mem (realLOf_mem ha))
    (realLOf_mem (ratNeg_mem_Rat ha)) ?_
  rw [toCut, toCut, realLNeg, fst_opair, realLOf, snd_opair, realLOf, fst_opair]
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨hpQ, r, hr, hlt⟩ := (mem_negLower_iff _ p).mp hp
    obtain ⟨hrQ, har⟩ := (mem_sep_iff _ r _).mp hr
    refine (mem_ratCut_iff _ p).mpr ⟨hpQ, ratLt_trans hpQ (ratNeg_mem_Rat hrQ)
      (ratNeg_mem_Rat ha) hlt ((ratNeg_lt_neg_iff hrQ ha).mpr har)⟩
  · obtain ⟨hpQ, hlt⟩ := (mem_ratCut_iff _ p).mp hp
    -- a rational strictly between `a` and `-p`
    have hanp : ratLt a (ratNeg p) := by
      have := (ratNeg_lt_neg_iff (ratNeg_mem_Rat ha) hpQ).mpr hlt
      rwa [ratNeg_ratNeg ha] at this
    obtain ⟨t, htQ, hat, htp⟩ := rat_dense ha (ratNeg_mem_Rat hpQ) hanp
    refine (mem_negLower_iff _ p).mpr ⟨hpQ, t, (mem_sep_iff _ t _).mpr ⟨htQ, hat⟩, ?_⟩
    have := (ratNeg_lt_neg_iff (ratNeg_mem_Rat hpQ) htQ).mpr htp
    rwa [ratNeg_ratNeg hpQ] at this

/-- A real between a rational and that rational plus `ε` is within `ε`
of it: both halves of the bracket, from the two order bounds. -/
theorem close_realLOf_of_between {x r ε : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hr : r ∈ NumberTheory.Rat.{u}) (hε : ε ∈ NumberTheory.Rat.{u}) (hε0 : ratLt ratZero.{u} ε)
    (hrx : realLLe (realLOf r) x)
    (hxle : realLLe x (realLOf (ratAdd r ε))) :
    Close x (realLOf r) (realLOf ε) := by
  refine ⟨?_, ?_⟩
  · have hstep := realLLe_add_right (realLOf_mem hr) hx
      (realLNeg_mem (realLOf_mem hr)) hrx
    rw [realLAdd_neg (realLOf_mem hr)] at hstep
    refine realLLe_trans (realLNeg_mem (realLOf_mem hε)) realLZero_mem
      (realLAdd_mem hx (realLNeg_mem (realLOf_mem hr))) ?_ hstep
    rw [realLOf_neg hε]
    refine (realLOf_le_realLOf (ratNeg_mem_Rat hε) ratZero_mem_Rat).mpr ?_
    have hflip := (ratNeg_lt_neg_iff hε ratZero_mem_Rat).mpr hε0
    rw [ratNeg_zero] at hflip
    exact hflip.left
  · have hstep := realLLe_add_right hx
      (realLOf_mem (ratAdd_mem_Rat hr hε))
      (realLNeg_mem (realLOf_mem hr)) hxle
    rwa [realLOf_add hr hε, realLAdd_comm (realLOf_mem hr) (realLOf_mem hε),
      realLAdd_assoc (realLOf_mem hε) (realLOf_mem hr)
        (realLNeg_mem (realLOf_mem hr)),
      realLAdd_neg (realLOf_mem hr), realLAdd_zero (realLOf_mem hε)]
      at hstep

#print axioms close_realLOf_of_between


/-- Closeness of two rationals, read into the reals. Both halves are rational
inequalities, which the two lemmas above supply. -/
theorem close_realLOf {a b w : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u}) (hb : b ∈ NumberTheory.Rat.{u})
    (hw : w ∈ NumberTheory.Rat.{u}) (h1 : ratLe (ratNeg w) (ratAdd a (ratNeg b)))
    (h2 : ratLe (ratAdd a (ratNeg b)) w) :
    Close (realLOf a) (realLOf b) (realLOf w) := by
  have hab := ratAdd_mem_Rat ha (ratNeg_mem_Rat hb)
  have hkey : realLAdd (realLOf a) (realLNeg (realLOf b))
      = realLOf (ratAdd a (ratNeg b)) := by
    rw [realLOf_neg hb, realLOf_add ha (ratNeg_mem_Rat hb)]
  refine ⟨?_, ?_⟩
  · rw [hkey, realLOf_neg hw]
    exact (realLOf_le_realLOf (ratNeg_mem_Rat hw) hab).mpr h1
  · rw [hkey]
    exact (realLOf_le_realLOf hab hw).mpr h2

/-! ## The grid

Rationals `p, p + δ, p + 2δ, …`, clamped at `q`. Clamping is what keeps every
point inside `[p, q]` without a separate argument about the last one: the walk
overshoots, `ratMin` cuts it back, and the step from the last interior point to
`q` is no wider than `δ` because clamping only shortens.

The ladder itself is the one `Located.lean` already uses -- `ratOf (intOfNat i) b`
with a fixed denominator -- so `ratOf_intOfNat_succ` gives the step. -/

/-- `p + i/(m+1)`, before clamping. -/
def ladder (p : ZFSet.{u}) (m i : Nat) : ZFSet.{u} :=
  ratAdd p (ratOf (intOfNat.{u} i) (intOf (succ (ofNat.{u} m)) empty.{u}))

/-- The `i`-th grid point of mesh `1/(m+1)` on `[p, q]`, clamped at `q`. -/
def gridPoint (p q : ZFSet.{u}) (m i : Nat) : ZFSet.{u} := ratMin (ladder p m i) q

theorem ladder_mem {p : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (m i : Nat) :
    ladder p m i ∈ NumberTheory.Rat.{u} :=
  ratAdd_mem_Rat hp (ratOf_mem_Rat (intOfNat_mem_Int i)
    (intOf_succ_pos (ofNat_mem_omega m)))

theorem ladder_zero {p : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (m : Nat) : ladder p m 0 = p := by
  rw [ladder, intOfNat_zero, ratOf_intZero (intOf_succ_pos (ofNat_mem_omega m)),
    ratAdd_zero hp]

theorem gridPoint_mem_Rat {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (m i : Nat) : gridPoint p q m i ∈ NumberTheory.Rat.{u} :=
  ratMin_mem_Rat (ladder_mem hp m i) hq

theorem gridPoint_eq_ladder {p q : ZFSet.{u}} {m i : Nat}
    (h : ratLt (ladder p m i) q) : gridPoint p q m i = ladder p m i := by
  rw [gridPoint, ratMin, condP_pos h]

theorem gridPoint_eq_right {p q : ZFSet.{u}} {m i : Nat}
    (h : ¬ ratLt (ladder p m i) q) : gridPoint p q m i = q := by
  rw [gridPoint, ratMin, condP_neg h]

/-- The walk starts at `p`. -/
theorem gridPoint_zero {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u})
    (h : ratLt p q) (m : Nat) : gridPoint p q m 0 = p := by
  rw [gridPoint_eq_ladder (by rw [ladder_zero hp m]; exact h), ladder_zero hp m]

/-- Each step advances by the mesh, before clamping. -/
theorem ladder_succ {p : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (m i : Nat) :
    ladder p m (i + 1) = ratAdd (ladder p m i) (invWidth (ofNat.{u} m)) := by
  rw [ladder, ladder, ratOf_intOfNat_succ (intOf_succ_pos (ofNat_mem_omega m)) i,
    ratAdd_assoc hp (ratOf_mem_Rat (intOfNat_mem_Int i)
      (intOf_succ_pos (ofNat_mem_omega m)))
      (invWidth_mem_Rat (ofNat_mem_omega m)), invWidth]

/-- The ladder only rises, so every rung is above `p`. -/
theorem ladder_ge {p : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (m : Nat) :
    ∀ i, ratLe p (ladder p m i)
  | 0 => by rw [ladder_zero hp m]; exact ratLe_refl hp
  | i + 1 => by
    refine ratLe_trans hp (ladder_mem hp m i) (ladder_mem hp m (i + 1))
      (ladder_ge hp m i) ?_
    rw [ladder_succ hp m i]
    have := (ratAdd_le_add_left_iff (ladder_mem hp m i) ratZero_mem_Rat
      (invWidth_mem_Rat (ofNat_mem_omega m))).mpr
      (invWidth_pos (ofNat_mem_omega m)).left
    rwa [ratAdd_zero (ladder_mem hp m i)] at this

/-- Every grid point lies in the interval. -/
theorem gridPoint_mem_Icc {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (hpq : ratLe p q) (m i : Nat) : realLOf (gridPoint p q m i) ∈ realLIcc p q := by
  have hg := gridPoint_mem_Rat hp hq m i
  refine (mem_realLIcc_iff p q _).mpr ⟨realLOf_mem hg, ?_, ?_⟩
  · exact (realLOf_le_realLOf hp hg).mpr
      (le_ratMin (ladder_mem hp m i) hq (ladder_ge hp m i) hpq)
  · exact (realLOf_le_realLOf hg hq).mpr (ratMin_le_right (ladder_mem hp m i) hq)

/-- Rearrangement, at the rational level: `b ≤ a + w` is `-w ≤ a - b`. -/
private theorem neg_le_sub_of_le_add {a b w : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u})
    (hb : b ∈ NumberTheory.Rat.{u}) (hw : w ∈ NumberTheory.Rat.{u}) (h : ratLe b (ratAdd a w)) :
    ratLe (ratNeg w) (ratAdd a (ratNeg b)) := by
  have hnw := ratNeg_mem_Rat hw
  have hnb := ratNeg_mem_Rat hb
  have h1 := (ratAdd_le_add_right_iff (ratAdd_mem_Rat hnb hnw) hb
    (ratAdd_mem_Rat ha hw)).mpr h
  have hL : ratAdd b (ratAdd (ratNeg b) (ratNeg w)) = ratNeg w := by
    rw [← ratAdd_assoc hb hnb hnw, ratAdd_neg hb,
      ratAdd_comm ratZero_mem_Rat hnw, ratAdd_zero hnw]
  have hR : ratAdd (ratAdd a w) (ratAdd (ratNeg b) (ratNeg w))
      = ratAdd a (ratNeg b) := by
    rw [ratAdd_assoc ha hw (ratAdd_mem_Rat hnb hnw),
      ratAdd_comm hnb hnw, ← ratAdd_assoc hw hnw hnb, ratAdd_neg hw,
      ratAdd_comm ratZero_mem_Rat hnb, ratAdd_zero hnb]
  rwa [hL, hR] at h1

theorem ladder_le_succ {p : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (m i : Nat) :
    ratLe (ladder p m i) (ladder p m (i + 1)) := by
  rw [ladder_succ hp m i]
  have := (ratAdd_le_add_left_iff (ladder_mem hp m i) ratZero_mem_Rat
    (invWidth_mem_Rat (ofNat_mem_omega m))).mpr (invWidth_pos (ofNat_mem_omega m)).left
  rwa [ratAdd_zero (ladder_mem hp m i)] at this

/-- The walk is non-decreasing. -/
theorem gridPoint_le_succ {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (m i : Nat) : ratLe (gridPoint p q m i) (gridPoint p q m (i + 1)) := by
  have hli := ladder_mem hp m i
  have hli' := ladder_mem hp m (i + 1)
  rcases ratLt_or_not hli' hq with hb | hb
  · have ha : ratLt (ladder p m i) q :=
      ratLt_of_le_of_lt hli hli' hq (ladder_le_succ hp m i) hb
    rw [gridPoint_eq_ladder ha, gridPoint_eq_ladder hb]
    exact ladder_le_succ hp m i
  · rw [gridPoint_eq_right hb]
    exact ratMin_le_right hli hq

/-- A step of the walk is no wider than the mesh. The clamping is what makes
this true at the end of the interval as well as inside it: overshooting is cut
back to `q`, and cutting back only shortens. -/
theorem gridPoint_step_le {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (m i : Nat) : ratLe (gridPoint p q m (i + 1))
      (ratAdd (gridPoint p q m i) (invWidth (ofNat.{u} m))) := by
  have hli := ladder_mem hp m i
  have hli' := ladder_mem hp m (i + 1)
  have hδ := invWidth_mem_Rat (ofNat_mem_omega.{u} m)
  rcases ratLt_or_not hli' hq with hb | hb
  · have ha : ratLt (ladder p m i) q :=
      ratLt_of_le_of_lt hli hli' hq (ladder_le_succ hp m i) hb
    rw [gridPoint_eq_ladder ha, gridPoint_eq_ladder hb, ladder_succ hp m i]
    exact ratLe_refl (ratAdd_mem_Rat hli hδ)
  · have hqle : ratLe q (ratAdd (ladder p m i) (invWidth (ofNat.{u} m))) := by
      rw [← ladder_succ hp m i]
      exact ratLe_of_not_lt hq hli' hb
    rw [gridPoint_eq_right hb]
    rcases ratLt_or_not hli hq with ha | ha
    · rw [gridPoint_eq_ladder ha]
      exact hqle
    · rw [gridPoint_eq_right ha]
      have := (ratAdd_le_add_left_iff hq ratZero_mem_Rat hδ).mpr
        (invWidth_pos (ofNat_mem_omega.{u} m)).left
      rwa [ratAdd_zero hq] at this

/-- Consecutive grid points are within the mesh, as reals. -/
theorem gridPoint_close {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (m i : Nat) :
    Close (realLOf (gridPoint p q m i)) (realLOf (gridPoint p q m (i + 1)))
      (invScale.{u} m) := by
  have hx := gridPoint_mem_Rat hp hq m i
  have hy := gridPoint_mem_Rat hp hq m (i + 1)
  have hδ := invWidth_mem_Rat (ofNat_mem_omega.{u} m)
  refine close_realLOf hx hy hδ ?_ ?_
  · exact neg_le_sub_of_le_add hx hy hδ (gridPoint_step_le hp hq m i)
  · -- `x ≤ y`, so `x - y ≤ 0 ≤ δ`
    have h1 : ratLe (ratAdd (gridPoint p q m i)
        (ratNeg (gridPoint p q m (i + 1)))) ratZero.{u} := by
      have := (ratAdd_le_add_right_iff (ratNeg_mem_Rat hy) hx hy).mpr
        (gridPoint_le_succ hp hq m i)
      rwa [ratAdd_neg hy] at this
    exact ratLe_trans (ratAdd_mem_Rat hx (ratNeg_mem_Rat hy)) ratZero_mem_Rat hδ h1
      (invWidth_pos (ofNat_mem_omega.{u} m)).left

/-! ## The step

The whole of the constructive content, and it is one application of
cotransitivity. Walking a grid whose mesh is below the modulus, each new point
either keeps the value at most zero -- so the walk continues -- or is itself
within `ε` of zero, because it cannot have risen more than `ε` above a value
that was at most zero.

No trisection and no bisection: those choose a side, and choosing is what this
development pays for elsewhere. A walk decides nothing, and the conclusion is a
disjunction rather than a construction. -/


theorem invScale_pos (n : Nat) : realLLt realLZero.{u} (invScale.{u} n) :=
  (realLOf_lt_realLOf ratZero_mem_Rat (invWidth_mem_Rat (ofNat_mem_omega n))).mpr
    (invWidth_pos (ofNat_mem_omega n))


/-- The step. At a point close enough to one where the value is at most
zero, the value is either again at most zero, or within `ε` of it. -/
theorem ivt_step {F : ZFSet.{u} → ZFSet.{u}} {p q : ZFSet.{u}} (hF : UniformOn F p q)
    (n : Nat) {x y : ZFSet.{u}} (hx : x ∈ realLIcc p q) (hy : y ∈ realLIcc p q)
    (hclose : Close x y (invScale.{u} (hF.modulus n)))
    (hxneg : realLLe (F x) realLZero.{u}) :
    WithinOf (F y) (invScale.{u} n) ∨ realLLe (F y) realLZero.{u} := by
  have hFx := hF.maps x hx
  have hFy := hF.maps y hy
  have hε := invScale_mem.{u} n
  have hεpos := invScale_pos.{u} n
  have hnε := realLNeg_mem hε
  have hlow : realLLt (realLNeg (invScale.{u} n)) realLZero.{u} := by
    have := realLNeg_lt_neg realLZero_mem hε hεpos
    rwa [realLNeg_zero] at this
  rcases realLLt_cotrans hnε realLZero_mem hFy hlow with hgt | hlt
  · refine Or.inl ⟨realLLe_of_lt hnε hFy hgt, ?_⟩
    -- the value cannot have risen more than `ε` above one that was at most zero
    have hspec := hF.spec n x y hx hy hclose
    have hle : realLLe (F y) (realLAdd (F x) (invScale.{u} n)) :=
      le_add_of_neg_le_sub' hFx hFy hε hspec.left
    refine realLLe_trans hFy (realLAdd_mem hFx hε) hε hle ?_
    have := realLLe_add_right hFx realLZero_mem hε hxneg
    rwa [realLAdd_comm realLZero_mem hε, realLAdd_zero hε] at this
  · exact Or.inr (realLLe_of_lt hFy realLZero_mem hlt)

/-! ## The walk, and the theorem

The induction is the whole proof: at every grid point, either a witness has
already been found or the value is still at most zero. The grid reaches `q`
because the ladder is Archimedean, and at `q` the two hypotheses close on each
other -- the value is at most zero and at least zero, so it is within anything.
-/

/-- The ladder passes `q`. -/
theorem exists_ladder_ge {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (m : Nat) : ∃ N, ¬ ratLt (ladder p m N) q := by
  have hden := intOf_succ_pos (ofNat_mem_omega.{u} m)
  obtain ⟨N, hN⟩ := rat_archimedean (ratAdd_mem_Rat hq (ratNeg_mem_Rat hp)) hden
  have hX := ratOf_mem_Rat (intOfNat_mem_Int N) hden
  have h1 := (ratAdd_lt_add_right_iff hp
    (ratAdd_mem_Rat hq (ratNeg_mem_Rat hp)) hX).mpr hN
  rw [ratAdd_assoc hq (ratNeg_mem_Rat hp) hp, ratAdd_comm (ratNeg_mem_Rat hp) hp,
    ratAdd_neg hp, ratAdd_zero hq] at h1
  have h2 : ratLt q (ladder p m N) := by
    show ratLt q (ratAdd p (ratOf (intOfNat.{u} N) (intOf (succ (ofNat.{u} m)) empty.{u})))
    rwa [ratAdd_comm hp hX]
  exact ⟨N, fun hlt => ratLt_irrefl (ratLt_trans hq (ladder_mem hp m N) hq h2 hlt)⟩

/-- The approximate intermediate value theorem. A uniformly continuous
function that is at most zero at `p` and at least zero at `q` comes within
`1/(n+1)` of zero somewhere in `[p, q]`.

Nothing is chosen. The walk's disjunction is eliminated inside a proof, and the
conclusion is an existential -- which is exactly why the exact theorem, whose
conclusion would be a point, does not follow. -/
theorem exists_approx_root {F : ZFSet.{u} → ZFSet.{u}} {p q : ZFSet.{u}}
    (hF : UniformOn F p q) (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hstart : realLLe (F (realLOf p)) realLZero.{u})
    (hend : realLLe realLZero.{u} (F (realLOf q))) (n : Nat) :
    ∃ x, x ∈ realLIcc p q ∧ WithinOf (F x) (invScale.{u} n) := by
  have hpqle : ratLe p q := hpq.left
  have hm := hF.modulus n
  -- the walk, by induction on the grid index
  have walk : ∀ i, (∃ x, x ∈ realLIcc p q ∧ WithinOf (F x) (invScale.{u} n)) ∨
      realLLe (F (realLOf (gridPoint p q (hF.modulus n) i))) realLZero.{u} := by
    intro i
    induction i with
    | zero =>
      refine Or.inr ?_
      rw [gridPoint_zero hp hpq (hF.modulus n)]
      exact hstart
    | succ k ih =>
      rcases ih with hfound | hle
      · exact Or.inl hfound
      · rcases ivt_step hF n (gridPoint_mem_Icc hp hq hpqle (hF.modulus n) k)
          (gridPoint_mem_Icc hp hq hpqle (hF.modulus n) (k + 1))
          (gridPoint_close hp hq (hF.modulus n) k) hle with hwin | hnext
        · exact Or.inl ⟨_, gridPoint_mem_Icc hp hq hpqle (hF.modulus n) (k + 1), hwin⟩
        · exact Or.inr hnext
  -- the grid reaches `q`, where the two hypotheses close on each other
  obtain ⟨N, hN⟩ := exists_ladder_ge hp hq (hF.modulus n)
  rcases walk N with hfound | hle
  · exact hfound
  rw [gridPoint_eq_right hN] at hle
  refine ⟨realLOf q, right_mem_realLIcc hp hq hpqle, ?_, ?_⟩
  · exact realLLe_trans (realLNeg_mem (invScale_mem.{u} n)) realLZero_mem
      (hF.maps _ (right_mem_realLIcc hp hq hpqle))
      (realLNeg_le_zero (invScale_mem.{u} n)
        (realLLe_of_lt realLZero_mem (invScale_mem.{u} n) (invScale_pos.{u} n)))
      hend
  · exact realLLe_trans (hF.maps _ (right_mem_realLIcc hp hq hpqle)) realLZero_mem
      (invScale_mem.{u} n) hle
      (realLLe_of_lt realLZero_mem (invScale_mem.{u} n) (invScale_pos.{u} n))

/-! ## The exact theorem, and what it costs

The approximate theorem is the honest one, and the exact statement -- a point
where the value is zero -- is not a strengthening of the proof but a different
hypothesis. What the walk never needed was to know the sign at a point; a
bisection needs exactly that, and cannot get it.

What is proved here is the first half of the reduction: with a readout, the
value at a rational is decided, so the approximate theorem's witnesses can be
taken at grid points chosen by the bit rather than found by a walk. -/

/-- Locatedness of `F c` against zero, as data. -/
structure SignReadout (F : ZFSet.{u} → ZFSet.{u}) : Type (u + 1) where
  bit : ZFSet.{u} → ZFSet.{u}
  mem_two : ∀ c, c ∈ NumberTheory.Rat.{u} → bit c ∈ ofNat.{u} 2
  nonpos : ∀ c, c ∈ NumberTheory.Rat.{u} → bit c = empty.{u} → realLLe (F (realLOf c)) realLZero.{u}
  nonneg : ∀ c, c ∈ NumberTheory.Rat.{u} → bit c = ofNat.{u} 1 →
    realLLe realLZero.{u} (F (realLOf c))

/-- With a readout, the sign at each rational is decided. -/
theorem sign_decided {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F) {c : ZFSet.{u}}
    (hc : c ∈ NumberTheory.Rat.{u}) :
    realLLe (F (realLOf c)) realLZero.{u} ∨ realLLe realLZero.{u} (F (realLOf c)) := by
  rcases mem_two_cases (σ.mem_two c hc) with he | he
  · exact Or.inl (σ.nonpos c hc he)
  · exact Or.inr (σ.nonneg c hc he)

/-! ## The bisection

With a readout the next interval is a term, which is the whole difference from
the walk. `condP` on the bit chooses the half, and the invariants -- endpoints
rational, ordered, and bracketing the sign change -- come out by induction.

The widths halve, so the limit is named by `isLocated_nest`; that assembly is
the remaining work. -/

/-- The `n`-th bisection interval, as an ordered pair. -/
def bisectPair {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F) (p q : ZFSet.{u}) :
    Nat → ZFSet.{u}
  | 0 => opair p q
  | n + 1 =>
    condP (σ.bit (ratMid (fst (bisectPair σ p q n)) (snd (bisectPair σ p q n)))
        = ofNat.{u} 1)
      (opair (fst (bisectPair σ p q n))
        (ratMid (fst (bisectPair σ p q n)) (snd (bisectPair σ p q n))))
      (opair (ratMid (fst (bisectPair σ p q n)) (snd (bisectPair σ p q n)))
        (snd (bisectPair σ p q n)))

/-- The invariants. Rational endpoints, strictly ordered, with the value at
most zero on the left and at least zero on the right. -/
theorem bisectPair_spec {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F)
    {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hstart : realLLe (F (realLOf p)) realLZero.{u})
    (hend : realLLe realLZero.{u} (F (realLOf q))) :
    ∀ n, fst (bisectPair σ p q n) ∈ NumberTheory.Rat.{u} ∧ snd (bisectPair σ p q n) ∈ NumberTheory.Rat.{u} ∧
      ratLt (fst (bisectPair σ p q n)) (snd (bisectPair σ p q n)) ∧
      realLLe (F (realLOf (fst (bisectPair σ p q n)))) realLZero.{u} ∧
      realLLe realLZero.{u} (F (realLOf (snd (bisectPair σ p q n))))
  | 0 => by
    rw [bisectPair, fst_opair, snd_opair]
    exact ⟨hp, hq, hpq, hstart, hend⟩
  | n + 1 => by
    obtain ⟨ha, hb, hab, hleft, hright⟩ := bisectPair_spec σ hp hq hpq hstart hend n
    have hmid := ratMid_mem_Rat ha hb
    rcases mem_two_cases (σ.mem_two _ hmid) with he | he
    · rw [bisectPair, condP_neg (fun h1 => empty_ne_one (he.symm.trans h1)),
        fst_opair, snd_opair]
      exact ⟨hmid, hb, ratMid_lt ha hb hab, σ.nonpos _ hmid he, hright⟩
    · rw [bisectPair, condP_pos he, fst_opair, snd_opair]
      exact ⟨ha, hmid, lt_ratMid ha hb hab, hleft, σ.nonneg _ hmid he⟩

/-! ### The same recursion, driven by a bare bit

`bisectPair` above takes a `SignReadout`, but it READS only `sigma.bit` --- the
sign clauses appear nowhere in the recursion, only in `bisectPair_spec`'s
invariant. So the tower generalises for free, and rung 16 needs it to: the
interval-preconnectedness bisection branches on a COVER bit, not a sign bit,
and rebuilding a second nested-interval tower for it would be the same
machinery twice.

Added ALONGSIDE rather than in place of the sign version. `bisectPair` and its
19 consumers are untouched, and `bisectPair_eq_bisectPairB` says the two agree,
so anything proved of the generic form transfers to the sign tower without
re-deriving it. -/

/-- The bisection recursion with the decision supplied as a bare bit. -/
def bisectPairB (bit : ZFSet.{u} → ZFSet.{u}) (p q : ZFSet.{u}) :
    Nat → ZFSet.{u}
  | 0 => opair p q
  | n + 1 =>
    condP (bit (ratMid (fst (bisectPairB bit p q n)) (snd (bisectPairB bit p q n)))
        = ofNat.{u} 1)
      (opair (fst (bisectPairB bit p q n))
        (ratMid (fst (bisectPairB bit p q n)) (snd (bisectPairB bit p q n))))
      (opair (ratMid (fst (bisectPairB bit p q n)) (snd (bisectPairB bit p q n)))
        (snd (bisectPairB bit p q n)))

/-- The invariant that needs no payload: rational endpoints, strictly
ordered. This is `bisectPair_spec` with its two sign clauses removed, and
removing them is exactly what makes it reusable --- the halving structure never
depended on what the bit MEANT. -/
theorem bisectPairB_spec (bit : ZFSet.{u} → ZFSet.{u})
    {p q : ZFSet.{u}}
    (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hbit : ∀ c, c ∈ NumberTheory.Rat.{u} → ratLe p c → ratLe c q → bit c ∈ ofNat.{u} 2) :
    ∀ n, fst (bisectPairB bit p q n) ∈ NumberTheory.Rat.{u} ∧
      snd (bisectPairB bit p q n) ∈ NumberTheory.Rat.{u} ∧
      ratLt (fst (bisectPairB bit p q n)) (snd (bisectPairB bit p q n)) ∧
      ratLe p (fst (bisectPairB bit p q n)) ∧
      ratLe (snd (bisectPairB bit p q n)) q
  | 0 => by
    rw [bisectPairB, fst_opair, snd_opair]
    exact ⟨hp, hq, hpq, ratLe_refl hp, ratLe_refl hq⟩
  | n + 1 => by
    obtain ⟨ha, hb, hab, hpa, hbq⟩ := bisectPairB_spec bit hp hq hpq hbit n
    have hmid := ratMid_mem_Rat ha hb
    -- the midpoint is inside `[p, q]`, so the RESTRICTED bit hypothesis fires:
    -- `p ≤ a < mid < b ≤ q`.
    have hpmid : ratLe p (ratMid (fst (bisectPairB bit p q n)) (snd (bisectPairB bit p q n))) :=
      ratLe_trans hp ha hmid hpa (lt_ratMid ha hb hab).left
    have hmidq : ratLe (ratMid (fst (bisectPairB bit p q n)) (snd (bisectPairB bit p q n))) q :=
      ratLe_trans hmid hb hq (ratMid_lt ha hb hab).left hbq
    -- `mem_two_cases`, NOT `by_cases`: the bit lands in `ofNat 2`, so the split
    -- is the two-element case analysis this tree already has. `by_cases` here
    -- compiles and quietly pulls in `Classical.choice`.
    rcases mem_two_cases (hbit _ hmid hpmid hmidq) with he | he
    · rw [bisectPairB, condP_neg (fun h1 => empty_ne_one (he.symm.trans h1)),
        fst_opair, snd_opair]
      exact ⟨hmid, hb, ratMid_lt ha hb hab, hpmid, hbq⟩
    · rw [bisectPairB, condP_pos he, fst_opair, snd_opair]
      exact ⟨ha, hmid, lt_ratMid ha hb hab, hpa, hmidq⟩

/-! ### The widths halve

`Ternary.lean` ran this argument for thirds, and `SqrtTwo.lean` already has
`pow2` with `n + 1 ≤ 2ⁿ` -- found by the build refusing a second definition of
it, which is the kind of duplication a name clash catches for free. What is new
here is the halving identity, stated as a multiplication so that no division
appears. -/


/-- `2/1` is two; `ratTwo` is defined above this file's imports of
`Rational.lean`, which is where `ratNat_one_one` sits. -/
theorem ratNat_two_one : ratNat.{u} 2 1 = ratTwo.{u} := by
  have h1 : intOfNat.{u} 1 = intOne.{u} := rfl
  rw [ratNat, ratTwo, ratOne, intOfNat_succ, h1,
    ← ratOf_add_same_denom intOne_mem_Int intOne_mem_Int one_mem_intPositive]

private theorem ratNat_two_mul (k : Nat) :
    ratNat.{u} (2 * k) 1 = ratMul (ratNat.{u} 2 1) (ratNat.{u} k 1) := by
  rw [ratNat_mul (show 0 < 1 by omega) (show 0 < 1 by omega)]

/-- The width at stage `n`, as a rational. -/
def bisectWidth {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F) (p q : ZFSet.{u})
    (n : Nat) : ZFSet.{u} :=
  ratAdd (snd (bisectPair σ p q n)) (ratNeg (fst (bisectPair σ p q n)))

/-- The widths halve, stated as `wₙ · 2ⁿ = w₀` so that nothing is divided. -/
theorem bisectWidth_scaled {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F)
    {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hstart : realLLe (F (realLOf p)) realLZero.{u})
    (hend : realLLe realLZero.{u} (F (realLOf q))) :
    ∀ n, ratMul (bisectWidth σ p q n) (ratNat.{u} (pow2 n) 1)
      = ratAdd q (ratNeg p)
  | 0 => by
    have : bisectWidth σ p q 0 = ratAdd q (ratNeg p) := by
      rw [bisectWidth, bisectPair, fst_opair, snd_opair]
    rw [this, pow2, ratNat_one_one, ratMul_one (ratAdd_mem_Rat hq (ratNeg_mem_Rat hp))]
  | n + 1 => by
    obtain ⟨ha, hb, hab, -, -⟩ := bisectPair_spec σ hp hq hpq hstart hend n
    have hmid := ratMid_mem_Rat ha hb
    have hw := bisectWidth_scaled σ hp hq hpq hstart hend n
    have hhalf : ratMul (bisectWidth σ p q (n + 1)) ratTwo.{u}
        = bisectWidth σ p q n := by
      rcases mem_two_cases (σ.mem_two _ hmid) with he | he
      · rw [bisectWidth, bisectPair,
          condP_neg (fun h1 => empty_ne_one (he.symm.trans h1)), fst_opair, snd_opair,
          bisectWidth, ratMid_sub_right ha hb]
      · rw [bisectWidth, bisectPair, condP_pos he, fst_opair, snd_opair,
          bisectWidth, ratMid_sub_left ha hb]
    have hwn := ratAdd_mem_Rat hb (ratNeg_mem_Rat ha)
    have hwn1 : bisectWidth σ p q (n + 1) ∈ NumberTheory.Rat.{u} := by
      obtain ⟨ha', hb', -, -, -⟩ := bisectPair_spec σ hp hq hpq hstart hend (n + 1)
      exact ratAdd_mem_Rat hb' (ratNeg_mem_Rat ha')
    rw [pow2, ratNat_two_mul (pow2 n), ratNat_two_one,
      ← ratMul_assoc hwn1 ratTwo_mem_Rat
        (ratNat_mem_Rat (show 0 < 1 by omega)), hhalf]
    exact hw

/-- The CARRIED half of the invariant: the endpoints keep their bits.

`Analysis.bisectPairB_spec` is the half that needs no payload. This is the other
half, and it is the one every application supplies for itself: start with the
low end reading `empty` and the high end reading `1`, and the recursion
preserves it --- because `Analysis.bisectPairB` sends the midpoint to the HIGH slot
exactly when its bit is `1`.

For `Analysis.SignReadout` this is `bisectPair_spec`'s two sign clauses read
through `Analysis.sign_decided`. For a cover readout it says the low endpoint
stays in one open and the high endpoint in the other, so the limit's own bit
produces a point in BOTH. -/
theorem bisectPairB_bits (bit : ZFSet.{u} → ZFSet.{u}) {p q : ZFSet.{u}}
    (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hbit : ∀ c, c ∈ NumberTheory.Rat.{u} → ratLe p c → ratLe c q → bit c ∈ ofNat.{u} 2)
    (h0 : bit p = empty.{u}) (h1 : bit q = ofNat.{u} 1) :
    ∀ n, bit (fst (bisectPairB bit p q n)) = empty.{u} ∧
      bit (snd (bisectPairB bit p q n)) = ofNat.{u} 1
  | 0 => by
    rw [bisectPairB, fst_opair, snd_opair]
    exact ⟨h0, h1⟩
  | n + 1 => by
    obtain ⟨ha, hb, hab, hpa, hbq⟩ := bisectPairB_spec bit hp hq hpq hbit n
    obtain ⟨hlo, hhi⟩ := bisectPairB_bits bit hp hq hpq hbit h0 h1 n
    have hmid := ratMid_mem_Rat ha hb
    have hpmid : ratLe p (ratMid (fst (bisectPairB bit p q n)) (snd (bisectPairB bit p q n))) :=
      ratLe_trans hp ha hmid hpa (lt_ratMid ha hb hab).left
    have hmidq : ratLe (ratMid (fst (bisectPairB bit p q n)) (snd (bisectPairB bit p q n))) q :=
      ratLe_trans hmid hb hq (ratMid_lt ha hb hab).left hbq
    rcases mem_two_cases (hbit _ hmid hpmid hmidq) with he | he
    · -- the midpoint reads `empty`, so it becomes the new LOW end
      rw [bisectPairB, condP_neg (fun hone => empty_ne_one (he.symm.trans hone)),
        fst_opair, snd_opair]
      exact ⟨he, hhi⟩
    · -- it reads `1`, so it becomes the new HIGH end
      rw [bisectPairB, condP_pos he, fst_opair, snd_opair]
      exact ⟨hlo, he⟩

/-- The width of the generic tower's `n`-th interval. -/
def bisectWidthB (bit : ZFSet.{u} → ZFSet.{u}) (p q : ZFSet.{u}) (n : Nat) :
    ZFSet.{u} :=
  ratAdd (snd (bisectPairB bit p q n)) (ratNeg (fst (bisectPairB bit p q n)))

/-- The widths halve for ANY two-valued bit, stated as `wₙ · 2ⁿ = w₀` so
that nothing is divided --- the same device `Analysis.bisectWidth_scaled` uses, and
the same proof with the sign hypotheses dropped. They were never used: halving
is a fact about `ratMid`, not about what the bit decides. -/
theorem bisectWidthB_scaled (bit : ZFSet.{u} → ZFSet.{u})
    {p q : ZFSet.{u}}
    (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hbit : ∀ c, c ∈ NumberTheory.Rat.{u} → ratLe p c → ratLe c q → bit c ∈ ofNat.{u} 2) :
    ∀ n, ratMul (bisectWidthB bit p q n) (ratNat.{u} (pow2 n) 1)
      = ratAdd q (ratNeg p)
  | 0 => by
    have h0 : bisectWidthB bit p q 0 = ratAdd q (ratNeg p) := by
      rw [bisectWidthB, bisectPairB, fst_opair, snd_opair]
    rw [h0, pow2, ratNat_one_one, ratMul_one (ratAdd_mem_Rat hq (ratNeg_mem_Rat hp))]
  | n + 1 => by
    obtain ⟨ha, hb, hab, hpa, hbq⟩ := bisectPairB_spec bit hp hq hpq hbit n
    have hmid := ratMid_mem_Rat ha hb
    have hpmid : ratLe p (ratMid (fst (bisectPairB bit p q n)) (snd (bisectPairB bit p q n))) :=
      ratLe_trans hp ha hmid hpa (lt_ratMid ha hb hab).left
    have hmidq : ratLe (ratMid (fst (bisectPairB bit p q n)) (snd (bisectPairB bit p q n))) q :=
      ratLe_trans hmid hb hq (ratMid_lt ha hb hab).left hbq
    have hw := bisectWidthB_scaled bit hp hq hpq hbit n
    have hhalf : ratMul (bisectWidthB bit p q (n + 1)) ratTwo.{u}
        = bisectWidthB bit p q n := by
      rcases mem_two_cases (hbit _ hmid hpmid hmidq) with he | he
      · rw [bisectWidthB, bisectPairB,
          condP_neg (fun h1 => empty_ne_one (he.symm.trans h1)), fst_opair, snd_opair,
          bisectWidthB, ratMid_sub_right ha hb]
      · rw [bisectWidthB, bisectPairB, condP_pos he, fst_opair, snd_opair,
          bisectWidthB, ratMid_sub_left ha hb]
    have hwn1 : bisectWidthB bit p q (n + 1) ∈ NumberTheory.Rat.{u} := by
      obtain ⟨ha', hb', -, -, -⟩ := bisectPairB_spec bit hp hq hpq hbit (n + 1)
      exact ratAdd_mem_Rat hb' (ratNeg_mem_Rat ha')
    rw [pow2, ratNat_two_mul (pow2 n), ratNat_two_one,
      ← ratMul_assoc hwn1 ratTwo_mem_Rat
        (ratNat_mem_Rat (show 0 < 1 by omega)), hhalf]
    exact hw

/-- `k/k = 1`. -/
theorem ratNat_self {k : Nat} (hk : 0 < k) : ratNat.{u} k k = ratOne.{u} := by
  have hkP := intOfNat_mem_intPositive.{u} hk
  rw [ratNat, ratOne, ← ratOf_cancel hkP intOne_mem_Int one_mem_intPositive,
    intMul_one (intPositive_subset _ hkP)]

/-- `(n+1) · 1/(n+1) = 1`, which turns the scaled width into a bound. -/
theorem succ_mul_invWidth (n : Nat) :
    ratMul (ratNat.{u} (n + 1) 1) (invWidth (ofNat.{u} n)) = ratOne.{u} := by
  rw [invWidth_ofNat, ratNat_mul (show 0 < 1 by omega) (show 0 < n + 1 by omega)]
  have h1 : (n + 1) * 1 = n + 1 := by omega
  have h2 : 1 * (n + 1) = n + 1 := by omega
  rw [h1, h2]
  exact ratNat_self (by omega)


/-- `n + 1 ≤ 2ⁿ`, as rationals. -/
theorem ratNat_succ_le_pow2 (N : Nat) :
    ratLe (ratNat.{u} (N + 1) 1) (ratNat.{u} (pow2 N) 1) :=
  (ratNat_le_iff (by omega) (by omega)).mpr (by
    have := succ_le_pow2 N
    omega)

/-- The widths shrink below any positive rational. Two steps: the scaled
identity gives `wₙ · 2ⁿ = w₀`, and `n + 1 ≤ 2ⁿ` turns that into
`wₙ ≤ w₀ · 1/(n+1)`; then Archimedes picks the index. -/
theorem exists_bisectWidth_lt {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F)
    {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hstart : realLLe (F (realLOf p)) realLZero.{u})
    (hend : realLLe realLZero.{u} (F (realLOf q)))
    {ε : ZFSet.{u}} (hε : ε ∈ NumberTheory.Rat.{u}) (hε0 : ratLt ratZero.{u} ε) :
    ∃ N : Nat, ratLt (bisectWidth σ p q N) ε := by
  have hW := ratAdd_mem_Rat hq (ratNeg_mem_Rat hp)
  have hW0 : ratLt ratZero.{u} (ratAdd q (ratNeg p)) := ratSub_pos hp hq hpq
  have hWne : ratAdd q (ratNeg p) ≠ ratZero.{u} := ratNe_zero_of_pos hW0
  have hinvW := ratInv_mem_Rat hW hWne
  have hinvW0 := ratInv_pos hW hW0
  -- an index whose width `1/(N+1)` is below `ε / w₀`
  obtain ⟨M, hM, hlt⟩ := exists_invWidth_lt (ratMul_mem_Rat hε hinvW)
    (ratMul_pos hε hinvW hε0 hinvW0)
  obtain ⟨N, rfl⟩ := (mem_omega_iff M).mp hM
  refine ⟨N, ?_⟩
  have hwQ : bisectWidth σ p q N ∈ NumberTheory.Rat.{u} := by
    obtain ⟨ha, hb, -, -, -⟩ := bisectPair_spec σ hp hq hpq hstart hend N
    exact ratAdd_mem_Rat hb (ratNeg_mem_Rat ha)
  have hw0 : ratLt ratZero.{u} (bisectWidth σ p q N) := by
    obtain ⟨ha, hb, hab, -, -⟩ := bisectPair_spec σ hp hq hpq hstart hend N
    exact ratSub_pos ha hb hab
  have hδ := invWidth_mem_Rat (ofNat_mem_omega.{u} N)
  have hδ0 := invWidth_pos (ofNat_mem_omega.{u} N)
  -- `w₀ · 1/(N+1) < ε`
  have hbound : ratLt (ratMul (ratAdd q (ratNeg p)) (invWidth (ofNat.{u} N))) ε := by
    have h1 := ratMul_lt_mul_right hδ (ratMul_mem_Rat hε hinvW) hW hWne hW0.left hlt
    rw [ratMul_assoc hε hinvW hW, ratMul_comm hinvW hW,
      ratMul_inv hW hWne, ratMul_one hε, ratMul_comm hδ hW] at h1
    exact h1
  -- `wₙ ≤ w₀ · 1/(N+1)`, from `n + 1 ≤ 2ⁿ`
  refine ratLt_of_le_of_lt hwQ (ratMul_mem_Rat hW hδ) hε ?_ hbound
  have hscaled := bisectWidth_scaled σ hp hq hpq hstart hend N
  have hone : ratNat.{u} (N + 1) 1 ∈ NumberTheory.Rat.{u} :=
    ratNat_mem_Rat (show 0 < 1 by omega)
  have hpw : ratNat.{u} (pow2 N) 1 ∈ NumberTheory.Rat.{u} :=
    ratNat_mem_Rat (show 0 < 1 by omega)
  have hstep : ratLe (ratMul (bisectWidth σ p q N) (ratNat.{u} (N + 1) 1))
      (ratAdd q (ratNeg p)) := by
    rw [← hscaled]
    have := ratMul_le_mul_right hone hpw hwQ (ratNat_succ_le_pow2 N) hw0.left
    rwa [ratMul_comm hone hwQ, ratMul_comm hpw hwQ] at this
  -- multiply through by `1/(N+1)`
  have hmul := ratMul_le_mul_right (ratMul_mem_Rat hwQ hone) hW hδ hstep hδ0.left
  rwa [ratMul_assoc hwQ hone hδ, succ_mul_invWidth N, ratMul_one hwQ] at hmul

/-- The widths get small, for any two-valued bit.
`Analysis.exists_bisectWidth_lt` with the sign hypotheses dropped. The Archimedean
step is the same one the mesh selection uses elsewhere on this track: an index
whose width falls below `ε / w₀`, then `n + 1 ≤ 2ⁿ` to trade the halving for
it. Nothing divides a real --- `ratInv` is taken of the RATIONAL `w₀`, which is
positive by hypothesis. -/
theorem exists_bisectWidthB_lt (bit : ZFSet.{u} → ZFSet.{u})
    {p q : ZFSet.{u}}
    (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hbit : ∀ c, c ∈ NumberTheory.Rat.{u} → ratLe p c → ratLe c q → bit c ∈ ofNat.{u} 2)
    {ε : ZFSet.{u}} (hε : ε ∈ NumberTheory.Rat.{u}) (hε0 : ratLt ratZero.{u} ε) :
    ∃ N : Nat, ratLt (bisectWidthB bit p q N) ε := by
  have hW := ratAdd_mem_Rat hq (ratNeg_mem_Rat hp)
  have hW0 : ratLt ratZero.{u} (ratAdd q (ratNeg p)) := ratSub_pos hp hq hpq
  have hWne : ratAdd q (ratNeg p) ≠ ratZero.{u} := ratNe_zero_of_pos hW0
  have hinvW := ratInv_mem_Rat hW hWne
  have hinvW0 := ratInv_pos hW hW0
  obtain ⟨M, hM, hlt⟩ := exists_invWidth_lt (ratMul_mem_Rat hε hinvW)
    (ratMul_pos hε hinvW hε0 hinvW0)
  obtain ⟨N, rfl⟩ := (mem_omega_iff M).mp hM
  refine ⟨N, ?_⟩
  have hwQ : bisectWidthB bit p q N ∈ NumberTheory.Rat.{u} := by
    obtain ⟨ha, hb, -, -, -⟩ := bisectPairB_spec bit hp hq hpq hbit N
    exact ratAdd_mem_Rat hb (ratNeg_mem_Rat ha)
  have hw0 : ratLt ratZero.{u} (bisectWidthB bit p q N) := by
    obtain ⟨ha, hb, hab, -, -⟩ := bisectPairB_spec bit hp hq hpq hbit N
    exact ratSub_pos ha hb hab
  have hδ := invWidth_mem_Rat (ofNat_mem_omega.{u} N)
  have hδ0 := invWidth_pos (ofNat_mem_omega.{u} N)
  have hbound : ratLt (ratMul (ratAdd q (ratNeg p)) (invWidth (ofNat.{u} N))) ε := by
    have h1 := ratMul_lt_mul_right hδ (ratMul_mem_Rat hε hinvW) hW hWne hW0.left hlt
    rw [ratMul_assoc hε hinvW hW, ratMul_comm hinvW hW,
      ratMul_inv hW hWne, ratMul_one hε, ratMul_comm hδ hW] at h1
    exact h1
  refine ratLt_of_le_of_lt hwQ (ratMul_mem_Rat hW hδ) hε ?_ hbound
  have hscaled := bisectWidthB_scaled bit hp hq hpq hbit N
  have hone : ratNat.{u} (N + 1) 1 ∈ NumberTheory.Rat.{u} :=
    ratNat_mem_Rat (show 0 < 1 by omega)
  have hpw : ratNat.{u} (pow2 N) 1 ∈ NumberTheory.Rat.{u} :=
    ratNat_mem_Rat (show 0 < 1 by omega)
  have hstep : ratLe (ratMul (bisectWidthB bit p q N) (ratNat.{u} (N + 1) 1))
      (ratAdd q (ratNeg p)) := by
    rw [← hscaled]
    have hle := ratMul_le_mul_right hone hpw hwQ (ratNat_succ_le_pow2 N) hw0.left
    rwa [ratMul_comm hone hwQ, ratMul_comm hpw hwQ] at hle
  have hmul := ratMul_le_mul_right (ratMul_mem_Rat hwQ hone) hW hδ hstep hδ0.left
  rwa [ratMul_assoc hwQ hone hδ, succ_mul_invWidth N, ratMul_one hwQ] at hmul

/-- The generic tower's endpoints, named as `Analysis.bisectLo` and
`Analysis.bisectHi` name the sign tower's. -/
def bisectLoB (bit : ZFSet.{u} → ZFSet.{u}) (p q : ZFSet.{u}) (n : Nat) :
    ZFSet.{u} := fst (bisectPairB bit p q n)

def bisectHiB (bit : ZFSet.{u} → ZFSet.{u}) (p q : ZFSet.{u}) (n : Nat) :
    ZFSet.{u} := snd (bisectPairB bit p q n)

/-- One step nests, for any two-valued bit. `Analysis.bisect_step` with the
sign hypotheses dropped --- they were not used there either. -/
theorem bisectB_step (bit : ZFSet.{u} → ZFSet.{u})
    {p q : ZFSet.{u}}
    (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hbit : ∀ c, c ∈ NumberTheory.Rat.{u} → ratLe p c → ratLe c q → bit c ∈ ofNat.{u} 2) (n : Nat) :
    ratLe (bisectLoB bit p q n) (bisectLoB bit p q (n + 1)) ∧
      ratLe (bisectHiB bit p q (n + 1)) (bisectHiB bit p q n) := by
  obtain ⟨ha, hb, hab, hpa, hbq⟩ := bisectPairB_spec bit hp hq hpq hbit n
  have hmid := ratMid_mem_Rat ha hb
  have hpmid : ratLe p (ratMid (fst (bisectPairB bit p q n)) (snd (bisectPairB bit p q n))) :=
    ratLe_trans hp ha hmid hpa (lt_ratMid ha hb hab).left
  have hmidq : ratLe (ratMid (fst (bisectPairB bit p q n)) (snd (bisectPairB bit p q n))) q :=
    ratLe_trans hmid hb hq (ratMid_lt ha hb hab).left hbq
  rcases mem_two_cases (hbit _ hmid hpmid hmidq) with he | he
  · rw [bisectLoB, bisectLoB, bisectHiB, bisectHiB, bisectPairB,
      condP_neg (fun h1 => empty_ne_one (he.symm.trans h1)), fst_opair, snd_opair]
    exact ⟨(lt_ratMid ha hb hab).left, ratLe_refl hb⟩
  · rw [bisectLoB, bisectLoB, bisectHiB, bisectHiB, bisectPairB, condP_pos he,
      fst_opair, snd_opair]
    exact ⟨ratLe_refl ha, (ratMid_lt ha hb hab).left⟩

/-- The nesting is monotone, for any two-valued bit. -/
theorem bisectB_mono (bit : ZFSet.{u} → ZFSet.{u})
    {p q : ZFSet.{u}}
    (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hbit : ∀ c, c ∈ NumberTheory.Rat.{u} → ratLe p c → ratLe c q → bit c ∈ ofNat.{u} 2) :
    ∀ m n : Nat, m ≤ n →
      ratLe (bisectLoB bit p q m) (bisectLoB bit p q n) ∧
        ratLe (bisectHiB bit p q n) (bisectHiB bit p q m) := by
  intro m n hmn
  induction n with
  | zero =>
    have hm0 : m = 0 := Nat.le_zero.mp hmn
    subst hm0
    obtain ⟨ha, hb, -, -, -⟩ := bisectPairB_spec bit hp hq hpq hbit 0
    exact ⟨ratLe_refl ha, ratLe_refl hb⟩
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · obtain ⟨ihlo, ihhi⟩ := ih (Nat.le_of_lt_succ hlt)
      obtain ⟨hstep_lo, hstep_hi⟩ := bisectB_step bit hp hq hpq hbit k
      obtain ⟨ham, hbm, -, -, -⟩ := bisectPairB_spec bit hp hq hpq hbit m
      obtain ⟨hak, hbk, -, -, -⟩ := bisectPairB_spec bit hp hq hpq hbit k
      obtain ⟨hak', hbk', -, -, -⟩ := bisectPairB_spec bit hp hq hpq hbit (k + 1)
      exact ⟨ratLe_trans ham hak hak' ihlo hstep_lo,
        ratLe_trans hbk' hbk hbm hstep_hi ihhi⟩
    · have hmk : m = k + 1 := Nat.le_antisymm hmn hge
      subst hmk
      obtain ⟨ha, hb, -, -, -⟩ := bisectPairB_spec bit hp hq hpq hbit (k + 1)
      exact ⟨ratLe_refl ha, ratLe_refl hb⟩

/-! ### Nesting

The endpoints move inward, which is one case split each, and then the induction
over `Nat` is routine. The `ω`-indexed form `IsNested` wants is the same
statement transported through `ofNat`. -/

def bisectLo {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F) (p q : ZFSet.{u})
    (n : Nat) : ZFSet.{u} := fst (bisectPair σ p q n)

def bisectHi {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F) (p q : ZFSet.{u})
    (n : Nat) : ZFSet.{u} := snd (bisectPair σ p q n)

theorem bisect_step {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F)
    {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hstart : realLLe (F (realLOf p)) realLZero.{u})
    (hend : realLLe realLZero.{u} (F (realLOf q))) (n : Nat) :
    ratLe (bisectLo σ p q n) (bisectLo σ p q (n + 1)) ∧
      ratLe (bisectHi σ p q (n + 1)) (bisectHi σ p q n) := by
  obtain ⟨ha, hb, hab, -, -⟩ := bisectPair_spec σ hp hq hpq hstart hend n
  have hmid := ratMid_mem_Rat ha hb
  rcases mem_two_cases (σ.mem_two _ hmid) with he | he
  · rw [bisectLo, bisectLo, bisectHi, bisectHi, bisectPair,
      condP_neg (fun h1 => empty_ne_one (he.symm.trans h1)), fst_opair, snd_opair]
    exact ⟨(lt_ratMid ha hb hab).left, ratLe_refl hb⟩
  · rw [bisectLo, bisectLo, bisectHi, bisectHi, bisectPair, condP_pos he,
      fst_opair, snd_opair]
    exact ⟨ratLe_refl ha, (ratMid_lt ha hb hab).left⟩

theorem bisect_mono {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F)
    {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hstart : realLLe (F (realLOf p)) realLZero.{u})
    (hend : realLLe realLZero.{u} (F (realLOf q))) :
    ∀ m n : Nat, m ≤ n →
      ratLe (bisectLo σ p q m) (bisectLo σ p q n) ∧
        ratLe (bisectHi σ p q n) (bisectHi σ p q m) := by
  intro m n hmn
  induction n with
  | zero =>
    have : m = 0 := Nat.le_zero.mp hmn
    subst this
    obtain ⟨ha, hb, -, -, -⟩ := bisectPair_spec σ hp hq hpq hstart hend 0
    exact ⟨ratLe_refl ha, ratLe_refl hb⟩
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · obtain ⟨ihlo, ihhi⟩ := ih (Nat.le_of_lt_succ hlt)
      obtain ⟨hstep_lo, hstep_hi⟩ := bisect_step σ hp hq hpq hstart hend k
      obtain ⟨ham, hbm, -, -, -⟩ := bisectPair_spec σ hp hq hpq hstart hend m
      obtain ⟨hak, hbk, -, -, -⟩ := bisectPair_spec σ hp hq hpq hstart hend k
      obtain ⟨hak', hbk', -, -, -⟩ := bisectPair_spec σ hp hq hpq hstart hend (k + 1)
      exact ⟨ratLe_trans ham hak hak' ihlo hstep_lo,
        ratLe_trans hbk' hbk hbm hstep_hi ihhi⟩
    · have : m = k + 1 := Nat.le_antisymm hmn hge
      subst this
      obtain ⟨ha, hb, -, -, -⟩ := bisectPair_spec σ hp hq hpq hstart hend (k + 1)
      exact ⟨ratLe_refl ha, ratLe_refl hb⟩

/-- The two endpoint sequences, as `ω`-indexed functions. -/
def bisectLoSeq {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F) (p q : ZFSet.{u}) :
    ZFSet.{u} := natSeq NumberTheory.Rat.{u} (fun n => bisectLo σ p q n)

def bisectHiSeq {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F) (p q : ZFSet.{u}) :
    ZFSet.{u} := natSeq NumberTheory.Rat.{u} (fun n => bisectHi σ p q n)

/-- The bisection intervals are nested. Everything the structure asks for is
already proved; this is the transport from `Nat` indices to `ω` ones. -/
theorem isNested_bisect {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F)
    {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hstart : realLLe (F (realLOf p)) realLZero.{u})
    (hend : realLLe realLZero.{u} (F (realLOf q))) :
    IsNested (bisectLoSeq σ p q) (bisectHiSeq σ p q) := by
  have hlo : ∀ n : Nat, bisectLo σ p q n ∈ NumberTheory.Rat.{u} := fun n =>
    (bisectPair_spec σ hp hq hpq hstart hend n).left
  have hhi : ∀ n : Nat, bisectHi σ p q n ∈ NumberTheory.Rat.{u} := fun n =>
    (bisectPair_spec σ hp hq hpq hstart hend n).right.left
  refine ⟨natSeq_mem_ratSeqs hlo, natSeq_mem_ratSeqs hhi, ?_, ?_, ?_, ?_⟩
  · intro m hm n hn hmn
    obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
    obtain ⟨j, rfl⟩ := (mem_omega_iff n).mp hn
    rw [bisectLoSeq, app_natSeq hlo i, app_natSeq hlo j]
    exact (bisect_mono σ hp hq hpq hstart hend i j ((ofNat_subset_iff i j).mp hmn)).left
  · intro m hm n hn hmn
    obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
    obtain ⟨j, rfl⟩ := (mem_omega_iff n).mp hn
    rw [bisectHiSeq, app_natSeq hhi i, app_natSeq hhi j]
    exact (bisect_mono σ hp hq hpq hstart hend i j ((ofNat_subset_iff i j).mp hmn)).right
  · intro n hn
    obtain ⟨i, rfl⟩ := (mem_omega_iff n).mp hn
    rw [bisectLoSeq, bisectHiSeq, app_natSeq hlo i, app_natSeq hhi i]
    exact (bisectPair_spec σ hp hq hpq hstart hend i).right.right.left
  · intro ε hε hε0
    obtain ⟨N, hN⟩ := exists_bisectWidth_lt σ hp hq hpq hstart hend hε hε0
    refine ⟨ofNat.{u} N, ofNat_mem_omega N, ?_⟩
    rw [bisectLoSeq, bisectHiSeq, app_natSeq hlo N, app_natSeq hhi N]
    exact hN

/-- The generic tower's endpoint sequences, as `ω`-indexed functions. -/
def bisectLoSeqB (bit : ZFSet.{u} → ZFSet.{u}) (p q : ZFSet.{u}) : ZFSet.{u} :=
  natSeq NumberTheory.Rat.{u} (fun n => bisectLoB bit p q n)

def bisectHiSeqB (bit : ZFSet.{u} → ZFSet.{u}) (p q : ZFSet.{u}) : ZFSet.{u} :=
  natSeq NumberTheory.Rat.{u} (fun n => bisectHiB bit p q n)

/-- The generic bisection intervals are nested. `Analysis.isNested_bisect` with
the sign hypotheses dropped --- and with them go the last of the sign tower's
assumptions, so from here the nested-interval principle applies to a bisection
driven by ANY two-valued bit: a cover bit is not a sign bit, and nothing below
this line cares. -/
theorem isNested_bisectB (bit : ZFSet.{u} → ZFSet.{u})
    {p q : ZFSet.{u}}
    (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hbit : ∀ c, c ∈ NumberTheory.Rat.{u} → ratLe p c → ratLe c q → bit c ∈ ofNat.{u} 2) :
    IsNested (bisectLoSeqB bit p q) (bisectHiSeqB bit p q) := by
  have hlo : ∀ n : Nat, bisectLoB bit p q n ∈ NumberTheory.Rat.{u} := fun n =>
    (bisectPairB_spec bit hp hq hpq hbit n).left
  have hhi : ∀ n : Nat, bisectHiB bit p q n ∈ NumberTheory.Rat.{u} := fun n =>
    (bisectPairB_spec bit hp hq hpq hbit n).right.left
  refine ⟨natSeq_mem_ratSeqs hlo, natSeq_mem_ratSeqs hhi, ?_, ?_, ?_, ?_⟩
  · intro m hm n hn hmn
    obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
    obtain ⟨j, rfl⟩ := (mem_omega_iff n).mp hn
    rw [bisectLoSeqB, app_natSeq hlo i, app_natSeq hlo j]
    exact (bisectB_mono bit hp hq hpq hbit i j ((ofNat_subset_iff i j).mp hmn)).left
  · intro m hm n hn hmn
    obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
    obtain ⟨j, rfl⟩ := (mem_omega_iff n).mp hn
    rw [bisectHiSeqB, app_natSeq hhi i, app_natSeq hhi j]
    exact (bisectB_mono bit hp hq hpq hbit i j ((ofNat_subset_iff i j).mp hmn)).right
  · intro n hn
    obtain ⟨i, rfl⟩ := (mem_omega_iff n).mp hn
    rw [bisectLoSeqB, bisectHiSeqB, app_natSeq hlo i, app_natSeq hhi i]
    exact (bisectPairB_spec bit hp hq hpq hbit i).right.right.left
  · intro ε hε hε0
    obtain ⟨N, hN⟩ := exists_bisectWidthB_lt bit hp hq hpq hbit hε hε0
    refine ⟨ofNat.{u} N, ofNat_mem_omega N, ?_⟩
    rw [bisectLoSeqB, bisectHiSeqB, app_natSeq hlo N, app_natSeq hhi N]
    exact hN

/-! ### Within every scale is zero

The Archimedean step, in the form the root needs: a real bracketed by `±1/(n+1)`
for every `n` is zero. Both halves find a rational strictly between the value
and zero, and then a scale below it. -/

theorem eq_zero_of_within_all {z : ZFSet.{u}} (hz : z ∈ RealL.{u})
    (h : ∀ n : Nat, WithinOf z (invScale.{u} n)) : z = realLZero.{u} := by
  refine realLLe_antisymm hz realLZero_mem ?_ ?_
  · -- `z ≤ 0`: a positive rational below `z` would beat every scale
    intro hlt
    obtain ⟨t, htU, htL⟩ := hlt
    rw [realLZero, realLOf, snd_opair] at htU
    obtain ⟨htQ, ht0⟩ := (mem_sep_iff _ t _).mp htU
    obtain ⟨N, hN, hNt⟩ := exists_invWidth_lt htQ ht0
    obtain ⟨n, rfl⟩ := (mem_omega_iff N).mp hN
    refine (h n).right ?_
    exact realLLt_trans (invScale_mem.{u} n) (realLOf_mem htQ) hz
      ((realLOf_lt_realLOf (invWidth_mem_Rat hN) htQ).mpr hNt)
      ((realLOf_lt_iff_mem_lower hz htQ).mpr htL)
  · -- `0 ≤ z`: symmetric, through the negation
    intro hlt
    obtain ⟨t, htU, htL⟩ := hlt
    rw [realLZero, realLOf, fst_opair] at htL
    obtain ⟨htQ, ht0⟩ := (mem_ratCut_iff _ t).mp htL
    have hs0 : ratLt ratZero.{u} (ratNeg t) := by
      have := (ratNeg_lt_neg_iff ratZero_mem_Rat htQ).mpr ht0
      rwa [ratNeg_zero] at this
    obtain ⟨N, hN, hNt⟩ := exists_invWidth_lt (ratNeg_mem_Rat htQ) hs0
    obtain ⟨n, rfl⟩ := (mem_omega_iff N).mp hN
    refine (h n).left ?_
    -- `z < t < -1/(n+1)`
    have hzt : realLLt z (realLOf t) := (lt_realLOf_iff_mem_upper hz htQ).mpr htU
    have hneg : realLLt (realLOf t) (realLNeg (invScale.{u} n)) := by
      rw [invScale, realLOf_neg (invWidth_mem_Rat hN)]
      refine (realLOf_lt_realLOf htQ (ratNeg_mem_Rat (invWidth_mem_Rat hN))).mpr ?_
      have := (ratNeg_lt_neg_iff (ratNeg_mem_Rat htQ) (invWidth_mem_Rat hN)).mpr hNt
      rwa [ratNeg_ratNeg htQ] at this
    exact realLLt_trans hz (realLOf_mem htQ) (realLNeg_mem (invScale_mem.{u} n))
      hzt hneg

/-! ### The root

Everything is in place: the intervals nest, their widths shrink, the limit sits
inside every one of them, and uniform continuity carries the endpoint bounds to
the limit. -/

private theorem sub_nonneg {a b : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (h : realLLe b a) : realLLe realLZero.{u} (realLAdd a (realLNeg b)) := by
  have := realLLe_add_right hb ha (realLNeg_mem hb) h
  rwa [realLAdd_neg hb] at this

/-- FROM `a <= b + e`, SUBTRACT `b`. `[propext, Quot.sound]`.

`Analysis/RangeSup.lean` needs this to turn `exists_rat_pos_above`'s overshoot
into the shape `width_bound` consumes. `Metamath.close_upper_of_le_add` has the
same type and is out of the cone. -/
theorem sub_le_of_le_add {a b e : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (he : e ∈ RealL.{u}) (h : realLLe a (realLAdd b e)) :
    realLLe (realLAdd a (realLNeg b)) e := by
  have hnb := realLNeg_mem hb
  have h1 := realLLe_add_right ha (realLAdd_mem hb he) hnb h
  rwa [realLAdd_assoc hb he hnb, realLAdd_comm he hnb, ← realLAdd_assoc hb hnb he,
    realLAdd_neg hb, realLAdd_comm realLZero_mem he, realLAdd_zero he] at h1


/-- The real the bisection converges to. -/
def bisectRoot {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F) (p q : ZFSet.{u}) :
    ZFSet.{u} :=
  opair (nestLower (bisectLoSeq σ p q)) (nestUpper (bisectHiSeq σ p q))

theorem bisectRoot_mem {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F)
    {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hstart : realLLe (F (realLOf p)) realLZero.{u})
    (hend : realLLe realLZero.{u} (F (realLOf q))) :
    bisectRoot σ p q ∈ RealL.{u} :=
  (mem_RealL_iff _).mpr
    ⟨_, _, rfl, isLocated_nest (isNested_bisect σ hp hq hpq hstart hend)⟩

/-- The limit lies inside every stage, in the form the continuity estimate
wants. -/
theorem bisectRoot_between {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F)
    {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hstart : realLLe (F (realLOf p)) realLZero.{u})
    (hend : realLLe realLZero.{u} (F (realLOf q))) (n : Nat) :
    realLLe (realLOf (bisectLo σ p q n)) (bisectRoot σ p q) ∧
      realLLe (bisectRoot σ p q) (realLOf (bisectHi σ p q n)) := by
  have hnest := isNested_bisect σ hp hq hpq hstart hend
  have hlo : ∀ k : Nat, bisectLo σ p q k ∈ NumberTheory.Rat.{u} := fun k =>
    (bisectPair_spec σ hp hq hpq hstart hend k).left
  have hhi : ∀ k : Nat, bisectHi σ p q k ∈ NumberTheory.Rat.{u} := fun k =>
    (bisectPair_spec σ hp hq hpq hstart hend k).right.left
  constructor
  · have := nest_ge hnest (ofNat_mem_omega.{u} n)
    rwa [bisectLoSeq, app_natSeq hlo n] at this
  · have := nest_le hnest (ofNat_mem_omega.{u} n)
    rwa [bisectHiSeq, app_natSeq hhi n] at this

/-- The limit is within the stage's width of each endpoint. -/
theorem bisectRoot_close {F : ZFSet.{u} → ZFSet.{u}} (σ : SignReadout F)
    {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q)
    (hstart : realLLe (F (realLOf p)) realLZero.{u})
    (hend : realLLe realLZero.{u} (F (realLOf q))) (n : Nat) {w : ZFSet.{u}}
    (hw : w ∈ NumberTheory.Rat.{u}) (hle : ratLe (bisectWidth σ p q n) w) :
    Close (bisectRoot σ p q) (realLOf (bisectLo σ p q n)) (realLOf w) ∧
      Close (realLOf (bisectHi σ p q n)) (bisectRoot σ p q) (realLOf w) := by
  obtain ⟨ha0, hb0, hab0, -, -⟩ := bisectPair_spec σ hp hq hpq hstart hend n
  have ha : bisectLo σ p q n ∈ NumberTheory.Rat.{u} := ha0
  have hb : bisectHi σ p q n ∈ NumberTheory.Rat.{u} := hb0
  have hab : ratLt (bisectLo σ p q n) (bisectHi σ p q n) := hab0
  obtain ⟨hge, hlefin⟩ := bisectRoot_between σ hp hq hpq hstart hend n
  have hx := bisectRoot_mem σ hp hq hpq hstart hend
  have hwR := realLOf_mem hw
  have hw0 : realLLe realLZero.{u} (realLOf w) := by
    refine (realLOf_le_realLOf ratZero_mem_Rat hw).mpr ?_
    have hwidth : bisectWidth σ p q n = ratAdd (bisectHi σ p q n)
        (ratNeg (bisectLo σ p q n)) := rfl
    rw [hwidth] at hle
    exact ratLe_trans ratZero_mem_Rat (ratAdd_mem_Rat hb (ratNeg_mem_Rat ha)) hw
      (ratSub_pos ha hb hab).left hle
  have hnw : realLLe (realLNeg (realLOf w)) realLZero.{u} :=
    realLNeg_le_zero hwR hw0
  -- `b n = a n + width`, and the width is below `w`
  have hsplit : realLLe (realLOf (bisectHi σ p q n))
      (realLAdd (realLOf (bisectLo σ p q n)) (realLOf w)) := by
    rw [← realLOf_add ha hw]
    refine (realLOf_le_realLOf hb (ratAdd_mem_Rat ha hw)).mpr ?_
    have hwidth : bisectWidth σ p q n = ratAdd (bisectHi σ p q n)
        (ratNeg (bisectLo σ p q n)) := rfl
    rw [hwidth] at hle
    have h1 := (ratAdd_le_add_left_iff ha (ratAdd_mem_Rat hb (ratNeg_mem_Rat ha)) hw).mpr hle
    rwa [← ratAdd_assoc ha hb (ratNeg_mem_Rat ha), ratAdd_comm ha hb,
      ratAdd_assoc hb ha (ratNeg_mem_Rat ha), ratAdd_neg ha, ratAdd_zero hb] at h1
  refine ⟨⟨realLLe_trans (realLNeg_mem hwR) realLZero_mem
      (realLAdd_mem hx (realLNeg_mem (realLOf_mem ha))) hnw
      (sub_nonneg hx (realLOf_mem ha) hge), ?_⟩, ?_, ?_⟩
  · exact sub_le_of_le_add hx (realLOf_mem ha) hwR
      (realLLe_trans hx (realLOf_mem hb) (realLAdd_mem (realLOf_mem ha) hwR)
        hlefin hsplit)
  · exact realLLe_trans (realLNeg_mem hwR) realLZero_mem
      (realLAdd_mem (realLOf_mem hb) (realLNeg_mem hx)) hnw
      (sub_nonneg (realLOf_mem hb) hx hlefin)
  · refine sub_le_of_le_add (realLOf_mem hb) hx hwR ?_
    refine realLLe_trans (realLOf_mem hb) (realLAdd_mem (realLOf_mem ha) hwR)
      (realLAdd_mem hx hwR) hsplit ?_
    exact realLLe_add_right (realLOf_mem ha) hx hwR hge

/-- The exact intermediate value theorem, from a sign readout. The value at
the limit is within every scale of zero, hence zero.

Both are proved for the contrast with `exists_approx_root`. That one takes no
principle and concludes an approximation; this one takes a readout -- whose
disjunction alone is `LLPO` (`llpo_of_signDisjunction`) -- and concludes a
root. The theorem is the same theorem; what differs is what is assumed and what
is delivered, and both are visible in the statement. -/
theorem exists_root {F : ZFSet.{u} → ZFSet.{u}} {p q : ZFSet.{u}}
    (hF : UniformOn F p q) (σ : SignReadout F) (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (hpq : ratLt p q) (hstart : realLLe (F (realLOf p)) realLZero.{u})
    (hend : realLLe realLZero.{u} (F (realLOf q))) :
    ∃ x, x ∈ realLIcc p q ∧ F x = realLZero.{u} := by
  have hpqle : ratLe p q := hpq.left
  have hx := bisectRoot_mem σ hp hq hpq hstart hend
  -- the limit is in `[p, q]`, because stage `0` is `[p, q]`
  have hzero : bisectLo σ p q 0 = p ∧ bisectHi σ p q 0 = q := by
    rw [bisectLo, bisectHi, bisectPair, fst_opair, snd_opair]
    exact ⟨rfl, rfl⟩
  have hicc : bisectRoot σ p q ∈ realLIcc p q := by
    obtain ⟨hge, hle⟩ := bisectRoot_between σ hp hq hpq hstart hend 0
    rw [hzero.left] at hge
    rw [hzero.right] at hle
    exact (mem_realLIcc_iff p q _).mpr ⟨hx, hge, hle⟩
  refine ⟨_, hicc, eq_zero_of_within_all (hF.maps _ hicc) fun n => ?_⟩
  -- a stage narrower than the modulus at scale `n`
  have hδQ := invWidth_mem_Rat (ofNat_mem_omega.{u} (hF.modulus n))
  obtain ⟨N, hN⟩ := exists_bisectWidth_lt σ hp hq hpq hstart hend hδQ
    (invWidth_pos (ofNat_mem_omega.{u} (hF.modulus n)))
  obtain ⟨ha0, hb0, -, hleft, hright⟩ := bisectPair_spec σ hp hq hpq hstart hend N
  have ha : bisectLo σ p q N ∈ NumberTheory.Rat.{u} := ha0
  have hb : bisectHi σ p q N ∈ NumberTheory.Rat.{u} := hb0
  obtain ⟨hcloseA, hcloseB⟩ := bisectRoot_close σ hp hq hpq hstart hend N hδQ hN.left
  obtain ⟨hgeN, hleN⟩ := bisectRoot_between σ hp hq hpq hstart hend N
  have hAicc : realLOf (bisectLo σ p q N) ∈ realLIcc p q := by
    obtain ⟨hge0, -⟩ := bisectRoot_between σ hp hq hpq hstart hend 0
    refine (mem_realLIcc_iff p q _).mpr ⟨realLOf_mem ha, ?_, ?_⟩
    · refine (realLOf_le_realLOf hp ha).mpr ?_
      have := (bisect_mono σ hp hq hpq hstart hend 0 N (Nat.zero_le N)).left
      rw [hzero.left] at this
      exact this
    · exact realLLe_trans (realLOf_mem ha) hx (realLOf_mem hq) hgeN
        ((mem_realLIcc_iff p q _).mp hicc).right.right
  have hBicc : realLOf (bisectHi σ p q N) ∈ realLIcc p q := by
    refine (mem_realLIcc_iff p q _).mpr ⟨realLOf_mem hb, ?_, ?_⟩
    · exact realLLe_trans (realLOf_mem hp) hx (realLOf_mem hb)
        ((mem_realLIcc_iff p q _).mp hicc).right.left hleN
    · refine (realLOf_le_realLOf hb hq).mpr ?_
      have := (bisect_mono σ hp hq hpq hstart hend 0 N (Nat.zero_le N)).right
      rw [hzero.right] at this
      exact this
  -- continuity at both ends
  have hFA := hF.spec n _ _ hicc hAicc hcloseA
  have hFB := hF.spec n _ _ hBicc hicc hcloseB
  have hFx := hF.maps _ hicc
  have hFa := hF.maps _ hAicc
  have hFb := hF.maps _ hBicc
  have hε := invScale_mem.{u} n
  refine ⟨?_, ?_⟩
  · -- `F x ≥ F b - ε ≥ -ε`
    have h1 : realLLe (F (realLOf (bisectHi σ p q N)))
        (realLAdd (F (bisectRoot σ p q)) (invScale.{u} n)) :=
      le_add_of_sub_le hFb hFx hε hFB.right
    have h2 : realLLe realLZero.{u}
        (realLAdd (F (bisectRoot σ p q)) (invScale.{u} n)) :=
      realLLe_trans realLZero_mem hFb (realLAdd_mem hFx hε) hright h1
    exact realLLe_neg_of_le_add hFx hε h2
  · -- `F x ≤ F a + ε ≤ ε`
    have h1 : realLLe (F (bisectRoot σ p q))
        (realLAdd (F (realLOf (bisectLo σ p q N))) (invScale.{u} n)) :=
      le_add_of_sub_le hFx hFa hε hFA.right
    refine realLLe_trans hFx (realLAdd_mem hFa hε) hε h1 ?_
    have := realLLe_add_right hFa realLZero_mem hε hleft
    rwa [realLAdd_comm realLZero_mem hε, realLAdd_zero hε] at this


/-- `1/2 + 1/2 = 1`.

Hosted here rather than in either tower that needs it: `Stirling` and `FourierL`
both reach this file and neither reaches the other, so this is the lowest
point that can serve both. -/
theorem realLHalf_add_half :
    realLAdd (realLOf (ratNat.{u} 1 2)) (realLOf (ratNat.{u} 1 2)) = realLOne.{u} := by
  rw [← realLOf_add (ratNat_mem_Rat (by omega : 0 < 2))
      (ratNat_mem_Rat (by omega : 0 < 2)),
    ratNat_add_same_denom (by omega : 0 < 2),
    show realLOne.{u} = realLOf ratOne.{u} from rfl, ← ratNat_one_one]
  exact congrArg realLOf ((ratNat_eq_iff (by omega) (Nat.succ_pos 0)).mpr (by omega))

#print axioms realLHalf_add_half

/-! ## Bisecting without choosing: the interpolated weight

The walk above avoids the choice problem by never forming a sequence. A
BISECTION forms one, and that is a second cost on top of the sign disjunction
and quite separate from it: even granted `F c ≤ 0 ∨ 0 ≤ F c` at every point, the
sequence of left-or-right decisions is a countable family of choices, and
picking one disjunct at each step is `ACC`, not the disjunction.

MATTHEW FRANK SHOWS THAT SECOND COST IS AVOIDABLE, and the trick is small
enough to state in one line. *Interpolating Between Choices for the Approximate
Intermediate Value Theorem*, Logical Methods in Computer Science 16(3:5), 2020,
DOI 10.23638/LMCS-16(3:5)2020, arXiv:1701.02227. His third constraint, in his
words:

> the proof should not use countable choice. Under countable choice, it suffices
> in the proof below to let dn = 0 if f(cn) < e or dn = 1 if f(cn) > -e, but
> without countable choice, such a sequence is ill-defined.

His replacement for the bit is an ARITHMETIC FORMULA,
`dn = max(0, min(1/2 + f(cn)/e, 1))`, which is a REAL in `[0, 1]` rather than a
choice between two of them. Feeding it to `a' = c - d(b-a)/2`, `b' = b - d(b-a)/2`
halves the interval whatever `d` is, so the sequence is definable outright and
the whole `ACC` cost disappears.

WHAT IT DOES NOT BUY IS EXACTNESS, and the two collapse lemmas below show why
rather than argue it: the weight is `1` only once the value reaches `1/2` and
`0` only once it reaches `-1/2`, so between those it slides, and a sliding
weight leaves BOTH endpoints of the next interval with an undecided sign. That
is the trade: the interpolation is definable BECAUSE it is allowed to take
intermediate values, and an exact root needs it not to. Frank concludes the
approximate theorem and says the exact one is out of reach [BR87, chapter 6.2].

So this section is not a route to `ExactIVT01`. It is the measurement that
SEPARATES the two costs the exact statement was being charged for, and it
localises the residue in the window where the weight is strictly between `0` and
`1`. -/

/-- Frank's interpolation weight at a value already divided by the scale:
`max(0, min(1/2 + v, 1))`. A real in `[0, 1]`, not a bit, and definable with no
choice and no decision. -/
def interpWeight (v : ZFSet.{u}) : ZFSet.{u} :=
  realLMax realLZero.{u}
    (realLMin (realLAdd (realLOf (ratNat.{u} 1 2)) v) realLOne.{u})

theorem interpWeight_mem {v : ZFSet.{u}} (hv : v ∈ RealL.{u}) :
    interpWeight v ∈ RealL.{u} :=
  realLMax_mem realLZero_mem
    (realLMin_mem (realLAdd_mem (realLOf_mem (ratNat_mem_Rat (by omega : 0 < 2))) hv)
      realLOne_mem)

#print axioms interpWeight_mem

/-- `0 ≤ interpWeight v ≤ 1`, with no hypothesis on `v` at all. This alone is
what makes the interpolated step a bisection: the next interval is
`[c - d(b-a)/2, b - d(b-a)/2]`, whose width is `(b-a)/2` for EVERY `d`, and
which is nested inside `[a, b]` exactly when `d` lies in `[0, 1]`. -/
theorem interpWeight_bracket {v : ZFSet.{u}} :
    And (realLLe realLZero.{u} (interpWeight v))
      (realLLe (interpWeight v) realLOne.{u}) := by
  refine ⟨realLLe_max_left realLZero_mem, ?_⟩
  exact realLMax_le
    (fun h => realLLt_irrefl realLZero_mem
      (realLLt_trans realLZero_mem realLOne_mem realLZero_mem
        ((realLOf_lt_realLOf ratZero_mem_Rat ratOne_mem_Rat).mpr ratZero_lt_one) h))
    (realLMin_le_right realLOne_mem)

#print axioms interpWeight_bracket

/-- The weight collapses to `1` once the value reaches `1/2`. This is the
half of the interpolation that makes it a bisection in the ordinary sense: where
the sign is known with a margin, Frank's step IS the classical step, and `1`
sends the next interval to `[a, c]`. -/
theorem interpWeight_eq_one_of_half_le {v : ZFSet.{u}} (hv : v ∈ RealL.{u})
    (h : realLLe (realLOf (ratNat.{u} 1 2)) v) : interpWeight v = realLOne.{u} := by
  have hh : realLOf (ratNat.{u} 1 2) ∈ RealL.{u} :=
    realLOf_mem (ratNat_mem_Rat (by omega : 0 < 2))
  have hone : realLLe realLOne.{u} (realLAdd (realLOf (ratNat.{u} 1 2)) v) := by
    have hstep : realLLe (realLAdd (realLOf (ratNat.{u} 1 2)) (realLOf (ratNat.{u} 1 2)))
        (realLAdd v (realLOf (ratNat.{u} 1 2))) := realLLe_add_right hh hv hh h
    rw [realLHalf_add_half] at hstep
    rwa [realLAdd_comm hh hv]
  have hmin : realLMin (realLAdd (realLOf (ratNat.{u} 1 2)) v) realLOne.{u}
      = realLOne.{u} :=
    realLLe_antisymm (realLMin_mem (realLAdd_mem hh hv) realLOne_mem) realLOne_mem
      (realLMin_le_right realLOne_mem)
      (le_realLMin hone (realLLe_refl realLOne_mem))
  rw [interpWeight, hmin]
  exact realLLe_antisymm (realLMax_mem realLZero_mem realLOne_mem) realLOne_mem
    (realLMax_le
      (fun hlt => realLLt_irrefl realLZero_mem
        (realLLt_trans realLZero_mem realLOne_mem realLZero_mem
          ((realLOf_lt_realLOf ratZero_mem_Rat ratOne_mem_Rat).mpr ratZero_lt_one) hlt))
      (realLLe_refl realLOne_mem))
    (realLLe_max_right realLOne_mem)

#print axioms interpWeight_eq_one_of_half_le

/-- And to `0` once the value reaches `-1/2`, sending the next interval to
`[c, b]`. BETWEEN THE TWO THE WEIGHT SLIDES, and that gap is the whole residue:
the interpolation buys with it, and an exact root cannot afford it. -/
theorem interpWeight_eq_zero_of_le_neg_half {v : ZFSet.{u}} (hv : v ∈ RealL.{u})
    (h : realLLe v (realLNeg (realLOf (ratNat.{u} 1 2)))) :
    interpWeight v = realLZero.{u} := by
  have hh : realLOf (ratNat.{u} 1 2) ∈ RealL.{u} :=
    realLOf_mem (ratNat_mem_Rat (by omega : 0 < 2))
  have hzero : realLLe (realLAdd (realLOf (ratNat.{u} 1 2)) v) realLZero.{u} := by
    have hstep : realLLe (realLAdd v (realLOf (ratNat.{u} 1 2)))
        (realLAdd (realLNeg (realLOf (ratNat.{u} 1 2))) (realLOf (ratNat.{u} 1 2))) :=
      realLLe_add_right hv (realLNeg_mem hh) hh h
    rw [realLAdd_comm (realLNeg_mem hh) hh, realLAdd_neg hh] at hstep
    rwa [realLAdd_comm hh hv]
  have hmin : realLLe (realLMin (realLAdd (realLOf (ratNat.{u} 1 2)) v) realLOne.{u})
      realLZero.{u} :=
    realLLe_trans (realLMin_mem (realLAdd_mem hh hv) realLOne_mem)
      (realLAdd_mem hh hv) realLZero_mem
      (realLMin_le_left (realLAdd_mem hh hv)) hzero
  exact realLMax_eq_left_of_le realLZero_mem
    (realLMin_mem (realLAdd_mem hh hv) realLOne_mem) hmin

#print axioms interpWeight_eq_zero_of_le_neg_half


/-- Every rational of the interval sits in a cell of the walk: some
grid point is at most one mesh below it. Found by descending the walk
with the decidable order, not by a floor. -/
theorem exists_grid_le_on {p q r : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u})
    (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q) (hr : r ∈ NumberTheory.Rat.{u})
    (h0 : ratLe p r) (m : Nat) :
    ∀ t, ratLe r (gridPoint p q m t) →
      ∃ i, And (i ≤ t) (And (ratLe (gridPoint p q m i) r)
        (ratLe r (ratAdd (gridPoint p q m i) (invWidth (ofNat.{u} m)))))
  | 0, htop => by
    have hg0 : gridPoint p q m 0 = p := gridPoint_zero hp hpq m
    rw [hg0] at htop
    have hδ := invWidth_mem_Rat (ofNat_mem_omega.{u} m)
    have hδ0 := (invWidth_pos (ofNat_mem_omega.{u} m)).left
    refine ⟨0, Nat.le_refl 0, ?_, ?_⟩
    · rw [hg0]; exact h0
    · rw [hg0]
      refine ratLe_trans hr hp (ratAdd_mem_Rat hp hδ) htop ?_
      have := (ratAdd_le_add_left_iff hp ratZero_mem_Rat hδ).mpr hδ0
      rwa [ratAdd_zero hp] at this
  | t + 1, htop => by
    have hgt := gridPoint_mem_Rat hp hq m t
    rcases ratLt_or_not hgt hr with hlt | hnlt
    · refine ⟨t, Nat.le_succ t, hlt.left, ?_⟩
      exact ratLe_trans hr (gridPoint_mem_Rat hp hq m (t + 1))
        (ratAdd_mem_Rat hgt (invWidth_mem_Rat (ofNat_mem_omega.{u} m)))
        htop (gridPoint_step_le hp hq m t)
    · obtain ⟨i, hit, hlow, hup⟩ :=
        exists_grid_le_on hp hq hpq hr h0 m t (ratLe_of_not_lt hr hgt hnlt)
      exact ⟨i, Nat.le_succ_of_le hit, hlow, hup⟩

#print axioms Analysis.exists_grid_le_on

/-- Every grid point lies between the endpoints, as rationals.

`gridPoint_mem_Icc` says this already, but in `realLIcc` form; the bound
hypotheses of `isIntegral_withinOf` are stated at rationals. -/
theorem gridPoint_between {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (hpq : ratLe p q) (m i : Nat) :
    ratLe p (gridPoint p q m i) ∧ ratLe (gridPoint p q m i) q :=
  ⟨le_ratMin (ladder_mem hp m i) hq (ladder_ge hp m i) hpq,
   ratMin_le_right (ladder_mem hp m i) hq⟩

/-- `exists_gridPoint_near` with the stage supplied rather than obtained, so
the index comes back BOUNDED. The bound is what a net's size needs. -/
theorem exists_gridPoint_near_le {p q : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u})
    (hq : q ∈ NumberTheory.Rat.{u}) (hpq : ratLt p q) (m N : Nat)
    (hN : ¬ ratLt (ladder p m N) q)
    {x : ZFSet.{u}} (hx : x ∈ realLIcc p q) :
    ∃ i, i ≤ N ∧ realLLe (realLOf (gridPoint p q m i)) x ∧
      realLLt x (realLOf (ratAdd (ratAdd (gridPoint p q m i)
        (invWidth (ofNat.{u} m))) (invWidth (ofNat.{u} m)))) := by
  have hw := invWidth_mem_Rat (ofNat_mem_omega.{u} m)
  have hw0 := invWidth_pos (ofNat_mem_omega.{u} m)
  obtain ⟨hxR, hpx, hxq⟩ := (mem_realLIcc_iff p q x).mp hx
  obtain ⟨c, r, hcQ, hrQ, hcx, hxr, hrc⟩ := exists_rat_bracket hxR hw hw0
  have hcq : ratLt c q := (realLOf_lt_realLOf hcQ hq).mp
    (realLLt_of_lt_of_le (realLOf_mem hcQ) hxR (realLOf_mem hq) hcx hxq)
  have hc0Q : ratMax p c ∈ NumberTheory.Rat.{u} := ratMax_mem_Rat hp hcQ
  have hpc0 : ratLe p (ratMax p c) := left_le_ratMax hp hcQ
  have hc0q : ratLe (ratMax p c) q := ratMax_le hp hcQ hpq.left hcq.left
  have hcc0 : ratLe c (ratMax p c) := right_le_ratMax hp hcQ
  have hc0x : realLLe (realLOf (ratMax p c)) x := by
    rcases ratLt_or_not hp hcQ with h | h
    · rw [ratMax, condP_pos h]
      exact realLLe_of_lt (realLOf_mem hcQ) hxR hcx
    · rw [ratMax, condP_neg h]
      exact hpx
  have htop : ratLe (ratMax p c) (gridPoint p q m N) := by
    rw [gridPoint_eq_right hN]
    exact hc0q
  obtain ⟨i, hiN, hlo, hhi⟩ := exists_grid_le_on hp hq hpq hc0Q hpc0 m N htop
  have hgQ := gridPoint_mem_Rat hp hq m i
  refine ⟨i, hiN, ?_, ?_⟩
  · exact realLLe_trans (realLOf_mem hgQ) (realLOf_mem hc0Q) hxR
      ((realLOf_le_realLOf hgQ hc0Q).mpr hlo) hc0x
  · refine realLLt_of_lt_of_le hxR (realLOf_mem hrQ)
      (realLOf_mem (ratAdd_mem_Rat (ratAdd_mem_Rat hgQ hw) hw)) hxr ?_
    refine (realLOf_le_realLOf hrQ
      (ratAdd_mem_Rat (ratAdd_mem_Rat hgQ hw) hw)).mpr ?_
    refine ratLe_trans hrQ (ratAdd_mem_Rat hc0Q hw)
      (ratAdd_mem_Rat (ratAdd_mem_Rat hgQ hw) hw) ?_ ?_
    · exact ratLe_trans hrQ (ratAdd_mem_Rat hcQ hw) (ratAdd_mem_Rat hc0Q hw)
        hrc.left ((ratAdd_le_add_right_iff hw hcQ hc0Q).mpr hcc0)
    · exact (ratAdd_le_add_right_iff hw hc0Q (ratAdd_mem_Rat hgQ hw)).mpr hhi

/-! ## The `invScale` scaling cluster, at every universe

NOTHING IN ANY OF THEM IS ABOUT UNIVERSE `0` or about characters. They name
`realLMul`, `invScale` and `realLOf`, all universe-polymorphic, and cite only
rational arithmetic and `Located` lemmas that are too.

THE NARROWNESS BITES BECAUSE OF WHERE THEY SIT. `Analysis.Fubini` is upstream
of `Analysis.DirichletChar` and a sibling of `ComplexRoot`, so the integration
layer can cite none of it --- and an estimate wanting "scale a constant below a
modulus" is exactly what a Cauchy stage bound needs. Hosted here because `IVT`
is upstream of `Fubini` and carries `invScale_pos`, the one ingredient not
already lower.

The `{0}` copies are left standing: retiring them is a move, and a move is
master's. -/

/-- `invScale j` IS `1/(j+1)` as a rational, at every universe. `rfl`.

Worth a name because nothing about `invScale`'s spelling says which rational it
is, and a search for one form does not find the other. With it,
`exists_scaled_invNat_le` reads as "any constant can be scaled below any
modulus", which is what a product rule needs to place its three error terms. -/
theorem invScale_eq_ratNat_gen (j : Nat) :
    invScale.{u} j = realLOf (ratNat.{u} 1 (j + 1)) := rfl

/-- The modulus as a formula, at every universe.

    p * (n + 1) ≤ j  →  (p : RealL) * invScale j ≤ invScale n

`invScale j` is `1/(j+1)`, so the claim reads `p/(j+1) ≤ 1/(n+1)`, which is
`p * (n+1) ≤ j+1`; the hypothesis gives one more than that. -/
theorem realLOf_natMul_invScale_le_gen (p n : Nat) :
    ∀ j : Nat, p * (n + 1) ≤ j →
      realLLe (realLMul (realLOf (ratNat.{u} p 1)) (invScale.{u} j))
        (invScale.{u} n) := by
  intro j hj
  have h1 : (0:Nat) < 1 := by omega
  have hj1 : (0:Nat) < j + 1 := by omega
  have hn1 : (0:Nat) < n + 1 := by omega
  rw [invScale_eq_ratNat_gen, invScale_eq_ratNat_gen,
    ← realLOf_mul (ratNat_mem_Rat h1) (ratNat_mem_Rat hj1), ratNat_mul h1 hj1]
  refine (realLOf_le_realLOf (ratNat_mem_Rat (by omega : 0 < 1 * (j + 1)))
    (ratNat_mem_Rat hn1)).mpr ?_
  exact (ratNat_le_iff (by omega : 0 < 1 * (j + 1)) hn1).mpr
    (by simp only [Nat.mul_one, Nat.one_mul]; omega)

/-- A REAL constant under a natural bound gets the same modulus.

    C ≤ p,  p * (n + 1) ≤ j   ⟹   C * invScale j ≤ invScale n

The form every consumer has: the constant is a real and what is known about it is
a natural upper bound.

NO NON-NEGATIVITY. `DirichletChar`'s `{0}` copy binds `hC0 : 0 ≤ C` and its
proof never mentions it. The bound `C ≤ p` and the positivity of `invScale`
carry the argument, so a caller who knows `C ≤ p` but not `0 ≤ C` is refused
there for no reason. Dropped. -/
theorem realLMul_invScale_le_of_le_nat_gen {C : ZFSet.{u}} (hC : C ∈ RealL.{u})
    {p : Nat} (hCp : realLLe C (realLOf (ratNat.{u} p 1))) (n : Nat) :
    ∀ j : Nat, p * (n + 1) ≤ j →
      realLLe (realLMul C (invScale.{u} j)) (invScale.{u} n) := by
  intro j hj
  have h1 : (0:Nat) < 1 := by omega
  have hp : realLOf (ratNat.{u} p 1) ∈ RealL.{u} := realLOf_mem (ratNat_mem_Rat h1)
  refine realLLe_trans (realLMul_mem hC (invScale_mem j))
    (realLMul_mem hp (invScale_mem j)) (invScale_mem n)
    (realLMul_le_right hC hp (invScale_mem j) hCp
      (realLLe_of_lt realLZero_mem (invScale_mem j) (invScale_pos j)))
    (realLOf_natMul_invScale_le_gen p n j hj)

/-- And the index form, which is what an estimate consumes.

    (∀ j, b j ≤ invScale j)  ⟹  ∃ m, ∀ j ≥ m, C * b j ≤ invScale n

A modulus sequence known to shrink, a fixed constant, and a demand to get under a
named scale eventually. `exists_natBound_realL` supplies the natural bound, so the
widening costs nothing at all. -/
theorem exists_index_mul_le_invScale_gen {C : ZFSet.{u}} (hC : C ∈ RealL.{u})
    (hC0 : realLLe realLZero.{u} C) {b : Nat → ZFSet.{u}}
    (hb : ∀ j : Nat, b j ∈ RealL.{u})
    (hble : ∀ j : Nat, realLLe (b j) (invScale.{u} j)) (n : Nat) :
    ∃ m : Nat, ∀ j : Nat, m ≤ j →
      realLLe (realLMul C (b j)) (invScale.{u} n) := by
  obtain ⟨p, hp⟩ := exists_natBound_realL hC
  refine ⟨p * (n + 1), ?_⟩
  intro j hj
  refine realLLe_trans (realLMul_mem hC (hb j)) (realLMul_mem hC (invScale_mem j))
    (invScale_mem n)
    (realLMul_le_left (hb j) (invScale_mem j) hC (hble j) hC0) ?_
  exact realLMul_invScale_le_of_le_nat_gen hC
    (realLLe_of_lt hC (realLOf_mem (ratNat_mem_Rat (by omega : (0:Nat) < 1))) hp)
    n j hj

#print axioms Analysis.exists_gridPoint_near_le
#print axioms Analysis.invScale_eq_ratNat_gen
#print axioms Analysis.realLOf_natMul_invScale_le_gen
#print axioms Analysis.realLMul_invScale_le_of_le_nat_gen
#print axioms Analysis.exists_index_mul_le_invScale_gen

#print axioms neg_le_sub_of_le_add
#print axioms ratNat_two_mul
#print axioms sub_nonneg
#print axioms sub_le_of_le_add

#print axioms mem_realLIcc_iff
#print axioms ladder_mem
#print axioms ladder_zero
#print axioms gridPoint_mem_Rat
#print axioms gridPoint_eq_ladder
#print axioms gridPoint_eq_right
#print axioms ladder_ge
#print axioms ladder_le_succ
#print axioms gridPoint_le_succ
#print axioms invScale_pos
#print axioms ratNat_two_one
#print axioms ratNat_self
#print axioms ratNat_succ_le_pow2
#print axioms bisect_step
#print axioms bisectRoot_mem
#print axioms gridPoint_between
end Analysis

#print axioms Analysis.left_mem_realLIcc
#print axioms Analysis.right_mem_realLIcc
#print axioms Analysis.realLOf_neg
#print axioms Analysis.close_realLOf
#print axioms Analysis.gridPoint_zero
#print axioms Analysis.gridPoint_mem_Icc
#print axioms Analysis.gridPoint_step_le
#print axioms Analysis.gridPoint_close
#print axioms Analysis.ladder_succ
#print axioms Analysis.ivt_step
#print axioms Analysis.exists_ladder_ge
#print axioms Analysis.exists_approx_root
#print axioms Analysis.sign_decided
#print axioms Analysis.bisectPair_spec
#print axioms Analysis.bisectWidth_scaled
#print axioms Analysis.succ_mul_invWidth
#print axioms Analysis.exists_bisectWidth_lt
#print axioms Analysis.bisect_mono
#print axioms Analysis.isNested_bisect
#print axioms Analysis.eq_zero_of_within_all
#print axioms Analysis.bisectRoot_between
#print axioms Analysis.bisectRoot_close
#print axioms Analysis.exists_root
#print axioms Analysis.bisectPairB
#print axioms Analysis.bisectPairB_spec
#print axioms Analysis.bisectWidthB
#print axioms Analysis.bisectWidthB_scaled
#print axioms Analysis.bisectLoB
#print axioms Analysis.bisectHiB
#print axioms Analysis.bisectB_step
#print axioms Analysis.bisectB_mono
#print axioms Analysis.exists_bisectWidthB_lt
#print axioms Analysis.bisectLoSeqB
#print axioms Analysis.bisectHiSeqB
#print axioms Analysis.isNested_bisectB
#print axioms Analysis.bisectPairB_bits
#print axioms Analysis.refl_mem_Icc01

namespace ZFSet
export Analysis (sub_le_of_le_add realLIcc_empty_empty realLIccR mem_realLIccR_iff realLIcc_eq_realLIccR realLIccR_bounds interpWeight interpWeight_mem interpWeight_bracket interpWeight_eq_one_of_half_le interpWeight_eq_zero_of_le_neg_half SignReadout UniformOn bisectB_mono bisectB_step bisectHi bisectHiB bisectHiSeq bisectHiSeqB bisectLo bisectLoB bisectLoSeq bisectLoSeqB bisectPair bisectPairB bisectPairB_bits bisectPairB_spec bisectPair_spec bisectRoot bisectRoot_between bisectRoot_close bisectRoot_mem bisectWidth bisectWidthB bisectWidthB_scaled bisectWidth_scaled bisect_mono bisect_step close_realLOf close_realLOf_of_between eq_zero_of_within_all exists_approx_root exists_bisectWidthB_lt exists_bisectWidth_lt exists_gridPoint_near_le exists_grid_le_on exists_index_mul_le_invScale_gen exists_ladder_ge exists_root gridPoint gridPoint_between gridPoint_close gridPoint_eq_ladder gridPoint_eq_right gridPoint_le_succ gridPoint_mem_Icc gridPoint_mem_Rat gridPoint_step_le gridPoint_zero invScale_eq_ratNat_gen invScale_pos isNested_bisect isNested_bisectB ivt_step ladder ladder_ge ladder_le_succ ladder_mem ladder_succ ladder_zero left_mem_realLIcc mem_realLIcc_iff mem_some_realLIcc ratNat_self ratNat_succ_le_pow2 ratNat_two_one realLHalf_add_half realLIcc realLMul_invScale_le_of_le_nat_gen realLOf_natMul_invScale_le_gen realLOf_neg refl_mem_Icc01 right_mem_realLIcc sign_decided succ_mul_invWidth)
end ZFSet
