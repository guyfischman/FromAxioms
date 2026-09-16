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

`realLOf` was built to place a rational among the located reals and nothing more
was asked of it: no file needed `realLOf (a + b) = realLOf a + realLOf b` until
a grid did, which is the same pattern the degenerate set-algebra cases turned
up.

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

#print axioms neg_le_sub_of_le_add
#print axioms mem_realLIcc_iff
#print axioms ladder_mem
#print axioms ladder_zero
#print axioms gridPoint_mem_Rat
#print axioms gridPoint_eq_ladder
#print axioms gridPoint_eq_right
#print axioms ladder_ge
#print axioms ratNat_two_one
#print axioms ratNat_self
#print axioms ratNat_succ_le_pow2
end Analysis

#print axioms Analysis.left_mem_realLIcc
#print axioms Analysis.right_mem_realLIcc
#print axioms Analysis.realLOf_neg
#print axioms Analysis.close_realLOf
#print axioms Analysis.gridPoint_zero
#print axioms Analysis.gridPoint_mem_Icc
#print axioms Analysis.ladder_succ
#print axioms Analysis.succ_mul_invWidth
#print axioms Analysis.refl_mem_Icc01

namespace ZFSet
export Analysis (realLIcc_empty_empty realLIccR mem_realLIccR_iff realLIcc_eq_realLIccR realLIccR_bounds SignReadout UniformOn close_realLOf close_realLOf_of_between gridPoint gridPoint_eq_ladder gridPoint_eq_right gridPoint_mem_Icc gridPoint_mem_Rat gridPoint_zero ladder ladder_ge ladder_mem ladder_succ ladder_zero left_mem_realLIcc mem_realLIcc_iff mem_some_realLIcc ratNat_self ratNat_succ_le_pow2 ratNat_two_one realLIcc realLOf_neg refl_mem_Icc01 right_mem_realLIcc succ_mul_invWidth)
end ZFSet
