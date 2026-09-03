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
import FromAxioms.NumberTheory.Prime
import FromAxioms.NumberTheory.SqrtTwo
import FromAxioms.Topology.Metric
import FromAxioms.Topology.Topology

universe u

open NumberTheory SetTheory Topology
namespace Analysis


/-- The closed interval, as a set of located reals. -/
def realLIcc (p q : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun x => realLLe (realLOf p) x ∧ realLLe x (realLOf q)) RealL.{u}

theorem mem_realLIcc_iff (p q x : ZFSet.{u}) :
    x ∈ realLIcc p q ↔ x ∈ RealL.{u} ∧ realLLe (realLOf p) x ∧ realLLe x (realLOf q) :=
  mem_sep_iff _ _ _

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

end Analysis

#print axioms Analysis.left_mem_realLIcc
#print axioms Analysis.right_mem_realLIcc
#print axioms Analysis.realLOf_neg
#print axioms Analysis.succ_mul_invWidth
namespace ZFSet
export Analysis (SignReadout UniformOn ladder left_mem_realLIcc mem_realLIcc_iff ratNat_self ratNat_succ_le_pow2 ratNat_two_one realLIcc realLOf_neg right_mem_realLIcc succ_mul_invWidth)
end ZFSet
