/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Ternary intervals.

A sequence of digits `c : Nat → Nat` with `c n ≤ 1` drives a walk down the
thirds of `[0,1]`: at each stage keep the left third if the digit is `0`, the
right third if it is `1`. Written with a common denominator the walk is pure
integer arithmetic --

    k₀ = 0        kₙ₊₁ = 3kₙ + 2cₙ        Iₙ = [kₙ/3ⁿ, (kₙ+1)/3ⁿ]

The obvious formulation branches on the digit, and a definition by cases costs
choice; this one multiplies by it instead, so the endpoints are
defined by a formula and the case split survives only inside proofs, where a
disjunction is enough.

The nested-interval machinery then applies unchanged, and the middle third that
is never used lands two digit sequences that first differ at `n` in intervals
that are strictly apart.

Everything here is over `intOfNat`, so the numerator arithmetic is `Nat`
arithmetic transported once and then handled by `omega`.
-/

import FromAxioms.Analysis.Nested
import FromAxioms.Core.CoreShim

universe u

open Core NumberTheory SetTheory
namespace Analysis


/-! ## The walk -/

/-- `3ⁿ`. -/
def pow3 : Nat → Nat
  | 0 => 1
  | n + 1 => 3 * pow3 n

theorem pow3_pos : ∀ n : Nat, 0 < pow3 n
  | 0 => by simp only [pow3]; omega
  | n + 1 => by
    have := pow3_pos n
    simp only [pow3]
    omega

/-- `n + 1 ≤ 3ⁿ`, which turns the geometric widths into the harmonic bound
`shrink_of_invWidth` wants. -/
theorem succ_le_pow3 : ∀ n : Nat, n + 1 ≤ pow3 n
  | 0 => by simp [pow3]
  | n + 1 => by
    have := succ_le_pow3 n
    simp only [pow3]
    omega

/-- The numerator after `n` steps. -/
def tnum (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 3 * tnum c n + 2 * c n

/-- The walk's numerator stays strictly below its denominator: with digits at
most `1`, `tnum c n ≤ 3^n - 1`. Induction, and the `+1` is what makes it usable
against `thigh`. -/
theorem tnum_lt_pow3 {c : Nat → Nat} (hc : ∀ i, c i ≤ 1) :
    ∀ n, tnum c n + 1 ≤ pow3 n
  | 0 => by simp [tnum, pow3]
  | n + 1 => by
    have ih := tnum_lt_pow3 hc n
    have := hc n
    simp only [tnum, pow3]
    omega

def tlow (c : Nat → Nat) (n : Nat) : ZFSet.{u} := ratNat (tnum c n) (pow3 n)

def thigh (c : Nat → Nat) (n : Nat) : ZFSet.{u} := ratNat (tnum c n + 1) (pow3 n)

theorem tlow_mem_Rat (c : Nat → Nat) (n : Nat) : tlow.{u} c n ∈ NumberTheory.Rat.{u} :=
  ratNat_mem_Rat (pow3_pos n)

theorem thigh_mem_Rat (c : Nat → Nat) (n : Nat) : thigh.{u} c n ∈ NumberTheory.Rat.{u} :=
  ratNat_mem_Rat (pow3_pos n)

private theorem mul3 (K P : Nat) : K * (3 * P) = 3 * K * P := by
  rw [← Nat.mul_assoc, Nat.mul_comm K 3]

/-- The left endpoint only moves right: the digit adds `2cₙ` to `3kₙ`. -/
theorem tlow_step (c : Nat → Nat) (n : Nat) : ratLe (tlow.{u} c n) (tlow.{u} c (n + 1)) := by
  refine (ratNat_le_iff (pow3_pos n) (pow3_pos (n + 1))).mpr ?_
  show tnum c n * pow3 (n + 1) ≤ tnum c (n + 1) * pow3 n
  simp only [pow3, tnum]
  rw [mul3]
  exact Nat.mul_le_mul_right _ (by omega)

/-- The right endpoint only moves left: `2cₙ + 1 ≤ 3` because the digit is at
most one. This is the only place the bound on the digits is used. -/
theorem thigh_step {c : Nat → Nat} (hc : ∀ n, c n ≤ 1) (n : Nat) :
    ratLe (thigh.{u} c (n + 1)) (thigh.{u} c n) := by
  refine (ratNat_le_iff (pow3_pos (n + 1)) (pow3_pos n)).mpr ?_
  show (tnum c (n + 1) + 1) * pow3 n ≤ (tnum c n + 1) * pow3 (n + 1)
  simp only [pow3, tnum]
  rw [mul3]
  exact Nat.mul_le_mul_right _ (by have := hc n; omega)

theorem tlow_mono (c : Nat → Nat) (m : Nat) :
    ∀ n : Nat, m ≤ n → ratLe (tlow.{u} c m) (tlow.{u} c n)
  | 0, h => by
    have : m = 0 := by omega
    rw [this]
    exact ratLe_refl (tlow_mem_Rat c 0)
  | n + 1, h => by
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact ratLe_trans (tlow_mem_Rat c m) (tlow_mem_Rat c n) (tlow_mem_Rat c (n + 1))
        (tlow_mono c m n (by omega)) (tlow_step c n)
    · have : m = n + 1 := by omega
      rw [this]
      exact ratLe_refl (tlow_mem_Rat c (n + 1))

theorem thigh_anti {c : Nat → Nat} (hc : ∀ n, c n ≤ 1) (m : Nat) :
    ∀ n : Nat, m ≤ n → ratLe (thigh.{u} c n) (thigh.{u} c m)
  | 0, h => by
    have : m = 0 := by omega
    rw [this]
    exact ratLe_refl (thigh_mem_Rat c 0)
  | n + 1, h => by
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · exact ratLe_trans (thigh_mem_Rat c (n + 1)) (thigh_mem_Rat c n) (thigh_mem_Rat c m)
        (thigh_step hc n) (thigh_anti hc m n (by omega))
    · have : m = n + 1 := by omega
      rw [this]
      exact ratLe_refl (thigh_mem_Rat c (n + 1))

theorem tlow_lt_thigh (c : Nat → Nat) (n : Nat) : ratLt (tlow.{u} c n) (thigh.{u} c n) := by
  refine (ratNat_lt_iff (pow3_pos n) (pow3_pos n)).mpr ?_
  -- not `Nat.mul_lt_mul_right`: core proves that one classically
  exact mul_lt_mul_right' (pow3_pos n) (by omega)

/-- The width at stage `n` is `1/3ⁿ`, which is at most `1/(n+1)`. -/
theorem ternary_width {c : Nat → Nat} (n : Nat) :
    ratLe (ratAdd (thigh.{u} c n) (ratNeg (tlow.{u} c n))) (ratNat.{u} 1 (n + 1)) := by
  rw [thigh, tlow, ratNat_width (pow3_pos n)]
  exact (ratNat_le_iff (pow3_pos n) (by omega)).mpr (by
    have := succ_le_pow3 n
    omega)

/-! ## The sequences as set functions -/

def tlowSeq (c : Nat → Nat) : ZFSet.{u} := natSeq NumberTheory.Rat.{u} (tlow c)

def thighSeq (c : Nat → Nat) : ZFSet.{u} := natSeq NumberTheory.Rat.{u} (thigh c)

theorem app_tlowSeq (c : Nat → Nat) (n : Nat) :
    app (tlowSeq.{u} c) (ofNat.{u} n) = tlow c n :=
  app_natSeq (tlow_mem_Rat c) n

theorem app_thighSeq (c : Nat → Nat) (n : Nat) :
    app (thighSeq.{u} c) (ofNat.{u} n) = thigh c n :=
  app_natSeq (thigh_mem_Rat c) n

/-- The ternary walk is a nested family, so every digit sequence names a
real. -/
theorem isNested_ternary {c : Nat → Nat} (hc : ∀ n, c n ≤ 1) :
    IsNested (tlowSeq.{u} c) (thighSeq.{u} c) where
  lower_seq := natSeq_mem_ratSeqs (tlow_mem_Rat c)
  upper_seq := natSeq_mem_ratSeqs (thigh_mem_Rat c)
  lower_mono m hm n hn hmn := by
    obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
    obtain ⟨j, rfl⟩ := (mem_omega_iff n).mp hn
    rw [app_tlowSeq, app_tlowSeq]
    exact tlow_mono c i j ((ofNat_subset_iff i j).mp hmn)
  upper_mono m hm n hn hmn := by
    obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
    obtain ⟨j, rfl⟩ := (mem_omega_iff n).mp hn
    rw [app_thighSeq, app_thighSeq]
    exact thigh_anti hc i j ((ofNat_subset_iff i j).mp hmn)
  bracket n hn := by
    obtain ⟨i, rfl⟩ := (mem_omega_iff n).mp hn
    rw [app_tlowSeq, app_thighSeq]
    exact tlow_lt_thigh c i
  shrink := by
    refine shrink_of_invWidth (natSeq_mem_ratSeqs (tlow_mem_Rat c))
      (natSeq_mem_ratSeqs (thigh_mem_Rat c)) (fun n hn => ?_)
    obtain ⟨i, rfl⟩ := (mem_omega_iff n).mp hn
    rw [app_tlowSeq, app_thighSeq, invWidth_ofNat]
    exact ternary_width i

#print axioms isNested_ternary
#print axioms tnum_lt_pow3
end Analysis

namespace ZFSet
export Analysis (app_thighSeq app_tlowSeq isNested_ternary pow3 pow3_pos succ_le_pow3 ternary_width thigh thighSeq thigh_anti thigh_mem_Rat thigh_step tlow tlowSeq tlow_lt_thigh tlow_mem_Rat tlow_mono tlow_step tnum tnum_lt_pow3)
end ZFSet
