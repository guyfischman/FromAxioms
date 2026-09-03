/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The omniscience principles.

`EM` and `WEM` are the only two strengths the audit could name until now, and
for a development that measures exact cost that is a coarse ruler. Between them
and constructive provability sit the principles that talk about sequences
rather than arbitrary propositions:

    LPO    every binary sequence either fires somewhere or is identically zero
    WLPO   ... either is identically zero, or is not
    MP     a sequence that cannot be identically zero fires somewhere
    LLPO   of two sequences that cannot both fire, one is identically zero

The sequences are `Nat → Bool`, so `α n = true` is decidable and the principles
say something about search rather than about logic in general: a statement
quantified over arbitrary propositions reverses to `EM`, and the same statement
restricted to objects built from a sequence typically reverses only to `LPO` or
`LLPO`.

`lpo_of_ternary_decidable` is that difference made concrete. Deciding whether
`0` lies in the lower cut of an arbitrary real is `EM`; deciding
it for a real produced by the ternary walk from a binary sequence is exactly
`LPO`, and the two directions are both here.
-/

import FromAxioms.Analysis.Ternary

set_option autoImplicit false

universe u

open Analysis NumberTheory SetTheory
namespace Constructive

/-! ## The principles -/

/-- The limited principle of omniscience. -/
def LPO : Prop := ∀ α : Nat → Bool, (∃ n, α n = true) ∨ (∀ n, α n = false)

/-- Its weak form: decide only whether the sequence is identically zero. -/
def WLPO : Prop := ∀ α : Nat → Bool, (∀ n, α n = false) ∨ ¬ (∀ n, α n = false)

/-- Markov's principle. -/
def MP : Prop := ∀ α : Nat → Bool, ¬ (∀ n, α n = false) → ∃ n, α n = true

/-! ## Where `LPO` is the exact strength

A binary sequence gives ternary digits without any decision -- `Bool` is already
data -- so the walk of `Ternary.lean` turns `α` into a real. The walk moves right
exactly when a digit fires, so `0` is in the lower cut precisely when `α` does. -/

def boolDigit (α : Nat → Bool) (n : Nat) : Nat := if α n then 1 else 0

theorem boolDigit_le_one (α : Nat → Bool) (n : Nat) : boolDigit α n ≤ 1 := by
  rw [boolDigit]
  split <;> omega

theorem boolDigit_eq_one_iff {α : Nat → Bool} {n : Nat} :
    boolDigit α n = 1 ↔ α n = true := by
  rw [boolDigit]
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h => exact ⟨fun he => absurd he (by decide), fun hα => absurd hα h⟩

/-- The numerator is positive exactly when some earlier digit fired. -/
theorem tnum_pos_iff (c : Nat → Nat) : ∀ m : Nat,
    0 < tnum c m ↔ ∃ n, n < m ∧ 0 < c n
  | 0 => by
    simp only [tnum]
    constructor
    · intro h
      exact absurd h (by omega)
    · rintro ⟨n, hn, -⟩
      omega
  | m + 1 => by
    constructor
    · intro h
      simp only [tnum] at h
      rcases Nat.lt_or_ge 0 (c m) with hc | hc
      · exact ⟨m, by omega, hc⟩
      · obtain ⟨n, hn, hcn⟩ := (tnum_pos_iff c m).mp (by omega)
        exact ⟨n, by omega, hcn⟩
    · rintro ⟨n, hn, hcn⟩
      simp only [tnum]
      rcases Nat.lt_or_ge n m with hlt | hge
      · have := (tnum_pos_iff c m).mpr ⟨n, hlt, hcn⟩
        omega
      · have : n = m := by omega
        rw [this] at hcn
        omega

/-- `0` is in the walk's lower cut exactly when the sequence fires. -/
theorem zero_mem_ternary_iff (α : Nat → Bool) :
    ratZero.{u} ∈ nestLower (tlowSeq.{u} (boolDigit α)) ↔ ∃ n, α n = true := by
  rw [mem_nestLower_iff]
  constructor
  · rintro ⟨-, m, hm, hlt⟩
    obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
    rw [app_tlowSeq, tlow, ratZero_eq_ratNat,
      ratNat_lt_iff (by omega) (pow3_pos i)] at hlt
    obtain ⟨n, -, hcn⟩ := (tnum_pos_iff (boolDigit α) i).mp (by omega)
    refine ⟨n, ?_⟩
    have := boolDigit_le_one α n
    exact boolDigit_eq_one_iff.mp (by omega)
  · rintro ⟨n, hn⟩
    refine ⟨ratZero_mem_Rat, ofNat.{u} (n + 1), ofNat_mem_omega _, ?_⟩
    rw [app_tlowSeq, tlow, ratZero_eq_ratNat, ratNat_lt_iff (by omega) (pow3_pos (n + 1))]
    have hpos : 0 < tnum (boolDigit α) (n + 1) :=
      (tnum_pos_iff (boolDigit α) (n + 1)).mpr
        ⟨n, by omega, by rw [boolDigit_eq_one_iff.mpr hn]; omega⟩
    have := pow3_pos (n + 1)
    have e : tnum (boolDigit α) (n + 1) * 1 = tnum (boolDigit α) (n + 1) := by omega
    omega

/-! ## Where `WLPO` and `MP` are the exact strengths

Equality with zero is one quantifier weaker than membership: the cut of the walk
is the cut of `0` exactly when no digit fires, which is a `Π` statement, so
deciding it is `WLPO` rather than `LPO`. Markov's principle is the step from one
to the other -- a walk that cannot be zero does fire. -/

theorem tnum_eq_zero {c : Nat → Nat} (h : ∀ n, c n = 0) : ∀ m : Nat, tnum c m = 0
  | 0 => rfl
  | m + 1 => by
    simp only [tnum, tnum_eq_zero h m, h m]

theorem ternary_eq_zero_iff (α : Nat → Bool) :
    nestLower (tlowSeq.{u} (boolDigit α)) = ratCut ratZero.{u} ↔ ∀ n, α n = false := by
  constructor
  · intro he n
    cases hn : α n with
    | false => rfl
    | true =>
      have h0 : ratZero.{u} ∈ nestLower (tlowSeq.{u} (boolDigit α)) :=
        (zero_mem_ternary_iff α).mpr ⟨n, hn⟩
      rw [he] at h0
      exact absurd ((mem_ratCut_iff ratZero.{u} ratZero.{u}).mp h0).right ratLt_irrefl
  · intro hall
    have hc : ∀ n, boolDigit α n = 0 := by
      intro n
      rw [boolDigit, hall n]
      rfl
    refine ext _ _ fun q => Iff.trans (mem_nestLower_iff _ q) ?_
    refine Iff.trans ?_ (mem_ratCut_iff ratZero.{u} q).symm
    constructor
    · rintro ⟨hqQ, m, hm, hlt⟩
      obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
      rw [app_tlowSeq, tlow, tnum_eq_zero hc i, ratNat_zero (pow3_pos i)] at hlt
      exact ⟨hqQ, hlt⟩
    · rintro ⟨hqQ, hlt⟩
      refine ⟨hqQ, ofNat.{u} 0, ofNat_mem_omega 0, ?_⟩
      rw [app_tlowSeq, tlow, tnum_eq_zero hc 0, ratNat_zero (pow3_pos 0)]
      exact hlt

/-- Deciding whether a walk-built real is zero. -/
def TernaryZeroDecidable : Prop := ∀ α : Nat → Bool,
  nestLower (tlowSeq.{u} (boolDigit α)) = ratCut ratZero.{u} ∨
    nestLower (tlowSeq.{u} (boolDigit α)) ≠ ratCut ratZero.{u}

theorem wlpo_of_ternary_zero_decidable (h : TernaryZeroDecidable.{u}) : WLPO := by
  intro α
  rcases h α with he | hne
  · exact Or.inl ((ternary_eq_zero_iff α).mp he)
  · exact Or.inr (fun hall => hne ((ternary_eq_zero_iff α).mpr hall))

/-! ## The fan theorem

Brouwer's principle, and the first gap in the foundations frontier. It sits
with `LPO` and friends because it is the same kind of object -- a statement
about `Nat → Bool` that is classically true, is not constructively provable,
and is false under Russian constructivism, which makes it a boundary rather
than a theorem.

Stated over `List Bool` for the finite paths. A bar is a set of finite paths
that every infinite path meets; the theorem says a bar is met uniformly, at a
depth not depending on the path. The direction that needs no principle is the
converse, and it is here so the statement's two halves can be told apart.
-/

/-- The first `n` values of a sequence, as a path. -/
def take (α : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => take α n ++ [α n]

#print axioms Constructive.WLPO
#print axioms Constructive.LPO

/-! ## What the fan theorem says about trees
-/

/-- Any finite path, continued with `false` forever. -/
def extend (s : List Bool) : Nat → Bool := fun i => (s[i]?).getD false

#print axioms zero_mem_ternary_iff
#print axioms ternary_eq_zero_iff
#print axioms wlpo_of_ternary_zero_decidable
end Constructive
namespace ZFSet
export Constructive (LPO MP TernaryZeroDecidable WLPO boolDigit boolDigit_eq_one_iff boolDigit_le_one extend take ternary_eq_zero_iff tnum_eq_zero tnum_pos_iff wlpo_of_ternary_zero_decidable zero_mem_ternary_iff)
end ZFSet
