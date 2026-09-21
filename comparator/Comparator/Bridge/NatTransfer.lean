/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
Bridge, rung 1: `omega` to Lean's `Nat`.

The ladder to Mathlib's `ℝ` has four rungs, and the top one is what `ivt-exact`
needs:

    1  omega  -> Nat      this file
    2  Int    -> ℤ
    3  Rat    -> ℚ
    4  RealL  -> ℝ        preserving order and limits

`SetTheory.mem_omega_iff` is exactly

    x ∈ omega ↔ ∃ n : Nat, x = ofNat n

so surjectivity is proved; `NumberTheory.ofNat_injective` gives uniqueness.
What needs a choice principle is the function alone: turning `∃ n, x = ofNat n`
into an `n`.

The choice is spent here, not in the tower, so the transfer sits under
`comparator/`. `Classical.choose` is unavailable under `FromAxioms/` by the
project's floor; it is unremarkable in a file that already imports Mathlib. So
`toNat` is classical and every tower theorem it carries across stays at
`[propext, Quot.sound]`.
-/
import Mathlib.Data.Nat.Basic
import FromAxioms

namespace Comparator

open SetTheory NumberTheory

/-- A member of `omega` as a Lean natural. Classical: `mem_omega_iff` gives
the existential and `Classical.choose` extracts the witness. -/
noncomputable def toNat (x : ZFSet) (hx : x ∈ omega) : Nat :=
  ((mem_omega_iff x).mp hx).choose

/-- `toNat` inverts `ofNat` on the nose. -/
theorem ofNat_toNat (x : ZFSet) (hx : x ∈ omega) : ofNat (toNat x hx) = x :=
  (((mem_omega_iff x).mp hx).choose_spec).symm

/-- And in the other direction, by injectivity. -/
theorem toNat_ofNat (n : Nat) (h : ofNat n ∈ omega := ofNat_mem_omega n) :
    toNat (ofNat n) h = n :=
  ofNat_injective (ofNat_toNat _ h)

/-- `toNat` is injective, so the transfer loses nothing. -/
theorem toNat_injective {x y : ZFSet} (hx : x ∈ omega) (hy : y ∈ omega)
    (h : toNat x hx = toNat y hy) : x = y := by
  rw [← ofNat_toNat x hx, ← ofNat_toNat y hy, h]

/-! ## Order and addition

The `RealL -> R` transfer needs the tower's order and addition to survive the
crossing: the Cauchy bound `|q_m - q_n| < 1/2^m + 1/2^n` is a comparison of
Lean rationals. These two are the bottom of that chain --- `toInt` reduces to
them, and `toRat` to `toInt`. -/

/-- `toNat` carries `add` to `+`.

The proof goes forward from `add_ofNat`, not by rewriting `a` and `b`:
`toNat a ha` carries a proof about `a`, so `rw [← ofNat_toNat a ha]` builds a
motive `fun _a => … toNat _a ha …` that does not typecheck. For the same reason
it finishes through `ofNat_injective` rather than `toNat_injective`. -/
theorem toNat_add (a b : ZFSet) (ha : a ∈ omega) (hb : b ∈ omega)
    (hab : NumberTheory.add a b ∈ omega) :
    toNat (NumberTheory.add a b) hab = toNat a ha + toNat b hb := by
  have hsum := NumberTheory.add_ofNat (toNat a ha) (toNat b hb)
  rw [ofNat_toNat a ha, ofNat_toNat b hb] at hsum
  apply ofNat_injective
  rw [ofNat_toNat (NumberTheory.add a b) hab]
  exact hsum

/-- `toNat` carries `⊆` to `≤`.

By contradiction on the indices: a strictly larger index on the left would put
`b` inside `a` --- membership is the order, by `mem_ofNat_iff` --- and the
subset then puts `b` inside itself. `not_mem_self` is the whole content, so no
order induction is needed. -/
theorem toNat_le_of_subset (a b : ZFSet) (ha : a ∈ omega) (hb : b ∈ omega)
    (hsub : a ⊆ b) : toNat a ha ≤ toNat b hb := by
  rcases Nat.lt_or_ge (toNat b hb) (toNat a ha) with h | h
  · exfalso
    have hmem : b ∈ a := by
      rw [← ofNat_toNat a ha]
      exact (mem_ofNat_iff b (toNat a ha)).mpr
        ⟨toNat b hb, h, (ofNat_toNat b hb).symm⟩
    exact not_mem_self b (hsub b hmem)
  · exact h

/-- `toNat` carries `mul` to `*`. Same shape as `toNat_add`, on
`mul_ofNat`. -/
theorem toNat_mul (a b : ZFSet) (ha : a ∈ omega) (hb : b ∈ omega)
    (hab : NumberTheory.mul a b ∈ omega) :
    toNat (NumberTheory.mul a b) hab = toNat a ha * toNat b hb := by
  have hprod := NumberTheory.mul_ofNat (toNat a ha) (toNat b hb)
  rw [ofNat_toNat a ha, ofNat_toNat b hb] at hprod
  apply ofNat_injective
  rw [ofNat_toNat (NumberTheory.mul a b) hab]
  exact hprod

/-- `toNat` reflects membership as `<`. -/
theorem toNat_lt_of_mem {x y : ZFSet} (hx : x ∈ omega) (hy : y ∈ omega)
    (hmem : x ∈ y) : toNat x hx < toNat y hy := by
  obtain ⟨k, hk, hxk⟩ :=
    (mem_ofNat_iff x (toNat y hy)).mp (by rw [ofNat_toNat y hy]; exact hmem)
  have : toNat x hx = k := by
    subst hxk
    exact toNat_ofNat k hx
  omega

end Comparator
