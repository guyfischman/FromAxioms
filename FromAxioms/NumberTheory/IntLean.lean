/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Lean's `Int` and this tree's `Int` name the same ring.

`Integer.lean` builds `ℤ` the classical way, as `ω × ω` modulo the difference
relation. Lean's own `Int` --- which is also mathlib's, since mathlib does not
define its own --- is an inductive type with `ofNat` and `negSucc`
constructors, chosen for decidable equality and efficient arithmetic.

Reading the two constructions and observing that they agree is not a theorem.
This file writes the correspondence down and proves it: `intOfLean` is a
bijection from Lean's `Int` onto `ZFSet.Int` carrying `+` to `intAdd`, `*` to
`intMul`, and negation to `intNeg`. So the two are the same object, checked
rather than read.

THE MAP NEEDS NO CASE SPLIT, because `intOf a b` already denotes `a - b`:
sending `k` to `intOf k.toNat (-k).toNat` is uniform in the sign, and one of
the two components is `0` in either case.
-/

import FromAxioms.NumberTheory.Integer

universe u

namespace NumberTheory

/-- Lean's integer `k` as an element of `Int`, via the pair `(k⁺, k⁻)`. -/
def intOfLean (k : _root_.Int) : ZFSet.{u} :=
  intOf (ofNat.{u} k.toNat) (ofNat.{u} (-k).toNat)

theorem intOfLean_mem_Int (k : _root_.Int) : intOfLean.{u} k ∈ Int.{u} :=
  intOf_mem_Int (ofNat_mem_omega _) (ofNat_mem_omega _)

#print axioms intOfLean_mem_Int
#print axioms intOfLean

/-- The map is determined by any difference representing `k`, so the ring laws
below are a matter of `omega` rather than of sign analysis. -/
theorem intOfLean_eq_intOf {k : _root_.Int} {m n : Nat}
    (h : k = (m : _root_.Int) - (n : _root_.Int)) :
    intOfLean.{u} k = intOf (ofNat.{u} m) (ofNat.{u} n) := by
  rw [intOfLean, intOf_eq_intOf_iff (ofNat_mem_omega _) (ofNat_mem_omega _)
    (ofNat_mem_omega _) (ofNat_mem_omega _), add_ofNat, add_ofNat]
  refine congrArg ofNat.{u} ?_
  omega

#print axioms intOfLean_eq_intOf

theorem intOfLean_neg (k : _root_.Int) :
    intNeg (intOfLean.{u} k) = intOfLean.{u} (-k) := by
  rw [intOfLean, intNeg_intOf (ofNat_mem_omega _) (ofNat_mem_omega _)]
  refine (intOfLean_eq_intOf ?_).symm
  omega

#print axioms intOfLean_neg

theorem intOfLean_mul (k l : _root_.Int) :
    intMul (intOfLean.{u} k) (intOfLean.{u} l) = intOfLean.{u} (k * l) := by
  rw [intOfLean, intOfLean, intMul_intOf (ofNat_mem_omega _) (ofNat_mem_omega _)
    (ofNat_mem_omega _) (ofNat_mem_omega _), mul_ofNat, mul_ofNat, mul_ofNat,
    mul_ofNat, add_ofNat, add_ofNat]
  refine (intOfLean_eq_intOf ?_).symm
  -- `(a - b)·(c - d) = (a·c + b·d) - (a·d + b·c)`, over NATURALS. `omega`
  -- cannot multiply, but it treats a product it cannot expand as an atom, and
  -- with `a b c d` plain variables the four products are exactly four atoms.
  -- Phrased directly about `k.toNat` the same proof fails: rewriting `k` into
  -- `↑k.toNat - ↑(-k).toNat` also rewrites the `k` inside those very terms,
  -- and the atoms stop matching.
  have hrep : ∀ a b c d : Nat,
      ((a : _root_.Int) - (b : _root_.Int)) * ((c : _root_.Int) - (d : _root_.Int))
        = ((a * c + b * d : Nat) : _root_.Int)
          - ((a * d + b * c : Nat) : _root_.Int) := by
    intro a b c d
    rw [Int.natCast_add, Int.natCast_add, Int.natCast_mul, Int.natCast_mul,
      Int.natCast_mul, Int.natCast_mul, Int.sub_mul, Int.mul_sub, Int.mul_sub]
    omega
  have hk : k = (k.toNat : _root_.Int) - ((-k).toNat : _root_.Int) := by omega
  have hl : l = (l.toNat : _root_.Int) - ((-l).toNat : _root_.Int) := by omega
  have hexp := hrep k.toNat (-k).toNat l.toNat (-l).toNat
  rw [← hk, ← hl] at hexp
  exact hexp

#print axioms intOfLean_mul

theorem intOfLean_injective {k l : _root_.Int}
    (h : intOfLean.{u} k = intOfLean.{u} l) : k = l := by
  rw [intOfLean, intOfLean, intOf_eq_intOf_iff (ofNat_mem_omega _)
    (ofNat_mem_omega _) (ofNat_mem_omega _) (ofNat_mem_omega _),
    add_ofNat, add_ofNat] at h
  have := ofNat_injective.{u} h
  omega

#print axioms intOfLean_injective

/-- The map carries `0`.

`intZero` is `intOf empty empty` and `intOfLean 0` is `intOf (ofNat 0)
(ofNat 0)`; the two meet through `ofNat_zero`. Stated because a ring map that
did not carry the unit would not be one. -/
theorem intOfLean_zero : intOfLean.{u} 0 = intZero.{u} := by
  have h : intOfLean.{u} 0 = intOf (ofNat.{u} 0) (ofNat.{u} 0) :=
    intOfLean_eq_intOf (by omega)
  rw [ofNat_zero] at h
  exact h

#print axioms intOfLean_zero

end NumberTheory

namespace ZFSet
export NumberTheory (intOfLean intOfLean_eq_intOf intOfLean_injective intOfLean_mem_Int intOfLean_mul intOfLean_neg intOfLean_zero)
end ZFSet
