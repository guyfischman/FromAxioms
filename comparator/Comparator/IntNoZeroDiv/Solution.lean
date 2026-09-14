/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`.

THE MATHEMATICS IS `NumberTheory.intMul_ne_zero` and `NumberTheory.intMul_neg`,
both about the tower's ZFSet integers:

    intMul_ne_zero (hz : z ∈ Int) (hw : w ∈ Int) (hz0 : z ≠ intZero)
      (hw0 : w ≠ intZero) : intMul z w ≠ intZero
    intMul_neg (hx : x ∈ Int) (hy : y ∈ Int) :
      intMul x (intNeg y) = intNeg (intMul x y)

The first is derived there from `intMul_left_cancel`, the second from
`intMul_comm` and `intNeg_mul`. `Int.mul_eq_zero`, `mul_eq_zero` and `mul_neg`
are not cited.

NO BRIDGE. `NumberTheory.intOfLean` is the TOWER's map from Lean's core `Int`
into its own, with `intOfLean_mul`, `intOfLean_neg`, `intOfLean_zero` and
`intOfLean_injective` beside it. So this Solution imports one tower file and
nothing from `comparator/Comparator/Bridge/`, because the tower reached out to
Lean's integers itself.

THE TRANSLATION LAWS ARE USED BUT NOT PAIRED. `intOfLean_mul` carries the
statement across; the CONTENT is `intMul_ne_zero`, which no homomorphism law
implies --- a ring homomorphism from `ℤ` to a ring with zero divisors exists,
so the transport alone could not give the challenge.

DIRECTION OF `intOfLean_mul`. It is stated as
`intMul (intOfLean k) (intOfLean l) = intOfLean (k * l)`, product first, so the
rewrites below go from the tower's operation to Lean's and the `←` appears where
the goal has a Lean product to break apart.
-/
import Comparator.IntNoZeroDiv.Challenge
import FromAxioms.NumberTheory.IntLean

open NumberTheory

namespace Comparator.IntNoZeroDiv

/-- `intOfLean` sends only `0` to the tower's zero, so a nonzero Lean integer
has a nonzero image --- the form both halves of the first conjunct need. -/
theorem intOfLean_ne_zero {k : Int} (hk : k ≠ 0) :
    intOfLean.{0} k ≠ intZero.{0} := by
  intro h
  exact hk (intOfLean_injective (h.trans intOfLean_zero.symm))

/-- The challenge, from `FromAxioms`. -/
theorem solution : challenge := by
  constructor
  · intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    by_cases hb : b = 0
    · exact Or.inr hb
    exfalso
    refine intMul_ne_zero (intOfLean_mem_Int.{0} a) (intOfLean_mem_Int.{0} b)
      (intOfLean_ne_zero ha) (intOfLean_ne_zero hb) ?_
    rw [intOfLean_mul, hab, intOfLean_zero]
  · intro a b
    refine intOfLean_injective.{0} ?_
    rw [← intOfLean_mul, ← intOfLean_neg, ← intOfLean_neg, ← intOfLean_mul,
      intMul_neg (intOfLean_mem_Int.{0} a) (intOfLean_mem_Int.{0} b)]

#print axioms solution

end Comparator.IntNoZeroDiv
