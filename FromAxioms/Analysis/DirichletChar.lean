/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# A Dirichlet character mod a prime

`cyclicCharSet` builds a character of a cyclic group out of a root of unity of
the right order, and `exists_primitive_root` says the units mod a prime are
cyclic. Neither file can see the other: `ComplexRoot` sits over the complex
numbers and `QuadRes` over the finite fields, and they are separate leaves of
the tower with nothing importing either. A character exists only where both are
in scope, which is what this file is for.

`cyclicCharSet` had no caller anywhere in the tree. It carried its hypotheses --
a generator, its order, a root of unity, and that the generator exhausts the
group -- and nothing supplied them, so its multiplicativity and its
orthogonality were statements about a map that had never been built. All four
are discharged here.

What comes out is the arithmetic input an L-function consumes: a complex-valued,
unital, multiplicative map on the units with every value of modulus one. The
modulus bound is exactly the hypothesis `isCauchyComplex_dirichlet_bounded`
asks for, and it is the only thing the analytic side ever reads about a
character.

The root is `cZeta`, which this file did not have to build. Rooting `cOne`
through `cUnitRootOf` produces only the principal character, because that
function follows the principal branch and returns `cOne`. `cZeta n` is the
exponential of a proper fraction of a turn and `cZeta_primitive` shows its
powers are apart from one below the order --- which is what orthogonality
consumes, and what `cZetaPowSum_zero` already applies.
-/
import FromAxioms.NumberTheory.Halving

open NumberTheory SetTheory

namespace ZFSet

open SetTheory NumberTheory

/-- Filtering `upto N` by divisibility of `N + 1` gives `divisorsBelow (N + 1)`,
as an equality of lists. -/
theorem filter_upto_dvd_succ (N : Nat) :
    List.filter (fun e => (N + 1) % e == 0) (upto N) = divisorsBelow (N + 1) := by
  have hsplit : ∀ M : Nat, (N + 1) / 2 ≤ M → M ≤ N →
      List.filter (fun e => (N + 1) % e == 0) (upto M)
        = List.filter (fun e => (N + 1) % e == 0) (upto ((N + 1) / 2)) := by
    intro M hM
    induction M with
    | zero =>
      intro _
      have hz : (N + 1) / 2 = 0 := by omega
      rw [hz]
    | succ M ih =>
      intro hMN
      rcases Nat.lt_or_ge ((N + 1) / 2) (M + 1) with hgt | hle
      · -- the head is above half, so it is not a proper divisor and drops
        have hnot : ((N + 1) % (M + 1) == 0) = false := by
          refine decide_eq_false ?_
          intro hz
          have hdvd : Divides (M + 1) (N + 1) := divides_of_mod_eq_zero (by
            simpa using hz)
          obtain ⟨k, hk⟩ := hdvd
          have hk2 : k = 1 := by
            rcases Nat.lt_or_ge k 2 with h2 | h2
            · rcases Nat.eq_zero_or_pos k with rfl | hp
              · rw [Nat.mul_zero] at hk; omega
              · omega
            · exfalso
              have hmul : (M + 1) * 2 ≤ (M + 1) * k := Nat.mul_le_mul_left _ h2
              have hge : 2 * (M + 1) ≤ N + 1 := by rw [hk]; omega
              omega
          rw [hk2, Nat.mul_one] at hk
          omega
        rw [upto, List.filter_cons]
        rw [hnot]
        exact ih (by omega) (by omega)
      · -- at or below half the two lists already agree
        have : M + 1 = (N + 1) / 2 := by omega
        rw [this]
  have hle : (N + 1) / 2 ≤ N := by omega
  rw [hsplit N hle (Nat.le_refl N), divisorsBelow]

#print axioms ZFSet.filter_upto_dvd_succ

end ZFSet
