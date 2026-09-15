/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# √2.

The oldest result this development reaches: there is a real whose square is
`2`, and no rational has that square.

Two halves, and they lean on each other.

`sq_two_irrational` is the Nat-level statement -- `p² = 2q²` forces `q = 0` --
by descent: `p²` even makes `p` even, halving gives a smaller pair, and strong
induction closes it. No axioms, and the arithmetic stays in `Nat`.

The real is then built by bisection. The interval `[kₙ/2ⁿ, (kₙ+1)/2ⁿ]` is
halved by asking whether `(2kₙ+1)² < 2·(2ⁿ⁺¹)²` -- a comparison of naturals,
which is decidable data rather than a `Prop` disjunction, so the sequence is
definable without any axiom. This is the same reason `Ternary.lean` is
choice-free, arrived at from the other direction: there the decision was pushed
into arithmetic, here it was arithmetic to begin with.

The invariant is `kₙ² < 2·4ⁿ < (kₙ+1)²`, and keeping it is exactly where
irrationality is needed: the middle point could a priori equal `2·4ⁿ`, and
`sq_two_irrational` is what rules that out.
-/

import FromAxioms.NumberTheory.Prime
import FromAxioms.NumberTheory.Rational

universe u

namespace NumberTheory

/-! ## The Nat-level theorem -/

/-- `(2m)² = 4m²`, and its odd companion. Without `ring`, the two identities the
descent needs are proved once and reused. -/
private theorem four_sq (m : Nat) : (2 * m) * (2 * m) = 4 * (m * m) := by
  rw [Nat.mul_assoc, ← Nat.mul_assoc m 2 m, Nat.mul_comm m 2, Nat.mul_assoc,
    ← Nat.mul_assoc]

/-- The irrationality of √2, as the prime case at `2`.

`prime_sq_irrational` runs the descent for an arbitrary prime modulus, and the
only thing this row adds is `isPrime_two`. The descent WAS written out here once,
with a private `odd_sq` and `even_of_sq_even` supplying `2 ∣ p² → 2 ∣ p` by
expanding `(2r+1)²`; the general lemma gets that step from `prime_divides_sq` and
needs no expansion, so the specialised proof and both helpers came out together.

The two case of `prime_sq_irrational`, whose type quantifies over `n` under
`IsPrime n` and so is a different statement from this one. -/
theorem sq_two_irrational : ∀ p q : Nat, p * p = 2 * (q * q) → q = 0 :=
  prime_sq_irrational isPrime_two

/-! ## The bisection -/

def pow2 : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * pow2 n

theorem succ_le_pow2 : ∀ n : Nat, n + 1 ≤ pow2 n
  | 0 => by simp [pow2]
  | n + 1 => by
    have := succ_le_pow2 n
    simp only [pow2]
    omega

/-! ## √2 is not a rational

If the cut of the walk were the cut of a rational `r`, then `r` would sit inside
every interval, and cross-multiplying gives, for every `n`,

    kₙ·q ≤ p·2ⁿ ≤ (kₙ+1)·q

with `r = p/q`. The invariant then squeezes `p² ` against `2q²` and the two can
never meet, because `sq_two_irrational` says they differ -- and differing by at
least one is enough: it forces `2ⁿ < 5q²` for every `n`, which one Archimedean
step refutes. No limits, and no arithmetic on `ℝ`. -/

/-- The numeric heart, with the products named so that the final step is linear:
either the left ends or the right ends of the intervals give `P² < 5·P·Q`. -/
private theorem squeeze {K P Q A : Nat} (hQ : 0 < Q)
    (hlo : K * K < 2 * (P * P)) (hhi : 2 * (P * P) < (K + 1) * (K + 1))
    (hK : K ≤ 2 * P) (_hP : 0 < P)
    (hlow : (K * K) * Q ≤ A * (P * P)) (hA : A + 1 ≤ 2 * Q) :
    P * P < 5 * (P * Q) := by
  have hexp : (K + 1) * (K + 1) = K * K + 2 * K + 1 := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  have hstep : 2 * (P * P) < K * K + 5 * P := by omega
  have h2 : (2 * (P * P)) * Q < (K * K + 5 * P) * Q :=
    Nat.mul_lt_mul_of_lt_of_le hstep (Nat.le_refl Q) hQ
  have e1 : (2 * (P * P)) * Q = 2 * ((P * P) * Q) := Nat.mul_assoc 2 (P * P) Q
  have e2 : (K * K + 5 * P) * Q = (K * K) * Q + 5 * (P * Q) := by
    rw [Nat.add_mul, Nat.mul_assoc 5 P Q]
  rw [e1, e2] at h2
  have h3 : A * (P * P) + (P * P) ≤ (2 * Q) * (P * P) := by
    have hstep' := Nat.mul_le_mul_right (P * P) hA
    rw [Nat.add_mul, Nat.one_mul] at hstep'
    exact hstep'
  have e3 : (2 * Q) * (P * P) = 2 * ((P * P) * Q) := by
    rw [Nat.mul_assoc 2 Q (P * P), Nat.mul_comm Q (P * P)]
  rw [e3] at h3
  omega

/-- No rational squares to a prime -- the 540 BCE theorem in the form it is
usually stated, at the generality `Nat.Prime.irrational_sqrt` has rather than at
`2` alone.

The trichotomy, the negative-case reflection and the zero case are all
independent of which number sits on the right, so releasing the `2` changes only
the arithmetic core: `prime_sq_irrational` in place of `sq_two_irrational`. -/
theorem no_rat_sq_prime {n : Nat} (hn : IsPrime n) {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) :
    ratMul r r ≠ ratNat.{u} n 1 := by
  have hn2 : 2 ≤ n := hn.left
  -- the positive case is the `Nat` theorem read through `exists_ratNat_of_pos`
  have hpos : ∀ s, s ∈ Rat.{u} → ratLt ratZero.{u} s → ratMul s s ≠ ratNat.{u} n 1 := by
    intro s hsQ hs0 he
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_ratNat_of_pos hsQ hs0
    rw [ratNat_mul hb hb] at he
    have := (ratNat_eq_iff (Nat.mul_pos hb hb) (by omega)).mp he
    exact absurd (prime_sq_irrational hn a b (by omega)) (by omega)
  intro he
  rcases ratLt_trichotomy hr ratZero_mem_Rat with hneg | hzero | hgt
  · -- `r < 0`, so `-r > 0` and squares to the same thing
    have hnr := ratNeg_mem_Rat hr
    have hnr0 : ratLt ratZero.{u} (ratNeg r) := by
      have hstep := (ratNeg_lt_neg_iff ratZero_mem_Rat hr).mpr hneg
      rwa [ratNeg_zero] at hstep
    refine hpos (ratNeg r) hnr hnr0 ?_
    rw [ratMul_neg hnr hr, ratMul_comm hnr hr, ratMul_neg hr hr, ratNeg_ratNeg
      (ratMul_mem_Rat hr hr)]
    exact he
  · -- `r = 0`, so the square is `0`
    rw [hzero, ratZero_mul ratZero_mem_Rat, ratZero_eq_ratNat] at he
    have h2 := (ratNat_eq_iff (by omega : 0 < 1) (by omega : 0 < 1)).mp he
    omega
  · exact hpos r hr hgt he

/-- No rational squares to `2`, the landmark's own statement, now READ OFF
the general one rather than proved beside it. -/
theorem no_rat_sq_two {r : ZFSet.{u}} (hr : r ∈ Rat.{u}) :
    ratMul r r ≠ ratNat.{u} 2 1 :=
  no_rat_sq_prime isPrime_two hr

#print axioms sq_two_irrational
#print axioms no_rat_sq_prime
#print axioms no_rat_sq_two
#print axioms four_sq
#print axioms squeeze
#print axioms succ_le_pow2
end NumberTheory

namespace ZFSet
export NumberTheory (no_rat_sq_prime no_rat_sq_two pow2 sq_two_irrational succ_le_pow2)
end ZFSet
