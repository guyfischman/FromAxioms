/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Congruences, and the Chinese remainder theorem

The first step of the arithmetic that discharges the incompleteness hypotheses
(QUEUE: representability). Gödel's β-function codes a finite sequence as a pair
of numbers, and it works because the moduli it uses are pairwise coprime and the
remainder theorem then recovers each entry.

`Prime.lean` has Bézout in its Nat form -- a disjunction, because which side
carries the coefficient flips with each Euclidean step -- and everything here is
built from it. Nothing is decided that is not computed: `%` is a function, and
congruence is an equation between its values.

The Nat-only presentation costs one thing and buys another. It costs the
inverse: `a·m ≡ 1 (mod n)` has to be extracted from both branches of Bézout, and
the second branch gives `-1` where the first gives `1`, which in `Nat` means
multiplying by `n - 1` rather than negating. It buys freedom from a subtraction
that would have to be justified, and from the integers entirely -- `Integer.lean`
exists, but the β-function is about `Nat`, and moving through `ℤ` would mean
transporting every statement back.
-/

import FromAxioms.NumberTheory.Prime

namespace NumberTheory

/-- `a` and `b` leave the same remainder mod `n`. An equation between computed
values, so every fact about it is a computation. -/
def Cong (n a b : Nat) : Prop := a % n = b % n

theorem cong_refl (n a : Nat) : Cong n a a := rfl

theorem cong_symm {n a b : Nat} (h : Cong n a b) : Cong n b a := h.symm

theorem cong_trans {n a b c : Nat} (h₁ : Cong n a b) (h₂ : Cong n b c) :
    Cong n a c := h₁.trans h₂

theorem cong_add {n a b c d : Nat} (h₁ : Cong n a b) (h₂ : Cong n c d) :
    Cong n (a + c) (b + d) := by
  show (a + c) % n = (b + d) % n
  rw [Nat.add_mod, Nat.add_mod b d, h₁, h₂]

theorem cong_mul {n a b c d : Nat} (h₁ : Cong n a b) (h₂ : Cong n c d) :
    Cong n (a * c) (b * d) := by
  show (a * c) % n = (b * d) % n
  rw [Nat.mul_mod, Nat.mul_mod b d, h₁, h₂]

/-- Adding a multiple of the modulus changes nothing. -/
theorem cong_add_mul (n a k : Nat) : Cong n (a + n * k) a := by
  show (a + n * k) % n = a % n
  rw [Nat.add_mul_mod_self_left]

/-- The form the theorem is used in: `x = a + n·k` is exactly `x ≡ a`, once `a`
is already reduced. -/
theorem cong_of_eq_add_mul {n a k x : Nat} (h : x = a + n * k) : Cong n x a := by
  rw [h]
  exact cong_add_mul n a k

/-! ## Inverses -/

private theorem inverse_of_two_le {m N : Nat} (hN : 2 ≤ N)
    (h : Nat.gcd m N = 1) : ∃ a, Cong N (a * m) 1 := by
  obtain ⟨a, b, hcase⟩ := bezout m N
  rw [h] at hcase
  rcases hcase with hc | hc
  · refine ⟨a, cong_of_eq_add_mul (k := b) ?_⟩
    rw [Nat.mul_comm N b]
    omega
  · -- `b·m + 1 = a·N`, so `b·m` is `-1`; scaling by `N - 1` turns it into `1`.
    have hbm : b * m + 1 = a * N := by omega
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · omega
      · exact ha
    have e1 : (N - 1) * (b * m) + (N - 1) = (N - 1) * (a * N) := by
      have e := congrArg (fun t => (N - 1) * t) hbm
      simp only [Nat.mul_add, Nat.mul_one] at e
      exact e
    have e2 : (N - 1) * (a * N) = N * ((N - 1) * a) := by
      rw [← Nat.mul_assoc, Nat.mul_comm ((N - 1) * a) N]
    have hpos : 1 ≤ (N - 1) * a :=
      Nat.one_le_iff_ne_zero.mpr fun hz => by
        rcases Nat.mul_eq_zero.mp hz with hz | hz <;> omega
    -- Naming the quotient keeps `omega` away from a product it cannot expand:
    -- `N * ((N-1)*a - 1)` is a multiplication over a subtraction, and omega
    -- decomposes it rather than treating it as an atom.
    obtain ⟨K, hK⟩ : ∃ K, (N - 1) * a = K + 1 := ⟨(N - 1) * a - 1, by omega⟩
    have e3 : N * ((N - 1) * a) = N * K + N := by
      rw [hK, Nat.mul_add, Nat.mul_one]
    refine ⟨(N - 1) * b, cong_of_eq_add_mul (k := K) ?_⟩
    rw [Nat.mul_assoc]
    omega

theorem exists_inverse : ∀ {m n : Nat}, Nat.gcd m n = 1 → ∃ a, Cong n (a * m) 1
  | m, 0, h => by
    rw [Nat.gcd_zero_right] at h
    exact ⟨1, by show (1 * m) % 0 = 1 % 0; rw [Nat.one_mul, h]⟩
  | _, 1, _ => ⟨1, by show _ % 1 = _ % 1; rw [Nat.mod_one, Nat.mod_one]⟩
  | _, _ + 2, h => inverse_of_two_le (by omega) h

/-! ## The Chinese remainder theorem

Two moduli, which is all the β-function needs: the sequence-coding argument
applies it repeatedly rather than to a family at once. -/

/-- The Chinese remainder theorem. Two coprime congruences have a common
solution, and the witness is built rather than chosen: `x = r + m·t` with `t`
the inverse of `m` scaled by the gap, every step a computation on numerals. -/
theorem crt {m n : Nat} (hco : Nat.gcd m n = 1) (hn : 0 < n)
    (r s : Nat) : ∃ x, Cong m x r ∧ Cong n x s := by
  obtain ⟨a, ha⟩ := exists_inverse hco
  -- `s + r·n ≥ r`, so the gap can be taken in `Nat` without a subtraction.
  refine ⟨r + m * (a * (s + r * n - r)), ?_, ?_⟩
  · exact cong_add_mul m r _
  · have hgap : s + r * n - r + r = s + r * n := by
      have : r ≤ r * n := Nat.le_mul_of_pos_right r hn
      omega
    have hstep : Cong n (m * (a * (s + r * n - r))) (s + r * n - r) := by
      have : Cong n (a * m * (s + r * n - r)) (1 * (s + r * n - r)) :=
        cong_mul ha (cong_refl n _)
      rw [Nat.one_mul] at this
      rw [show m * (a * (s + r * n - r)) = a * m * (s + r * n - r) by
        rw [← Nat.mul_assoc, Nat.mul_comm m a]]
      exact this
    have := cong_add (cong_refl n r) hstep
    refine cong_trans this ?_
    rw [Nat.add_comm r (s + r * n - r), hgap]
    show (s + r * n) % n = s % n
    rw [Nat.add_mul_mod_self_right]

/-! ## The β-function's moduli

Gödel codes a finite sequence by a pair `(a, b)`, reading entry `i` as
`a % (1 + (i+1)·b)`. The construction works because those moduli are pairwise
coprime whenever `b` is divisible by every difference of indices -- which a
factorial supplies -- and because the remainder theorem then solves all the
congruences at once. -/

def betaMod (b i : Nat) : Nat := 1 + (i + 1) * b

/-! ## Gödel's β-function

A pair of numbers codes any finite sequence, so a theory with only `+` and `×`
can talk about recursion: a primitive recursive definition is a statement about
a sequence, and a sequence is a pair.

Two conditions have to hold at once, and the factorial supplies both. The gaps
between indices must divide `b`, which makes the moduli coprime; and every entry
must be smaller than its modulus, so that reducing it changes nothing. Taking
`b = fact m` for an `m` bounding both the length and every entry does it. -/

def beta (a b i : Nat) : Nat := a % betaMod b i

#print axioms Cong
#print axioms cong_mul
#print axioms exists_inverse
#print axioms crt
#print axioms cong_symm

/-- A congruence yields an additive witness, in one orientation or the other.
`Nat` subtraction truncates, so `a - b` is not the difference when `b` exceeds
`a`; naming which side is larger keeps every later step additive. -/
theorem cong_cases {n a b : Nat} (h : Cong n a b) :
    ∃ c, a = b + n * c ∨ b = a + n * c := by
  unfold Cong at h
  obtain ⟨qa, hqa⟩ : ∃ q, a / n = q := ⟨_, rfl⟩
  obtain ⟨qb, hqb⟩ : ∃ q, b / n = q := ⟨_, rfl⟩
  have ha : a = n * qa + a % n := by rw [← hqa]; exact (Nat.div_add_mod a n).symm
  have hb : b = n * qb + a % n := by
    rw [← hqb, h]; exact (Nat.div_add_mod b n).symm
  cases Nat.le_total qa qb with
  | inl hle =>
    obtain ⟨d, hd⟩ : ∃ d, qb = qa + d := ⟨qb - qa, by omega⟩
    rw [hd, Nat.mul_add] at hb
    exact ⟨d, Or.inr (by omega)⟩
  | inr hle =>
    obtain ⟨d, hd⟩ : ∃ d, qa = qb + d := ⟨qa - qb, by omega⟩
    rw [hd, Nat.mul_add] at ha
    exact ⟨d, Or.inl (by omega)⟩


#print axioms inverse_of_two_le

#print axioms cong_refl
#print axioms cong_trans
#print axioms cong_add
#print axioms cong_add_mul
#print axioms cong_of_eq_add_mul
end NumberTheory

namespace ZFSet
export NumberTheory (Cong beta betaMod cong_add cong_add_mul cong_cases cong_mul cong_of_eq_add_mul cong_refl cong_symm cong_trans crt exists_inverse)
#print axioms NumberTheory.cong_cases
end ZFSet
