/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Primes, and Euclid's theorem.

The number-theory track opens here, at the next dated result after √2: 300 BCE,
infinitely many primes.

Everything is decidable, which is what makes this cheap. `d ∣ n` is `n % d =
0`, a `Bool`-level test, so the least non-trivial factor can be found by
bounded search and defined rather than chosen. Compare `Uncountable.lean`,
where the search is over a `Prop` disjunction and costs an axiom: the
difference is not the shape of the argument but what is being decided.

Euclid's step is then the usual one. `minFac (n! + 1)` is prime, and it cannot
be `≤ n`, because anything in that range divides `n!` and would have to divide
`1` as well.

The results are stated in `Nat` and transported to `ω` at the end: `ofNat` is a
bijection onto `ω` that carries `+` and `×`, so the set-theoretic
statement is the `Nat` one read through it.
-/

import FromAxioms.Core.NatSearch
import FromAxioms.NumberTheory.Arith
import FromAxioms.SetTheory.Pair

universe u

open SetTheory
namespace NumberTheory

/-! ## Divisibility in `Nat` -/

def Divides (d n : Nat) : Prop := ∃ k, n = d * k

theorem divides_refl (n : Nat) : Divides n n := ⟨1, by omega⟩

theorem divides_trans {a b c : Nat} (h₁ : Divides a b) (h₂ : Divides b c) :
    Divides a c := by
  obtain ⟨k, rfl⟩ := h₁
  obtain ⟨m, rfl⟩ := h₂
  exact ⟨k * m, Nat.mul_assoc a k m⟩

theorem divides_of_mod_eq_zero {d n : Nat} (h : n % d = 0) :
    Divides d n := ⟨n / d, by have := Nat.div_add_mod n d; omega⟩

theorem mod_eq_zero_of_divides {d n : Nat} (h : Divides d n) : n % d = 0 := by
  obtain ⟨k, rfl⟩ := h
  exact Nat.mul_mod_right d k

/-- Divisibility of naturals is a decision, not a search.

A remainder settles it, so the bounded searches the Gauss argument needs -- least
index whose coefficient a prime does NOT divide -- can branch without reaching
for a principle. `Eis.dvd_or_not` says the same for the Eisenstein integers and
is the model; nothing said it for `Nat`, where it is two lines.

Stated as the disjunction a search consumes, which is the form
`exists_lt_or_not` wants. No positivity hypothesis: it is not needed, and the
`p = 0` case is honest -- `n % 0` is `n`, so the decision reads is `n` zero,
which is what dividing by zero means. -/
theorem divides_or_not_nat (p n : Nat) :
    Divides p n ∨ ¬ Divides p n := by
  rcases Nat.eq_zero_or_pos (n % p) with h | h
  · exact Or.inl (divides_of_mod_eq_zero h)
  · refine Or.inr (fun hd => ?_)
    have := mod_eq_zero_of_divides hd
    omega


theorem divides_le {d n : Nat} (hn : 0 < n) (h : Divides d n) : d ≤ n := by
  obtain ⟨k, rfl⟩ := h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · omega
  · exact Nat.le_mul_of_pos_right d hk

theorem eq_one_of_divides_one {d : Nat} (h : Divides d 1) : d = 1 := by
  obtain ⟨k, hk⟩ := h
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · omega
  · have := Nat.le_mul_of_pos_right d (show 0 < k by
      rcases Nat.eq_zero_or_pos k with rfl | hk'
      · omega
      · exact hk')
    omega

/-! ## The least non-trivial factor

Bounded search, with the bound as fuel. Nothing is chosen: `n % k = 0` is
decided by computation. -/

def minFacAux (n : Nat) : Nat → Nat → Nat
  | _, 0 => n
  | k, fuel + 1 => if n % k = 0 then k else minFacAux n (k + 1) fuel

def minFac (n : Nat) : Nat := minFacAux n 2 n

theorem minFacAux_divides {n : Nat} (hn : 2 ≤ n) :
    ∀ fuel k : Nat, 2 ≤ k → Divides (minFacAux n k fuel) n
  | 0, k, _ => by
    simp only [minFacAux]
    exact divides_refl n
  | fuel + 1, k, hk => by
    simp only [minFacAux]
    split
    · next h => exact divides_of_mod_eq_zero h
    · next h => exact minFacAux_divides hn fuel (k + 1) (by omega)

theorem minFac_divides {n : Nat} (hn : 2 ≤ n) : Divides (minFac n) n :=
  minFacAux_divides hn n 2 (by omega)

theorem minFacAux_ge {n : Nat} (hn : 2 ≤ n) :
    ∀ fuel k : Nat, 2 ≤ k → 2 ≤ minFacAux n k fuel
  | 0, k, _ => by
    simp only [minFacAux]
    exact hn
  | fuel + 1, k, hk => by
    simp only [minFacAux]
    split
    · next h => exact hk
    · next h => exact minFacAux_ge hn fuel (k + 1) (by omega)

theorem minFac_ge {n : Nat} (hn : 2 ≤ n) : 2 ≤ minFac n := minFacAux_ge hn n 2 (by omega)

/-- Nothing strictly between `k` and the value found divides `n`: the search
passed those and they failed. -/
theorem minFacAux_least {n : Nat} (hn : 2 ≤ n) :
    ∀ fuel k : Nat, 2 ≤ k → k + fuel ≥ n →
      ∀ d, 2 ≤ d → d < minFacAux n k fuel → d < k ∨ ¬ Divides d n
  | 0, k, hk, hfuel, d, hd, hlt => by
    simp only [minFacAux] at hlt
    exact Or.inl (by omega)
  | fuel + 1, k, hk, hfuel, d, hd, hlt => by
    simp only [minFacAux] at hlt
    split at hlt
    · next h => exact Or.inl hlt
    · next h =>
      rcases minFacAux_least hn fuel (k + 1) (by omega) (by omega) d hd hlt with hkd | hnd
      · rcases Nat.lt_or_ge d k with h' | h'
        · exact Or.inl h'
        · refine Or.inr (fun hdiv => h ?_)
          have : d = k := by omega
          rw [← this]
          exact mod_eq_zero_of_divides hdiv
      · exact Or.inr hnd

theorem minFac_least {n : Nat} (hn : 2 ≤ n) (d : Nat) (hd : 2 ≤ d)
    (hlt : d < minFac n) : ¬ Divides d n := by
  rcases minFacAux_least hn n 2 (by omega) (by omega) d hd hlt with h | h
  · omega
  · exact h

/-! ## Primality -/

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, 2 ≤ d → Divides d p → d = p

/-- The least non-trivial factor of anything above `1` is prime: a factor of it
would be a smaller factor of `n`, and the search would have found that first. -/
theorem isPrime_minFac {n : Nat} (hn : 2 ≤ n) : IsPrime (minFac n) := by
  refine ⟨minFac_ge hn, fun d hd hdvd => ?_⟩
  rcases Nat.lt_or_ge d (minFac n) with hlt | hge
  · exact absurd (divides_trans hdvd (minFac_divides hn)) (minFac_least hn d hd hlt)
  · have := divides_le (by have := minFac_ge hn; omega) hdvd
    omega

/-! ## Euclid -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-! ## Bézout, and Euclid's lemma

`Nat.gcd` and its divisibility lemmas are Lean core's, and axiom-free; what is
missing is the Bézout identity, which core does not state for `Nat` because the
coefficients want a sign. Carrying the sign as which side the coefficient is
on avoids ℤ entirely, and the Euclidean recursion swaps sides at each step. -/

private theorem mul_shuffle (a x d : Nat) : a * (x * d) = a * d * x := by
  rw [Nat.mul_assoc, Nat.mul_comm d x]

/-- Bezout's identity. One of the two sides carries the coefficient; which
one flips with each Euclidean step, which is why the statement is a
disjunction. -/
theorem bezout : ∀ x y : Nat, ∃ a b : Nat,
    a * x = b * y + Nat.gcd x y ∨ a * y = b * x + Nat.gcd x y := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro y
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · refine ⟨1, 0, Or.inr ?_⟩
      rw [Nat.gcd_zero_left]
      omega
    · obtain ⟨a, b, hcase⟩ := ih (y % x) (Nat.mod_lt y hx) x
      rw [← Nat.gcd_rec x y] at hcase
      have hmd : y % x + x * (y / x) = y := Nat.mod_add_div y x
      rcases hcase with h | h
      · refine ⟨a, b + a * (y / x), Or.inr ?_⟩
        have key : a * (y % x) + a * (x * (y / x)) = a * y := by
          rw [← Nat.mul_add, hmd]
        rw [Nat.add_mul, ← mul_shuffle]
        omega
      · refine ⟨a + b * (y / x), b, Or.inl ?_⟩
        have key : b * (y % x) + b * (x * (y / x)) = b * y := by
          rw [← Nat.mul_add, hmd]
        rw [Nat.add_mul, ← mul_shuffle]
        omega

/-- Euclid's lemma for coprime numbers. Bézout again: if `u` and `v` share
no factor and `u` divides `v·t`, the `v` can be dropped. -/
theorem coprime_divides {u v t : Nat} (h : Nat.gcd u v = 1) (hd : Divides u (v * t)) :
    Divides u t := by
  rcases Nat.eq_zero_or_pos u with rfl | hu
  · rw [Nat.gcd_zero_left] at h
    obtain ⟨w, hw⟩ := hd
    rw [h, Nat.one_mul] at hw
    exact ⟨t, by omega⟩
  obtain ⟨w, hw⟩ := hd
  obtain ⟨c, d, hcase⟩ := bezout u v
  rw [h] at hcase
  rcases hcase with hc | hc
  · -- `c·u = d·v + 1`, so `t = u·(tc) - u·(dw)`
    have hmul : t * (c * u) = t * (d * v) + t := by
      rw [hc, Nat.mul_add, Nat.mul_one]
    have hvw : t * (d * v) = u * (d * w) := by
      have hstep : d * (v * t) = d * (u * w) := congrArg (fun z => d * z) hw
      have hL : t * (d * v) = d * (v * t) := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have hR : u * (d * w) = d * (u * w) := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      rw [hL, hR, hstep]
    have h1 : t * (c * u) = u * (t * c) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hle : d * w ≤ t * c := by
      rcases Nat.lt_or_ge (t * c) (d * w) with hlt | hge
      · exfalso
        have hstep : u * (d * w) = u * (t * c) + u * (d * w - t * c) := by
          rw [← Nat.mul_add]
          exact congrArg _ (by omega)
        have hbig : u * 1 ≤ u * (d * w - t * c) := Nat.mul_le_mul_left u (by omega)
        omega
      · exact hge
    refine ⟨t * c - d * w, ?_⟩
    have hexp : u * (t * c) = u * (d * w) + u * (t * c - d * w) := by
      rw [← Nat.mul_add]
      exact congrArg _ (by omega)
    omega
  · -- `c·v = d·u + 1`, so `t = u·(cw) - u·(td)`
    have hmul : t * (c * v) = t * (d * u) + t := by
      rw [hc, Nat.mul_add, Nat.mul_one]
    have hvw : t * (c * v) = u * (c * w) := by
      have hstep : c * (v * t) = c * (u * w) := congrArg (fun z => c * z) hw
      have hL : t * (c * v) = c * (v * t) := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have hR : u * (c * w) = c * (u * w) := by
        simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      rw [hL, hR, hstep]
    have h2 : t * (d * u) = u * (t * d) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    have hle : t * d ≤ c * w := by
      rcases Nat.lt_or_ge (c * w) (t * d) with hlt | hge
      · exfalso
        have hstep : u * (t * d) = u * (c * w) + u * (t * d - c * w) := by
          rw [← Nat.mul_add]
          exact congrArg _ (by omega)
        have hbig : u * 1 ≤ u * (t * d - c * w) := Nat.mul_le_mul_left u (by omega)
        omega
      · exact hge
    refine ⟨c * w - t * d, ?_⟩
    have hexp : u * (c * w) = u * (t * d) + u * (c * w - t * d) := by
      rw [← Nat.mul_add]
      exact congrArg _ (by omega)
    omega

theorem gcd_eq_one_of_prime_not_divides {p a : Nat} (hp : IsPrime p)
    (h : ¬ Divides p a) : Nat.gcd p a = 1 := by
  have hd : Divides (Nat.gcd p a) p := Nat.gcd_dvd_left p a
  rcases Nat.lt_or_ge (Nat.gcd p a) 2 with hlt | hge
  · rcases Nat.eq_zero_or_pos (Nat.gcd p a) with h0 | h1
    · exfalso
      obtain ⟨k, hk⟩ := hd
      rw [h0] at hk
      have := hp.left
      omega
    · omega
  · exact absurd ((hp.right _ hge hd) ▸ (Nat.gcd_dvd_right p a : Divides (Nat.gcd p a) a)) h

/-- Euclid's lemma. Divisibility is decidable, so the case split is free;
Bézout does the rest. -/
theorem prime_divides_mul {p a b : Nat} (hp : IsPrime p) (h : Divides p (a * b)) :
    Divides p a ∨ Divides p b := by
  rcases Nat.eq_zero_or_pos (a % p) with hmod | hmod
  · exact Or.inl (divides_of_mod_eq_zero hmod)
  refine Or.inr ?_
  have hpa : ¬ Divides p a := fun hd => by
    have := mod_eq_zero_of_divides hd
    omega
  have hg := gcd_eq_one_of_prime_not_divides hp hpa
  obtain ⟨k, hk⟩ := h
  obtain ⟨u, v, hb⟩ := bezout p a
  rw [hg] at hb
  have hp0 : 0 < p := by have := hp.left; omega
  rcases hb with h1 | h1
  · -- `u p = v a + 1`, so `b = p (u b - v k)`
    refine ⟨u * b - v * k, ?_⟩
    have e1 : u * p * b = v * a * b + b := by
      rw [h1, Nat.add_mul, Nat.one_mul]
    have e2 : v * a * b = v * (p * k) := by rw [← hk, Nat.mul_assoc]
    have e3 : u * p * b = p * (u * b) := by
      rw [Nat.mul_comm u p, Nat.mul_assoc]
    have e4 : v * (p * k) = p * (v * k) := by
      rw [← Nat.mul_assoc, Nat.mul_comm v p, Nat.mul_assoc]
    rw [Nat.mul_sub]
    omega
  · -- `u a = v p + 1`, so `b = p (u k - v b)`
    refine ⟨u * k - v * b, ?_⟩
    have e1 : u * a * b = v * p * b + b := by
      rw [h1, Nat.add_mul, Nat.one_mul]
    have e2 : u * a * b = u * (p * k) := by rw [← hk, Nat.mul_assoc]
    have e3 : u * (p * k) = p * (u * k) := by
      rw [← Nat.mul_assoc, Nat.mul_comm u p, Nat.mul_assoc]
    have e4 : v * p * b = p * (v * b) := by
      rw [Nat.mul_comm v p, Nat.mul_assoc]
    rw [Nat.mul_sub]
    omega

/-! ## Factorization

Lists are core's; the product is not, so it is defined here. Existence is
`minFac` plus strong induction. Uniqueness up to permutation is not proved --
what is proved is its engine, that a prime dividing a product divides one of the
factors, which is what makes any two factorizations line up. -/

def prodList : List Nat → Nat
  | [] => 1
  | p :: t => p * prodList t

def IsFactorization (l : List Nat) (n : Nat) : Prop :=
  (∀ p, p ∈ l → IsPrime p) ∧ prodList l = n

theorem exists_factorization : ∀ n : Nat, 1 ≤ n → ∃ l : List Nat, IsFactorization l n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · refine ⟨[], fun p hp => absurd hp (by simp), ?_⟩
      simp only [prodList]
      omega
    · have hprime := isPrime_minFac hge
      obtain ⟨m, hm⟩ := minFac_divides hge
      have hpm : minFac n ≥ 2 := minFac_ge hge
      have hmlt : m < n := by
        rcases Nat.lt_or_ge m n with h | h
        · exact h
        · exfalso
          have : n ≤ minFac n * m := by
            calc n = 1 * n := by omega
            _ ≤ minFac n * n := Nat.mul_le_mul_right n (by omega)
            _ ≤ minFac n * m := Nat.mul_le_mul_left _ h
          have h2 : 2 * m ≤ minFac n * m := Nat.mul_le_mul_right m hpm
          omega
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · omega
        · exact h
      obtain ⟨l, hlp, hlprod⟩ := ih m hmlt hm1
      refine ⟨minFac n :: l, fun p hp => ?_, ?_⟩
      · rcases List.mem_cons.mp hp with rfl | hp'
        · exact hprime
        · exact hlp p hp'
      · simp only [prodList, hlprod]
        omega

/-! ## Inside the theory

`ofNat` carries `+` and `×`, so divisibility and primality read
across to `ω` unchanged. -/

def DividesSet (d n : ZFSet.{u}) : Prop := ∃ k, k ∈ omega.{u} ∧ n = mul d k

/-! ## Binomial coefficients

Lean's core has no `choose`, so here it is, defined by Pascal's rule. -/

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

theorem choose_zero (n : Nat) : choose n 0 = 1 := by
  cases n <;> rfl

theorem choose_succ_succ (n k : Nat) :
    choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

theorem choose_gt : ∀ n k : Nat, n < k → choose n k = 0
  | _, 0, h => absurd h (by omega)
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [choose_succ_succ, choose_gt n k (by omega), choose_gt n (k + 1) (by omega)]

#print axioms isPrime_minFac
#print axioms bezout
#print axioms prime_divides_mul
#print axioms coprime_divides
#print axioms exists_factorization
namespace Eis

#print axioms mul_comm
#print axioms add_comm
end Eis

#print axioms NumberTheory.divides_or_not_nat


end NumberTheory

namespace ZFSet
export NumberTheory (Divides DividesSet IsFactorization IsPrime bezout choose choose_gt choose_succ_succ choose_zero coprime_divides divides_le divides_of_mod_eq_zero divides_or_not_nat divides_refl divides_trans eq_one_of_divides_one exists_factorization fact gcd_eq_one_of_prime_not_divides isPrime_minFac minFac minFacAux minFacAux_divides minFacAux_ge minFacAux_least minFac_divides minFac_ge minFac_least mod_eq_zero_of_divides prime_divides_mul prodList)
end ZFSet
