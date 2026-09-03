/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Primes, and Euclid's theorem.

The number-theory track opens here, at the next dated result after √2: 300 BCE,
infinitely many primes.

Everything is decidable, so this is cheap. `d ∣ n` is `n % d = 0`, a
`Bool`-level test, so the least non-trivial factor can be found by bounded
search and defined rather than chosen. Compare `Uncountable.lean`, where the
search is over a `Prop` disjunction and costs an axiom: the difference is not
the shape of the argument but what is being decided.

Euclid's step is then the usual one. `minFac (n! + 1)` is prime, and it cannot
be `≤ n`, because anything in that range divides `n!` and would have to divide
`1` as well.

The results are stated in `Nat` and transported to `ω` at the end: `ofNat` is a
bijection onto `ω` that carries `+` and `×`, so the set-theoretic
statement is the `Nat` one read through it.
-/

import FromAxioms.Core.NatSearch
import FromAxioms.NumberTheory.Arith

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
one flips with each Euclidean step, so the statement is a disjunction. -/
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
what is proved is its engine, that a prime dividing a product divides one of
the factors, so any two factorizations line up. -/

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

theorem choose_self : ∀ n : Nat, choose n n = 1
  | 0 => rfl
  | n + 1 => by
    rw [choose_succ_succ, choose_self n, choose_gt n (n + 1) (by omega)]

theorem choose_one : ∀ n : Nat, choose n 1 = n
  | 0 => rfl
  | n + 1 => by
    rw [choose_succ_succ, choose_zero, choose_one n]
    omega

/-- The identity behind `p ∣ C(p,k)`: `(n+1)·C(n,k) = C(n+1,k+1)·(k+1)`. -/
theorem succ_mul_choose : ∀ n k : Nat, (n + 1) * choose n k = choose (n + 1) (k + 1) * (k + 1)
  | 0, 0 => rfl
  | 0, k + 1 => by
    show 1 * choose 0 (k + 1) = choose 1 (k + 2) * (k + 2)
    rw [show choose 0 (k + 1) = 0 from rfl, choose_gt 1 (k + 2) (by omega)]
    omega
  | n + 1, 0 => by
    show (n + 2) * choose (n + 1) 0 = choose (n + 2) 1 * 1
    rw [choose_zero, choose_one (n + 2)]
  | n + 1, k + 1 => by
    have h₁ := succ_mul_choose n k
    have h₂ := succ_mul_choose n (k + 1)
    have hX : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl
    have hY : choose (n + 2) (k + 1 + 1)
        = choose (n + 1) (k + 1) + choose (n + 1) (k + 1 + 1) := rfl
    show (n + 2) * choose (n + 1) (k + 1) = choose (n + 2) (k + 1 + 1) * (k + 1 + 1)
    have e1 : (n + 2) * choose (n + 1) (k + 1)
        = (n + 1) * choose (n + 1) (k + 1) + choose (n + 1) (k + 1) := by
      rw [show n + 2 = (n + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
    have e2 : (n + 1) * choose (n + 1) (k + 1)
        = (n + 1) * choose n k + (n + 1) * choose n (k + 1) := by
      rw [hX, Nat.mul_add]
    have e3 : choose (n + 2) (k + 1 + 1) * (k + 1 + 1)
        = choose (n + 1) (k + 1) * (k + 1 + 1)
          + choose (n + 1) (k + 1 + 1) * (k + 1 + 1) := by
      rw [hY, Nat.add_mul]
    have e4 : choose (n + 1) (k + 1) * (k + 1 + 1)
        = choose (n + 1) (k + 1) * (k + 1) + choose (n + 1) (k + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    omega


/-- A prime divides its own binomial coefficients, away from the ends. -/
theorem prime_dvd_choose {p k : Nat} (hp : IsPrime p) (hk : 0 < k) (hkp : k < p) :
    Divides p (choose p k) := by
  have hp2 := hp.left
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  -- `(q+1)·C(q,j) = C(q+1,j+1)·(j+1)`, so `p` divides the right side
  have hid := succ_mul_choose q j
  have hdvd : Divides (q + 1) (choose (q + 1) (j + 1) * (j + 1)) := ⟨choose q j, hid.symm⟩
  refine coprime_divides (v := j + 1) ?_ ?_
  · -- `p` and `j+1` are coprime, since `p` is prime and `j+1 < p`
    refine gcd_eq_one_of_prime_not_divides hp (fun hd => ?_)
    have := divides_le (show 0 < j + 1 by omega) hd
    omega
  · obtain ⟨w, hw⟩ := hdvd
    exact ⟨w, by rw [← hw, Nat.mul_comm]⟩

/-! ## Divisor sums, and a geometric bound

The arithmetic half of counting irreducible polynomials: a sum over the proper
divisors of `d`, and `∑_{e ∣ d, e < d} q^e < q^d`, so the count of degree-`d`
irreducibles is positive. -/

/-- The shifted cyclotomic polynomial satisfies Eisenstein's conditions at
`p`.

`Φp(x+1) = ((x+1)^p - 1)/x`, so its coefficient of `x^j` is `C(p, j+1)`. The
three Eisenstein hypotheses are then binomial facts:

* every coefficient below the top is divisible by `p` -- `prime_dvd_choose`;
* the top one is `C(p,p) = 1`, which `p` does not divide;
* the constant term is `C(p,1) = p`, which `p²` does not divide.

Stated over the coefficient FUNCTION rather than over a polynomial object,
because the substitution `x → x+1` does not exist in this tree and is not needed
to state the conditions -- only to transfer the resulting irreducibility back to
`Φp` itself, which is a separate rung. -/
theorem cyclotomicShift_eisenstein {p : Nat} (hp : IsPrime p) :
    (∀ j, j < p - 1 -> Divides p (choose p (j + 1)))
      ∧ ¬ Divides p (choose p (p - 1 + 1))
      ∧ choose p 1 = p
      ∧ ¬ Divides (p * p) (choose p 1) := by
  have hp2 : 2 <= p := hp.left
  refine ⟨fun j hj => prime_dvd_choose hp (by omega) (by omega), ?_, choose_one p, ?_⟩
  · have hpp : p - 1 + 1 = p := by omega
    rw [hpp, choose_self p]
    intro hcon
    exact absurd (eq_one_of_divides_one hcon) (by omega)
  · rw [choose_one p]
    intro hcon
    obtain ⟨c, hc⟩ := hcon
    rcases Nat.eq_zero_or_pos c with rfl | hcp
    · omega
    · -- `p = p²c` with `c ≥ 1` forces `p ≥ p² ≥ 2p`, so `p ≤ 0`
      have h1 : p * p <= p * p * c := by
        have hstep := Nat.mul_le_mul_left (p * p) hcp
        rw [Nat.mul_one] at hstep
        exact hstep
      have h2 : 2 * p <= p * p := Nat.mul_le_mul_right p hp2
      omega

#print axioms isPrime_minFac
#print axioms bezout
#print axioms prime_divides_mul
#print axioms coprime_divides
#print axioms prime_dvd_choose
#print axioms cyclotomicShift_eisenstein
#print axioms exists_factorization
/-! ### Summing over the indices, continued -/

/-- `2` is prime: a divisor at least `2` cannot exceed it. -/
theorem isPrime_two : IsPrime 2 := by
  refine ⟨by omega, fun d hd hdvd => ?_⟩
  obtain ⟨c, hc⟩ := hdvd
  rcases Nat.eq_zero_or_pos c with h0 | hcp
  · rw [h0, Nat.mul_zero] at hc; omega
  · have : d * 1 ≤ d * c := Nat.mul_le_mul_left d hcp
    omega

#print axioms isPrime_two
/-- `3` is prime. -/
theorem isPrime_three : IsPrime 3 := by
  refine ⟨by omega, fun d hd hdvd => ?_⟩
  obtain ⟨k, hk⟩ := hdvd
  have hle : d ≤ 3 := divides_le (by omega) ⟨k, hk⟩
  rcases Nat.lt_or_ge d 3 with hlt | hge
  · obtain rfl : d = 2 := by omega
    omega
  · omega

#print axioms isPrime_three

/-! ## The Eisenstein integers

`ℤ[ω]` with `ω` a primitive cube root of `1`, so `ω² = -ω - 1`. Written as a
pair of integers `a + bω`, which makes multiplication

    (a + bω)(c + dω) = ac + (ad + bc)ω + bd ω²
                     = (ac - bd) + (ad + bc - bd)ω

The second case of Fermat for `n = 3` is a descent in this ring; the norm below
is what turns that descent into one on the naturals. -/

structure Eis where
  re : Int
  im : Int

namespace Eis

def zero : Eis := ⟨0, 0⟩
def one : Eis := ⟨1, 0⟩
def omega : Eis := ⟨0, 1⟩

def mul (x y : Eis) : Eis :=
  ⟨x.re * y.re - x.im * y.im,
   x.re * y.im + x.im * y.re - x.im * y.im⟩

/-- The field norm `N(a + bω) = a² - ab + b²`, which is `(a + bω)` times its
conjugate. It is never negative -- `4N = (2a - b)² + 3b²` -- so it lands in the
naturals and a descent on it terminates. -/
def norm (x : Eis) : Int := x.re * x.re - x.re * x.im + x.im * x.im

private theorem int_sq_nonneg (a : Int) : 0 <= a * a := by
  rcases Int.lt_or_le a 0 with h | h
  · rw [← Int.neg_mul_neg]
    exact Int.mul_nonneg (by omega) (by omega)
  · exact Int.mul_nonneg h h

private theorem int_sq_eq_zero {a : Int} (h : a * a = 0) : a = 0 := by
  rcases Int.mul_eq_zero.mp h with h' | h' <;> exact h'

/-- `(a - b)² = a² - 2ab + b²`, expanded so that only products of the two
variables appear -- no numeral is multiplied into a product, so `omega`
finishes from here treating each product as an atom. -/
private theorem sq_sub_expand (a b : Int) :
    (a - b) * (a - b) = a * a - (a * b + a * b) + b * b := by
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
  have hc : b * a = a * b := Int.mul_comm b a
  omega

/-- `N(a + bω) = (a - b)² + ab`, which is the split the sign of `ab` decides. -/
private theorem norm_split (x : Eis) :
    norm x = (x.re - x.im) * (x.re - x.im) + x.re * x.im := by
  rw [sq_sub_expand]; simp [norm]; omega

theorem norm_nonneg (x : Eis) : 0 <= norm x := by
  rcases Int.lt_or_le (x.re * x.im) 0 with h | h
  · have h1 := int_sq_nonneg x.re
    have h2 := int_sq_nonneg x.im
    simp [norm]; omega
  · have h1 := int_sq_nonneg (x.re - x.im)
    rw [norm_split]; omega

/-- The norm is multiplicative, so a factorisation in `ℤ[ω]` becomes a
factorisation of a natural number, in which a proper factor is strictly
smaller, so the descent terminates. -/
theorem norm_mul (x y : Eis) : norm (mul x y) = norm x * norm y := by
  simp [norm, mul, Int.sub_mul, Int.mul_sub, Int.mul_add, Int.add_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

theorem norm_eq_zero {x : Eis} (h : norm x = 0) : x.re = 0 ∧ x.im = 0 := by
  rcases Int.lt_or_le (x.re * x.im) 0 with hs | hs
  · exfalso
    have h1 := int_sq_nonneg x.re
    have h2 := int_sq_nonneg x.im
    simp [norm] at h; omega
  · have h1 := int_sq_nonneg (x.re - x.im)
    rw [norm_split] at h
    have hd : (x.re - x.im) * (x.re - x.im) = 0 := by omega
    have hp : x.re * x.im = 0 := by omega
    have hdz : x.re - x.im = 0 := int_sq_eq_zero hd
    rcases Int.mul_eq_zero.mp hp with hz | hz
    · exact ⟨hz, by omega⟩
    · exact ⟨by omega, hz⟩

/-! ### The ring laws, and the six units

`ℤ[ω]` is a commutative ring, and its units are exactly the six elements of
norm `1`: `±1, ±ω, ±ω²`. The descent for `n = 3` runs modulo those, so the
finiteness is what makes the case analysis terminate. -/

theorem mul_comm (x y : Eis) : mul x y = mul y x := by
  simp [mul, Int.mul_comm]; omega

theorem mul_assoc (x y z : Eis) : mul (mul x y) z = mul x (mul y z) := by
  simp [mul, Int.sub_mul, Int.mul_sub, Int.mul_add, Int.add_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  exact ⟨by omega, by omega⟩

/-! ### Conjugation, and the road to division with remainder

`x * conj x = N(x)`, so dividing by `x` is dividing by the integer `N(x)` after
multiplying by the conjugate. That is the whole content of the Euclidean
algorithm here; what remains is rounding, and the geometric fact that the
hexagonal lattice's covering radius is under `1`. -/

def conj (x : Eis) : Eis := ⟨x.re - x.im, -x.im⟩

def ofInt (n : Int) : Eis := ⟨n, 0⟩

theorem mul_conj (x : Eis) : mul x (conj x) = ofInt (norm x) := by
  simp [mul, conj, ofInt, norm, Int.mul_sub, Int.mul_neg, Int.neg_neg]
  have hc : x.im * x.re = x.re * x.im := Int.mul_comm x.im x.re
  omega

theorem norm_conj (x : Eis) : norm (conj x) = norm x := by
  simp [norm, conj, Int.mul_sub,
    Int.mul_neg, Int.neg_mul, Int.neg_neg, Int.mul_comm]

/-- Cancellation: `ℤ[ω]` has no zero divisors, because the norm has none in
`ℤ`. The descent needs this to know a proper factor is proper. -/
theorem eq_zero_of_mul_eq_zero {x y : Eis} (h : mul x y = zero)
    (hx : ¬ (x.re = 0 ∧ x.im = 0)) : y.re = 0 ∧ y.im = 0 := by
  have hn : norm x * norm y = 0 := by
    rw [← norm_mul, h]; simp [norm, zero]
  rcases Int.mul_eq_zero.mp hn with h' | h'
  · exact absurd (norm_eq_zero h') hx
  · exact norm_eq_zero h'

/-! ### The Euclidean property

`x = q·y + r` with `N(r) < N(y)`. The quotient rounds `x·conj y` coordinatewise
by `N(y)`; the remainder's norm then satisfies `N(r)·N(y) = N(x·conj y - N(y)·q)`,
which the covering bound puts under `N(y)²`. -/

def sub (x y : Eis) : Eis := ⟨x.re - y.re, x.im - y.im⟩

theorem mul_ofInt (a : Eis) (n : Int) : mul a (ofInt n) = ⟨a.re * n, a.im * n⟩ := by
  simp [mul, ofInt]

/-! ### `λ = 1 - ω`, the ramified prime above 3

`N(λ) = 3`, and `3 = -ω² λ²` up to a unit: the rational prime `3` ramifies. The
descent for `n = 3` is a descent on the power of `λ` dividing one of the three
terms, so this element and not `3` is the right object. -/

def lam : Eis := ⟨1, -1⟩

/-! ### Divisibility, and the descent the Euclidean property licenses -/

def Dvd (d x : Eis) : Prop := ∃ k : Eis, x = mul d k

/-! ### Cubes modulo `λ⁴`

The `n = 3` descent turns on one congruence: a cube prime to `λ` is `±1` modulo
`λ⁴`. That is the Eisenstein analogue of cubes are `0, ±1` mod `9` -- indeed
`λ⁴` has norm `81` and `9` is `-ω²λ²` up to a unit -- and it rules out a sum of
three such cubes.

The residues are recorded here as a divisibility statement rather than as a
quotient ring, so nothing is constructed that a descent does not use. -/

/-- `λ` divides `a + bω` exactly when `3` divides `a + b`.

Mod `λ` we have `ω ≡ 1`, so `a + bω ≡ a + b`; and the rational integers `λ`
divides are exactly the multiples of `3`. Both directions are computations:
`λ·(c + dω) = (c + d) + (2d - c)ω`, whose coordinate sum is `3d`, and
conversely `a + b = 3m` is solved by `c = a - m`, `d = m`.

This makes `λ`-divisibility DECIDABLE by an integer test, turning the descent's
case analysis into arithmetic rather than search. -/
theorem lam_dvd_iff {x : Eis} :
    Dvd lam x ↔ ∃ m : Int, x.re + x.im = 3 * m := by
  obtain ⟨a, b⟩ := x
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k.im, ?_⟩
    rw [hk]
    simp [mul, lam]
    omega
  · intro h
    obtain ⟨m, hm⟩ := h
    refine ⟨⟨a - m, m⟩, ?_⟩
    simp [mul, lam] at hm ⊢
    omega

#print axioms norm_nonneg
#print axioms norm_mul
#print axioms norm_eq_zero
#print axioms mul_comm
#print axioms mul_assoc
#print axioms mul_conj
#print axioms norm_conj
#print axioms eq_zero_of_mul_eq_zero
#print axioms lam_dvd_iff
/-! ### The cube congruence

`x³ ≡ ±1 (mod λ⁴)` for `x` prime to `λ`. The coordinates make it finite:

    (a + bω)³ = (a³ - 3ab² + b³) + 3ab(a - b)·ω -/

theorem mul_sub (a b c : Eis) : mul a (sub b c) = sub (mul a b) (mul a c) := by
  simp [sub, mul, Int.mul_sub]
  exact ⟨by omega, by omega⟩

theorem ext_of_coords {a b : Eis} (hr : a.re = b.re) (hi : a.im = b.im) : a = b := by
  obtain ⟨p, q⟩ := a
  obtain ⟨r, s⟩ := b
  simp at hr hi
  simp [hr, hi]

/-- Cancellation. `ℤ[ω]` has no zero divisors, so a non-zero factor may be
struck from both sides, turning `λ⁴ ∣ λ³w³` into `λ ∣ w³`. -/
theorem eq_of_mul_left_cancel {a b c : Eis}
    (ha : ¬ (a.re = 0 ∧ a.im = 0)) (h : mul a b = mul a c) : b = c := by
  have hz : mul a (sub b c) = zero := by
    rw [mul_sub, h]
    simp [sub, zero]
  obtain ⟨h1, h2⟩ := eq_zero_of_mul_eq_zero hz ha
  simp [sub] at h1 h2
  exact ext_of_coords (by omega) (by omega)

/-! ### Discharging the split decision

A hypothesis that could be a theorem makes the price look higher than it is,
which is the opposite of what the measurements here are for. -/

/-- Divisibility in `ℤ[ω]` is DECIDABLE, by the same route `lam_dvd_iff`
takes for `λ`: `a ∣ x` exactly when `N(a)` divides both coordinates of
`x · conj a`, which is a question about two integers.

This is the step that makes the split search decidable rather than merely
finite, and it needs `a ≠ 0` -- nothing divides by zero. -/
theorem dvd_iff_norm_dvd_coords {a x : Eis}
    (ha : ¬ (a.re = 0 ∧ a.im = 0)) :
    Dvd a x ↔ (∃ p : Int, (mul x (conj a)).re = norm a * p)
              ∧ (∃ q : Int, (mul x (conj a)).im = norm a * q) := by
  constructor
  · rintro ⟨k, rfl⟩
    -- `(a k) · conj a = k · (a · conj a) = k · N(a)`
    have h : mul (mul a k) (conj a) = mul k (ofInt (norm a)) := by
      rw [mul_comm a k, mul_assoc, mul_conj]
    rw [h, mul_ofInt]
    exact ⟨⟨k.re, by simp [Int.mul_comm]⟩, ⟨k.im, by simp [Int.mul_comm]⟩⟩
  · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    -- `x · conj a = N(a) · ⟨p,q⟩`, and cancelling `conj a` leaves `x = a⟨p,q⟩`
    refine ⟨⟨p, q⟩, ?_⟩
    have hn : norm a ≠ 0 := fun h0 => ha (norm_eq_zero h0)
    refine eq_of_mul_left_cancel (a := conj a) ?_ ?_
    · intro ⟨h1, h2⟩
      refine ha ?_
      have : norm (conj a) = 0 := by simp [norm, h1, h2]
      rw [norm_conj] at this
      exact norm_eq_zero this
    · -- both sides equal `⟨N(a)·p, N(a)·q⟩`; computed separately so neither
      -- rewrite has to match a shape the other has already changed
      have hl : mul (conj a) x = ⟨norm a * p, norm a * q⟩ := by
        rw [mul_comm (conj a) x]
        exact ext_of_coords hp hq
      have hr : mul (conj a) (mul a ⟨p, q⟩) = ⟨norm a * p, norm a * q⟩ := by
        rw [← mul_assoc, mul_comm (conj a) a, mul_conj]
        refine ext_of_coords ?_ ?_ <;> simp [mul, ofInt] <;> omega
      rw [hl, hr]

/-- Testing one candidate is a decision, not a search. `a ∣ x` reduces to two
integer divisibility questions by `dvd_iff_norm_dvd_coords`, and integer
divisibility is decidable by a remainder -- so the enumeration's inner step
needs no principle.

Stated as the disjunction the search consumes, so the outer loop can branch on
it without reaching for `em`. -/
theorem dvd_or_not (a x : Eis) (ha : ¬ (a.re = 0 ∧ a.im = 0)) :
    Dvd a x ∨ ¬ Dvd a x := by
  have hn0 : norm a ≠ 0 := fun h0 => ha (norm_eq_zero h0)
  have hnp : 0 < norm a := by have := norm_nonneg a; omega
  have hd := Int.mul_ediv_add_emod (mul x (conj a)).re (norm a)
  have he := Int.mul_ediv_add_emod (mul x (conj a)).im (norm a)
  have hr0 : 0 <= (mul x (conj a)).re % norm a := Int.emod_nonneg _ hn0
  have hi0 : 0 <= (mul x (conj a)).im % norm a := Int.emod_nonneg _ hn0
  -- `Int.lt_or_le`, never `by omega : _ ∨ _`: omega on a DISJUNCTION routes
  -- through `Classical.em` and only the audit line tells the two apart.
  rcases Int.lt_or_le 0 ((mul x (conj a)).re % norm a) with hre | hre
  · exact Or.inr (fun hdv => by
      obtain ⟨⟨u, hu⟩, _⟩ := (dvd_iff_norm_dvd_coords ha).mp hdv
      -- `(N a * u) % N a = 0` is the fact omega cannot derive: it would have to
      -- relate two products, which is outside linear arithmetic.
      have hz : (mul x (conj a)).re % norm a = 0 := by
        rw [hu]; exact Int.mul_emod_right _ _
      rw [hz] at hre
      exact Int.lt_irrefl 0 hre)
  · rcases Int.lt_or_le 0 ((mul x (conj a)).im % norm a) with him | him
    · exact Or.inr (fun hdv => by
        obtain ⟨_, ⟨v, hv⟩⟩ := (dvd_iff_norm_dvd_coords ha).mp hdv
        have hz : (mul x (conj a)).im % norm a = 0 := by
          rw [hv]; exact Int.mul_emod_right _ _
        rw [hz] at him
        exact Int.lt_irrefl 0 him)
    · -- The two components are built SEPARATELY and the division is never
      -- handed to `omega`: it interprets `/` and `%` by CONSTANTS only, and by
      -- a variable it reaches for a classical route -- the audit line was
      -- `[propext, Classical.choice, Quot.sound]` until this was split out.
      -- `Int.le_antisymm`, not `omega`: the remainders are bounded above and
      -- below already, and handing omega a `%` by a VARIABLE is what pulled
      -- `Classical.choice` into the audit line. It interprets `/` and `%` by
      -- CONSTANTS only; by a variable it takes a classical route and nothing
      -- about the proof text shows it.
      have hre0 : (mul x (conj a)).re % norm a = 0 := Int.le_antisymm hre hr0
      have him0 : (mul x (conj a)).im % norm a = 0 := Int.le_antisymm him hi0
      rw [hre0, Int.add_zero] at hd
      rw [him0, Int.add_zero] at he
      exact Or.inl ((dvd_iff_norm_dvd_coords ha).mpr
        ⟨⟨(mul x (conj a)).re / norm a, hd.symm⟩,
         ⟨(mul x (conj a)).im / norm a, he.symm⟩⟩)

#print axioms mul_sub
#print axioms eq_of_mul_left_cancel
#print axioms dvd_iff_norm_dvd_coords
#print axioms dvd_or_not
#print axioms add_comm
end Eis

#print axioms NumberTheory.divides_or_not_nat


end NumberTheory

namespace ZFSet
export NumberTheory (Divides DividesSet Eis IsFactorization IsPrime bezout choose choose_gt choose_one choose_self choose_succ_succ choose_zero coprime_divides cyclotomicShift_eisenstein divides_le divides_of_mod_eq_zero divides_or_not_nat divides_refl divides_trans eq_one_of_divides_one exists_factorization fact gcd_eq_one_of_prime_not_divides isPrime_minFac isPrime_three isPrime_two minFac minFacAux minFacAux_divides minFacAux_ge minFacAux_least minFac_divides minFac_ge minFac_least mod_eq_zero_of_divides prime_divides_mul prime_dvd_choose prodList succ_mul_choose)
end ZFSet
