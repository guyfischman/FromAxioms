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

import FromAxioms.Core.CoreShim
import FromAxioms.Core.NatSearch
import FromAxioms.NumberTheory.Arith
import FromAxioms.SetTheory.Relation

universe u

open Core SetTheory
namespace NumberTheory

/-! ## Divisibility in `Nat` -/

def Divides (d n : Nat) : Prop := ∃ k, n = d * k

theorem divides_refl (n : Nat) : Divides n n := ⟨1, by omega⟩

theorem one_divides (n : Nat) : Divides 1 n := ⟨n, by omega⟩

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

theorem divides_sub {d a b : Nat} (h₁ : Divides d a) (h₂ : Divides d b) (hab : a ≤ b) :
    Divides d (b - a) := by
  obtain ⟨k, rfl⟩ := h₁
  obtain ⟨m, rfl⟩ := h₂
  exact ⟨m - k, by rw [Nat.mul_sub]⟩

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

theorem fact_pos : ∀ n : Nat, 0 < fact n
  | 0 => by simp only [fact]; omega
  | n + 1 => by
    have := fact_pos n
    simp only [fact]
    exact Nat.mul_pos (by omega) this

/-- Everything from `1` to `n` divides `n!`. -/
theorem divides_fact : ∀ n d : Nat, 1 ≤ d → d ≤ n → Divides d (fact n)
  -- `omega` on a non-arithmetic goal proves `False` classically; `absurd` does not
  | 0, d, hd, hdn => absurd hdn (by omega)
  | n + 1, d, hd, hdn => by
    simp only [fact]
    rcases Nat.lt_or_ge d (n + 1) with hlt | hge
    · exact divides_trans (divides_fact n d hd (by omega)) ⟨n + 1, Nat.mul_comm _ _⟩
    · have : d = n + 1 := by omega
      rw [this]
      exact ⟨fact n, rfl⟩

/-- Euclid's step, as a bound rather than an existence claim.

    n < minFac (n! + 1)

A prime at most `n` divides `n!`, and `minFac (n! + 1)` divides `n! + 1`, so if
it were at most `n` it would divide their difference, which is one.

Stated separately from `exists_prime_gt` because a prime ENUMERATION needs the
witness as a TERM: `exists_prime_gt` hands back an existential, and extracting a
function from it would be a choice. Here the successor is named outright. -/
theorem lt_minFac_fact_succ (n : Nat) : n < minFac (fact n + 1) := by
  have hf := fact_pos n
  have hn2 : 2 ≤ fact n + 1 := by omega
  rcases Nat.lt_or_ge n (minFac (fact n + 1)) with hgt | hle
  · exact hgt
  exfalso
  -- a prime `≤ n` divides `n!`, and it divides `n! + 1`, so it divides `1`
  have hp2 := minFac_ge hn2
  have hdvd_fact : Divides (minFac (fact n + 1)) (fact n) :=
    divides_fact n _ (by omega) (by omega)
  have hdvd_succ : Divides (minFac (fact n + 1)) (fact n + 1) := minFac_divides hn2
  have hone : Divides (minFac (fact n + 1)) 1 := by
    have hsub := divides_sub hdvd_fact hdvd_succ (by omega)
    have he : fact n + 1 - fact n = 1 := by omega
    rw [he] at hsub
    exact hsub
  exact absurd (eq_one_of_divides_one hone) (by omega)

#print axioms lt_minFac_fact_succ

/-- Euclid's theorem, the infinitude of the primes: there is a prime
above every bound. -/
theorem exists_prime_gt (n : Nat) : ∃ p, IsPrime p ∧ n < p := by
  have hf := fact_pos n
  have hn2 : 2 ≤ fact n + 1 := by omega
  exact ⟨minFac (fact n + 1), isPrime_minFac hn2, lt_minFac_fact_succ n⟩
/-- `mathlib_form` for the `infinitude of primes` landmark: a prime at or
above every bound.

Weaker than `exists_prime_gt`, which gives a prime STRICTLY above `n`; that
implies this and is not implied by it. Stated separately because the non-strict
form is the one `Nat.exists_infinite_primes` takes. -/
theorem exists_prime_ge (n : Nat) : ∃ p, IsPrime p ∧ n ≤ p := by
  obtain ⟨p, hp, hlt⟩ := exists_prime_gt n
  exact ⟨p, hp, Nat.le_of_lt hlt⟩

#print axioms NumberTheory.exists_prime_ge

/-! ## Bézout, and Euclid's lemma

`Nat.gcd` and its divisibility lemmas are Lean core's, and axiom-free; what is
missing is the Bézout identity, which core does not state for `Nat` because the
coefficients want a sign. Carrying the sign as which side the coefficient is
on avoids ℤ entirely, and the Euclidean recursion swaps sides at each step. -/

private theorem mul_shuffle (a x d : Nat) : a * (x * d) = a * d * x := by
  rw [Nat.mul_assoc, Nat.mul_comm d x]

/-- Bezout's identity. One of the two sides carries the coefficient; which
one flips with each Euclidean step, so the statement is a
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

/-- Mathlib's form. `Nat.gcd_eq_gcd_ab` writes the gcd as an INTEGER
combination, `(gcd x y : ℤ) = x·u + y·v`. `bezout` cannot say that: `Nat` has
no subtraction, so it carries a DISJUNCTION instead, naming which of the two
sides the remainder falls on.

Over `Int` the disjunction collapses, and that is the whole content here. Both
branches are one equation with the sign of `v` flipped -- `(a, -b)` on the
left, `(-b, a)` on the right. Each product is left as an atom for `omega`,
so the two commutations are spelled out rather than rewritten. -/
theorem bezout_int (x y : Nat) :
    ∃ u v : Int, (Nat.gcd x y : Int) = (x : Int) * u + (y : Int) * v := by
  obtain ⟨a, b, h | h⟩ := bezout x y
  · refine ⟨(a : Int), -(b : Int), ?_⟩
    have h' : (a : Int) * (x : Int)
        = (b : Int) * (y : Int) + (Nat.gcd x y : Int) := by
      simpa [Int.natCast_mul, Int.natCast_add] using
        congrArg (fun n : Nat => (n : Int)) h
    have c1 : (x : Int) * (a : Int) = (a : Int) * (x : Int) := Int.mul_comm _ _
    have c2 : (y : Int) * (b : Int) = (b : Int) * (y : Int) := Int.mul_comm _ _
    rw [Int.mul_neg]
    omega
  · refine ⟨-(b : Int), (a : Int), ?_⟩
    have h' : (a : Int) * (y : Int)
        = (b : Int) * (x : Int) + (Nat.gcd x y : Int) := by
      simpa [Int.natCast_mul, Int.natCast_add] using
        congrArg (fun n : Nat => (n : Int)) h
    have c1 : (x : Int) * (b : Int) = (b : Int) * (x : Int) := Int.mul_comm _ _
    have c2 : (y : Int) * (a : Int) = (a : Int) * (y : Int) := Int.mul_comm _ _
    rw [Int.mul_neg]
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

/-- A modular inverse, as a NATURAL NUMBER.

For a prime `p` and `j` strictly between `0` and `p`, some `k` has
`j * k % p = 1`.

`Field.lean`'s `mem_modInv_iff_gcd_one` says the class is invertible, but it is
stated at universe `0` and yields a CLASS. Bezout gives the witness directly
and stays in `Nat`, so nothing crosses a universe or a quotient.

Bezout's two cases are not symmetric here. One gives `j * b + 1` as a multiple
of `p` outright; the other only gives `j * b` congruent to `-1`, and its
witness is `b * (p - 1)`, since `(p-1)^2 = (p-2)*p + 1`. -/
theorem exists_mul_mod_one {p j : Nat} (hp : IsPrime p)
    (hj : 0 < j) (hjp : j < p) :
    ∃ k : Nat, j * k % p = 1 := by
  have hp2 : 2 ≤ p := hp.left
  have hnd : ¬ Divides p j := by
    intro ⟨c, hc⟩
    rcases Nat.eq_zero_or_pos c with rfl | hcpos
    · omega
    · have : p ≤ p * c := Nat.le_mul_of_pos_right p hcpos
      omega
  have hg : Nat.gcd p j = 1 := gcd_eq_one_of_prime_not_divides hp hnd
  obtain ⟨a, b, hcase⟩ := bezout p j
  rw [hg] at hcase
  rcases hcase with he | he
  · -- `a * p = b * j + 1`: so `j * b` is `-1` mod `p`, and `b * (p-1)` inverts
    refine ⟨b * (p - 1), ?_⟩
    -- peel `a` to a successor so `omega` sees `a' * p` as one atom
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by
      rcases Nat.eq_zero_or_pos a with rfl | h; · omega
      omega⟩
    have hap : (a' + 1) * p = a' * p + p := by
      rw [Nat.add_mul, Nat.one_mul]
    have hjb : j * b = a' * p + (p - 1) := by
      rw [Nat.mul_comm j b]; omega
    -- `j * b % p = p - 1`
    have hmod : j * b % p = p - 1 := by
      rw [hjb, Nat.add_comm (a' * p) (p - 1), Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (by omega)]
    -- `(p-1) * (p-1) = (p-2) * p + 1`
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
    have hsq : (m + 1) * (m + 1) = m * (m + 2) + 1 := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
      omega
    have h21 : m + 2 - 1 = m + 1 := by omega
    rw [← Nat.mul_assoc, Nat.mul_mod, hmod, h21]
    -- name the reduction: bare `Nat.mod_eq_of_lt` leaves `rw` to choose an
    -- occurrence, and it picks the wrong one
    have hlt : (m + 1) % (m + 2) = m + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hlt, hsq, Nat.add_comm (m * (m + 2)) 1, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by omega)]
  · -- `a * j = b * p + 1`: `a` inverts directly
    refine ⟨a, ?_⟩
    have h1 : j * a = b * p + 1 := by rw [Nat.mul_comm j a]; exact he
    rw [h1, Nat.add_comm (b * p) 1, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by omega)]

#print axioms exists_mul_mod_one


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

/-! ## The irrationality of a prime's square root, at the Nat level

`SqrtTwo.lean` proves `p² = 2q² → q = 0` by descent, with a parity step that
expands `(2r+1)²`. Nothing in that descent is about `2` beyond `2 ≤ 2`: the step
only needs the prime divides `a` when it divides `a²`, which is Euclid's lemma
with both factors the same. Stated that way the argument runs for every prime,
which is the generality `Nat.Prime.irrational_sqrt` has. -/

/-- `(n·c)² = n²·c²`, the shape the descent rewrites through. This is
`SqrtTwo.lean`'s `four_sq` with the `2` released: the same five rewrites, none
of them about `2`. -/
private theorem nat_sq_mul_sq (n c : Nat) : (n * c) * (n * c) = n * n * (c * c) := by
  rw [Nat.mul_assoc, ← Nat.mul_assoc c n c, Nat.mul_comm c n, Nat.mul_assoc,
    ← Nat.mul_assoc]

/-- A prime divides a square only by dividing its root. Euclid's lemma with
both factors the same. -/
theorem prime_divides_sq {n a : Nat} (hn : IsPrime n) (h : Divides n (a * a)) :
    Divides n a :=
  (prime_divides_mul hn h).elim id id

#print axioms prime_divides_sq

/-- The irrationality of `√n` for every prime `n`, with no reals in the
statement: `a² = n·b²` forces `b = 0`.

The descent is the one `sq_two_irrational` runs. Where `2 ∣ a²` gave `2 ∣ a` by
an expansion of `(2r+1)²`, `prime_divides_sq` gives `n ∣ a` for any prime, and
the only other use of the modulus is `2 ≤ n`, which every prime satisfies. -/
theorem prime_sq_irrational {n : Nat} (hn : IsPrime n) :
    ∀ a b : Nat, a * a = n * (b * b) → b = 0 := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
    intro b hab
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · rfl
    · exfalso
      have hn2 : 2 ≤ n := hn.left
      have hbb : 0 < b * b := Nat.mul_pos hb hb
      -- `n` divides `a²`, hence `a`; write `a = n·c`
      obtain ⟨c, hc⟩ : Divides n a := prime_divides_sq hn ⟨b * b, hab⟩
      -- and then `b² = n·c²`, the same equation one step down
      have hbc : b * b = n * (c * c) := by
        have h1 : n * n * (c * c) = n * (b * b) := by
          rw [← nat_sq_mul_sq, ← hc]; exact hab
        have h2 : n * (n * (c * c)) = n * (b * b) := by
          rw [← Nat.mul_assoc]; exact h1
        exact (Nat.eq_of_mul_eq_mul_left (by omega) h2).symm
      -- the descent step: `b < a`, because `n ≥ 2` makes `a²` exceed `b²`
      have hba : b < a := by
        rcases Nat.lt_or_ge b a with h | h
        · exact h
        · exfalso
          have h2 : a * a ≤ b * b := Nat.mul_le_mul h h
          have h3 : 2 * (b * b) ≤ n * (b * b) := Nat.mul_le_mul_right _ hn2
          omega
      have hc0 : c = 0 := ih b hba c hbc
      rw [hc0, Nat.zero_mul, Nat.mul_zero] at hbc
      omega

#print axioms prime_sq_irrational

/-! ## Factorization

Lists are core's; the product is not, so it is defined here. Existence is
`minFac` plus strong induction. Uniqueness up to permutation is not proved --
what is proved is its engine, that a prime dividing a product divides one of the
factors, so any two factorizations line up. -/

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

/-- A prime dividing a product divides one of its factors. -/
theorem prime_divides_prodList {p : Nat} (hp : IsPrime p) : ∀ l : List Nat,
    Divides p (prodList l) → ∃ q, q ∈ l ∧ Divides p q
  | [], h => by
    exact absurd (eq_one_of_divides_one h) (by have := hp.left; omega)
  | q :: t, h => by
    rcases prime_divides_mul hp h with hq | ht
    · exact ⟨q, List.mem_cons_self, hq⟩
    · obtain ⟨r, hr, hpr⟩ := prime_divides_prodList hp t ht
      exact ⟨r, List.mem_cons_of_mem q hr, hpr⟩

/-- Primes dividing primes are equal, so the factor found is the prime itself. -/
theorem prime_eq_of_divides {p q : Nat} (hp : IsPrime p) (hq : IsPrime q)
    (h : Divides p q) : p = q := hq.right p hp.left h

/-- The product is a permutation invariant, by induction on the permutation. -/
theorem prodList_perm {l₁ l₂ : List Nat} (h : l₁.Perm l₂) : prodList l₁ = prodList l₂ := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [prodList, ih]
  | swap a b l =>
    simp only [prodList]
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm b a]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- Unique factorisation. Two prime factorizations of the same
number are permutations of each other: Euclid's lemma finds each prime of one
inside the other, and erasing it recurses. -/
theorem factorization_perm : ∀ l₁ l₂ : List Nat,
    (∀ p, p ∈ l₁ → IsPrime p) → (∀ p, p ∈ l₂ → IsPrime p) →
      prodList l₁ = prodList l₂ → l₁.Perm l₂
  | [], l₂, _, h₂, hprod => by
    -- the empty product is `1`, and a prime cannot divide `1`
    cases l₂ with
    | nil => exact List.Perm.refl []
    | cons q t =>
      exfalso
      have hq : IsPrime q := h₂ q List.mem_cons_self
      simp only [prodList] at hprod
      have := eq_one_of_divides_one ⟨prodList t, hprod⟩
      have := hq.left
      omega
  | p :: t, l₂, h₁, h₂, hprod => by
    have hp : IsPrime p := h₁ p List.mem_cons_self
    have hpdvd : Divides p (prodList l₂) := by
      rw [← hprod]
      exact ⟨prodList t, rfl⟩
    obtain ⟨q, hq, hpq⟩ := prime_divides_prodList hp l₂ hpdvd
    have hqp : p = q := prime_eq_of_divides hp (h₂ q hq) hpq
    subst hqp
    -- move `p` to the front of `l₂` and cancel it
    have hperm := perm_cons_erase' p l₂ hq
    have hprod' : prodList l₂ = p * prodList (l₂.erase p) := by
      rw [prodList_perm hperm]
      rfl
    rw [hprod'] at hprod
    simp only [prodList] at hprod
    have hp0 : 0 < p := by have := hp.left; omega
    have hcancel : prodList t = prodList (l₂.erase p) :=
      Nat.eq_of_mul_eq_mul_left hp0 hprod
    have hrec := factorization_perm t (l₂.erase p)
      (fun r hr => h₁ r (List.mem_cons_of_mem p hr))
      (fun r hr => h₂ r (List.mem_of_mem_erase hr)) hcancel
    exact List.Perm.trans (List.Perm.cons p hrec) (List.Perm.symm hperm)

/-! ## Inside the theory

`ofNat` carries `+` and `×`, so divisibility and primality read
across to `ω` unchanged. -/

def DividesSet (d n : ZFSet.{u}) : Prop := ∃ k, k ∈ omega.{u} ∧ n = mul d k

/-! ## Prime powers

What separates two numbers when one does not divide the other: some prime power
divides the first and not the second. The witness is produced by an induction
through `minFac`, not by contraposing a `∀`, so nothing here is classical. -/

theorem prime_divides_pow {p q : Nat} (hp : IsPrime p) (hq : IsPrime q) :
    ∀ k : Nat, Divides p (q ^ k) → p = q
  | 0, hd => by
    have := hp.left
    have h1 : q ^ 0 = 1 := rfl
    rw [h1] at hd
    exact absurd (eq_one_of_divides_one hd) (by omega)
  | k + 1, hd => by
    have hstep : Divides p (q ^ k * q) := hd
    rcases prime_divides_mul hp hstep with h | h
    · exact prime_divides_pow hp hq k h
    · exact prime_eq_of_divides hp hq h

/-- A prime power and a number the prime misses are coprime. -/
theorem gcd_prime_pow_eq_one {p z : Nat} (hp : IsPrime p) (hz : ¬ Divides p z) (k : Nat) :
    Nat.gcd (p ^ k) z = 1 := by
  have hp2 := hp.left
  have hpow : 0 < p ^ k := Nat.pow_pos (by omega)
  have hg : Divides (Nat.gcd (p ^ k) z) (p ^ k) := Nat.gcd_dvd_left _ _
  rcases Nat.lt_or_ge (Nat.gcd (p ^ k) z) 2 with hlt | hge
  · rcases Nat.eq_zero_or_pos (Nat.gcd (p ^ k) z) with h0 | h1
    · exfalso
      obtain ⟨w, hw⟩ := hg
      rw [h0, Nat.zero_mul] at hw
      omega
    · omega
  · exfalso
    have hfac : IsPrime (minFac (Nat.gcd (p ^ k) z)) := isPrime_minFac hge
    have hdiv : Divides (minFac (Nat.gcd (p ^ k) z)) (p ^ k) :=
      divides_trans (minFac_divides hge) hg
    have hpe : minFac (Nat.gcd (p ^ k) z) = p := prime_divides_pow hfac hp k hdiv
    have hstep := minFac_divides hge
    rw [hpe] at hstep
    exact hz (divides_trans hstep (Nat.gcd_dvd_right (p ^ k) z : Divides _ z))


/-- Splitting off the `p`-part. -/
theorem prime_pow_split {p : Nat} (hp : IsPrime p) :
    ∀ n : Nat, 0 < n → ∃ k z : Nat, 0 < z ∧ n = p ^ k * z ∧ ¬ Divides p z := by
  have hp2 := hp.left
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    rcases Nat.decEq (n % p) 0 with hne | heq
    · exact ⟨0, n, hn, by rw [Nat.pow_zero, Nat.one_mul], fun hd =>
        hne (mod_eq_zero_of_divides hd)⟩
    · obtain ⟨w, hw⟩ := divides_of_mod_eq_zero heq
      have hwpos : 0 < w := by
        rcases Nat.eq_zero_or_pos w with rfl | h
        · rw [Nat.mul_zero] at hw
          omega
        · exact h
      have hlt : w < n := by
        rcases Nat.lt_or_ge w n with h | h
        · exact h
        · have h1 : p * w ≥ p * n := Nat.mul_le_mul_left p h
          have h2 : 2 * n ≤ p * n := Nat.mul_le_mul_right n hp2
          omega
      obtain ⟨k, z, hzpos, hz, hnd⟩ := ih w hlt hwpos
      refine ⟨k + 1, z, hzpos, ?_, hnd⟩
      rw [hw, hz, Nat.pow_succ]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- A failure to divide is witnessed by a prime power. -/
theorem exists_prime_pow_not_divides : ∀ r : Nat, 0 < r → ∀ m : Nat, 0 < m →
    ¬ Divides r m → ∃ p k : Nat, IsPrime p ∧ Divides (p ^ k) r ∧ ¬ Divides (p ^ k) m := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro hr m hm hnd
    rcases Nat.lt_or_ge r 2 with hlt | hge
    · obtain rfl : r = 1 := by omega
      exact absurd (one_divides m) hnd
    · have hp0 : IsPrime (minFac r) := isPrime_minFac hge
      obtain ⟨r₁, hr₁0⟩ : Divides (minFac r) r := minFac_divides hge
      -- the prime is opaque from here, so rewriting `r` cannot reach inside `minFac`
      obtain ⟨p, hpdef⟩ : ∃ p, minFac r = p := ⟨_, rfl⟩
      rw [hpdef] at hp0 hr₁0
      have hp := hp0
      have hr₁ := hr₁0
      have hp2 := hp.left
      have hr₁pos : 0 < r₁ := by
        rcases Nat.eq_zero_or_pos r₁ with rfl | h
        · rw [Nat.mul_zero] at hr₁
          omega
        · exact h
      rcases Nat.decEq (m % p) 0 with hnodiv | hdiv
      · -- the prime itself already fails to divide `m`
        refine ⟨p, 1, hp, ?_, ?_⟩
        · rw [Nat.pow_one]
          exact ⟨r₁, hr₁⟩
        · rw [Nat.pow_one]
          exact fun hd => hnodiv (mod_eq_zero_of_divides hd)
      · obtain ⟨m₁, hm₁⟩ := divides_of_mod_eq_zero hdiv
        have hm₁pos : 0 < m₁ := by
          rcases Nat.eq_zero_or_pos m₁ with rfl | h
          · rw [Nat.mul_zero] at hm₁
            omega
          · exact h
        have hlt : r₁ < r := by
          rcases Nat.lt_or_ge r₁ r with h | h
          · exact h
          · have h1 : p * r ≤ p * r₁ := Nat.mul_le_mul_left _ h
            have h2 : 2 * r ≤ p * r := Nat.mul_le_mul_right r hp2
            omega
        have hnd₁ : ¬ Divides r₁ m₁ := by
          intro ⟨y, hy⟩
          refine hnd ⟨y, ?_⟩
          rw [hm₁, hy, hr₁]
          simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        obtain ⟨q, k, hq, hqr, hqm⟩ := ih r₁ hlt hr₁pos m₁ hm₁pos hnd₁
        rcases Nat.decEq q p with hne | rfl
        · -- a different prime: cancelling `minFac r` cannot have helped
          refine ⟨q, k, hq, divides_trans hqr ⟨p, by rw [hr₁]; simp [Nat.mul_comm]⟩,
            fun hd => hqm ?_⟩
          obtain ⟨w, hw⟩ := hd
          refine coprime_divides
            (gcd_prime_pow_eq_one hq (fun hdd => hne (prime_eq_of_divides hq hp hdd)) k)
            ⟨w, ?_⟩
          rw [← hm₁]
          exact hw
        · -- the same prime: one more power
          refine ⟨q, k + 1, hq, ?_, fun hd => hqm ?_⟩
          · obtain ⟨w, hw⟩ := hqr
            exact ⟨w, by rw [hr₁, hw, Nat.pow_succ]; simp [Nat.mul_comm, Nat.mul_left_comm,
              Nat.mul_assoc]⟩
          · obtain ⟨w, hw⟩ := hd
            refine ⟨w, ?_⟩
            have hstep : q * m₁ = q * (q ^ k * w) := by
              rw [← hm₁, hw, Nat.pow_succ]
              simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
            exact Nat.eq_of_mul_eq_mul_left (by omega) hstep

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


/-- The falling product on naturals, peeling the FIRST factor:
`i * (i-1) * ... * (i-k+1)`.

Peeled at the front rather than the back so it matches `succ_mul_choose`, which
is the only absorption identity the tree carries. Defining it the other way makes
the induction want `choose i (k+1) * (k+1) = choose i k * (i-k)`, which is true
and is NOT what is available. -/
def fallNat : Nat → Nat → Nat
  | _, 0 => 1
  | i, k + 1 => i * fallNat (i - 1) k

/-- `C(i,k) * k! = i(i-1)...(i-k+1)`.

The arithmetic core of the binomial polynomial: it says `C(x,k)` evaluated at a
natural `i` really is the NUMBER `C(i,k)`, once the falling product is divided by
`k!`. Everything else about `C(x,k)` is ring bookkeeping; this is the content. -/
theorem choose_mul_fact : ∀ (i k : Nat), choose i k * fact k = fallNat i k
  | i, 0 => by
    show choose i 0 * 1 = 1
    rw [choose_zero]
  | 0, k + 1 => by
    show choose 0 (k + 1) * fact (k + 1) = 0 * fallNat 0 k
    rw [choose_gt 0 (k + 1) (by omega), Nat.zero_mul, Nat.zero_mul]
  | i + 1, k + 1 => by
    show choose (i + 1) (k + 1) * fact (k + 1) = (i + 1) * fallNat i k
    rw [← choose_mul_fact i k]
    -- fact (k+1) is (k+1) * fact k, and succ_mul_choose absorbs the (k+1)
    show choose (i + 1) (k + 1) * ((k + 1) * fact k) = _
    rw [← Nat.mul_assoc, ← succ_mul_choose i k, Nat.mul_assoc]


/-- The falling product peels from the BACK as well as the front:
`fallNat i (k+1) = fallNat i k * (i - k)`.

Both forms are needed and neither is definitional. `choose_mul_fact` wants the
FRONT peel, because `succ_mul_choose` absorbs at the front; a `foldF` over
`j < k` produces the BACK peel, because that is the order a fold visits. This is
the bridge, and the induction runs at `i - 1` rather than at `i`. -/
theorem fallNat_succ_back : ∀ (i k : Nat), k ≤ i →
    fallNat i (k + 1) = fallNat i k * (i - k)
  | i, 0, _ => by
    show i * fallNat (i - 1) 0 = 1 * (i - 0)
    show i * 1 = 1 * (i - 0)
    omega
  | i, k + 1, hk => by
    have hik : k ≤ i - 1 := by omega
    show i * fallNat (i - 1) (k + 1) = (i * fallNat (i - 1) k) * (i - (k + 1))
    rw [fallNat_succ_back (i - 1) k hik, Nat.mul_assoc]
    congr 1
    congr 1
    omega

/-- `fallNat n k · (n-k)! = n!` for `k <= n` --- the falling product times
what it left behind. -/
theorem fallNat_mul_fact : ∀ (n k : Nat), k ≤ n → fallNat n k * fact (n - k) = fact n
  | n, 0, _ => by
    show 1 * fact (n - 0) = fact n
    rw [Nat.one_mul, Nat.sub_zero]
  | n, k + 1, hk => by
    have hkn : k ≤ n := by omega
    have hstep : fact (n - k) = (n - k) * fact (n - (k + 1)) := by
      obtain ⟨d, hd⟩ : ∃ d, n - k = d + 1 := ⟨n - k - 1, by omega⟩
      rw [hd, show n - (k + 1) = d by omega]
      rfl
    rw [fallNat_succ_back n k hkn, Nat.mul_assoc, ← hstep]
    exact fallNat_mul_fact n k hkn

/-- `C(n,k) · k! · (n-k)! = n!` for `k <= n`.

The bridge between the BINOMIAL form of the Bernoulli recursion
(`sum_k choose (n+1) k * B_k = 0`) and the CONVOLUTION form a generating
function speaks (`sum_k B_k/(k! (n-k+1)!)`). -/
theorem choose_mul_fact_mul_fact (n k : Nat) (hk : k ≤ n) :
    choose n k * (fact k * fact (n - k)) = fact n := by
  rw [← Nat.mul_assoc, choose_mul_fact n k]
  exact fallNat_mul_fact n k hk

#print axioms fallNat_succ_back
#print axioms choose_mul_fact
#print axioms fallNat_mul_fact
#print axioms choose_mul_fact_mul_fact
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
divisors of `d`, and `∑_{e ∣ d, e < d} q^e < q^d`, so the count
of degree-`d` irreducibles is positive. -/

/-- `[m, m-1, …, 1]`. -/
def upto : Nat → List Nat
  | 0 => []
  | m + 1 => (m + 1) :: upto m

def sumOver (g : Nat → Nat) : List Nat → Nat
  | [] => 0
  | e :: es => g e + sumOver g es

/-- A zero remainder is a divisibility. -/
theorem dvd_of_mod_zero {a d : Nat} (h : a % d = 0) : Divides d a := by
  refine ⟨a / d, ?_⟩
  have hs := Nat.div_add_mod a d
  omega

/-- The shifted cyclotomic polynomial satisfies Eisenstein's conditions at
`p`.

`Φp(x+1) = ((x+1)^p - 1)/x`, so its coefficient of `x^j` is `C(p, j+1)`. The
three Eisenstein hypotheses are then binomial facts:

* every coefficient below the top is divisible by `p` -- `prime_dvd_choose`;
* the top one is `C(p,p) = 1`, which `p` does not divide;
* the constant term is `C(p,1) = p`, which `p²` does not divide.

Stated over the coefficient FUNCTION rather than over a polynomial object,
because the substitution `x → x+1` does not exist in this tree and is not
needed to state the conditions -- only to transfer the resulting irreducibility
back to `Φp` itself, which is a separate rung. -/
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

/-- The proper divisors of `d`, which are exactly the divisors at most `d/2`. -/
def divisorsBelow (d : Nat) : List Nat := (upto (d / 2)).filter (fun e => d % e == 0)

#print axioms isPrime_minFac
#print axioms bezout
#print axioms bezout_int
#print axioms prime_divides_mul
#print axioms coprime_divides
#print axioms exists_prime_pow_not_divides
#print axioms prime_dvd_choose
#print axioms dvd_of_mod_zero
#print axioms cyclotomicShift_eisenstein
#print axioms exists_factorization
#print axioms factorization_perm
#print axioms prime_divides_prodList
#print axioms exists_prime_gt
/-! ### Summing over the indices, continued

Additivity, vanishing and congruence for `sumOver`. -/

theorem sumOver_add (g h : Nat → Nat) :
    ∀ l : List Nat, sumOver (fun i => g i + h i) l = sumOver g l + sumOver h l
  | [] => rfl
  | e :: es => by
    show g e + h e + sumOver (fun i => g i + h i) es = _
    rw [sumOver_add g h es]
    show _ = (g e + sumOver g es) + (h e + sumOver h es)
    omega

theorem sumOver_zero {g : Nat → Nat} :
    ∀ l : List Nat, (∀ e, e ∈ l → g e = 0) → sumOver g l = 0
  | [], _ => rfl
  | e :: es, h => by
    show g e + sumOver g es = 0
    rw [h e (List.Mem.head _), sumOver_zero es (fun x hx => h x (List.Mem.tail _ hx))]

theorem sumOver_congr {g h : Nat → Nat} :
    ∀ l : List Nat, (∀ e, e ∈ l → g e = h e) → sumOver g l = sumOver h l
  | [], _ => rfl
  | e :: es, hgh => by
    show g e + sumOver g es = h e + sumOver h es
    rw [hgh e (List.Mem.head _),
      sumOver_congr es (fun x hx => hgh x (List.Mem.tail _ hx))]

#print axioms sumOver_add
#print axioms sumOver_zero
#print axioms sumOver_congr

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

def add (x y : Eis) : Eis := ⟨x.re + y.re, x.im + y.im⟩
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
variables appear -- no numeral is multiplied into a product, so
`omega` finishes from here treating each product as an atom. -/
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

theorem mul_one (x : Eis) : mul x one = x := by
  simp [mul, one]

theorem mul_assoc (x y z : Eis) : mul (mul x y) z = mul x (mul y z) := by
  simp [mul, Int.sub_mul, Int.mul_sub, Int.mul_add, Int.add_mul,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  exact ⟨by omega, by omega⟩

theorem norm_one : norm one = 1 := by simp [norm, one]

/-- A unit has norm `1`. The converse holds too, and this direction is the
one a descent needs: a factor of norm `1` is not a proper factor. -/
theorem norm_eq_one_of_unit {x y : Eis} (h : mul x y = one) : norm x = 1 := by
  have hn : norm x * norm y = 1 := by rw [← norm_mul, h, norm_one]
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  rcases Int.lt_or_le (norm x) 2 with hlt | hge
  · rcases Int.lt_or_le (norm x) 1 with h0 | h1
    · have : norm x = 0 := by omega
      rw [this] at hn; omega
    · omega
  · rcases Int.lt_or_le (norm y) 1 with h0 | h1
    · have : norm y = 0 := by omega
      rw [this] at hn; omega
    · have := Int.mul_le_mul hge h1 (by omega) (by omega)
      omega

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

/-! ### Division with remainder

`ℤ[ω]` is Euclidean for the norm. To divide `x` by `y` one takes `x * conj y`,
divides both coordinates by `N(y)` with ROUNDING, and the error is a lattice
point at distance under `1` from an arbitrary point of the plane -- the
hexagonal covering radius. In coordinates that is the bound below, proved as an
inequality on integers rather than as geometry.

`roundDiv n d` is `n / d` rounded to the nearest integer, written as a floor of
`n + d/2` so that no case split on signs is needed. -/

def roundDiv (n d : Int) : Int := (2 * n + d) / (2 * d)

/-- The rounding error is at most half the divisor, in the form the norm bound
needs: `2 * |n - d * roundDiv n d| <= d`. -/
theorem roundDiv_error {n d : Int} (hd : 0 < d) :
    2 * (n - d * roundDiv n d) <= d ∧ -(d) <= 2 * (n - d * roundDiv n d) := by
  have h2d : 0 < 2 * d := by omega
  have hq := Int.mul_ediv_add_emod (2 * n + d) (2 * d)
  have hr0 : 0 <= (2 * n + d) % (2 * d) := Int.emod_nonneg _ (by omega)
  have hr1 : (2 * n + d) % (2 * d) < 2 * d := Int.emod_lt_of_pos _ h2d
  have hunfold : roundDiv n d = (2 * n + d) / (2 * d) := rfl
  have hassoc : 2 * (d * ((2 * n + d) / (2 * d)))
      = 2 * d * ((2 * n + d) / (2 * d)) := (Int.mul_assoc 2 d _).symm
  rw [hunfold]
  exact ⟨by omega, by omega⟩

/-- `|A| <= N` gives `A² <= N²`, by cases on the sign. -/
private theorem sq_le_sq {A N : Int} (h1 : -N <= A) (h2 : A <= N) :
    A * A <= N * N := by
  rcases Int.lt_or_le A 0 with h | h
  · have hm := Int.mul_le_mul (a := -A) (b := -A) (c := N) (d := N)
      (by omega) (by omega) (by omega) (by omega)
    rw [Int.neg_mul_neg] at hm
    exact hm
  · exact Int.mul_le_mul h2 h2 h (by omega)

/-- `|A| <= N` and `|B| <= N` give `-(AB) <= N²`, by cases on the two signs. -/
private theorem neg_mul_le {A B N : Int} (hA : -N <= A) (hA' : A <= N)
    (hB : -N <= B) (hB' : B <= N) : -(A * B) <= N * N := by
  rcases Int.lt_or_le A 0 with ha | ha
  · rcases Int.lt_or_le B 0 with hb | hb
    · have hp : 0 <= A * B := by
        rw [← Int.neg_mul_neg]
        exact Int.mul_nonneg (by omega) (by omega)
      have hn : 0 <= N * N := Int.mul_nonneg (by omega) (by omega)
      omega
    · have hm := Int.mul_le_mul (a := -A) (b := B) (c := N) (d := N)
        (by omega) hB' hb (by omega)
      rw [Int.neg_mul] at hm
      omega
  · rcases Int.lt_or_le B 0 with hb | hb
    · have hm := Int.mul_le_mul (a := A) (b := -B) (c := N) (d := N)
        hA' (by omega) (by omega) (by omega)
      rw [Int.mul_neg] at hm
      omega
    · have hm : 0 <= A * B := Int.mul_nonneg ha hb
      have hn : 0 <= N * N := Int.mul_nonneg (by omega) (by omega)
      omega

/-- The covering bound. With both coordinates of the error inside half the
divisor, the error's norm is at most three quarters of the divisor's square --
strictly less, which is what a Euclidean algorithm needs. `3/4` rather than
`1/2` is the hexagonal lattice showing through: the `-ab` term is what costs the
extra quarter, and it is still under `1`. -/
theorem norm_error_bound {e : Eis} {N : Int}
    (h1 : -N <= 2 * e.re) (h2 : 2 * e.re <= N)
    (h3 : -N <= 2 * e.im) (h4 : 2 * e.im <= N) :
    4 * norm e <= 3 * (N * N) := by
  -- `a` and `b` are BOUND here rather than instantiated, so `omega` sees three
  -- clean atoms rather than three spellings of each numeral-scaled product.
  have key : ∀ a b : Int, -N <= 2 * a -> 2 * a <= N -> -N <= 2 * b -> 2 * b <= N ->
      4 * (a * a - a * b + b * b) <= 3 * (N * N) := by
    intro a b p1 p2 p3 p4
    have ha := sq_le_sq p1 p2
    have hb := sq_le_sq p3 p4
    have hc := neg_mul_le p1 p2 p3 p4
    have hcm : a * b = b * a := Int.mul_comm a b
    have e1 : (2 * a) * (2 * a) = 4 * (a * a) := by
      rw [Int.mul_assoc, Int.mul_comm a (2 * a), Int.mul_assoc, Int.mul_comm a a]
      omega
    have e2 : (2 * a) * (2 * b) = 4 * (a * b) := by
      rw [Int.mul_assoc, Int.mul_comm a (2 * b), Int.mul_assoc]
      omega
    have e3 : (2 * b) * (2 * b) = 4 * (b * b) := by
      rw [Int.mul_assoc, Int.mul_comm b (2 * b), Int.mul_assoc, Int.mul_comm b b]
      omega
    omega
  have hk := key e.re e.im h1 h2 h3 h4
  have hn : norm e = e.re * e.re - e.re * e.im + e.im * e.im := rfl
  omega

/-! ### The Euclidean property

`x = q·y + r` with `N(r) < N(y)`. The quotient rounds `x·conj y` coordinatewise
by `N(y)`; the remainder's norm then satisfies `N(r)·N(y) = N(x·conj y - N(y)·q)`,
which the covering bound puts under `N(y)²`. -/

def sub (x y : Eis) : Eis := ⟨x.re - y.re, x.im - y.im⟩

def div (x y : Eis) : Eis :=
  ⟨roundDiv (mul x (conj y)).re (norm y), roundDiv (mul x (conj y)).im (norm y)⟩

def mod (x y : Eis) : Eis := sub x (mul (div x y) y)

theorem sub_mul (a b c : Eis) : mul (sub a b) c = sub (mul a c) (mul b c) := by
  simp [sub, mul, Int.sub_mul]
  exact ⟨by omega, by omega⟩

theorem mul_ofInt (a : Eis) (n : Int) : mul a (ofInt n) = ⟨a.re * n, a.im * n⟩ := by
  simp [mul, ofInt]

theorem mod_add_div (x y : Eis) : sub x (mod x y) = mul (div x y) y := by
  simp [mod, sub, Int.sub_sub_self]

/-- The remainder times the conjugate of the divisor is exactly the pair of
rounding errors -- which is the identity the whole Euclidean argument turns on:
it converts a statement about `ℤ[ω]` into two statements about `Int` division. -/
theorem mod_mul_conj (x y : Eis) :
    mul (mod x y) (conj y)
      = ⟨(mul x (conj y)).re - (div x y).re * norm y,
         (mul x (conj y)).im - (div x y).im * norm y⟩ := by
  rw [mod, sub_mul, mul_assoc, mul_conj, mul_ofInt]
  simp [sub]

/-- `ℤ[ω]` is Euclidean for the norm. The remainder of `x` by a non-zero `y`
has strictly smaller norm.

The chain: `r · conj y` has the two rounding errors as its coordinates, so the
covering bound gives `4 N(r · conj y) <= 3 N(y)²`; and `N` is multiplicative
with `N(conj y) = N(y)`, so `4 N(r) N(y) <= 3 N(y)²`. With `N(y) > 0` that
forces `N(r) < N(y)`. -/
theorem norm_mod_lt {x y : Eis} (hy : 0 < norm y) : norm (mod x y) < norm y := by
  have hcoord := mod_mul_conj x y
  have hre := roundDiv_error (n := (mul x (conj y)).re) (d := norm y) hy
  have him := roundDiv_error (n := (mul x (conj y)).im) (d := norm y) hy
  have hre_eq : (mul (mod x y) (conj y)).re
      = (mul x (conj y)).re - norm y * roundDiv (mul x (conj y)).re (norm y) := by
    rw [hcoord]
    show (mul x (conj y)).re - (div x y).re * norm y
       = (mul x (conj y)).re - norm y * roundDiv (mul x (conj y)).re (norm y)
    rw [Int.mul_comm (norm y)]
    rfl
  have him_eq : (mul (mod x y) (conj y)).im
      = (mul x (conj y)).im - norm y * roundDiv (mul x (conj y)).im (norm y) := by
    rw [hcoord]
    show (mul x (conj y)).im - (div x y).im * norm y
       = (mul x (conj y)).im - norm y * roundDiv (mul x (conj y)).im (norm y)
    rw [Int.mul_comm (norm y)]
    rfl
  have hb1l : -(norm y) <= 2 * (mul (mod x y) (conj y)).re := by
    rw [hre_eq]; omega
  have hb1r : 2 * (mul (mod x y) (conj y)).re <= norm y := by
    rw [hre_eq]; omega
  have hb2l : -(norm y) <= 2 * (mul (mod x y) (conj y)).im := by
    rw [him_eq]; omega
  have hb2r : 2 * (mul (mod x y) (conj y)).im <= norm y := by
    rw [him_eq]; omega
  have hbound := norm_error_bound hb1l hb1r hb2l hb2r
  rw [norm_mul, norm_conj] at hbound
  have hnr := norm_nonneg (mod x y)
  rcases Int.lt_or_le (norm (mod x y)) (norm y) with h | h
  · exact h
  · exfalso
    have hstep : norm y * norm y <= norm (mod x y) * norm y :=
      Int.mul_le_mul h (by omega) (by omega) (by omega)
    have hpos : 0 < norm y * norm y := Int.mul_pos hy hy
    omega

/-! ### `λ = 1 - ω`, the ramified prime above 3

`N(λ) = 3`, and `3 = -ω² λ²` up to a unit: the rational prime `3` ramifies. The
descent for `n = 3` is a descent on the power of `λ` dividing one of the three
terms, so this element and not `3` is the right object. -/

def lam : Eis := ⟨1, -1⟩

/-- `(2a - b)² + 3b² = 4(a² - ab + b²)`, the identity every coordinate bound
here comes from. The form is symmetric in `a` and `b`, so instantiating it both
ways bounds both coordinates. -/
private theorem four_norm_form (a b : Int) :
    (2 * a - b) * (2 * a - b) + 3 * (b * b) = 4 * (a * a - a * b + b * b) := by
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
  have hcm : b * a = a * b := Int.mul_comm b a
  have h2 : 2 * a * (2 * a) = 4 * (a * a) := by
    rw [Int.mul_assoc, Int.mul_comm a (2 * a), Int.mul_assoc, Int.mul_comm a a]
    omega
  have h3 : 2 * a * b = 2 * (a * b) := by rw [Int.mul_assoc]
  have h4 : b * (2 * a) = 2 * (a * b) := by
    rw [Int.mul_comm b (2 * a), Int.mul_assoc]
  omega

/-! ### Divisibility, and the descent the Euclidean property licenses

`norm_mod_lt` makes the norm a strictly decreasing measure, so any argument that
replaces a pair by `(y, x mod y)` terminates. That is stated here as a strong
induction on the norm rather than as a greatest-common-divisor function,
because what the
factorisation argument needs is the INDUCTION and not the algorithm. -/

def Dvd (d x : Eis) : Prop := ∃ k : Eis, x = mul d k

theorem dvd_refl (x : Eis) : Dvd x x := ⟨one, (mul_one x).symm⟩

theorem dvd_zero (x : Eis) : Dvd x zero := ⟨zero, by simp [mul, zero]⟩

theorem dvd_trans {a b c : Eis} (h1 : Dvd a b) (h2 : Dvd b c) : Dvd a c := by
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨l, rfl⟩ := h2
  exact ⟨mul k l, mul_assoc a k l⟩

/-- Descent on the norm. Anything true of `y` and `x mod y` whenever it is
true one step down is true everywhere -- which is the Euclidean algorithm's
termination, with no algorithm written. -/
theorem norm_induction {P : Eis -> Prop}
    (step : ∀ y : Eis, (∀ z : Eis, norm z < norm y -> P z) -> P y) :
    ∀ y : Eis, P y := by
  have key : ∀ n : Nat, ∀ y : Eis, norm y < (n : Int) -> P y := by
    intro n
    induction n with
    | zero => intro y hy; exact absurd hy (by have := norm_nonneg y; omega)
    | succ m ih =>
      intro y hy
      refine step y (fun z hz => ih z ?_)
      have := norm_nonneg z
      omega
  intro y
  obtain ⟨n, hn⟩ : ∃ n : Nat, norm y < (n : Int) := by
    refine ⟨(norm y).toNat + 1, ?_⟩
    have h := norm_nonneg y
    omega
  exact key n y hn

theorem dvd_add {d a b : Eis} (h1 : Dvd d a) (h2 : Dvd d b) : Dvd d (add a b) := by
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨l, rfl⟩ := h2
  refine ⟨add k l, ?_⟩
  simp [add, mul, Int.mul_add, Int.add_mul]
  exact ⟨by omega, by omega⟩

theorem add_sub_cancel (x r : Eis) : add (sub x r) r = x := by
  simp [add, sub]

/-- Bezout for `ℤ[ω]`. A common divisor of `x` and `y` that is itself a
combination of them -- proved by the norm descent, so the algorithm is never
written down and no choice is made.

The recursion is the Euclidean one: `gcd(x, y)` becomes `gcd(y, x mod y)`, and
`norm_mod_lt` is what makes that terminate. -/
theorem bezout : ∀ y x : Eis, ∃ g : Eis,
    Dvd g x ∧ Dvd g y ∧ ∃ s t : Eis, g = add (mul x s) (mul y t) := by
  refine norm_induction (P := fun y => ∀ x : Eis, ∃ g : Eis,
    Dvd g x ∧ Dvd g y ∧ ∃ s t : Eis, g = add (mul x s) (mul y t)) ?_
  intro y ih x
  rcases Int.lt_or_le 0 (norm y) with hy | hy
  · obtain ⟨g, hgy, hgm, s, t, hst⟩ := ih (mod x y) (norm_mod_lt (x := x) hy) y
    refine ⟨g, ?_, hgy, ?_⟩
    · have hx : x = add (mul (div x y) y) (mod x y) := by
        rw [← mod_add_div x y, add_sub_cancel]
      rw [hx]
      exact dvd_add (dvd_trans hgy ⟨div x y, mul_comm (div x y) y⟩) hgm
    · refine ⟨t, sub s (mul (div x y) t), ?_⟩
      rw [hst, mod]
      simp [add, sub, mul, Int.mul_sub, Int.sub_mul, Int.mul_add, Int.add_mul,
        Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      exact ⟨by omega, by omega⟩
  · have hz : y = zero := by
      have h0 : norm y = 0 := by have := norm_nonneg y; omega
      obtain ⟨h1, h2⟩ := norm_eq_zero h0
      obtain ⟨a, b⟩ := y
      simp at h1 h2
      simp [zero, h1, h2]
    exact ⟨x, dvd_refl x, by rw [hz]; exact dvd_zero x,
      one, zero, by rw [mul_one]; simp [add, mul, zero]⟩

/-! ### Euclid's lemma, and primality by norm

A `λ` that divides a product divides a factor. With Bezout in hand that is the
usual two lines, and it is the last general fact the `n = 3` descent needs
before the descent itself. -/

def IsUnit (u : Eis) : Prop := ∃ v : Eis, mul u v = one

/-- Norm `1` IS the unit condition, not just a consequence of it: `x · conj x`
is `N(x)`, so an element of norm `1` has its own conjugate as an inverse. -/
theorem isUnit_of_norm_eq_one {x : Eis} (h : norm x = 1) : IsUnit x :=
  ⟨conj x, by rw [mul_conj, h]; rfl⟩

/-! ### Cubes modulo `λ⁴`

The `n = 3` descent turns on one congruence: a cube prime to `λ` is `±1` modulo
`λ⁴`. That is the Eisenstein analogue of cubes are `0, ±1` mod `9` -- indeed
`λ⁴` has norm `81` and `9` is `-ω²λ²` up to a unit -- and it rules out a
sum of three such cubes.

The residues are recorded here as a divisibility statement rather than as a
quotient ring, so nothing is constructed that a descent does not use. -/

/-- `λ` divides `a + bω` exactly when `3` divides `a + b`.

Mod `λ` we have `ω ≡ 1`, so `a + bω ≡ a + b`; and the rational integers `λ`
divides are exactly the multiples of `3`. Both directions are computations:
`λ·(c + dω) = (c + d) + (2d - c)ω`, whose coordinate sum is `3d`, and
conversely `a + b = 3m` is solved by `c = a - m`, `d = m`.

This makes `λ`-divisibility DECIDABLE by an integer test, turning
the descent's case analysis into arithmetic rather than search. -/
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
#print axioms norm_eq_one_of_unit
#print axioms mul_conj
#print axioms norm_conj
#print axioms eq_zero_of_mul_eq_zero
#print axioms roundDiv_error
#print axioms norm_error_bound
#print axioms sub_mul
#print axioms mod_mul_conj
#print axioms norm_mod_lt
#print axioms dvd_trans
#print axioms norm_induction
#print axioms dvd_add
#print axioms mul_add
#print axioms isUnit_of_norm_eq_one
#print axioms lam_dvd_iff
#print axioms mod_add_div

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

/-! ### Toward unique factorisation

The descent for `n = 3` case II needs each of the three factors to be a unit
times a cube times a power of `λ`, which is unique factorisation. The first half
is that a factorisation exists at all, and the NORM is what makes the recursion
terminate: it is multiplicative, so a proper factor has a strictly smaller one,
and `norm_induction` already turns that into an induction. -/

def IsIrreducible (p : Eis) : Prop :=
  ¬ IsUnit p ∧ ¬ (p.re = 0 ∧ p.im = 0) ∧
    ∀ a b : Eis, p = mul a b → IsUnit a ∨ IsUnit b

/-- A factor of norm one is a unit, so a product of norm one has two. The
step that makes `SplitDecision` unsatisfiable when stated over every element,
and the one an argument by cases on the norm keeps needing. -/
theorem norm_mul_eq_one {a b : Eis} (h : norm a * norm b = 1) :
    norm a = 1 ∧ norm b = 1 := by
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have ha1 : 1 <= norm a := by
    rcases Int.lt_or_le 0 (norm a) with hp | hz
    · omega
    · have h0 : norm a = 0 := by omega
      rw [h0] at h; simp at h
  have hb1 : 1 <= norm b := by
    rcases Int.lt_or_le 0 (norm b) with hp | hz
    · omega
    · have h0 : norm b = 0 := by omega
      rw [h0] at h; simp at h
  have hae : norm a = 1 := by
    rcases Int.lt_or_le 1 (norm a) with hp | hle
    · exfalso
      have hgrow : 2 * norm b <= norm a * norm b :=
        Int.mul_le_mul_of_nonneg_right (by omega) hb
      omega
    · omega
  refine ⟨hae, ?_⟩
  rw [hae] at h
  omega

/-- The decision the factorisation needs, as a HYPOTHESIS rather than an
axiom. Is this element irreducible, or does it split into two non-units?

Taken as a supplied readout in the manner of `DC` and the locators, because the
constructive content is exactly here and hiding it in a `Classical.em` would
put the whole factorisation above the base without a single audit line moving.

The two hypotheses make it satisfiable. Stated over every `x` the
disjunction is FALSE at a unit: `IsIrreducible u` fails on its own first
clause, and `u = a·b` forces `N(a)·N(b) = 1`, hence two units by
`norm_mul_eq_one`. `not_splitDecision_unrestricted` proves that, so the
unrestricted form is a hypothesis nothing can supply, and every theorem
carrying it is vacuous.

It is PROVABLE rather than assumed in this restricted form: a proper factor
of `x` has norm strictly between `1` and `N(x)`, `coord_bounds` puts its
coordinates in a box of side `O(N(x))`, and `dvd_or_not` decides each candidate.
`splitDecision` discharges it. -/
def SplitDecision : Prop :=
  ∀ x : Eis, ¬ IsUnit x -> ¬ (x.re = 0 ∧ x.im = 0) ->
    IsIrreducible x ∨ ∃ a b : Eis, x = mul a b ∧ ¬ IsUnit a ∧ ¬ IsUnit b

/-- The unrestricted split decision is FALSE. Not merely unproved: `one` is
a counterexample, so any theorem taking the unrestricted form as a hypothesis
is vacuously true and measures nothing.

An unsatisfiable hypothesis leaves no mark on an audit line: a vacuous theorem
prints as cleanly as an honest one. -/
theorem not_splitDecision_unrestricted :
    ¬ (∀ x : Eis, IsIrreducible x
        ∨ ∃ a b : Eis, x = mul a b ∧ ¬ IsUnit a ∧ ¬ IsUnit b) := by
  intro h
  rcases h one with hirr | ⟨a, b, hx, ha, hb⟩
  · exact hirr.left ⟨one, mul_one one⟩
  · refine ha (isUnit_of_norm_eq_one ?_)
    have hn : norm a * norm b = 1 := by rw [← norm_mul, ← hx, norm_one]
    exact (norm_mul_eq_one hn).left

/-! ### Discharging the split decision

Deciding irreducibility needs a search, and the search is FINITE:
`4N = (2a - b)² + 3b²` bounds both coordinates of any element by its norm, so
the candidate divisors of `x` live in a box of side `O(√N(x))` and divisibility
inside the box is arithmetic.

A hypothesis that could be a theorem overstates the price. -/

/-- Both coordinates of an element are bounded by its norm: `3b² ≤ 4N` and
`(2a - b)² ≤ 4N`, from the same identity every bound in this file comes from. -/
theorem coord_bounds (x : Eis) :
    3 * (x.im * x.im) <= 4 * norm x
      ∧ (2 * x.re - x.im) * (2 * x.re - x.im) <= 4 * norm x := by
  have h := four_norm_form x.re x.im
  have h1 := int_sq_nonneg (2 * x.re - x.im)
  have h2 := int_sq_nonneg x.im
  have hn : norm x = x.re * x.re - x.re * x.im + x.im * x.im := rfl
  constructor <;> omega

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

/-- A non-unit divisor of `x` other than an associate is PROPER: its norm is
strictly between `1` and `N(x)`. The band the search runs over, stated so the
enumeration has a `Nat` to count.

`1 < N(a)` because `a` is not a unit and not zero; `N(a) < N(x)` because the
cofactor is not a unit either -- which is exactly what "splits into two
non-units" says. -/
theorem norm_band_of_split {x a b : Eis} (h : x = mul a b)
    (ha : ¬ IsUnit a) (hb : ¬ IsUnit b)
    (hx : ¬ (x.re = 0 ∧ x.im = 0)) :
    1 < norm a ∧ norm a < norm x := by
  have hn : norm x = norm a * norm b := by rw [h, norm_mul]
  have ha0 := norm_nonneg a
  have hb0 := norm_nonneg b
  have hane : norm a ≠ 1 := fun he => ha (isUnit_of_norm_eq_one he)
  have hbne : norm b ≠ 1 := fun he => hb (isUnit_of_norm_eq_one he)
  have hxn : norm x ≠ 0 := fun he => hx (norm_eq_zero he)
  have haz : norm a ≠ 0 := by intro he; rw [hn, he] at hxn; simp at hxn
  have hbz : norm b ≠ 0 := by intro he; rw [hn, he] at hxn; simp at hxn
  have hgrow : norm a * 2 <= norm a * norm b :=
    Int.mul_le_mul_of_nonneg_left (by omega) ha0
  exact ⟨by omega, by omega⟩

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

/-! ### The search that discharges the decision

Three facts make the search finite and its inner step free: `norm_band_of_split`
puts a proper factor's norm strictly between `1` and `N(x)`, `coord_bounds`
turns that into a box on the coordinates, and `dvd_iff_norm_dvd_coords` makes
membership a question about two integer remainders.

The enumeration returns a `Bool`, so the outer branch is `Bool.rec` and never
`em`, and no `Classical.em` enters where the audit line would not show it. -/

/-- `c ≤ c·c` and `-(c·c) ≤ c`, for every integer.

Crude: it turns a SQUARE bound into a LINEAR box, which `omega` can carry
through the rest of the argument. A tight bound would need a square root and
buy nothing, since the box only has to be finite. -/
theorem le_sq_self (c : Int) : c <= c * c ∧ -(c * c) <= c := by
  have hsq := int_sq_nonneg c
  constructor
  · rcases Int.lt_or_le 0 c with hp | hz
    · have h1 : c * 1 <= c * c := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      omega
    · omega
  · rcases Int.lt_or_le c 0 with hn | hz
    · -- `(-c)·(-c) = c·c` is spelled out rather than handed to `simp`: the
      -- three core rewrites are certain and the simp set at this point is not.
      have hnn : (-c) * (-c) = c * c := by
        rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      have h1 : (-c) * 1 <= (-c) * (-c) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      rw [hnn] at h1
      omega
    · omega

/-- Both coordinates of a divisor lie in a box of side `4N(x)`. From
`coord_bounds` and `le_sq_self`, with nothing sharp attempted. -/
theorem coord_box {a : Int} {N : Int} (h : a * a <= 4 * N) :
    -(4 * N) <= a ∧ a <= 4 * N := by
  obtain ⟨h1, h2⟩ := le_sq_self a
  exact ⟨by omega, by omega⟩

/-- The candidate test, as a `Bool`. Divisibility by `a` is two integer
remainders (`dvd_iff_norm_dvd_coords`) and the band is two comparisons, so the
whole test decides without a principle. -/
def properTest (x a : Eis) : Bool :=
  decide (1 < norm a) && decide (norm a < norm x)
    && decide ((mul x (conj a)).re % norm a = 0)
    && decide ((mul x (conj a)).im % norm a = 0)

/-- A candidate the test accepts really does split `x` into two non-units. The
cofactor is a non-unit because `N(a) < N(x) = N(a)·N(b)` forces `1 < N(b)`. -/
theorem properTest_sound {x a : Eis} (h : properTest x a = true) :
    ∃ b : Eis, x = mul a b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
  simp only [properTest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, hre⟩, him⟩ := h
  have ha : ¬ (a.re = 0 ∧ a.im = 0) := by
    intro h0
    obtain ⟨p, q⟩ := h0
    have : norm a = 0 := by simp [norm, p, q]
    omega
  have hd := Int.mul_ediv_add_emod (mul x (conj a)).re (norm a)
  have he := Int.mul_ediv_add_emod (mul x (conj a)).im (norm a)
  rw [hre, Int.add_zero] at hd
  rw [him, Int.add_zero] at he
  obtain ⟨b, hb⟩ := (dvd_iff_norm_dvd_coords ha).mpr
    ⟨⟨(mul x (conj a)).re / norm a, hd.symm⟩,
     ⟨(mul x (conj a)).im / norm a, he.symm⟩⟩
  refine ⟨b, hb, ?_, ?_⟩
  · -- The witness of an `IsUnit` is extracted by the eliminator. Reaching for
    -- `Exists.choose` instead would put `Classical.choice` on every theorem
    -- downstream of the search.
    intro hu
    obtain ⟨v, hv⟩ := hu
    have := norm_eq_one_of_unit hv
    omega
  · intro hu
    obtain ⟨v, hv⟩ := hu
    have hbn : norm b = 1 := norm_eq_one_of_unit hv
    have hn : norm x = norm a * norm b := by rw [hb, norm_mul]
    rw [hbn] at hn
    omega

/-- Conversely, a genuine proper factor is accepted. Both halves are needed:
soundness makes a hit meaningful, completeness makes a MISS meaningful, and it
is the miss that proves irreducibility. -/
theorem properTest_complete {x a b : Eis} (hx : x = mul a b)
    (ha : ¬ IsUnit a) (hb : ¬ IsUnit b) (hz : ¬ (x.re = 0 ∧ x.im = 0)) :
    properTest x a = true := by
  obtain ⟨h1, h2⟩ := norm_band_of_split hx ha hb hz
  have haz : ¬ (a.re = 0 ∧ a.im = 0) := by
    intro h0
    obtain ⟨p, q⟩ := h0
    have : norm a = 0 := by simp [norm, p, q]
    omega
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := (dvd_iff_norm_dvd_coords haz).mp ⟨b, hx⟩
  simp only [properTest, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨h1, h2⟩, ?_⟩, ?_⟩
  · rw [hp]; exact Int.mul_emod_right _ _
  · rw [hq]; exact Int.mul_emod_right _ _

/-- One row of the box: the candidates `⟨base + i, im⟩` for `i < n`. -/
def rowFind (x : Eis) (im base : Int) : Nat → Bool
  | 0 => false
  | Nat.succ n => properTest x ⟨base + (n : Int), im⟩ || rowFind x im base n

/-- The box: `w` candidates in each of `n` rows, the rows indexed from `base`. -/
def boxFind (x : Eis) (base : Int) (w : Nat) : Nat → Bool
  | 0 => false
  | Nat.succ n => rowFind x (base + (n : Int)) base w || boxFind x base w n

theorem rowFind_sound {x : Eis} {im base : Int} (n : Nat)
    (h : rowFind x im base n = true) : ∃ a : Eis, properTest x a = true := by
  induction n with
  | zero => simp [rowFind] at h
  | succ m ih =>
      simp only [rowFind, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨⟨base + (m : Int), im⟩, h⟩
      · exact ih h

theorem boxFind_sound {x : Eis} {base : Int} {w : Nat} (n : Nat)
    (h : boxFind x base w n = true) : ∃ a : Eis, properTest x a = true := by
  induction n with
  | zero => simp [boxFind] at h
  | succ m ih =>
      simp only [boxFind, Bool.or_eq_true] at h
      rcases h with h | h
      · exact rowFind_sound w h
      · exact ih h

theorem rowFind_complete {x : Eis} {im base : Int} (i : Nat) :
    ∀ n : Nat, i < n -> properTest x ⟨base + (i : Int), im⟩ = true ->
      rowFind x im base n = true := by
  intro n
  induction n with
  | zero => intro hlt _; omega
  | succ m ih =>
      intro hlt h
      simp only [rowFind, Bool.or_eq_true]
      rcases Nat.lt_or_ge i m with hm | hm
      · exact Or.inr (ih hm h)
      · have he : i = m := by omega
        exact Or.inl (he ▸ h)

theorem boxFind_complete {x : Eis} {base : Int} {w : Nat} (j : Nat) :
    ∀ n : Nat, j < n -> rowFind x (base + (j : Int)) base w = true ->
      boxFind x base w n = true := by
  intro n
  induction n with
  | zero => intro hlt _; omega
  | succ m ih =>
      intro hlt h
      simp only [boxFind, Bool.or_eq_true]
      rcases Nat.lt_or_ge j m with hm | hm
      · exact Or.inr (ih hm h)
      · have he : j = m := by omega
        exact Or.inl (he ▸ h)

/-- The split decision is a THEOREM. The box is `[-4N, 4N]²` with
`N = N(x)`, every candidate in it is tested by an integer remainder, and the
outer branch is on a `Bool`.

The bound is crude by a factor of about four in each direction, since the
statement to be proved is that the search TERMINATES and is complete, and a
sharp box would cost a square root without changing either. -/
theorem splitDecision : SplitDecision := by
  intro x hu hz
  have hN := norm_nonneg x
  have hk : ((norm x).toNat : Int) = norm x := Int.toNat_of_nonneg hN
  -- `base` is the low corner and `w` the side; both are read back off `hk`, so
  -- the `Nat` the recursion counts and the `Int` the bound speaks about are the
  -- same number rather than two that happen to agree.
  rcases hbf : boxFind x (-(4 * norm x)) (8 * (norm x).toNat + 1)
      (8 * (norm x).toNat + 1) with _ | _
  · -- The search came back empty, so nothing in the box splits `x`, so nothing
    -- splits `x` at all -- `coord_box` is what makes those the same statement.
    refine Or.inl ⟨hu, hz, ?_⟩
    intro a b hab
    rcases Int.lt_trichotomy (norm a) 1 with hlt | heq | hgt
    · -- `N(a) < 1` with `N(a) ≥ 0` means `a = 0`, hence `x = 0`.
      exfalso
      have ha0 : norm a = 0 := by have := norm_nonneg a; omega
      have : norm x = 0 := by rw [hab, norm_mul, ha0]; simp
      exact hz (norm_eq_zero this)
    · exact Or.inl (isUnit_of_norm_eq_one heq)
    · rcases Int.lt_trichotomy (norm b) 1 with hlt' | heq' | hgt'
      · exfalso
        have hb0 : norm b = 0 := by have := norm_nonneg b; omega
        have : norm x = 0 := by rw [hab, norm_mul, hb0]; simp
        exact hz (norm_eq_zero this)
      · exact Or.inr (isUnit_of_norm_eq_one heq')
      · exfalso
        have hna : ¬ IsUnit a := fun h => by
          obtain ⟨v, hv⟩ := h; have := norm_eq_one_of_unit hv; omega
        have hnb : ¬ IsUnit b := fun h => by
          obtain ⟨v, hv⟩ := h; have := norm_eq_one_of_unit hv; omega
        obtain ⟨hb1, hb2⟩ := norm_band_of_split hab hna hnb hz
        -- `a` is inside the box: its norm is below `N(x)`, and `coord_bounds`
        -- turns that into a square bound on each coordinate.
        obtain ⟨hc1, hc2⟩ := coord_bounds a
        have him : a.im * a.im <= 4 * norm x := by
          have := int_sq_nonneg a.im; omega
        have hre : (2 * a.re - a.im) * (2 * a.re - a.im) <= 4 * norm x := by
          have := int_sq_nonneg (2 * a.re - a.im); omega
        obtain ⟨hi1, hi2⟩ := coord_box him
        obtain ⟨hr1, hr2⟩ := coord_box hre
        -- The indices, and that they land under the side length.
        have hjn : ((a.im + 4 * norm x).toNat : Int) = a.im + 4 * norm x :=
          Int.toNat_of_nonneg (by omega)
        have hin : ((a.re + 4 * norm x).toNat : Int) = a.re + 4 * norm x :=
          Int.toNat_of_nonneg (by omega)
        have hjlt : (a.im + 4 * norm x).toNat < 8 * (norm x).toNat + 1 := by
          omega
        have hilt : (a.re + 4 * norm x).toNat < 8 * (norm x).toNat + 1 := by
          omega
        have hrow : rowFind x (-(4 * norm x) + ((a.im + 4 * norm x).toNat : Int))
            (-(4 * norm x)) (8 * (norm x).toNat + 1) = true := by
          refine rowFind_complete (a.re + 4 * norm x).toNat _ hilt ?_
          have hpt : properTest x a = true :=
            properTest_complete hab hna hnb hz
          have hre' : -(4 * norm x) + ((a.re + 4 * norm x).toNat : Int) = a.re := by
            omega
          have him' : -(4 * norm x) + ((a.im + 4 * norm x).toNat : Int) = a.im := by
            omega
          rw [hre', him']
          exact hpt
        have := boxFind_complete (a.im + 4 * norm x).toNat _ hjlt hrow
        rw [hbf] at this
        exact Bool.noConfusion this
  · obtain ⟨a, hpt⟩ := boxFind_sound _ hbf
    obtain ⟨b, hb, hna, hnb⟩ := properTest_sound hpt
    exact Or.inr ⟨a, b, hb, hna, hnb⟩

#print axioms mul_sub
#print axioms eq_of_mul_left_cancel
#print axioms coord_bounds
#print axioms dvd_iff_norm_dvd_coords
#print axioms norm_band_of_split
#print axioms dvd_or_not
#print axioms norm_mul_eq_one
#print axioms not_splitDecision_unrestricted
#print axioms le_sq_self
#print axioms coord_box
#print axioms properTest_sound
#print axioms properTest_complete
#print axioms boxFind_sound
#print axioms boxFind_complete
#print axioms splitDecision
#print axioms add_comm
#print axioms int_sq_nonneg
#print axioms int_sq_eq_zero
#print axioms sq_sub_expand
#print axioms norm_split
#print axioms sq_le_sq
#print axioms neg_mul_le
#print axioms four_norm_form
#print axioms mul_one
#print axioms one_mul
#print axioms norm_one
#print axioms mul_ofInt
#print axioms dvd_refl
#print axioms dvd_zero
#print axioms add_sub_cancel
#print axioms ext_of_coords
#print axioms rowFind_sound
#print axioms rowFind_complete
end Eis

#print axioms NumberTheory.divides_or_not_nat


/-! ## The cyclotomic degree, by fuel -/

/-- The primes, enumerated. `nthPrime 0 = 2` and each successor is the least
factor of `(previous)! + 1`.

NOT the `k`-th prime in order --- it skips. What it is, and what an Euler
product needs, is a STRICTLY INCREASING sequence of primes given as a TERM.
`exists_prime_gt` says one exists past every bound; turning that existential
into a function would be a choice, so the witness is named directly instead. -/
def nthPrime : Nat → Nat
  | 0 => 2
  | k + 1 => minFac (fact (nthPrime k) + 1)

#print axioms nthPrime
/-- The `p`-adic decomposition is UNIQUE.

    p^a * z = p^b * w,  p dividing neither z nor w   ->   a = b  and  z = w

`prime_pow_split` gives existence; uniqueness is the half that recovers an
EXPONENT from a product --- which is what identifies the summands of an
expanded Euler product with integers.

The argument is trichotomy on the exponents: write the larger as `i + (d + 1)`,
cancel the common power (positive, so cancellable in `Nat`), and the surviving
factor of `p` divides the cofactor that was assumed coprime to it. No
factorisation list and no permutation appear, so this does not go through
`factorization_perm`. -/
theorem prime_pow_split_unique {p a b z w : Nat} (hp : IsPrime p)
    (hz : ¬ Divides p z) (hw : ¬ Divides p w)
    (h : p ^ a * z = p ^ b * w) : a = b ∧ z = w := by
  have hp2 := hp.left
  have hppos : ∀ n : Nat, 0 < p ^ n := by
    intro n
    induction n with
    | zero => show 0 < 1; omega
    | succ k ih => rw [Nat.pow_succ]; exact Nat.mul_pos ih (by omega)
  -- the unequal case is impossible on whichever side has the smaller exponent
  have key : ∀ i j u v : Nat, i < j → ¬ Divides p u →
      p ^ i * u = p ^ j * v → False := by
    intro i j u v hij hu heq
    obtain ⟨d, hd⟩ : ∃ d, j = i + (d + 1) := ⟨j - i - 1, by omega⟩
    rw [hd, Nat.pow_add, Nat.mul_assoc] at heq
    have hcancel := Nat.eq_of_mul_eq_mul_left (hppos i) heq
    refine hu ⟨p ^ d * v, ?_⟩
    rw [hcancel, Nat.pow_succ, Nat.mul_comm (p ^ d) p, Nat.mul_assoc]
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · exact (key a b z w hlt hz h).elim
  · subst heq
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (hppos a) h⟩
  · exact (key b a w z hgt hw h.symm).elim


/-- Primality, decidably. `minFac` is computable and returns the least
divisor at least two, so a number at least two is prime exactly when it is its
own least divisor. So a search over primes can use a `Bool` predicate without a
`Decidable (IsPrime k)` instance --- which matters, because `by_cases` is
choice-free here only under such an instance. -/
theorem isPrime_iff_minFac_self {k : Nat} (hk : 2 ≤ k) :
    IsPrime k ↔ minFac k = k := by
  constructor
  · intro hp
    exact hp.right (minFac k) (minFac_ge hk) (minFac_divides hk)
  · intro h
    have hmf := isPrime_minFac hk
    rwa [h] at hmf

/-- The search terminates. Hoisted into its own lemma rather than inlined
twice: `natFind` takes the existence proof as an ARGUMENT, so the definition
and its specification have to hand it the same term. -/
theorem exists_primeTest_above (n : Nat) :
    ∃ k, (fun k => decide (n < k ∧ 2 ≤ k ∧ minFac k = k)) k = true := by
  obtain ⟨p, hp, hnp⟩ := exists_prime_gt n
  refine ⟨p, ?_⟩
  have hp2 := hp.left
  have hmf : minFac p = p := (isPrime_iff_minFac_self hp2).mp hp
  simp only [decide_eq_true_eq]
  exact ⟨hnp, hp2, hmf⟩

/-- The least prime strictly above `n`.

`nthPrime` gives an indexed family of DISTINCT primes and skips wildly, which
is all an indexed family needs. A product over the primes needs them IN ORDER,
and this supplies that: `natFind` walks up from zero, `exists_primeTest_above`
proves the walk terminates, and `minFac` makes the test computable. -/
noncomputable def leastPrimeAbove (n : Nat) : Nat :=
  natFind (fun k => decide (n < k ∧ 2 ≤ k ∧ minFac k = k))
    (exists_primeTest_above n)

theorem leastPrimeAbove_spec (n : Nat) :
    n < leastPrimeAbove n ∧ IsPrime (leastPrimeAbove n) := by
  have hhit := natFind_spec (fun k => decide (n < k ∧ 2 ≤ k ∧ minFac k = k))
    (exists_primeTest_above n)
  simp only [decide_eq_true_eq] at hhit
  exact ⟨hhit.left, (isPrime_iff_minFac_self hhit.right.left).mpr hhit.right.right⟩



/-- A product of TWO naturals prime to `p` is prime to `p`.

Euclid's lemma in the `% p /= 0` spelling. `prime_divides_mul` splits the
divisibility and each branch contradicts a hypothesis. -/
theorem mul_mod_ne_zero {p a b : Nat} (hp : IsPrime p)
    (ha : a % p ≠ 0) (hb : b % p ≠ 0) : (a * b) % p ≠ 0 := by
  intro h
  rcases prime_divides_mul hp (dvd_of_mod_zero h) with hd | hd
  · exact ha (mod_eq_zero_of_divides hd)
  · exact hb (mod_eq_zero_of_divides hd)

#print axioms NumberTheory.mul_mod_ne_zero

/-- A product of naturals prime to `p` is prime to `p`.

Euclid's lemma folded along `prodUpto`. The hypothesis is bounded because the
consumer below has a family of DISTINCT primes and can only show the factors
below `K` are prime to `P K`, so a version demanding it at every index would
compile and never apply.

The two-factor case is `mul_mod_ne_zero` above.
-/
theorem prodUpto_mod_ne_zero {p : Nat} (hp : IsPrime p) {F : Nat → Nat} :
    ∀ K : Nat, (∀ k : Nat, k < K → F k % p ≠ 0) → prodUpto F K % p ≠ 0
  | 0, _ => by
    have hp2 := hp.left
    show (1 : Nat) % p ≠ 0
    rw [Nat.one_mod_eq_one.mpr (by omega)]
    omega
  | K + 1, hF => by
    intro h
    have h' : (prodUpto F K * F K) % p = 0 := h
    rcases prime_divides_mul hp (dvd_of_mod_zero h') with hd | hd
    · exact prodUpto_mod_ne_zero hp K (fun k hk => hF k (by omega))
        (mod_eq_zero_of_divides hd)
    · exact hF K (by omega) (mod_eq_zero_of_divides hd)

/-- An exponent vector is determined by the product it names.

    prod_{k<K} P k ^ d k = prod_{k<K} P k ^ e k   ->   d k = e k for k < K

for a family of pairwise distinct primes. `prime_pow_split_unique` peels one
prime, and what it needs of the remaining factor --- that it is prime to the
peeled prime --- is `prodUpto_mod_ne_zero` applied through `prime_divides_pow`,
which says a prime dividing a prime power divides its base.

This is the injectivity an Euler product needs: with it, the flat sum produced
by expanding the product is a sum over DISTINCT naturals rather than a sum with
repetitions. Unique factorisation is not invoked --- the statement is about a
fixed family in a fixed order, so no permutation appears. -/
theorem prodUpto_pow_inj {P : Nat → Nat} (hP : ∀ k : Nat, IsPrime (P k))
    (hne : ∀ i j : Nat, i ≠ j → P i ≠ P j) {d e : Nat → Nat} :
    ∀ K : Nat,
      prodUpto (fun k => P k ^ d k) K = prodUpto (fun k => P k ^ e k) K →
      ∀ k : Nat, k < K → d k = e k
  | 0, _, _, hk => absurd hk (by omega)
  | K + 1, h, k, hk => by
    have hfac : ∀ g : Nat → Nat, ∀ i : Nat, i < K → (P i ^ g i) % P K ≠ 0 := by
      intro g i hi hzero
      exact hne i K (by omega)
        (prime_divides_pow (hP K) (hP i) (g i) (dvd_of_mod_zero hzero)).symm
    have hz : ¬ Divides (P K) (prodUpto (fun i => P i ^ d i) K) := fun hd =>
      prodUpto_mod_ne_zero (hP K) K (hfac d) (mod_eq_zero_of_divides hd)
    have hw : ¬ Divides (P K) (prodUpto (fun i => P i ^ e i) K) := fun hd =>
      prodUpto_mod_ne_zero (hP K) K (hfac e) (mod_eq_zero_of_divides hd)
    have hcomm : P K ^ d K * prodUpto (fun i => P i ^ d i) K
        = P K ^ e K * prodUpto (fun i => P i ^ e i) K := by
      have h' : prodUpto (fun i => P i ^ d i) K * P K ^ d K
          = prodUpto (fun i => P i ^ e i) K * P K ^ e K := h
      rw [Nat.mul_comm (prodUpto (fun i => P i ^ d i) K),
        Nat.mul_comm (prodUpto (fun i => P i ^ e i) K)] at h'
      exact h'
    obtain ⟨hdK, hrest⟩ := prime_pow_split_unique (hP K) hz hw hcomm
    rcases Nat.lt_or_ge k K with hkK | hkK
    · exact prodUpto_pow_inj hP hne K hrest k hkK
    · obtain rfl : k = K := by omega
      exact hdK


/-- The primes in order. `leastPrimeAbove` is the step; this is the family
it generates, starting at two.

`nthPrime` is an indexed family of DISTINCT primes and skips wildly, which is
all a family of distinct primes needs. An Euler product ranges over the primes
in order, and its convergence is read off from how fast they GROW, so it needs
this one. -/
noncomputable def orderedPrime : Nat → Nat
  | 0 => 2
  | k + 1 => leastPrimeAbove (orderedPrime k)

theorem orderedPrime_isPrime : ∀ k : Nat, IsPrime (orderedPrime k)
  | 0 => isPrime_two
  | k + 1 => (leastPrimeAbove_spec (orderedPrime k)).right

/-- The family is strictly increasing, which is what "in order" means here
and what makes its members pairwise distinct. -/
theorem orderedPrime_lt_succ (k : Nat) :
    orderedPrime k < orderedPrime (k + 1) :=
  (leastPrimeAbove_spec (orderedPrime k)).left

theorem orderedPrime_strictMono : ∀ i j : Nat, i < j →
    orderedPrime i < orderedPrime j
  | i, 0, h => absurd h (by omega)
  | i, j + 1, h => by
    rcases Nat.lt_or_ge i j with hij | hij
    · exact Nat.lt_trans (orderedPrime_strictMono i j hij)
        (orderedPrime_lt_succ j)
    · have hij' : i = j := by omega
      rw [hij']
      exact orderedPrime_lt_succ j

/-- Distinct indices give distinct primes. The hypothesis
`prodUpto_pow_inj` asks for, discharged once for this family. -/
theorem orderedPrime_ne {i j : Nat} (h : i ≠ j) :
    orderedPrime i ≠ orderedPrime j := by
  rcases Nat.lt_or_ge i j with hij | hij
  · exact Nat.ne_of_lt (orderedPrime_strictMono i j hij)
  · have hji : j < i := by omega
    exact Nat.ne_of_gt (orderedPrime_strictMono j i hji)

/-- The `k`-th prime in order is at least `k + 2`.

The growth bound a comparison test reads: `1 / P k ^ s <= 1 / (k+2) ^ s`, so
summability over the ordered primes follows from summability over ALL naturals
with no relation between the two families. Going through `nthPrime`'s
summability instead would need a bijection between the families, which is
exactly the reindexing an Euler product must avoid. -/
theorem orderedPrime_ge : ∀ k : Nat, k + 2 ≤ orderedPrime k
  | 0 => by
    show 2 ≤ 2
    omega
  | k + 1 => by
    have hstep := orderedPrime_lt_succ k
    have hih := orderedPrime_ge k
    omega


/-- A `prodUpto` only reads its family below the bound. -/
theorem prodUpto_congr {F G : Nat → Nat} :
    ∀ K : Nat, (∀ k : Nat, k < K → F k = G k) → prodUpto F K = prodUpto G K
  | 0, _ => rfl
  | K + 1, h => by
    show prodUpto F K * F K = prodUpto G K * G K
    rw [prodUpto_congr K (fun k hk => h k (by omega)), h K (by omega)]

/-- A number whose prime factors all lie among the first `K` of a family is a
product of their powers.

The converse of `prodUpto_pow_inj`: that says an exponent vector is determined
by its product, this says every admissible product ARISES from one. An Euler
product needs both --- injectivity to know the expanded sum has no repeats,
this to know it omits nothing below the truncation point.

`prime_pow_split` peels one prime at a time with exactly the shape the
induction wants (`n = p ^ a * z` with `z` prime to `p`), and the residue `z`
inherits the hypothesis because every prime dividing it divides `n` and cannot
be the peeled prime. -/
theorem exists_prodUpto_pow {P : Nat → Nat} (hP : ∀ k : Nat, IsPrime (P k)) :
    ∀ K : Nat, ∀ n : Nat, 0 < n →
      (∀ q : Nat, IsPrime q → Divides q n → ∃ k : Nat, k < K ∧ P k = q) →
      ∃ d : Nat → Nat, n = prodUpto (fun k => P k ^ d k) K
  | 0, n, hn, hfac => by
    refine ⟨fun _ => 0, ?_⟩
    show n = 1
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · omega
    · obtain ⟨k, hk, -⟩ := hfac (minFac n) (isPrime_minFac h2) (minFac_divides h2)
      omega
  | K + 1, n, hn, hfac => by
    obtain ⟨a, z, hz0, hnz, hzp⟩ := prime_pow_split (hP K) n hn
    have hzfac : ∀ q : Nat, IsPrime q → Divides q z →
        ∃ k : Nat, k < K ∧ P k = q := by
      intro q hq hqz
      obtain ⟨c, hc⟩ := hqz
      obtain ⟨k, hk, hkq⟩ := hfac q hq
        ⟨P K ^ a * c, by rw [hnz, hc]; exact Nat.mul_left_comm _ _ _⟩
      rcases Nat.lt_or_ge k K with hlt | hge
      · exact ⟨k, hlt, hkq⟩
      · have hKq : k = K := by omega
        rw [hKq] at hkq
        exact absurd (show Divides (P K) z by rw [hkq]; exact ⟨c, hc⟩) hzp
    obtain ⟨d, hd⟩ := exists_prodUpto_pow hP K z hz0 hzfac
    refine ⟨fun k => if k = K then a else d k, ?_⟩
    show n = prodUpto (fun k => P k ^ (if k = K then a else d k)) K
      * P K ^ (if K = K then a else d K)
    rw [if_pos rfl,
      prodUpto_congr K (fun k hk => by rw [if_neg (by omega)]),
      ← hd, hnz, Nat.mul_comm]


/-- A product of positive factors is positive. -/
theorem prodUpto_pos {F : Nat → Nat} (hF : ∀ i : Nat, 0 < F i) :
    ∀ K : Nat, 0 < prodUpto F K
  | 0 => by
    show 0 < 1
    omega
  | K + 1 => by
    show 0 < prodUpto F K * F K
    have hrec := prodUpto_pos hF K
    have hk := hF K
    exact Nat.mul_pos hrec hk

/-- Each factor is at most the product, when the factors are positive.

The bound that converts "the product is below `N`" into a bound on each
exponent: with every prime at least two, `2 ^ d k <= P k ^ d k <= n`, so a
truncation `J` above `n` covers every exponent that can occur. Positivity is
required --- one zero factor collapses the product below its other factors. -/
theorem prodUpto_factor_le {F : Nat → Nat} (hF : ∀ i : Nat, 0 < F i) :
    ∀ K k : Nat, k < K → F k ≤ prodUpto F K
  | 0, k, hk => absurd hk (by omega)
  | K + 1, k, hk => by
    show F k ≤ prodUpto F K * F K
    rcases Nat.lt_or_ge k K with hlt | hge
    · exact Nat.le_trans (prodUpto_factor_le hF K k hlt)
        (Nat.le_mul_of_pos_right _ (hF K))
    · have hkK : k = K := by omega
      rw [hkK]
      exact Nat.le_mul_of_pos_left _ (prodUpto_pos hF K)


/-- No prime lies strictly between `n` and the least prime above it.

`leastPrimeAbove_spec` says the value is a prime above `n`; it does NOT say it
is the LEAST such, and the enumeration's completeness needs exactly that.
`natFind_least` supplies it: every candidate below the found one fails the
test, and failing the test while being above `n` and at least two means not
being its own least factor, which for a prime is false. -/
theorem leastPrimeAbove_least {n q : Nat} (hn : n < q) (hq : IsPrime q) :
    leastPrimeAbove n ≤ q := by
  rcases Nat.lt_or_ge q (leastPrimeAbove n) with hlt | hge
  · have hfail := natFind_least
      (fun k => decide (n < k ∧ 2 ≤ k ∧ minFac k = k))
      (exists_primeTest_above n) q hlt
    have hgood : n < q ∧ 2 ≤ q ∧ minFac q = q :=
      ⟨hn, hq.left, (isPrime_iff_minFac_self hq.left).mp hq⟩
    rw [decide_eq_false_iff_not] at hfail
    exact absurd hgood hfail
  · exact hge

/-- The ordered enumeration is COMPLETE below its own values.

Every prime strictly below `orderedPrime K` is `orderedPrime i` for some
`i < K`. So every `n` below the `K`-th prime is `K`-smooth, and an Euler
product's flat sum contains every term of the L-series partial sum up to that
point.

The induction is on `K`: a prime below `orderedPrime (K+1)` is either below
`orderedPrime K`, and the hypothesis applies, or it lies in the closed gap
between them --- which `leastPrimeAbove_least` rules out unless it IS
`orderedPrime K`. -/
theorem orderedPrime_complete {q : Nat} (hq : IsPrime q) :
    ∀ K : Nat, q < orderedPrime K → ∃ i : Nat, i < K ∧ orderedPrime i = q
  | 0, hlt => by
    have h2 := hq.left
    have : orderedPrime 0 = 2 := rfl
    omega
  | K + 1, hlt => by
    rcases Nat.lt_or_ge q (orderedPrime K) with hbelow | habove
    · obtain ⟨i, hi, hval⟩ := orderedPrime_complete hq K hbelow
      exact ⟨i, by omega, hval⟩
    · rcases Nat.lt_or_ge (orderedPrime K) q with hstrict | hle
      · have hstep : leastPrimeAbove (orderedPrime K) ≤ q :=
          leastPrimeAbove_least hstrict hq
        show ∃ i, i < K + 1 ∧ orderedPrime i = q
        have : orderedPrime (K + 1) = leastPrimeAbove (orderedPrime K) := rfl
        omega
      · have hEq : orderedPrime K = q := by omega
        exact ⟨K, by omega, hEq⟩


/-- Every positive number below the `K`-th prime factors over the first `K`
primes, with every exponent bounded by the number itself.

This is the step that makes the Euler comparison FINITE. The product side is
truncated twice --- at `K` primes and at exponent depth `J` --- and this fixes
both truncations at once against a single bound `n`:

  * the factorisation exists over the first `K` primes, because a prime divisor
    of `n` is at most `n`, hence strictly below `orderedPrime K`, and
    `orderedPrime_complete` then places it in the enumeration below `K`;
  * each exponent obeys `2 ^ d k <= n`, because the factor `p k ^ d k` divides
    --- indeed is dominated by --- the whole product, and every prime is at
    least two.

The exponent bound is stated against `2 ^ d k` rather than `d k` because what
the truncation depth must satisfy is `2 ^ J > n`, so this is the form the
consumer uses, with no logarithm needed anywhere. -/
theorem exists_orderedPrime_pow_of_lt {n K : Nat} (hn : 0 < n)
    (hlt : n < orderedPrime K) :
    ∃ d : Nat → Nat, n = prodUpto (fun k => orderedPrime k ^ d k) K ∧
      ∀ k : Nat, k < K → 2 ^ d k ≤ n := by
  have hfac : ∀ q : Nat, IsPrime q → Divides q n →
      ∃ k : Nat, k < K ∧ orderedPrime k = q := by
    intro q hq hqn
    have hqle : q ≤ n := divides_le hn hqn
    exact orderedPrime_complete hq K (by omega)
  obtain ⟨d, hd⟩ := exists_prodUpto_pow orderedPrime_isPrime K n hn hfac
  refine ⟨d, hd, ?_⟩
  intro k hk
  have hF : ∀ i : Nat, 0 < orderedPrime i ^ d i := fun i =>
    Nat.pow_pos (by have := orderedPrime_ge i; omega)
  have hle : orderedPrime k ^ d k ≤ prodUpto (fun k => orderedPrime k ^ d k) K :=
    prodUpto_factor_le hF K k hk
  have h2 : 2 ≤ orderedPrime k := by have := orderedPrime_ge k; omega
  have hpow : 2 ^ d k ≤ orderedPrime k ^ d k := Nat.pow_le_pow_left h2 (d k)
  omega


/-- A product grows with its factors.

Termwise monotonicity, bounded like every other `prodUpto` fact by the range
rather than demanded at every index --- the consumer compares digit exponents,
which agree with the bound only below `K`.

Positivity of the SMALLER family is what makes the step sound: without it a
zero factor collapses the left product and the induction's multiplication step
carries no information. -/
theorem prodUpto_le_of_le {F G : Nat → Nat} (hF : ∀ i : Nat, 0 < F i) :
    ∀ K : Nat, (∀ k : Nat, k < K → F k ≤ G k) → prodUpto F K ≤ prodUpto G K
  | 0, _ => by
    show 1 ≤ 1
    omega
  | K + 1, h => by
    show prodUpto F K * F K ≤ prodUpto G K * G K
    exact Nat.mul_le_mul (prodUpto_le_of_le hF K (fun k hk => h k (by omega)))
      (h K (by omega))

/-- The fibre congruence behind the character-family product.

    (a + f*b) * (g*k')  ==  a * (g*k')   (mod f*g)

Splitting `j < n` as `j = a + f*b` with `n = f*g`, the exponent `j*k` depends
only on `a`, because the `f*b` part contributes a multiple of `n`.  This is why
the product over the family FIBRES over the inner index rather than permuting:
`j |-> j*k mod n` is `g`-to-one, not a bijection, unless `p` generates. -/
theorem mul_mod_of_split (f g a b k' : Nat) :
    ((a + f * b) * (g * k')) % (f * g) = (a * (g * k')) % (f * g) := by
  have h : (a + f * b) * (g * k') = a * (g * k') + (f * g) * (b * k') := by
    rw [Nat.add_mul, Nat.mul_assoc f b (g * k'), ← Nat.mul_assoc b g k',
      Nat.mul_comm b g, Nat.mul_assoc g b k', ← Nat.mul_assoc f g (b * k')]
  rw [h, Nat.add_mul_mod_self_left]

/-- Multiplication by a unit is injective on residues.

    a*k == b*k  (mod f),  gcd f k = 1,  a,b < f   ==>   a = b

`coprime_divides` is the content: `f` divides `(a-b)*k` and is coprime to `k`,
so it divides `a-b`, which is below `f` and therefore zero.  This is the
injectivity `foldF_permOn` asks for, and with it `a |-> a*k' mod f` is a
permutation of the INNER index in the character-family product --- the outer
index fibres instead, which no permutation lemma can express. -/
theorem mul_mod_inj_of_gcd_one {f k : Nat} (hf : 0 < f)
    (hgcd : Nat.gcd f k = 1) {a b : Nat} (ha : a < f) (hb : b < f)
    (h : (a * k) % f = (b * k) % f) : a = b := by
  have key : ∀ x y : Nat, y ≤ x → x < f →
      (x * k) % f = (y * k) % f → x = y := by
    intro x y hyx hxf hxy
    have hz : (x * k - y * k) % f = 0 := Nat.sub_mod_eq_zero_of_mod_eq hxy
    have hd : Divides f (k * (x - y)) := by
      rw [Nat.mul_comm k (x - y), Nat.sub_mul]
      exact divides_of_mod_eq_zero hz
    obtain ⟨w, hw⟩ := coprime_divides hgcd hd
    rcases Nat.eq_zero_or_pos w with rfl | hwpos
    · omega
    · have : f ≤ f * w := Nat.le_mul_of_pos_right f hwpos
      omega
  rcases Nat.le_total b a with hle | hle
  · exact key a b hle ha h
  · exact (key b a hle hb h.symm).symm

/-- MULTIPLYING THE INDEX BY A UNIT PERMUTES THE NON-ZERO RESIDUES.

    gcd(p,a) = 1   ==>   j |-> (j*a) mod p  is a bijection of {1,...,p-1}

Stated on the shifted index `i |-> ((i+1)*a) % p - 1` because that is the form
`foldF_permOn` consumes: folds here run over `i < p - 1` and the residues they
name are `i + 1`.

THE NON-VANISHING CONJUNCT IS NEEDED. `Nat` subtraction is TRUNCATED, so
`0 - 1 = 0` and the bound `((i+1)*a) % p - 1 < p - 1` is satisfied by the very
index it was meant to exclude. A caller reindexing along this map needs to know
the scaled residue is non-zero to shift back, and cannot recover it from the
bound. Without it the statement is true, compiles, and cannot be used.

The halves are `mul_mod_inj_of_gcd_one` for injectivity, and primality for the
image being non-zero. -/
theorem mulShift_maps_and_inj {p a : Nat} (hp : IsPrime p) (hp3 : 3 ≤ p)
    (hgcd : Nat.gcd p a = 1) :
    (∀ i, i < p - 1 → ((i + 1) * a) % p ≠ 0)
      ∧ (∀ i, i < p - 1 → ((i + 1) * a) % p - 1 < p - 1)
      ∧ (∀ i j, i < p - 1 → j < p - 1 →
          ((i + 1) * a) % p - 1 = ((j + 1) * a) % p - 1 → i = j) := by
  have hp0 : 0 < p := by omega
  -- the image is never zero: `p` is prime and neither factor is a multiple
  have hne : ∀ i, i < p - 1 → ((i + 1) * a) % p ≠ 0 := by
    intro i hi hz
    rcases prime_divides_mul hp (divides_of_mod_eq_zero hz) with hpi | hpa
    · obtain ⟨c, hc⟩ := hpi
      have hp2 := hp.left
      rcases Nat.eq_zero_or_pos c with rfl | hcpos
      · omega
      · have : p * 1 ≤ p * c := Nat.mul_le_mul_left p hcpos
        omega
    · have : Nat.gcd p a = 1 := hgcd
      have hnd : ¬ Divides p a := by
        intro hd
        have hpa : p ∣ Nat.gcd p a := Nat.dvd_gcd (Nat.dvd_refl p)
          (by obtain ⟨c, hc⟩ := hd; exact ⟨c, hc⟩)
        have hp2 := hp.left
        rw [this] at hpa
        exact absurd (Nat.le_of_dvd (by omega) hpa) (by omega)
      exact hnd hpa
  refine ⟨hne, fun i hi => ?_, fun i j hi hj he => ?_⟩
  · have h1 : ((i + 1) * a) % p < p := Nat.mod_lt _ hp0
    have h2 := hne i hi
    omega
  · have h1 : ((i + 1) * a) % p ≠ 0 := hne i hi
    have h2 : ((j + 1) * a) % p ≠ 0 := hne j hj
    have heq : ((i + 1) * a) % p = ((j + 1) * a) % p := by
      have l1 : ((i + 1) * a) % p < p := Nat.mod_lt _ hp0
      have l2 : ((j + 1) * a) % p < p := Nat.mod_lt _ hp0
      omega
    have := mul_mod_inj_of_gcd_one hp0 hgcd
      (show i + 1 < p by omega) (show j + 1 < p by omega) heq
    omega

#print axioms mulShift_maps_and_inj

/-- Every exponent splits for the fibration.

    n = f * g,   k = g * k',   gcd f k' = 1        with g = gcd n k

`f` is the order of the element `b^k` in a cyclic group of order `n`, and `g`
the size of each fibre. Dividing both by their gcd is what makes the inner
reindexing a permutation, which is the hypothesis
`foldF_one_sub_cZetaPow_fibre` asks for. -/
theorem exists_fibre_split {n : Nat} (hn : 0 < n) (k : Nat) :
    ∃ f g k' : Nat, 0 < f ∧ 0 < g ∧ n = f * g ∧ k = g * k'
      ∧ Nat.gcd f k' = 1 := by
  have hg : 0 < Nat.gcd n k := Nat.gcd_pos_of_pos_left k hn
  have hnf : n / Nat.gcd n k * Nat.gcd n k = n :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left n k)
  refine ⟨n / Nat.gcd n k, Nat.gcd n k, k / Nat.gcd n k, ?_, hg, ?_, ?_, ?_⟩
  · -- NOT `Nat.div_pos`: that is proved classically in core and pulls
    -- `Classical.choice`. The quotient is positive because its product with
    -- `g` is `n`, which is positive.
    rcases Nat.eq_zero_or_pos (n / Nat.gcd n k) with h0 | hpos
    · rw [h0, Nat.zero_mul] at hnf; omega
    · exact hpos
  · exact (Nat.div_mul_cancel (Nat.gcd_dvd_left n k)).symm
  · exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right n k)).symm
  · exact Nat.coprime_div_gcd_div_gcd hg

/-- The conjugate index is the complement.

    0 < j < n   ==>   ((n-1) * j) % n  =  n - j

`(n-1)*j` is `n*j - j`, and `n*j - j` is `(n-j) + n*(j-1)`, whose remainder mod
`n` is `n-j` --- which is below `n`, so the outer remainder does nothing.

`cConj_cPow_cZeta` gives the conjugate index as `(n-1)*j`, `cPow_cZeta_mod`
reduces it mod `n`, and this says the reduction is simply `n - j`. Two facts
then follow by arithmetic: it is non-zero because `j < n`, and it differs from
`j` unless `n = 2j` --- which is the QUADRATIC character, the one real
non-principal character, and the case the other branch handles. -/
theorem conj_index_complement {n j : Nat} (hj0 : 0 < j) (hjn : j < n) :
    ((n - 1) * j) % n = n - j := by
  have hsplit : (n - 1) * j = (n - j) + n * (j - 1) := by
    rw [Nat.sub_mul, Nat.mul_sub, Nat.one_mul, Nat.mul_one]
    have hle : n ≤ n * j := Nat.le_mul_of_pos_right n hj0
    omega
  rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

#print axioms mul_shuffle
#print axioms nat_sq_mul_sq

#print axioms divides_refl
#print axioms one_divides
#print axioms divides_trans
#print axioms divides_of_mod_eq_zero
#print axioms mod_eq_zero_of_divides
#print axioms divides_le
#print axioms divides_sub
#print axioms eq_one_of_divides_one
#print axioms minFacAux_divides
#print axioms minFac_divides
#print axioms minFacAux_ge
#print axioms minFac_ge
#print axioms minFacAux_least
#print axioms minFac_least
#print axioms fact_pos
#print axioms divides_fact
#print axioms gcd_eq_one_of_prime_not_divides
#print axioms prime_eq_of_divides
#print axioms prodList_perm
#print axioms prime_divides_pow
#print axioms gcd_prime_pow_eq_one
#print axioms prime_pow_split
#print axioms choose_zero
#print axioms choose_succ_succ
#print axioms choose_gt
#print axioms choose_self
#print axioms choose_one
#print axioms succ_mul_choose
end NumberTheory

namespace ZFSet
export NumberTheory (Divides DividesSet Eis IsFactorization IsPrime bezout bezout_int choose choose_gt choose_mul_fact choose_one choose_self choose_succ_succ choose_zero conj_index_complement coprime_divides cyclotomicShift_eisenstein divides_fact divides_le divides_of_mod_eq_zero divides_or_not_nat divides_refl divides_sub divides_trans divisorsBelow dvd_of_mod_zero eq_one_of_divides_one exists_factorization exists_fibre_split exists_mul_mod_one exists_orderedPrime_pow_of_lt exists_primeTest_above exists_prime_ge exists_prime_gt exists_prime_pow_not_divides exists_prodUpto_pow fact fact_pos factorization_perm fallNat fallNat_mul_fact fallNat_succ_back choose_mul_fact_mul_fact gcd_eq_one_of_prime_not_divides gcd_prime_pow_eq_one isPrime_iff_minFac_self isPrime_minFac isPrime_three isPrime_two leastPrimeAbove leastPrimeAbove_least leastPrimeAbove_spec lt_minFac_fact_succ minFac minFacAux minFacAux_divides minFacAux_ge minFacAux_least minFac_divides minFac_ge minFac_least mod_eq_zero_of_divides mul_mod_inj_of_gcd_one mul_mod_of_split nthPrime one_divides orderedPrime orderedPrime_complete orderedPrime_ge orderedPrime_isPrime orderedPrime_lt_succ orderedPrime_ne orderedPrime_strictMono prime_divides_mul prime_divides_pow prime_divides_prodList prime_divides_sq prime_dvd_choose prime_eq_of_divides prime_pow_split prime_pow_split_unique prime_sq_irrational prodList prodList_perm prodUpto_congr prodUpto_factor_le prodUpto_le_of_le prodUpto_mod_ne_zero prodUpto_pos prodUpto_pow_inj succ_mul_choose sumOver sumOver_add sumOver_congr sumOver_zero upto)
#print axioms NumberTheory.prime_pow_split_unique
#print axioms NumberTheory.isPrime_iff_minFac_self
#print axioms NumberTheory.exists_primeTest_above
#print axioms NumberTheory.leastPrimeAbove_spec
#print axioms NumberTheory.prodUpto_mod_ne_zero
#print axioms NumberTheory.prodUpto_pow_inj
#print axioms NumberTheory.orderedPrime
#print axioms NumberTheory.orderedPrime_isPrime
#print axioms NumberTheory.orderedPrime_lt_succ
#print axioms NumberTheory.orderedPrime_strictMono
#print axioms NumberTheory.orderedPrime_ne
#print axioms NumberTheory.orderedPrime_ge
#print axioms NumberTheory.prodUpto_congr
#print axioms NumberTheory.exists_prodUpto_pow
#print axioms NumberTheory.prodUpto_pos
#print axioms NumberTheory.prodUpto_factor_le
#print axioms NumberTheory.leastPrimeAbove_least
#print axioms NumberTheory.orderedPrime_complete
#print axioms NumberTheory.exists_orderedPrime_pow_of_lt
#print axioms NumberTheory.prodUpto_le_of_le
#print axioms NumberTheory.mul_mod_of_split
#print axioms NumberTheory.mul_mod_inj_of_gcd_one

#print axioms NumberTheory.exists_fibre_split
#print axioms NumberTheory.conj_index_complement
end ZFSet
