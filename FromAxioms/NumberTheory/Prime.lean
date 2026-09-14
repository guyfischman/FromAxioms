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

/-- `[m, m-1, …, 1]`. -/
def upto : Nat → List Nat
  | 0 => []
  | m + 1 => (m + 1) :: upto m

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

/-- The proper divisors of `d`, which are exactly the divisors at most `d/2`. -/
def divisorsBelow (d : Nat) : List Nat := (upto (d / 2)).filter (fun e => d % e == 0)

#print axioms isPrime_minFac
#print axioms bezout
#print axioms bezout_int
#print axioms prime_divides_mul
#print axioms coprime_divides
#print axioms prime_dvd_choose
#print axioms cyclotomicShift_eisenstein
#print axioms exists_factorization
#print axioms exists_prime_gt
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

theorem mul_one (x : Eis) : mul x one = x := by
  simp [mul, one]

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
#print axioms roundDiv_error
#print axioms norm_error_bound
#print axioms sub_mul
#print axioms mod_mul_conj
#print axioms norm_mod_lt
#print axioms dvd_trans
#print axioms norm_induction
#print axioms dvd_add
#print axioms mul_add
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
#print axioms int_sq_nonneg
#print axioms int_sq_eq_zero
#print axioms sq_sub_expand
#print axioms norm_split
#print axioms sq_le_sq
#print axioms neg_mul_le
#print axioms mul_one
#print axioms one_mul
#print axioms mul_ofInt
#print axioms dvd_refl
#print axioms dvd_zero
#print axioms add_sub_cancel
#print axioms ext_of_coords
end Eis

#print axioms NumberTheory.divides_or_not_nat


#print axioms mul_shuffle
#print axioms nat_sq_mul_sq

#print axioms divides_refl
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
#print axioms choose_zero
#print axioms choose_succ_succ
#print axioms choose_gt
#print axioms choose_self
#print axioms choose_one
#print axioms succ_mul_choose
end NumberTheory

namespace ZFSet
export NumberTheory (Divides DividesSet Eis IsFactorization IsPrime bezout bezout_int choose choose_gt choose_one choose_self choose_succ_succ choose_zero coprime_divides cyclotomicShift_eisenstein divides_fact divides_le divides_of_mod_eq_zero divides_or_not_nat divides_refl divides_sub divides_trans divisorsBelow eq_one_of_divides_one exists_factorization exists_prime_ge exists_prime_gt fact fact_pos gcd_eq_one_of_prime_not_divides isPrime_minFac isPrime_three isPrime_two lt_minFac_fact_succ minFac minFacAux minFacAux_divides minFacAux_ge minFacAux_least minFac_divides minFac_ge minFac_least mod_eq_zero_of_divides prime_divides_mul prime_divides_sq prime_dvd_choose prime_sq_irrational prodList succ_mul_choose upto)
end ZFSet
