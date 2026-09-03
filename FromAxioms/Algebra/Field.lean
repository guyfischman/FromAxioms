/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Rings and fields.

The same recognition move as `Group.lean`, one level up. A ring is
an abelian group with a second set function on it; a field is a commutative ring
in which every non-zero element is invertible.

`Rational.lean` proves every one of those axioms already -- associativity and
commutativity of both operations, the two identities, negation, distributivity,
and `ratMul_inv`. Nothing about ℚ is proved here. What is written down is the
definition that recognises it.
-/

import FromAxioms.Algebra.Ring

universe u

open NumberTheory SetTheory
namespace Algebra

/-! ## ℚ -/

def ratAddOp : ZFSet.{u} :=
  graphOn (prod NumberTheory.Rat.{u} NumberTheory.Rat.{u}) NumberTheory.Rat.{u} (fun z => ratAdd (fst z) (snd z))

def ratMulOp : ZFSet.{u} :=
  graphOn (prod NumberTheory.Rat.{u} NumberTheory.Rat.{u}) NumberTheory.Rat.{u} (fun z => ratMul (fst z) (snd z))

private theorem ratAdd_maps {z : ZFSet.{u}} (hz : z ∈ prod NumberTheory.Rat.{u} NumberTheory.Rat.{u}) :
    ratAdd (fst z) (snd z) ∈ NumberTheory.Rat.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff z _ _).mp hz
  rw [fst_opair, snd_opair]
  exact ratAdd_mem_Rat ha hb

private theorem ratMul_maps {z : ZFSet.{u}} (hz : z ∈ prod NumberTheory.Rat.{u} NumberTheory.Rat.{u}) :
    ratMul (fst z) (snd z) ∈ NumberTheory.Rat.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff z _ _).mp hz
  rw [fst_opair, snd_opair]
  exact ratMul_mem_Rat ha hb

theorem opAt_ratAddOp {a b : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u}) (hb : b ∈ NumberTheory.Rat.{u}) :
    opAt ratAddOp.{u} a b = ratAdd a b := by
  rw [opAt, ratAddOp, app_graphOn (fun _ hm => ratAdd_maps hm) (opair_mem_prod ha hb),
    fst_opair, snd_opair]

theorem opAt_ratMulOp {a b : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u}) (hb : b ∈ NumberTheory.Rat.{u}) :
    opAt ratMulOp.{u} a b = ratMul a b := by
  rw [opAt, ratMulOp, app_graphOn (fun _ hm => ratMul_maps hm) (opair_mem_prod ha hb),
    fst_opair, snd_opair]

theorem isGroup_ratAdd : IsGroup NumberTheory.Rat.{u} ratAddOp.{u} ratZero.{u} where
  isFun := graphOn_isFunction _ _ _
  dom := graphOn_domain (fun _ hm => ratAdd_maps hm)
  ran := graphOn_range
  mem_e := ratZero_mem_Rat
  assoc a ha b hb c hc := by
    rw [opAt_ratAddOp ha hb, opAt_ratAddOp (ratAdd_mem_Rat ha hb) hc,
      opAt_ratAddOp hb hc, opAt_ratAddOp ha (ratAdd_mem_Rat hb hc)]
    exact ratAdd_assoc ha hb hc
  left_id a ha := by
    rw [opAt_ratAddOp ratZero_mem_Rat ha, ratAdd_comm ratZero_mem_Rat ha, ratAdd_zero ha]
  right_id a ha := by
    rw [opAt_ratAddOp ha ratZero_mem_Rat, ratAdd_zero ha]
  inverses a ha := by
    refine ⟨ratNeg a, ratNeg_mem_Rat ha, ?_, ?_⟩
    · rw [opAt_ratAddOp ha (ratNeg_mem_Rat ha)]
      exact ratAdd_neg ha
    · rw [opAt_ratAddOp (ratNeg_mem_Rat ha) ha, ratAdd_comm (ratNeg_mem_Rat ha) ha]
      exact ratAdd_neg ha

theorem isRing_rat : IsRing NumberTheory.Rat.{u} ratAddOp.{u} ratMulOp.{u} ratZero.{u} ratOne.{u} where
  addGroup := isGroup_ratAdd
  addComm a ha b hb := by
    rw [opAt_ratAddOp ha hb, opAt_ratAddOp hb ha]
    exact ratAdd_comm ha hb
  mulFun := graphOn_isFunction _ _ _
  mulDom := graphOn_domain (fun _ hm => ratMul_maps hm)
  mulRan := graphOn_range
  mulAssoc a ha b hb c hc := by
    rw [opAt_ratMulOp ha hb, opAt_ratMulOp (ratMul_mem_Rat ha hb) hc,
      opAt_ratMulOp hb hc, opAt_ratMulOp ha (ratMul_mem_Rat hb hc)]
    exact ratMul_assoc ha hb hc
  mulComm a ha b hb := by
    rw [opAt_ratMulOp ha hb, opAt_ratMulOp hb ha]
    exact ratMul_comm ha hb
  mem_one := ratOne_mem_Rat
  mul_one a ha := by
    rw [opAt_ratMulOp ha ratOne_mem_Rat, ratMul_one ha]
  distrib a ha b hb c hc := by
    rw [opAt_ratAddOp hb hc, opAt_ratMulOp ha (ratAdd_mem_Rat hb hc),
      opAt_ratMulOp ha hb, opAt_ratMulOp ha hc,
      opAt_ratAddOp (ratMul_mem_Rat ha hb) (ratMul_mem_Rat ha hc)]
    exact ratMul_add ha hb hc

/-- Cancellation by a nonzero element of a field. One step from the inverse
the field supplies, and stated because nothing in the library states it. -/
theorem mul_right_cancel_field {R add mul zero one x y a : ZFSet.{u}}
    (hF : IsField R add mul zero one) (hx : x ∈ R) (hy : y ∈ R) (ha : a ∈ R)
    (hane : a ≠ zero) (he : opAt mul x a = opAt mul y a) : x = y := by
  have hR := hF.ring
  obtain ⟨a', ha', haa'⟩ := hF.inverses a ha hane
  have hstep : opAt mul (opAt mul x a) a' = opAt mul (opAt mul y a) a' := by
    rw [he]
  rwa [hR.mulAssoc x hx a ha a' ha', hR.mulAssoc y hy a ha a' ha', haa',
    hR.mul_one x hx, hR.mul_one y hy] at hstep

#print axioms mul_right_cancel_field

/-- No zero divisors, negatively, which a field gives for free.

The disjunctive form needs `DecidableVanishing` to choose a side; this one
does not, because it never chooses -- it assumes both factors nonzero and
contradicts. Callers that only ever eliminate the disjunct should take this
and pay nothing. The analysis track reached the same rule from the fraction
field, independently. -/
theorem field_no_zero_divisors_ne {R add mul zero one : ZFSet.{u}}
    (hF : IsField R add mul zero one) :
    ∀ a, a ∈ R → ∀ b, b ∈ R → a ≠ zero → b ≠ zero → opAt mul a b ≠ zero :=
  fun _ ha _ hb hane hbne he => hbne (field_mul_eq_zero hF ha hb he hane)

#print axioms field_no_zero_divisors_ne

/-- ℚ is a field. -/
theorem isField_rat : IsField NumberTheory.Rat.{u} ratAddOp.{u} ratMulOp.{u} ratZero.{u} ratOne.{u} where
  ring := isRing_rat
  zero_ne_one := fun he => ratZero_lt_one.right he
  inverses a ha h0 := by
    refine ⟨ratInv a, ratInv_mem_Rat ha h0, ?_⟩
    rw [opAt_ratMulOp ha (ratInv_mem_Rat ha h0)]
    exact ratMul_inv ha h0

def intMulOp : ZFSet.{u} :=
  graphOn (prod NumberTheory.Int.{u} NumberTheory.Int.{u}) NumberTheory.Int.{u} (fun z => intMul (fst z) (snd z))

private theorem intMul_maps {z : ZFSet.{u}} (hz : z ∈ prod NumberTheory.Int.{u} NumberTheory.Int.{u}) :
    intMul (fst z) (snd z) ∈ NumberTheory.Int.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff z _ _).mp hz
  rw [fst_opair, snd_opair]
  exact intMul_mem_Int ha hb

theorem opAt_intMulOp {a b : ZFSet.{u}} (ha : a ∈ NumberTheory.Int.{u}) (hb : b ∈ NumberTheory.Int.{u}) :
    opAt intMulOp.{u} a b = intMul a b := by
  rw [opAt, intMulOp, app_graphOn (fun _ hm => intMul_maps hm) (opair_mem_prod ha hb),
    fst_opair, snd_opair]

/-- ℤ is a ring, by the same recognition as ℚ. -/
theorem isRing_int : IsRing NumberTheory.Int.{u} intAddOp.{u} intMulOp.{u} intZero.{u} intOne.{u} where
  addGroup := isGroup_intAdd
  addComm := isAbelian_intAdd
  mulFun := graphOn_isFunction _ _ _
  mulDom := graphOn_domain (fun _ hm => intMul_maps hm)
  mulRan := graphOn_range
  mulAssoc a ha b hb c hc := by
    rw [opAt_intMulOp ha hb, opAt_intMulOp (intMul_mem_Int ha hb) hc,
      opAt_intMulOp hb hc, opAt_intMulOp ha (intMul_mem_Int hb hc)]
    exact intMul_assoc ha hb hc
  mulComm a ha b hb := by
    rw [opAt_intMulOp ha hb, opAt_intMulOp hb ha]
    exact intMul_comm ha hb
  mem_one := intOne_mem_Int
  mul_one a ha := by
    rw [opAt_intMulOp ha intOne_mem_Int, intMul_one ha]
  distrib a ha b hb c hc := by
    rw [opAt_intAddOp hb hc, opAt_intMulOp ha (intAdd_mem_Int hb hc),
      opAt_intMulOp ha hb, opAt_intMulOp ha hc,
      opAt_intAddOp (intMul_mem_Int ha hb) (intMul_mem_Int ha hc)]
    exact intMul_add ha hb hc

/-! ## Audit

Nothing classical, and nothing new about ℚ: every clause is a `Rational.lean`
lemma read through `app`. -/

#print axioms isGroup_ratAdd
#print axioms isRing_rat
#print axioms isField_rat
#print axioms isRing_int
/-- A divisibility of naturals, carried into `ℤ` as a ring.

`Divides a b` says `b = a·k` in `Nat`; `eisenstein_least_index` and the rest of
the polynomial layer state divisibility as `∃ c ∈ R, x = opAt mul d c` over an
arbitrary ring. It is the one rewrite between them, and it lets the cyclotomic
coefficient conditions -- which are facts about `choose` in `Nat` -- discharge
the criterion's hypotheses over `ℤ`.

The two layers meet through `intOfNat_mul`. -/
theorem intDvd_of_divides {a b : Nat} (h : Divides a b) :
    ∃ c, c ∈ NumberTheory.Int.{u} ∧
      intOfNat.{u} b = opAt intMulOp.{u} (intOfNat.{u} a) c := by
  obtain ⟨k, hk⟩ := h
  refine ⟨intOfNat.{u} k, intOfNat_mem_Int k, ?_⟩
  rw [opAt_intMulOp (intOfNat_mem_Int a) (intOfNat_mem_Int k), intOfNat_mul, hk]

/-- A numeral divisibility, read back into `Nat`. The converse of
`intDvd_of_divides`, for a numeral cofactor -- which is what the sign step
delivers, so the sign argument and the arithmetic stay separate.

The two layers meet in BOTH directions, through `intOfNat_mul` one way and
`intOfNat_injective` the other. -/
theorem divides_of_intMul_ofNat {a b c : Nat}
    (h : intOfNat.{u} b = intMul (intOfNat.{u} a) (intOfNat.{u} c)) :
    Divides a b := by
  rw [intOfNat_mul] at h
  exact ⟨c, intOfNat_injective h⟩

#print axioms intDvd_of_divides
/-- An integer factorisation of numerals is a `Nat` divisibility.

The sign split, once: the cofactor is zero, positive, or the negation of a
positive, and only the middle case carries content -- the other two force the
dividend to vanish. Nothing is decided that is not computed.

The same derivation appears in `intDvd_ofNat_decidable` and in the Euclid-style
lemma above it. -/
theorem divides_of_intOfNat_eq_mul {a b : Nat} {c : ZFSet.{u}} (hc : c ∈ NumberTheory.Int.{u})
    (he : intOfNat.{u} b = intMul (intOfNat.{u} a) c) : Divides a b := by
  rcases int_eq_or_ne hc intZero_mem_Int with rfl | hcne
  · rw [intMul_zero (intOfNat_mem_Int a)] at he
    have hb0 : b = 0 :=
      intOfNat_injective (by rw [he, intOfNat, ofNat_zero]; rfl)
    exact ⟨0, by rw [hb0, Nat.mul_zero]⟩
  rcases intPositive_or_neg hc hcne with hpos | hneg
  · obtain ⟨m, -, rfl⟩ := exists_intOfNat_of_intPositive hpos
    rw [intOfNat_mul] at he
    exact ⟨m, intOfNat_injective he⟩
  · obtain ⟨m, -, hcm⟩ := exists_intOfNat_of_intPositive hneg
    have hcv : c = intNeg (intOfNat.{u} m) := by rw [← hcm, intNeg_intNeg hc]
    rw [hcv, intMul_neg (intOfNat_mem_Int a) (intOfNat_mem_Int m),
      intOfNat_mul] at he
    rcases Nat.eq_zero_or_pos b with hz | hz
    · exact ⟨0, by rw [hz, Nat.mul_zero]⟩
    · exact absurd (he ▸ intOfNat_mem_intPositive hz)
        (not_intPositive_intNeg_intOfNat (a * m))

#print axioms divides_of_intOfNat_eq_mul

/-- Euclid's lemma over `ℤ`, in the ring-level divisibility form.

`prime_divides_mul` is stated over `Nat`; the `IsEisenstein` `prime` clause
quantifies over all of `NumberTheory.Int`, and the gap is the SIGN CASE-SPLIT. Zero gives the
product zero, a positive cofactor is a numeral outright, and a negative one
makes the right side the negation of a positive numeral while the left is a
numeral -- which only both-vanishing allows.

That case-split IS the `natAbs` argument, done inline, so `natAbs` need not
exist for this. -/
theorem intPrime_divides_mul_ofNat {p j k : Nat} (hp : IsPrime p)
    (h : ∃ c, c ∈ NumberTheory.Int.{u} ∧
      intOfNat.{u} (j * k) = intMul (intOfNat.{u} p) c) :
    Divides p j ∨ Divides p k := by
  obtain ⟨c, hc, he⟩ := h
  refine prime_divides_mul hp ?_
  exact divides_of_intOfNat_eq_mul hc he

/-- Divisibility by a numeral is decidable, on numerals. The `dec` clause of
`IsEisenstein` at `ℤ`. `Nat` divides by a remainder test, `intDvd_of_divides`
carries the positive answer across, and the negative answer is the sign split
again -- so nothing here is decided that is not computed. -/
theorem intDvd_ofNat_decidable {a b : Nat} :
    (∃ c, c ∈ NumberTheory.Int.{u} ∧ intOfNat.{u} b = intMul (intOfNat.{u} a) c)
      ∨ ¬ (∃ c, c ∈ NumberTheory.Int.{u} ∧ intOfNat.{u} b = intMul (intOfNat.{u} a) c) := by
  rcases Nat.eq_zero_or_pos (b % a) with heq | hne
  · obtain ⟨k, hk⟩ : Divides a b := divides_of_mod_eq_zero heq
    exact Or.inl ⟨intOfNat.{u} k, intOfNat_mem_Int k, by rw [intOfNat_mul, hk]⟩
  refine Or.inr ?_
  rintro ⟨c, hc, he⟩
  have hb : Divides a b := divides_of_intOfNat_eq_mul hc he
  exact absurd (mod_eq_zero_of_divides hb) (by omega)

/-- Every integer is a numeral or the negation of one. The reduction that
turns the numeral-restricted divisibility lemmas into the arbitrary-element
clauses `IsEisenstein` quantifies over. Three sign splits rather than one, and
each is this lemma. -/
theorem int_eq_ofNat_or_neg {z : ZFSet.{u}} (hz : z ∈ NumberTheory.Int.{u}) :
    (∃ n : Nat, z = intOfNat.{u} n)
      ∨ (∃ n : Nat, z = intNeg (intOfNat.{u} n)) := by
  rcases int_eq_or_ne hz intZero_mem_Int with rfl | hne
  · exact Or.inl ⟨0, by rw [intOfNat, ofNat_zero]; rfl⟩
  rcases intPositive_or_neg hz hne with hpos | hneg
  · obtain ⟨n, -, rfl⟩ := exists_intOfNat_of_intPositive hpos
    exact Or.inl ⟨n, rfl⟩
  · obtain ⟨n, -, hcm⟩ := exists_intOfNat_of_intPositive hneg
    exact Or.inr ⟨n, by rw [← hcm, intNeg_intNeg hz]⟩

/-- A numeral divides an integer exactly when it divides its magnitude.
The sign is absorbed on both sides: if `d` divides `z` then it divides `-z`,
because negating the cofactor suffices. -/
theorem intDvd_neg_iff {d z : ZFSet.{u}} (hd : d ∈ NumberTheory.Int.{u}) (hz : z ∈ NumberTheory.Int.{u}) :
    (∃ c, c ∈ NumberTheory.Int.{u} ∧ z = intMul d c)
      ↔ (∃ c, c ∈ NumberTheory.Int.{u} ∧ intNeg z = intMul d c) := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨intNeg c, intNeg_mem_Int hc, by rw [intMul_neg hd hc]⟩
  · rintro ⟨c, hc, he⟩
    refine ⟨intNeg c, intNeg_mem_Int hc, ?_⟩
    rw [intMul_neg hd hc, ← he, intNeg_intNeg hz]

#print axioms divides_of_intMul_ofNat
#print axioms intPrime_divides_mul_ofNat
#print axioms intDvd_ofNat_decidable
#print axioms int_eq_ofNat_or_neg
/-- Divisibility by a numeral is decidable, at ANY integer. The `dec` clause
of `IsEisenstein` at `ℤ`, general rather than numeral-restricted: the dividend
normalises to a numeral by `int_eq_ofNat_or_neg` and the sign is absorbed by
`intDvd_neg_iff`, so the two cases are the SAME case. -/
theorem intDvd_decidable {a : Nat} {z : ZFSet.{u}} (hz : z ∈ NumberTheory.Int.{u}) :
    (∃ c, c ∈ NumberTheory.Int.{u} ∧ z = intMul (intOfNat.{u} a) c)
      ∨ ¬ (∃ c, c ∈ NumberTheory.Int.{u} ∧ z = intMul (intOfNat.{u} a) c) := by
  rcases int_eq_ofNat_or_neg hz with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · exact intDvd_ofNat_decidable
  · rcases (intDvd_ofNat_decidable (a := a) (b := n)) with hy | hn
    · exact Or.inl ((intDvd_neg_iff (intOfNat_mem_Int a)
        (intOfNat_mem_Int n)).mp hy)
    · exact Or.inr (fun hc => hn ((intDvd_neg_iff (intOfNat_mem_Int a)
        (intOfNat_mem_Int n)).mpr hc))

#print axioms intDvd_neg_iff
/-- Euclid's lemma over `ℤ` at ARBITRARY elements. The `prime` clause of
`IsEisenstein` at the integers. Each factor normalises to a numeral by
`int_eq_ofNat_or_neg`; the sign leaves the product, and the conclusion
transports back by `intDvd_neg_iff`.

`intDvd_of_divides` states its conclusion with `opAt intMulOp` and the sign
machinery uses `intMul`, so `opAt_intMulOp` converts -- two spellings of one
operation, meeting here. -/
theorem intPrime_divides_mul {p : Nat} (hp : IsPrime p) {a b : ZFSet.{u}}
    (ha : a ∈ NumberTheory.Int.{u}) (hb : b ∈ NumberTheory.Int.{u})
    (h : ∃ c, c ∈ NumberTheory.Int.{u} ∧ intMul a b = intMul (intOfNat.{u} p) c) :
    (∃ c, c ∈ NumberTheory.Int.{u} ∧ a = intMul (intOfNat.{u} p) c)
      ∨ (∃ c, c ∈ NumberTheory.Int.{u} ∧ b = intMul (intOfNat.{u} p) c) := by
  have conv : ∀ {m n : Nat}, Divides m n ->
      ∃ c, c ∈ NumberTheory.Int.{u} ∧ intOfNat.{u} n = intMul (intOfNat.{u} m) c := by
    intro m n hd
    obtain ⟨c, hc, he⟩ := intDvd_of_divides hd
    exact ⟨c, hc, by rw [he, opAt_intMulOp (intOfNat_mem_Int m) hc]⟩
  have key : ∀ j k : Nat,
      (∃ c, c ∈ NumberTheory.Int.{u} ∧
        intMul (intOfNat.{u} j) (intOfNat.{u} k) = intMul (intOfNat.{u} p) c) ->
      (∃ c, c ∈ NumberTheory.Int.{u} ∧ intOfNat.{u} j = intMul (intOfNat.{u} p) c)
        ∨ (∃ c, c ∈ NumberTheory.Int.{u} ∧ intOfNat.{u} k = intMul (intOfNat.{u} p) c) := by
    intro j k hjk
    rw [intOfNat_mul] at hjk
    rcases intPrime_divides_mul_ofNat hp hjk with hd | hd
    · exact Or.inl (conv hd)
    · exact Or.inr (conv hd)
  have hmul : ∀ j k : Nat, intMul (intOfNat.{u} j) (intOfNat.{u} k) ∈ NumberTheory.Int.{u} :=
    fun j k => by rw [intOfNat_mul]; exact intOfNat_mem_Int _
  rcases int_eq_ofNat_or_neg ha with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    rcases int_eq_ofNat_or_neg hb with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact key j k h
  · rw [intMul_neg (intOfNat_mem_Int j) (intOfNat_mem_Int k),
      ← intDvd_neg_iff (intOfNat_mem_Int p) (hmul j k)] at h
    exact (key j k h).imp id
      (intDvd_neg_iff (intOfNat_mem_Int p) (intOfNat_mem_Int k)).mp
  · rw [intNeg_mul (intOfNat_mem_Int j) (intOfNat_mem_Int k),
      ← intDvd_neg_iff (intOfNat_mem_Int p) (hmul j k)] at h
    exact (key j k h).imp
      (intDvd_neg_iff (intOfNat_mem_Int p) (intOfNat_mem_Int j)).mp id
  · rw [intNeg_mul (intOfNat_mem_Int j) (intNeg_mem_Int (intOfNat_mem_Int k)),
      intMul_neg (intOfNat_mem_Int j) (intOfNat_mem_Int k),
      intNeg_intNeg (hmul j k)] at h
    exact (key j k h).imp
      (intDvd_neg_iff (intOfNat_mem_Int p) (intOfNat_mem_Int j)).mp
      (intDvd_neg_iff (intOfNat_mem_Int p) (intOfNat_mem_Int k)).mp

#print axioms intDvd_decidable

#print axioms intPrime_divides_mul

/-- The cyclotomic coefficient conditions, in the ring form the criterion
takes.

`cyclotomicShift_eisenstein` proves `p ∣ C(p, j+1)` in `Nat`;
`eisenstein_least_index` wants divisibility as `∃ c ∈ R, x = d·c` over a ring.
This is the composition, and it is one application of `intDvd_of_divides` --
which is the whole of the distance between the two layers the criterion was
built from opposite ends of. -/
theorem cyclotomicShift_dvd_int {p : Nat} (hp : IsPrime p) {j : Nat}
    (hj : j < p - 1) :
    ∃ c, c ∈ NumberTheory.Int.{u} ∧ intOfNat.{u} (choose p (j + 1))
      = opAt intMulOp.{u} (intOfNat.{u} p) c :=
  intDvd_of_divides ((cyclotomicShift_eisenstein hp).left j hj)

#print axioms cyclotomicShift_dvd_int

end Algebra

namespace ZFSet
export Algebra (cyclotomicShift_dvd_int divides_of_intMul_ofNat divides_of_intOfNat_eq_mul field_no_zero_divisors_ne intDvd_decidable intDvd_neg_iff intDvd_ofNat_decidable intDvd_of_divides intMulOp intPrime_divides_mul intPrime_divides_mul_ofNat int_eq_ofNat_or_neg isField_rat isGroup_ratAdd isRing_int isRing_rat mul_right_cancel_field opAt_intMulOp opAt_ratAddOp opAt_ratMulOp ratAddOp ratMulOp)
end ZFSet
