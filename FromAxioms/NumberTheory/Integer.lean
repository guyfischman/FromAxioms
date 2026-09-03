/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The integers.

`ℤ` is `ω × ω` modulo `(a,b) ~ (c,d) ↔ a + d = c + b`, the pair `(a,b)` standing
for `a - b`.

Transitivity is where `add_left_cancel` earns its place: from `a+d = c+b` and
`c+f = e+d` one has to reach `a+f = e+b`, which needs cancellation, not just
commutativity and associativity.
-/

import FromAxioms.NumberTheory.Arith
import FromAxioms.SetTheory.EquivClass

universe u

open SetTheory
namespace NumberTheory

def omegaPairs : ZFSet.{u} := prod omega.{u} omega.{u}

theorem mem_omegaPairs_iff (p : ZFSet.{u}) :
    p ∈ omegaPairs.{u} ↔ ∃ a, a ∈ omega.{u} ∧ ∃ b, b ∈ omega.{u} ∧ p = opair a b :=
  mem_prod_iff p omega omega

def intRel : ZFSet.{u} :=
  sep (fun p => ∃ a b c d, p = opair (opair a b) (opair c d) ∧ add a d = add c b)
    (prod omegaPairs.{u} omegaPairs.{u})

theorem mem_intRel_iff {a b c d : ZFSet.{u}}
    (ha : a ∈ omega.{u}) (hb : b ∈ omega.{u})
    (hc : c ∈ omega.{u}) (hd : d ∈ omega.{u}) :
    opair (opair a b) (opair c d) ∈ intRel.{u} ↔ add a d = add c b :=
  mem_pairRel_iff (opair_mem_prod ha hb) (opair_mem_prod hc hd)

theorem intRel_isEquivRel : IsEquivRel intRel.{u} omegaPairs.{u} where
  refl p hp := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_omegaPairs_iff p).mp hp
    exact (mem_intRel_iff ha hb ha hb).mpr rfl
  symm p q hp hq h := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_omegaPairs_iff p).mp hp
    obtain ⟨c, hc, d, hd, rfl⟩ := (mem_omegaPairs_iff q).mp hq
    exact (mem_intRel_iff hc hd ha hb).mpr
      ((mem_intRel_iff ha hb hc hd).mp h).symm
  trans p q s hp hq hs h₁ h₂ := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_omegaPairs_iff p).mp hp
    obtain ⟨c, hc, d, hd, rfl⟩ := (mem_omegaPairs_iff q).mp hq
    obtain ⟨e, he, f, hf, rfl⟩ := (mem_omegaPairs_iff s).mp hs
    have e₁ := (mem_intRel_iff ha hb hc hd).mp h₁
    have e₂ := (mem_intRel_iff hc hd he hf).mp h₂
    refine (mem_intRel_iff ha hb he hf).mpr ?_
    -- transport to `Nat`, where the cancellation is `omega`
    obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
    obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
    obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
    obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
    obtain ⟨ne, rfl⟩ := (mem_omega_iff e).mp he
    obtain ⟨nf, rfl⟩ := (mem_omega_iff f).mp hf
    rw [add_ofNat, add_ofNat] at e₁ e₂ ⊢
    have k₁ := ofNat_injective e₁
    have k₂ := ofNat_injective e₂
    exact congrArg ofNat (by omega)

/-- The integers: zero and the negative numbers, adjoined to the naturals as
differences. -/
def Int : ZFSet.{u} := quotientSet intRel.{u} omegaPairs.{u}

/-- `a - b` as an integer. -/
def intOf (a b : ZFSet.{u}) : ZFSet.{u} := cls intRel.{u} omegaPairs.{u} (opair a b)

theorem intOf_mem_Int {a b : ZFSet.{u}} (ha : a ∈ omega.{u}) (hb : b ∈ omega.{u}) :
    intOf a b ∈ Int.{u} :=
  cls_mem_quotientSet (opair_mem_prod ha hb)

/-- The defining property: two pairs name the same integer exactly when they
differ by the same amount. -/
theorem intOf_eq_intOf_iff {a b c d : ZFSet.{u}}
    (ha : a ∈ omega.{u}) (hb : b ∈ omega.{u})
    (hc : c ∈ omega.{u}) (hd : d ∈ omega.{u}) :
    intOf a b = intOf c d ↔ add a d = add c b :=
  Iff.trans
    (cls_eq_cls_iff intRel_isEquivRel (opair_mem_prod ha hb) (opair_mem_prod hc hd))
    (mem_intRel_iff ha hb hc hd)

theorem mem_Int_iff (z : ZFSet.{u}) :
    z ∈ Int.{u} ↔ ∃ a, a ∈ omega.{u} ∧ ∃ b, b ∈ omega.{u} ∧ z = intOf a b := by
  refine Iff.trans (mem_quotientSet_iff _ _ z) ⟨?_, ?_⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_omegaPairs_iff p).mp hp
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨opair a b, opair_mem_prod ha hb, rfl⟩

theorem mem_intOf_iff {a b : ZFSet.{u}} (ha : a ∈ omega.{u}) (hb : b ∈ omega.{u})
    (p : ZFSet.{u}) :
    p ∈ intOf a b ↔ ∃ s, s ∈ omega.{u} ∧ ∃ t, t ∈ omega.{u} ∧
      p = opair s t ∧ add a t = add s b := by
  refine Iff.trans (mem_cls_iff _ _ _ p) ⟨?_, ?_⟩
  · rintro ⟨hp, hr⟩
    obtain ⟨s, hs, t, ht, rfl⟩ := (mem_omegaPairs_iff p).mp hp
    exact ⟨s, hs, t, ht, rfl, (mem_intRel_iff ha hb hs ht).mp hr⟩
  · rintro ⟨s, hs, t, ht, rfl, he⟩
    exact ⟨opair_mem_prod hs ht, (mem_intRel_iff ha hb hs ht).mpr he⟩

/-! ## Arithmetic

The operations are carved out of `ω × ω` by separation, quantifying into the
classes rather than selecting representatives from them, which keeps them
choice-free. -/

def intAdd (z w : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ a b c d, opair a b ∈ z ∧ opair c d ∈ w ∧
        ∃ s t, p = opair s t ∧ add (add a c) t = add s (add b d)) omegaPairs.{u}

def intNeg (z : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ a b, opair a b ∈ z ∧
        ∃ s t, p = opair s t ∧ add b t = add s a) omegaPairs.{u}

#print axioms Int

/-- Multiplication of integers, on the difference classes. -/
def intMul (z w : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ a b c d, opair a b ∈ z ∧ opair c d ∈ w ∧
        ∃ s t, p = opair s t ∧
          add (add (mul a c) (mul b d)) t = add s (add (mul a d) (mul b c)))
    omegaPairs.{u}

theorem intAdd_intOf {a b c d : ZFSet.{u}} (ha : a ∈ omega.{u}) (hb : b ∈ omega.{u})
    (hc : c ∈ omega.{u}) (hd : d ∈ omega.{u}) :
    intAdd (intOf a b) (intOf c d) = intOf (add a c) (add b d) := by
  refine ext _ _ fun p => ?_
  refine Iff.trans (mem_sep_iff _ p _) ?_
  refine Iff.trans ?_
    (mem_intOf_iff (add_mem_omega ha hc) (add_mem_omega hb hd) p).symm
  constructor
  · rintro ⟨hp, a', b', c', d', h₁, h₂, s, t, rfl, he⟩
    obtain ⟨_, ha', _, hb', h1e, r₁⟩ := (mem_intOf_iff ha hb _).mp h₁
    obtain ⟨rfl, rfl⟩ := opair_injective h1e
    obtain ⟨_, hc', _, hd', h2e, r₂⟩ := (mem_intOf_iff hc hd _).mp h₂
    obtain ⟨rfl, rfl⟩ := opair_injective h2e
    have hs := mem_prod_left hp
    have ht := mem_prod_right hp
    refine ⟨s, hs, t, ht, rfl, ?_⟩
    obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
    obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
    obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
    obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
    obtain ⟨na', rfl⟩ := (mem_omega_iff _).mp ha'
    obtain ⟨nb', rfl⟩ := (mem_omega_iff _).mp hb'
    obtain ⟨nc', rfl⟩ := (mem_omega_iff _).mp hc'
    obtain ⟨nd', rfl⟩ := (mem_omega_iff _).mp hd'
    obtain ⟨ns, rfl⟩ := (mem_omega_iff s).mp hs
    obtain ⟨nt, rfl⟩ := (mem_omega_iff t).mp ht
    rw [add_ofNat, add_ofNat] at r₁ r₂
    rw [add_ofNat, add_ofNat, add_ofNat, add_ofNat] at he
    rw [add_ofNat, add_ofNat, add_ofNat, add_ofNat]
    have k₁ := ofNat_injective r₁
    have k₂ := ofNat_injective r₂
    have k₃ := ofNat_injective he
    exact congrArg ofNat (by omega)
  · rintro ⟨s, hs, t, ht, rfl, he⟩
    exact ⟨opair_mem_prod hs ht, a, b, c, d,
      mem_cls_self intRel_isEquivRel (opair_mem_prod ha hb),
      mem_cls_self intRel_isEquivRel (opair_mem_prod hc hd), s, t, rfl, he⟩

theorem intAdd_mem_Int {z w : ZFSet.{u}} (hz : z ∈ Int.{u}) (hw : w ∈ Int.{u}) :
    intAdd z w ∈ Int.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff w).mp hw
  rw [intAdd_intOf ha hb hc hd]
  exact intOf_mem_Int (add_mem_omega ha hc) (add_mem_omega hb hd)

theorem intAdd_comm {z w : ZFSet.{u}} (hz : z ∈ Int.{u}) (hw : w ∈ Int.{u}) :
    intAdd z w = intAdd w z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff w).mp hw
  rw [intAdd_intOf ha hb hc hd, intAdd_intOf hc hd ha hb,
      add_comm ha hc, add_comm hb hd]

theorem intAdd_assoc {z w v : ZFSet.{u}} (hz : z ∈ Int.{u}) (hw : w ∈ Int.{u})
    (hv : v ∈ Int.{u}) : intAdd (intAdd z w) v = intAdd z (intAdd w v) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff w).mp hw
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_Int_iff v).mp hv
  rw [intAdd_intOf ha hb hc hd, intAdd_intOf hc hd he hf,
      intAdd_intOf (add_mem_omega ha hc) (add_mem_omega hb hd) he hf,
      intAdd_intOf ha hb (add_mem_omega hc he) (add_mem_omega hd hf),
      add_assoc ha hc he, add_assoc hb hd hf]

theorem intAdd_left_cancel {k x y : ZFSet.{u}} (hk : k ∈ Int.{u}) (hx : x ∈ Int.{u})
    (hy : y ∈ Int.{u}) (h : intAdd k x = intAdd k y) : x = y := by
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_Int_iff k).mp hk
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff x).mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff y).mp hy
  obtain ⟨np, rfl⟩ := (mem_omega_iff p).mp hp
  obtain ⟨nq, rfl⟩ := (mem_omega_iff q).mp hq
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
  obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
  rw [intAdd_intOf hp hq ha hb, intAdd_intOf hp hq hc hd,
      intOf_eq_intOf_iff (add_mem_omega hp ha) (add_mem_omega hq hb)
        (add_mem_omega hp hc) (add_mem_omega hq hd)] at h
  simp only [add_ofNat] at h
  refine (intOf_eq_intOf_iff (ofNat_mem_omega na) (ofNat_mem_omega nb)
    (ofNat_mem_omega nc) (ofNat_mem_omega nd)).mpr ?_
  simp only [add_ofNat]
  exact congrArg ofNat (by have := ofNat_injective h; omega)

/-- Zero. -/
def intZero : ZFSet.{u} := intOf empty.{u} empty.{u}

theorem intZero_mem_Int : intZero.{u} ∈ Int.{u} :=
  intOf_mem_Int empty_mem_omega empty_mem_omega

@[simp] theorem intAdd_zero {z : ZFSet.{u}} (hz : z ∈ Int.{u}) :
    intAdd z intZero.{u} = z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  rw [intZero, intAdd_intOf ha hb empty_mem_omega empty_mem_omega,
      add_empty, add_empty]

theorem intNeg_intOf {a b : ZFSet.{u}} (ha : a ∈ omega.{u}) (hb : b ∈ omega.{u}) :
    intNeg (intOf a b) = intOf b a := by
  refine ext _ _ fun p => ?_
  refine Iff.trans (mem_sep_iff _ p _) (Iff.trans ?_ (mem_intOf_iff hb ha p).symm)
  constructor
  · rintro ⟨hp, a', b', h₁, s, t, rfl, he⟩
    obtain ⟨_, ha', _, hb', h1e, r₁⟩ := (mem_intOf_iff ha hb _).mp h₁
    obtain ⟨rfl, rfl⟩ := opair_injective h1e
    have hs := mem_prod_left hp
    have ht := mem_prod_right hp
    refine ⟨s, hs, t, ht, rfl, ?_⟩
    obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
    obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
    obtain ⟨na', rfl⟩ := (mem_omega_iff _).mp ha'
    obtain ⟨nb', rfl⟩ := (mem_omega_iff _).mp hb'
    obtain ⟨ns, rfl⟩ := (mem_omega_iff s).mp hs
    obtain ⟨nt, rfl⟩ := (mem_omega_iff t).mp ht
    rw [add_ofNat, add_ofNat] at r₁ he
    rw [add_ofNat, add_ofNat]
    have k₁ := ofNat_injective r₁
    have k₂ := ofNat_injective he
    exact congrArg ofNat (by omega)
  · rintro ⟨s, hs, t, ht, rfl, he⟩
    exact ⟨opair_mem_prod hs ht, a, b,
      mem_cls_self intRel_isEquivRel (opair_mem_prod ha hb), s, t, rfl, he⟩

@[simp] theorem intNeg_zero : intNeg intZero.{u} = intZero.{u} := by
  rw [intZero, intNeg_intOf empty_mem_omega empty_mem_omega]

theorem intAdd_neg {z : ZFSet.{u}} (hz : z ∈ Int.{u}) :
    intAdd z (intNeg z) = intZero.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  rw [intNeg_intOf ha hb, intAdd_intOf ha hb hb ha, intZero]
  refine (intOf_eq_intOf_iff (add_mem_omega ha hb) (add_mem_omega hb ha)
    empty_mem_omega empty_mem_omega).mpr ?_
  rw [add_empty, empty_add (add_mem_omega hb ha)]
  exact add_comm ha hb

/-- Well-definedness of multiplication, at the `Nat` level.

Nonlinear, so `omega` cannot see it directly. Supplying the two products of the
hypotheses as separate linear facts reduces it to linear arithmetic over the
product atoms; the two `have`s are the two halves of varying one pair at a
time. -/
private theorem nat_cancel {p q X Y : Nat} (hpq : p ≠ q)
    (h : p * X + q * Y = p * Y + q * X) : X = Y := by
  rcases Nat.lt_or_ge q p with hlt | hge
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
    subst hk
    simp only [Nat.add_mul, Nat.one_mul] at h
    refine Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) ?_
    rw [Nat.succ_mul, Nat.succ_mul]; omega
  · rcases Nat.eq_or_lt_of_le hge with rfl | hlt
    · exact absurd rfl hpq
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
      subst hk
      simp only [Nat.add_mul, Nat.one_mul] at h
      refine (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) ?_).symm
      rw [Nat.succ_mul, Nat.succ_mul]; omega

private theorem nat_mul_wd {a b a' b' c d c' d' : Nat}
    (h₁ : a + b' = a' + b) (h₂ : c + d' = c' + d) :
    (a * c + b * d) + (a' * d' + b' * c') = (a' * c' + b' * d') + (a * d + b * c) := by
  have s1 : (a * c + b * d) + (a' * d + b' * c)
      = (a' * c + b' * d) + (a * d + b * c) := by
    have e1 : (a + b') * c = (a' + b) * c := by rw [h₁]
    have e2 : (a + b') * d = (a' + b) * d := by rw [h₁]
    rw [Nat.add_mul, Nat.add_mul] at e1 e2
    omega
  have s2 : (a' * c + b' * d) + (a' * d' + b' * c')
      = (a' * c' + b' * d') + (a' * d + b' * c) := by
    have e3 : a' * (c + d') = a' * (c' + d) := by rw [h₂]
    have e4 : b' * (c + d') = b' * (c' + d) := by rw [h₂]
    rw [Nat.mul_add, Nat.mul_add] at e3 e4
    omega
  omega

theorem intMul_intOf {a b c d : ZFSet.{u}} (ha : a ∈ omega.{u}) (hb : b ∈ omega.{u})
    (hc : c ∈ omega.{u}) (hd : d ∈ omega.{u}) :
    intMul (intOf a b) (intOf c d)
      = intOf (add (mul a c) (mul b d)) (add (mul a d) (mul b c)) := by
  refine ext _ _ fun p => ?_
  refine Iff.trans (mem_sep_iff _ p _) ?_
  refine Iff.trans ?_ (mem_intOf_iff
    (add_mem_omega (mul_mem_omega ha hc) (mul_mem_omega hb hd))
    (add_mem_omega (mul_mem_omega ha hd) (mul_mem_omega hb hc)) p).symm
  constructor
  · rintro ⟨hp, a', b', c', d', h₁, h₂, s, t, rfl, he⟩
    obtain ⟨_, ha', _, hb', h1e, r₁⟩ := (mem_intOf_iff ha hb _).mp h₁
    obtain ⟨rfl, rfl⟩ := opair_injective h1e
    obtain ⟨_, hc', _, hd', h2e, r₂⟩ := (mem_intOf_iff hc hd _).mp h₂
    obtain ⟨rfl, rfl⟩ := opair_injective h2e
    have hs := mem_prod_left hp
    have ht := mem_prod_right hp
    refine ⟨s, hs, t, ht, rfl, ?_⟩
    obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
    obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
    obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
    obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
    obtain ⟨na', rfl⟩ := (mem_omega_iff _).mp ha'
    obtain ⟨nb', rfl⟩ := (mem_omega_iff _).mp hb'
    obtain ⟨nc', rfl⟩ := (mem_omega_iff _).mp hc'
    obtain ⟨nd', rfl⟩ := (mem_omega_iff _).mp hd'
    obtain ⟨ns, rfl⟩ := (mem_omega_iff s).mp hs
    obtain ⟨nt, rfl⟩ := (mem_omega_iff t).mp ht
    rw [add_ofNat, add_ofNat] at r₁ r₂
    rw [mul_ofNat, mul_ofNat, mul_ofNat, mul_ofNat,
        add_ofNat, add_ofNat, add_ofNat, add_ofNat] at he
    rw [mul_ofNat, mul_ofNat, mul_ofNat, mul_ofNat,
        add_ofNat, add_ofNat, add_ofNat, add_ofNat]
    have k₁ := ofNat_injective r₁
    have k₂ := ofNat_injective r₂
    have k₃ := ofNat_injective he
    have w := nat_mul_wd k₁ k₂
    exact congrArg ofNat (by omega)
  · rintro ⟨s, hs, t, ht, rfl, he⟩
    exact ⟨opair_mem_prod hs ht, a, b, c, d,
      mem_cls_self intRel_isEquivRel (opair_mem_prod ha hb),
      mem_cls_self intRel_isEquivRel (opair_mem_prod hc hd), s, t, rfl, he⟩

theorem intMul_mem_Int {z w : ZFSet.{u}} (hz : z ∈ Int.{u}) (hw : w ∈ Int.{u}) :
    intMul z w ∈ Int.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff w).mp hw
  rw [intMul_intOf ha hb hc hd]
  exact intOf_mem_Int (add_mem_omega (mul_mem_omega ha hc) (mul_mem_omega hb hd))
    (add_mem_omega (mul_mem_omega ha hd) (mul_mem_omega hb hc))

theorem intMul_comm {z w : ZFSet.{u}} (hz : z ∈ Int.{u}) (hw : w ∈ Int.{u}) :
    intMul z w = intMul w z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff w).mp hw
  rw [intMul_intOf ha hb hc hd, intMul_intOf hc hd ha hb,
      mul_comm ha hc, mul_comm hb hd, mul_comm hc hb, mul_comm hd ha,
      add_comm (mul_mem_omega ha hd) (mul_mem_omega hb hc)]

/-- One. -/
def intOne : ZFSet.{u} := intOf (ofNat.{u} 1) empty.{u}

theorem intOne_mem_Int : intOne.{u} ∈ Int.{u} :=
  intOf_mem_Int (ofNat_mem_omega 1) empty_mem_omega

@[simp] theorem intMul_one {z : ZFSet.{u}} (hz : z ∈ Int.{u}) :
    intMul z intOne.{u} = z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨m, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨n, rfl⟩ := (mem_omega_iff b).mp hb
  rw [intOne, intMul_intOf ha hb (ofNat_mem_omega 1) empty_mem_omega,
      ← ofNat_zero, mul_ofNat, mul_ofNat, mul_ofNat, mul_ofNat,
      add_ofNat, add_ofNat]
  simp

@[simp] theorem intMul_zero {z : ZFSet.{u}} (hz : z ∈ Int.{u}) :
    intMul z intZero.{u} = intZero.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  rw [intZero, ← ofNat_zero, intMul_intOf ha hb (ofNat_mem_omega 0) (ofNat_mem_omega 0)]
  simp only [mul_ofNat, add_ofNat, Nat.mul_zero, Nat.add_zero]

theorem intZero_mul {z : ZFSet.{u}} (hz : z ∈ Int.{u}) :
    intMul intZero.{u} z = intZero.{u} := by
  rw [intMul_comm intZero_mem_Int hz, intMul_zero hz]

theorem intOne_mul {z : ZFSet.{u}} (hz : z ∈ Int.{u}) : intMul intOne.{u} z = z := by
  rw [intMul_comm intOne_mem_Int hz]
  exact intMul_one hz

theorem intMul_assoc {z w v : ZFSet.{u}} (hz : z ∈ Int.{u}) (hw : w ∈ Int.{u})
    (hv : v ∈ Int.{u}) : intMul (intMul z w) v = intMul z (intMul w v) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff w).mp hw
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_Int_iff v).mp hv
  rw [intMul_intOf ha hb hc hd, intMul_intOf hc hd he hf,
      intMul_intOf (add_mem_omega (mul_mem_omega ha hc) (mul_mem_omega hb hd))
        (add_mem_omega (mul_mem_omega ha hd) (mul_mem_omega hb hc)) he hf,
      intMul_intOf ha hb (add_mem_omega (mul_mem_omega hc he) (mul_mem_omega hd hf))
        (add_mem_omega (mul_mem_omega hc hf) (mul_mem_omega hd he))]
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
  obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
  obtain ⟨ne, rfl⟩ := (mem_omega_iff e).mp he
  obtain ⟨nf, rfl⟩ := (mem_omega_iff f).mp hf
  simp only [mul_ofNat, add_ofNat]
  congr 1 <;> refine congrArg ofNat ?_ <;>
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] <;> omega

theorem intNeg_mem_Int {z : ZFSet.{u}} (hz : z ∈ Int.{u}) : intNeg z ∈ Int.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  rw [intNeg_intOf ha hb]
  exact intOf_mem_Int hb ha

theorem intNeg_mul {x y : ZFSet.{u}} (hx : x ∈ Int.{u}) (hy : y ∈ Int.{u}) :
    intMul (intNeg x) y = intNeg (intMul x y) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff x).mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff y).mp hy
  rw [intNeg_intOf ha hb, intMul_intOf hb ha hc hd, intMul_intOf ha hb hc hd,
      intNeg_intOf (add_mem_omega (mul_mem_omega ha hc) (mul_mem_omega hb hd))
        (add_mem_omega (mul_mem_omega ha hd) (mul_mem_omega hb hc))]
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
  obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
  simp only [mul_ofNat, add_ofNat]
  congr 1 <;> exact congrArg ofNat (by omega)

@[simp] theorem intNeg_intNeg {z : ZFSet.{u}} (hz : z ∈ Int.{u}) :
    intNeg (intNeg z) = z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  rw [intNeg_intOf ha hb, intNeg_intOf hb ha]

theorem intMul_neg {x y : ZFSet.{u}} (hx : x ∈ Int.{u}) (hy : y ∈ Int.{u}) :
    intMul x (intNeg y) = intNeg (intMul x y) := by
  rw [intMul_comm hx (intNeg_mem_Int hy), intNeg_mul hy hx, intMul_comm hy hx]

/-- The four-factor rearrangement the order on ℚ is proved well defined by. -/
theorem intMul_mul_comm {x y z w : ZFSet.{u}} (hx : x ∈ Int.{u}) (hy : y ∈ Int.{u})
    (hz : z ∈ Int.{u}) (hw : w ∈ Int.{u}) :
    intMul (intMul x y) (intMul z w) = intMul (intMul x z) (intMul y w) := by
  rw [intMul_assoc hx hy (intMul_mem_Int hz hw), ← intMul_assoc hy hz hw,
      intMul_comm hy hz, intMul_assoc hz hy hw,
      ← intMul_assoc hx hz (intMul_mem_Int hy hw)]

theorem intMul_add {x y z : ZFSet.{u}} (hx : x ∈ Int.{u}) (hy : y ∈ Int.{u})
    (hz : z ∈ Int.{u}) : intMul x (intAdd y z) = intAdd (intMul x y) (intMul x z) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff x).mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff y).mp hy
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_Int_iff z).mp hz
  rw [intAdd_intOf hc hd he hf,
      intMul_intOf ha hb (add_mem_omega hc he) (add_mem_omega hd hf),
      intMul_intOf ha hb hc hd, intMul_intOf ha hb he hf,
      intAdd_intOf (add_mem_omega (mul_mem_omega ha hc) (mul_mem_omega hb hd))
        (add_mem_omega (mul_mem_omega ha hd) (mul_mem_omega hb hc))
        (add_mem_omega (mul_mem_omega ha he) (mul_mem_omega hb hf))
        (add_mem_omega (mul_mem_omega ha hf) (mul_mem_omega hb he))]
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
  obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
  obtain ⟨ne, rfl⟩ := (mem_omega_iff e).mp he
  obtain ⟨nf, rfl⟩ := (mem_omega_iff f).mp hf
  simp only [mul_ofNat, add_ofNat]
  congr 1 <;> refine congrArg ofNat ?_ <;> simp only [Nat.mul_add] <;> omega

theorem intAdd_mul {x y z : ZFSet.{u}} (hx : x ∈ Int.{u}) (hy : y ∈ Int.{u})
    (hz : z ∈ Int.{u}) : intMul (intAdd x y) z = intAdd (intMul x z) (intMul y z) := by
  rw [intMul_comm (intAdd_mem_Int hx hy) hz, intMul_add hz hx hy,
      intMul_comm hz hx, intMul_comm hz hy]

theorem intMul_left_cancel {d x y : ZFSet.{u}} (hd : d ∈ Int.{u}) (hx : x ∈ Int.{u})
    (hy : y ∈ Int.{u}) (hd0 : d ≠ intZero.{u}) (h : intMul d x = intMul d y) : x = y := by
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_Int_iff d).mp hd
  obtain ⟨r, hr, s, hs, rfl⟩ := (mem_Int_iff x).mp hx
  obtain ⟨t, ht, u, hu, rfl⟩ := (mem_Int_iff y).mp hy
  rw [intMul_intOf hp hq hr hs, intMul_intOf hp hq ht hu] at h
  obtain ⟨np, rfl⟩ := (mem_omega_iff p).mp hp
  obtain ⟨nq, rfl⟩ := (mem_omega_iff q).mp hq
  obtain ⟨nr, rfl⟩ := (mem_omega_iff r).mp hr
  obtain ⟨ns, rfl⟩ := (mem_omega_iff s).mp hs
  obtain ⟨nt, rfl⟩ := (mem_omega_iff t).mp ht
  obtain ⟨nu, rfl⟩ := (mem_omega_iff u).mp hu
  have hpq : np ≠ nq := by
    intro hEq
    apply hd0
    rw [intZero]
    refine (intOf_eq_intOf_iff hp hq empty_mem_omega empty_mem_omega).mpr ?_
    rw [add_empty, empty_add hq, hEq]
  rw [intOf_eq_intOf_iff
    (add_mem_omega (mul_mem_omega hp hr) (mul_mem_omega hq hs))
    (add_mem_omega (mul_mem_omega hp hs) (mul_mem_omega hq hr))
    (add_mem_omega (mul_mem_omega hp ht) (mul_mem_omega hq hu))
    (add_mem_omega (mul_mem_omega hp hu) (mul_mem_omega hq ht))] at h
  simp only [mul_ofNat, add_ofNat] at h
  have hn := ofNat_injective h
  refine (intOf_eq_intOf_iff hr hs ht hu).mpr ?_
  simp only [add_ofNat]
  refine congrArg ofNat (nat_cancel hpq ?_)
  simp only [Nat.mul_add]
  omega

/-! ## Positivity

`intOf a b` is non-negative when `b ⊆ a`. The definition quantifies over
representatives; `intNonneg_iff` shows any one of them decides it. -/

def intNonneg (z : ZFSet.{u}) : Prop :=
  ∃ a b, a ∈ omega.{u} ∧ b ∈ omega.{u} ∧ z = intOf a b ∧ b ⊆ a

theorem intNonneg_iff {a b : ZFSet.{u}} (ha : a ∈ omega.{u}) (hb : b ∈ omega.{u}) :
    intNonneg (intOf a b) ↔ b ⊆ a := by
  refine ⟨?_, fun h => ⟨a, b, ha, hb, rfl, h⟩⟩
  rintro ⟨a', b', ha', hb', he, hs⟩
  have hr := (intOf_eq_intOf_iff ha hb ha' hb').mp he
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨na', rfl⟩ := (mem_omega_iff a').mp ha'
  obtain ⟨nb', rfl⟩ := (mem_omega_iff b').mp hb'
  rw [add_ofNat, add_ofNat] at hr
  rw [ofNat_subset_iff] at hs ⊢
  have := ofNat_injective hr
  omega

def intPositive : ZFSet.{u} :=
  sep (fun z => intNonneg z ∧ z ≠ intZero.{u}) Int.{u}

theorem mem_intPositive_iff (z : ZFSet.{u}) :
    z ∈ intPositive.{u} ↔ z ∈ Int.{u} ∧ intNonneg z ∧ z ≠ intZero.{u} :=
  mem_sep_iff _ z _

theorem intPositive_subset : intPositive.{u} ⊆ Int.{u} :=
  fun _ h => ((mem_intPositive_iff _).mp h).left

theorem intPositive_ne_zero {z : ZFSet.{u}} (h : z ∈ intPositive.{u}) :
    z ≠ intZero.{u} :=
  ((mem_intPositive_iff z).mp h).right.right

theorem one_mem_intPositive : intOne.{u} ∈ intPositive.{u} := by
  refine (mem_intPositive_iff _).mpr ⟨intOne_mem_Int, ?_, ?_⟩
  · exact (intNonneg_iff (ofNat_mem_omega 1) empty_mem_omega).mpr
      (by rw [← ofNat_zero]; exact (ofNat_subset_iff 0 1).mpr (by omega))
  · intro h
    have := (intOf_eq_intOf_iff (ofNat_mem_omega 1) empty_mem_omega
      empty_mem_omega empty_mem_omega).mp h
    rw [add_empty, empty_add empty_mem_omega, ← ofNat_zero] at this
    exact absurd (ofNat_injective this) (by omega)

private theorem nat_le_cancel {p q X Y : Nat} (hq : q < p)
    (h : p * X + q * Y ≤ p * Y + q * X) : X ≤ Y := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hq
  subst hk
  simp only [Nat.add_mul, Nat.one_mul] at h
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos k)
  rw [Nat.succ_mul, Nat.succ_mul]; omega

private theorem nat_le_mul {p q X Y : Nat} (hqp : q ≤ p) (h : X ≤ Y) :
    p * X + q * Y ≤ p * Y + q * X := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.mul_add]
  have := Nat.mul_le_mul_right (k := m) hqp
  omega

/-! ## Order

`z ≤ w` is `w - z` being non-negative. Every order fact then transports to `Nat`
through `intLe_ofNat` and is closed by `omega`. -/

def intLe (z w : ZFSet.{u}) : Prop := intNonneg (intAdd w (intNeg z))

theorem intLe_intOf {a b c d : ZFSet.{u}} (ha : a ∈ omega.{u}) (hb : b ∈ omega.{u})
    (hc : c ∈ omega.{u}) (hd : d ∈ omega.{u}) :
    intLe (intOf a b) (intOf c d) ↔ add a d ⊆ add c b := by
  rw [intLe, intNeg_intOf ha hb, intAdd_intOf hc hd hb ha,
      intNonneg_iff (add_mem_omega hc hb) (add_mem_omega hd ha), add_comm hd ha]

theorem intLe_ofNat (na nb nc nd : Nat) :
    intLe (intOf (ofNat.{u} na) (ofNat.{u} nb)) (intOf (ofNat.{u} nc) (ofNat.{u} nd))
      ↔ na + nd ≤ nc + nb := by
  rw [intLe_intOf (ofNat_mem_omega na) (ofNat_mem_omega nb)
        (ofNat_mem_omega nc) (ofNat_mem_omega nd),
      add_ofNat, add_ofNat, ofNat_subset_iff]

theorem intLe_refl {z : ZFSet.{u}} (hz : z ∈ Int.{u}) : intLe z z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  exact (intLe_ofNat na nb na nb).mpr (Nat.le_refl _)

theorem intLe_trans {z w v : ZFSet.{u}} (hz : z ∈ Int.{u}) (hw : w ∈ Int.{u})
    (hv : v ∈ Int.{u}) (h₁ : intLe z w) (h₂ : intLe w v) : intLe z v := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff w).mp hw
  obtain ⟨e, he, f, hf, rfl⟩ := (mem_Int_iff v).mp hv
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
  obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
  obtain ⟨ne, rfl⟩ := (mem_omega_iff e).mp he
  obtain ⟨nf, rfl⟩ := (mem_omega_iff f).mp hf
  rw [intLe_ofNat] at h₁ h₂ ⊢
  omega

theorem intLe_total {z w : ZFSet.{u}} (hz : z ∈ Int.{u}) (hw : w ∈ Int.{u}) :
    intLe z w ∨ intLe w z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff w).mp hw
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
  obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
  rw [intLe_ofNat, intLe_ofNat]
  omega

theorem intLe_antisymm {z w : ZFSet.{u}} (hz : z ∈ Int.{u}) (hw : w ∈ Int.{u})
    (h₁ : intLe z w) (h₂ : intLe w z) : z = w := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff w).mp hw
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
  obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
  rw [intLe_ofNat] at h₁ h₂
  refine (intOf_eq_intOf_iff (ofNat_mem_omega na) (ofNat_mem_omega nb)
    (ofNat_mem_omega nc) (ofNat_mem_omega nd)).mpr ?_
  rw [add_ofNat, add_ofNat]
  exact congrArg ofNat (by omega)

/-- A positive integer, read off a numeral representative. -/
theorem intPositive_ofNat {np nq : Nat}
    (h : intOf (ofNat.{u} np) (ofNat.{u} nq) ∈ intPositive.{u}) : nq < np := by
  obtain ⟨_, hnn, hne⟩ := (mem_intPositive_iff _).mp h
  rw [intNonneg_iff (ofNat_mem_omega np) (ofNat_mem_omega nq), ofNat_subset_iff] at hnn
  rcases Nat.eq_or_lt_of_le hnn with rfl | hlt
  · exact absurd (by
      rw [intZero]
      refine (intOf_eq_intOf_iff (ofNat_mem_omega _) (ofNat_mem_omega _)
        empty_mem_omega empty_mem_omega).mpr ?_
      rw [add_empty, empty_add (ofNat_mem_omega nq)]) hne
  · exact hlt

/-- The converse of `intPositive_ofNat`: a numeral representative certifies
positivity. -/
theorem ofNat_mem_intPositive {np nq : Nat} (h : nq < np) :
    intOf (ofNat.{u} np) (ofNat.{u} nq) ∈ intPositive.{u} := by
  refine (mem_intPositive_iff _).mpr
    ⟨intOf_mem_Int (ofNat_mem_omega np) (ofNat_mem_omega nq), ?_, ?_⟩
  · exact (intNonneg_iff (ofNat_mem_omega np) (ofNat_mem_omega nq)).mpr
      ((ofNat_subset_iff nq np).mpr (Nat.le_of_lt h))
  · intro he
    rw [intZero] at he
    have := (intOf_eq_intOf_iff (ofNat_mem_omega np) (ofNat_mem_omega nq)
      empty_mem_omega empty_mem_omega).mp he
    rw [add_empty, empty_add (ofNat_mem_omega nq)] at this
    exact absurd (ofNat_injective this) (by omega)

theorem intAdd_mem_intPositive {z w : ZFSet.{u}} (hz : z ∈ intPositive.{u})
    (hw : w ∈ intPositive.{u}) : intAdd z w ∈ intPositive.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp (intPositive_subset _ hz)
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff w).mp (intPositive_subset _ hw)
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
  obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
  have h₁ := intPositive_ofNat hz
  have h₂ := intPositive_ofNat hw
  rw [intAdd_intOf ha hb hc hd]
  simp only [add_ofNat]
  exact ofNat_mem_intPositive (by omega)

theorem intMul_mem_intPositive {z w : ZFSet.{u}} (hz : z ∈ intPositive.{u})
    (hw : w ∈ intPositive.{u}) : intMul z w ∈ intPositive.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp (intPositive_subset _ hz)
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff w).mp (intPositive_subset _ hw)
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
  obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
  have h₁ := intPositive_ofNat hz
  have h₂ := intPositive_ofNat hw
  rw [intMul_intOf ha hb hc hd]
  simp only [mul_ofNat, add_ofNat]
  refine ofNat_mem_intPositive ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h₁
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h₂
  simp only [Nat.add_mul, Nat.mul_add]
  omega

theorem intAdd_le_add_left_iff {k x y : ZFSet.{u}} (hk : k ∈ Int.{u}) (hx : x ∈ Int.{u})
    (hy : y ∈ Int.{u}) : intLe (intAdd k x) (intAdd k y) ↔ intLe x y := by
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_Int_iff k).mp hk
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff x).mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff y).mp hy
  obtain ⟨np, rfl⟩ := (mem_omega_iff p).mp hp
  obtain ⟨nq, rfl⟩ := (mem_omega_iff q).mp hq
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
  obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
  rw [intAdd_intOf hp hq ha hb, intAdd_intOf hp hq hc hd]
  simp only [add_ofNat, intLe_ofNat]
  -- `omega` on the `↔` itself would route through `Classical.em`; each
  -- direction separately stays constructive.
  exact ⟨fun h => by omega, fun h => by omega⟩

/-! ### The natural numbers inside ℤ

`intOfNat` is the ladder that makes ℤ -- and then ℚ -- Archimedean: every
integer is below some `intOfNat n`, and multiplying that by a positive integer
only moves it further up. -/

def intOfNat (n : Nat) : ZFSet.{u} := intOf (ofNat.{u} n) empty.{u}

theorem intOfNat_mem_Int (n : Nat) : intOfNat.{u} n ∈ Int.{u} :=
  intOf_mem_Int (ofNat_mem_omega n) empty_mem_omega

theorem intOne_le_of_intPositive {z : ZFSet.{u}} (hz : z ∈ intPositive.{u}) :
    intLe intOne.{u} z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp (intPositive_subset _ hz)
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  have h := intPositive_ofNat hz
  rw [intOne, ← ofNat_zero, intLe_ofNat]
  omega

/-- `intOne` and `intOfNat 1` are the same term. Both unfold to
`intOf (ofNat 1) empty`, so this is `rfl` -- but nothing said so, and a lemma
stated with `intOne` silently fails to meet `intOfNat_add` and the other
conversion lemmas, whose entry point is `intOfNat`. -/
theorem intOne_eq_intOfNat_one : intOne.{u} = intOfNat.{u} 1 := rfl

#print axioms intOne_eq_intOfNat_one

/-! ### The `ofNat` face of the pairing

`intAdd_intOf` and `intMul_intOf` are stated over `omega` members, which is the
right generality for `Integer.lean` itself and the wrong one for any map OUT of
`Int` that is indexed by `Nat` --- such a map's graph quantifies over
`intOf (ofNat a) (ofNat b)`, and every ring law it has to satisfy must be put
back into that form before the `Nat`-level law can be handed over. The three
below are that translation, done once.

`intMul_intOf`'s PAIRING IS `(ac + bd, ad + bc)`. `(a - b)(c - d) =
(ac + bd) - (ad + bc)`, and with everything a natural that is the only way to
state it: both components are sums and the sign lives in which pair goes where.
A wrong pairing still typechecks and still names an integer, so the
identity is written here rather than inlined at a rewrite site. -/

theorem intOfNat_succ (n : Nat) :
    intOfNat.{u} (n + 1) = intAdd (intOfNat.{u} n) intOne.{u} := by
  rw [intOfNat, intOfNat, intOne, intAdd_intOf (ofNat_mem_omega n) empty_mem_omega
    (ofNat_mem_omega 1) empty_mem_omega, add_ofNat, add_empty]

@[simp] theorem intOfNat_zero : intOfNat.{u} 0 = intZero.{u} := by
  rw [intOfNat, intZero, ofNat_zero]

theorem intPositive_of_intZero_le {z : ZFSet.{u}} (hz : z ∈ Int.{u})
    (h : intLe intZero.{u} z) (hne : z ≠ intZero.{u}) : z ∈ intPositive.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  rw [intZero, ← ofNat_zero, intLe_ofNat] at h
  refine ofNat_mem_intPositive ?_
  rcases Nat.eq_or_lt_of_le h with heq | hlt
  · exact absurd (by
      rw [intZero, ← ofNat_zero]
      refine (intOf_eq_intOf_iff (ofNat_mem_omega _) (ofNat_mem_omega _)
        (ofNat_mem_omega 0) (ofNat_mem_omega 0)).mpr ?_
      rw [add_ofNat, add_ofNat]
      exact congrArg ofNat (by omega)) hne
  · omega

/-- Archimedes for ℤ: every integer is strictly below some `n · d` with `d`
positive and `n` a natural number. -/
theorem int_lt_intOfNat_mul {z d : ZFSet.{u}} (hz : z ∈ Int.{u}) (hd : d ∈ intPositive.{u}) :
    ∃ n : Nat, intLe z (intMul (intOfNat.{u} n) d) ∧ z ≠ intMul (intOfNat.{u} n) d := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨c, hc, e, he, rfl⟩ := (mem_Int_iff _).mp (intPositive_subset _ hd)
  obtain ⟨za, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨zb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨dc, rfl⟩ := (mem_omega_iff c).mp hc
  obtain ⟨de, rfl⟩ := (mem_omega_iff e).mp he
  have hlt := intPositive_ofNat hd
  refine ⟨za + 1, ?_, ?_⟩ <;>
    rw [intOfNat, ← ofNat_zero, intMul_intOf (ofNat_mem_omega _) (ofNat_mem_omega 0) hc he] <;>
    simp only [mul_ofNat, add_ofNat]
  · rw [intLe_ofNat]
    have step : (za + 1) * de + (za + 1) ≤ (za + 1) * dc := by
      have h₁ : (za + 1) * (de + 1) ≤ (za + 1) * dc :=
        Nat.mul_le_mul_left (za + 1) (by omega)
      rw [Nat.mul_succ] at h₁
      omega
    omega
  · intro heq
    rw [intOf_eq_intOf_iff (ofNat_mem_omega _) (ofNat_mem_omega _)
      (ofNat_mem_omega _) (ofNat_mem_omega _), add_ofNat, add_ofNat] at heq
    have hn := ofNat_injective heq
    have step : (za + 1) * de + (za + 1) ≤ (za + 1) * dc := by
      have h₁ : (za + 1) * (de + 1) ≤ (za + 1) * dc :=
        Nat.mul_le_mul_left (za + 1) (by omega)
      rw [Nat.mul_succ] at h₁
      omega
    omega

theorem intAdd_le_add_right_iff {k x y : ZFSet.{u}} (hk : k ∈ Int.{u}) (hx : x ∈ Int.{u})
    (hy : y ∈ Int.{u}) : intLe (intAdd x k) (intAdd y k) ↔ intLe x y := by
  rw [intAdd_comm hx hk, intAdd_comm hy hk]
  exact intAdd_le_add_left_iff hk hx hy

theorem intAdd_right_cancel {k x y : ZFSet.{u}} (hk : k ∈ Int.{u}) (hx : x ∈ Int.{u})
    (hy : y ∈ Int.{u}) (h : intAdd x k = intAdd y k) : x = y := by
  rw [intAdd_comm hx hk, intAdd_comm hy hk] at h
  exact intAdd_left_cancel hk hx hy h

theorem intZero_le_of_intPositive {z : ZFSet.{u}} (hz : z ∈ intPositive.{u}) :
    intLe intZero.{u} z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp (intPositive_subset _ hz)
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  have h := intPositive_ofNat hz
  rw [intZero, ← ofNat_zero, intLe_ofNat]
  omega

theorem intNeg_eq_zero_iff {z : ZFSet.{u}} (hz : z ∈ Int.{u}) :
    intNeg z = intZero.{u} ↔ z = intZero.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  rw [intNeg_intOf ha hb, intZero,
      intOf_eq_intOf_iff hb ha empty_mem_omega empty_mem_omega,
      intOf_eq_intOf_iff ha hb empty_mem_omega empty_mem_omega,
      add_empty, add_empty, empty_add ha, empty_add hb]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem intLe_neg_zero_iff {z : ZFSet.{u}} (hz : z ∈ Int.{u}) :
    intLe (intNeg z) intZero.{u} ↔ intLe intZero.{u} z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  rw [intNeg_intOf ha hb, intZero, ← ofNat_zero, intLe_ofNat, intLe_ofNat]
  exact ⟨fun h => by omega, fun h => by omega⟩

theorem intMul_ne_zero {z w : ZFSet.{u}} (hz : z ∈ Int.{u}) (hw : w ∈ Int.{u})
    (hz0 : z ≠ intZero.{u}) (hw0 : w ≠ intZero.{u}) : intMul z w ≠ intZero.{u} := by
  intro h
  exact hw0 (intMul_left_cancel hz hw intZero_mem_Int hz0 (by rw [h, intMul_zero hz]))

/-- Trichotomy on ℤ: a nonzero integer is positive or its negation is. Both
sides are decided at the level of `Nat`, so no excluded middle is involved. -/
theorem intPositive_or_neg {z : ZFSet.{u}} (hz : z ∈ Int.{u}) (h : z ≠ intZero.{u}) :
    z ∈ intPositive.{u} ∨ intNeg z ∈ intPositive.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  have hne : na ≠ nb := by
    intro he
    refine h ?_
    rw [intZero]
    refine (intOf_eq_intOf_iff ha hb empty_mem_omega empty_mem_omega).mpr ?_
    rw [add_empty, empty_add hb, he]
  rcases Nat.lt_or_ge na nb with hlt | hge
  · rw [intNeg_intOf ha hb]
    exact Or.inr (ofNat_mem_intPositive hlt)
  · exact Or.inl (ofNat_mem_intPositive (by omega))

/-- Multiplying by a non-negative integer preserves `≤`. Only the strictly
positive case can reflect it, which is `intMul_le_mul_right_iff` below. -/
theorem intMul_le_mul_right {x y k : ZFSet.{u}} (hx : x ∈ Int.{u}) (hy : y ∈ Int.{u})
    (hk : k ∈ Int.{u}) (hk0 : intLe intZero.{u} k) (h : intLe x y) :
    intLe (intMul x k) (intMul y k) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff x).mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff y).mp hy
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_Int_iff k).mp hk
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
  obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
  obtain ⟨np, rfl⟩ := (mem_omega_iff p).mp hp
  obtain ⟨nq, rfl⟩ := (mem_omega_iff q).mp hq
  rw [intZero, ← ofNat_zero, intLe_ofNat] at hk0
  rw [intLe_ofNat] at h
  rw [intMul_intOf ha hb hp hq, intMul_intOf hc hd hp hq]
  simp only [mul_ofNat, add_ofNat, intLe_ofNat]
  have c1 : na * np = np * na := Nat.mul_comm _ _
  have c2 : nb * nq = nq * nb := Nat.mul_comm _ _
  have c3 : nc * nq = nq * nc := Nat.mul_comm _ _
  have c4 : nd * np = np * nd := Nat.mul_comm _ _
  have c5 : nc * np = np * nc := Nat.mul_comm _ _
  have c6 : nd * nq = nq * nd := Nat.mul_comm _ _
  have c7 : na * nq = nq * na := Nat.mul_comm _ _
  have c8 : nb * np = np * nb := Nat.mul_comm _ _
  have hm := nat_le_mul (X := na + nd) (Y := nc + nb) (show nq ≤ np by omega) h
  simp only [Nat.mul_add] at hm
  omega

/-- Multiplying by a positive integer both preserves and reflects `≤`, which is
what the order on ℚ is defined by. -/
theorem intMul_le_mul_right_iff {x y k : ZFSet.{u}} (hx : x ∈ Int.{u})
    (hy : y ∈ Int.{u}) (hk : k ∈ intPositive.{u}) :
    intLe (intMul x k) (intMul y k) ↔ intLe x y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff x).mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff y).mp hy
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_Int_iff _).mp (intPositive_subset _ hk)
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
  obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
  obtain ⟨np, rfl⟩ := (mem_omega_iff p).mp hp
  obtain ⟨nq, rfl⟩ := (mem_omega_iff q).mp hq
  have hlt := intPositive_ofNat hk
  rw [intMul_intOf ha hb hp hq, intMul_intOf hc hd hp hq]
  simp only [mul_ofNat, add_ofNat, intLe_ofNat]
  -- `omega` sees `na * np` and `np * na` as unrelated atoms, so the
  -- commutations have to be supplied explicitly.
  have c1 : na * np = np * na := Nat.mul_comm _ _
  have c2 : nb * nq = nq * nb := Nat.mul_comm _ _
  have c3 : nc * nq = nq * nc := Nat.mul_comm _ _
  have c4 : nd * np = np * nd := Nat.mul_comm _ _
  have c5 : nc * np = np * nc := Nat.mul_comm _ _
  have c6 : nd * nq = nq * nd := Nat.mul_comm _ _
  have c7 : na * nq = nq * na := Nat.mul_comm _ _
  have c8 : nb * np = np * nb := Nat.mul_comm _ _
  constructor
  · intro h
    refine nat_le_cancel hlt ?_
    simp only [Nat.mul_add]
    omega
  · intro h
    have hm := nat_le_mul (X := na + nd) (Y := nc + nb) (Nat.le_of_lt hlt) h
    simp only [Nat.mul_add] at hm
    omega

/-- Equality of integers reduces to an equality of naturals, which `Nat.decEq`
decides. Trichotomy on ℤ therefore costs nothing. -/
theorem int_eq_or_ne {z w : ZFSet.{u}} (hz : z ∈ Int.{u}) (hw : w ∈ Int.{u}) :
    z = w ∨ z ≠ w := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff w).mp hw
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  obtain ⟨nc, rfl⟩ := (mem_omega_iff c).mp hc
  obtain ⟨nd, rfl⟩ := (mem_omega_iff d).mp hd
  have key : intOf (ofNat.{u} na) (ofNat.{u} nb) = intOf (ofNat.{u} nc) (ofNat.{u} nd)
      ↔ na + nd = nc + nb := by
    rw [intOf_eq_intOf_iff ha hb hc hd, add_ofNat, add_ofNat]
    exact ⟨fun h => ofNat_injective h, fun h => congrArg ofNat h⟩
  rcases Nat.decEq (na + nd) (nc + nb) with h | h
  · exact Or.inr fun he => h (key.mp he)
  · exact Or.inl (key.mpr h)

/-! ## Naturals as integers

`intOfNat` is a ring map on the non-negative part. Everything downstream that
wants to do integer arithmetic in `Nat` goes through these. -/

theorem intOfNat_add (m n : Nat) :
    intAdd (intOfNat.{u} m) (intOfNat.{u} n) = intOfNat.{u} (m + n) := by
  rw [intOfNat, intOfNat, intOfNat, intAdd_intOf (ofNat_mem_omega m) empty_mem_omega
    (ofNat_mem_omega n) empty_mem_omega, add_ofNat, add_empty]

theorem intOfNat_mul (m n : Nat) :
    intMul (intOfNat.{u} m) (intOfNat.{u} n) = intOfNat.{u} (m * n) := by
  rw [intOfNat, intOfNat, intOfNat, ← ofNat_zero,
    intMul_intOf (ofNat_mem_omega m) (ofNat_mem_omega 0)
      (ofNat_mem_omega n) (ofNat_mem_omega 0)]
  simp only [mul_ofNat, add_ofNat]
  have h1 : m * n + 0 * 0 = m * n := by omega
  have h2 : m * 0 + 0 * n = 0 := by omega
  rw [h1, h2]

theorem intOfNat_le_iff (m n : Nat) : intLe (intOfNat.{u} m) (intOfNat.{u} n) ↔ m ≤ n := by
  rw [intOfNat, intOfNat, ← ofNat_zero, intLe_ofNat]
  -- `omega` closes an `↔` goal only by way of `Classical.em`
  exact ⟨fun h => by omega, fun h => by omega⟩

theorem intOfNat_eq_iff (m n : Nat) : intOfNat.{u} m = intOfNat.{u} n ↔ m = n := by
  rw [intOfNat, intOfNat, intOf_eq_intOf_iff (ofNat_mem_omega m) empty_mem_omega
    (ofNat_mem_omega n) empty_mem_omega, add_empty, add_empty]
  exact ⟨fun h => ofNat_injective h, fun h => by rw [h]⟩

theorem intOfNat_mem_intPositive {n : Nat} (h : 0 < n) : intOfNat.{u} n ∈ intPositive.{u} := by
  rw [intOfNat, ← ofNat_zero]
  exact ofNat_mem_intPositive h

/-- A numeral is not negative. `intPositive` is defined by `intNonneg` and
`≠ 0`, and `intNeg (intOfNat n)` is `intOf ∅ (ofNat n)`, whose non-negativity
reads as `ofNat n ⊆ ∅`. So the only numeral whose negation could be positive is
zero, and that one is not `≠ 0`.

Stated because the SIGN STEP of any descent from `Rat` needs it: a positive `r`
with `r * z` a numeral forces `z` to be one, and the negative case is refuted
here. `intPositive_or_neg` gives the trichotomy and nothing closed this branch
of it. -/
theorem not_intPositive_intNeg_intOfNat (n : Nat) :
    intNeg (intOfNat.{u} n) ∉ intPositive.{u} := by
  intro h
  obtain ⟨-, hnn, hne⟩ := (mem_intPositive_iff _).mp h
  rw [intOfNat, intNeg_intOf (ofNat_mem_omega n) empty_mem_omega,
    intNonneg_iff empty_mem_omega (ofNat_mem_omega n)] at hnn
  rw [intOfNat, intNeg_intOf (ofNat_mem_omega n) empty_mem_omega] at hne
  rw [← ofNat_zero, ofNat_subset_iff] at hnn
  obtain rfl : n = 0 := Nat.le_zero.mp hnn
  exact hne (by rw [ofNat_zero]; rfl)

/-- The numerals embed injectively. `intOf_eq_intOf_iff` turns the class
equality into `add m 0 = add n 0`, and cancelling the zero addend leaves the
`ω`-level equation `ofNat_injective` settles.

Needed to read an integer equation back in `Nat`, where `Divides` lives:
`intDvd_of_divides` sends divisibility one way and nothing sent it back, so the
polynomial layer's ring-level divisibility could not meet `prime_divides_mul`. -/
theorem intOfNat_injective {m n : Nat} (h : intOfNat.{u} m = intOfNat.{u} n) :
    m = n := by
  rw [intOfNat, intOfNat] at h
  have hadd := (intOf_eq_intOf_iff (ofNat_mem_omega m) empty_mem_omega
    (ofNat_mem_omega n) empty_mem_omega).mp h
  exact ofNat_injective (by simpa using hadd)

#print axioms not_intPositive_intNeg_intOfNat

/-- Adding one to a negative numeral: `-(m+1) + 1 = -m`.

Mixed signs are not reachable by `intOfNat_add`, so this goes through the PAIR
representation directly. -/
theorem intNeg_succ_add_one (m : Nat) :
    intAdd (intNeg (intOfNat.{u} (m + 1))) (intOfNat.{u} 1)
      = intNeg (intOfNat.{u} m) := by
  have hm1 := ofNat_mem_omega.{u} (m + 1)
  have hm := ofNat_mem_omega.{u} m
  have h1 := ofNat_mem_omega.{u} 1
  have he := empty_mem_omega.{u}
  rw [intOfNat, intOfNat, intOfNat, intNeg_intOf hm1 he, intNeg_intOf hm he,
    intAdd_intOf he hm1 h1 he]
  refine (intOf_eq_intOf_iff (add_mem_omega he h1) (add_mem_omega hm1 he)
    he hm).mpr ?_
  rw [empty_add h1, add_empty, add_ofNat, empty_add hm1]
  exact congrArg _ (by omega)

#print axioms intNeg_succ_add_one
#print axioms intOfNat_injective




/-- A positive integer IS a positive numeral.

`intPositive_ofNat` reads the inequality off a representative someone already
holds; this produces the representative, which is what a proof descending from
`Int` to `Nat` needs and what nothing here supplied. -/
theorem exists_intOfNat_of_intPositive {z : ZFSet.{u}} (hz : z ∈ intPositive.{u}) :
    ∃ n : Nat, 0 < n ∧ z = intOfNat.{u} n := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp (intPositive_subset _ hz)
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  have hlt := intPositive_ofNat hz
  refine ⟨na - nb, by omega, ?_⟩
  rw [intOfNat, ← ofNat_zero,
    intOf_eq_intOf_iff (ofNat_mem_omega na) (ofNat_mem_omega nb)
      (ofNat_mem_omega (na - nb)) (ofNat_mem_omega 0), add_ofNat, add_ofNat]
  have h : na + 0 = na - nb + nb := by omega
  rw [h]

/-- A non-negative integer IS a numeral.

`exists_intOfNat_of_intPositive` produces the representative for a POSITIVE
integer, and the bounded-coordinate argument Floor 2 waits on needs the
non-strict version: a coordinate may be zero, and excluding it would make the
count off by the origin. Nothing is decided -- the representative's own
subtraction supplies the numeral. -/
theorem exists_intOfNat_of_intNonneg {z : ZFSet.{u}} (hz : z ∈ Int.{u})
    (hnn : intNonneg z) : ∃ n : Nat, z = intOfNat.{u} n := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨na, rfl⟩ := (mem_omega_iff a).mp ha
  obtain ⟨nb, rfl⟩ := (mem_omega_iff b).mp hb
  rw [intNonneg_iff (ofNat_mem_omega na) (ofNat_mem_omega nb), ofNat_subset_iff] at hnn
  refine ⟨na - nb, ?_⟩
  rw [intOfNat, ← ofNat_zero,
    intOf_eq_intOf_iff (ofNat_mem_omega na) (ofNat_mem_omega nb)
      (ofNat_mem_omega (na - nb)) (ofNat_mem_omega 0), add_ofNat, add_ofNat]
  have h : na + 0 = na - nb + nb := by omega
  rw [h]

/-- `m - n` for `n ≤ m`, staying inside the numerals. -/
theorem intOfNat_sub (m n : Nat) (h : n ≤ m) :
    intAdd (intOfNat.{u} m) (intNeg (intOfNat.{u} n)) = intOfNat.{u} (m - n) := by
  rw [intOfNat, intOfNat, intOfNat, intNeg_intOf (ofNat_mem_omega n) empty_mem_omega,
    intAdd_intOf (ofNat_mem_omega m) empty_mem_omega empty_mem_omega (ofNat_mem_omega n),
    add_empty, empty_add (ofNat_mem_omega n), ← ofNat_zero,
    intOf_eq_intOf_iff (ofNat_mem_omega m) (ofNat_mem_omega n)
      (ofNat_mem_omega (m - n)) (ofNat_mem_omega 0), add_ofNat, add_ofNat]
  have : m + 0 = m - n + n := by omega
  rw [this]

/-! ## Audit -/

#print axioms intRel_isEquivRel
#print axioms intOf_eq_intOf_iff
#print axioms intAdd_intOf
#print axioms intAdd_assoc
#print axioms intAdd_neg
#print axioms intMul_intOf
#print axioms intMul_comm
#print axioms intMul_assoc
#print axioms intMul_add
#print axioms intMul_mul_comm
#print axioms intMul_left_cancel
#print axioms intAdd_left_cancel
#print axioms intLe_trans
#print axioms intLe_total
#print axioms intAdd_le_add_left_iff
#print axioms intMul_le_mul_right_iff
#print axioms intMul_mem_intPositive
#print axioms intNeg_mul
#print axioms intLe_neg_zero_iff
#print axioms exists_intOfNat_of_intPositive
#print axioms exists_intOfNat_of_intNonneg

/-- The integers from `-B` to `B`, as a set. -/
def boundedInts (B : Nat) : ZFSet.{u} :=
  sep (fun z => intLe (intNeg (intOfNat.{u} B)) z ∧ intLe z (intOfNat.{u} B)) Int.{u}

theorem mem_boundedInts_iff (B : Nat) (z : ZFSet.{u}) :
    z ∈ boundedInts.{u} B ↔
      z ∈ Int.{u} ∧ intLe (intNeg (intOfNat.{u} B)) z ∧ intLe z (intOfNat.{u} B) :=
  mem_sep_iff _ z _

theorem boundedInts_subset (B : Nat) : boundedInts.{u} B ⊆ Int.{u} :=
  fun _ h => ((mem_boundedInts_iff B _).mp h).left

/-- And every shifted numeral below `2B + 1` is bounded.

The other half, so the two together say the set IS the image. -/
theorem shift_mem_boundedInts {B k : Nat} (hk : k < 2 * B + 1) :
    intAdd (intOfNat.{u} k) (intNeg (intOfNat.{u} B)) ∈ boundedInts.{u} B := by
  have hB := intOfNat_mem_Int.{u} B
  have hnB := intNeg_mem_Int hB
  have hk' := intOfNat_mem_Int.{u} k
  refine (mem_boundedInts_iff B _).mpr ⟨intAdd_mem_Int hk' hnB, ?_, ?_⟩
  · have h : intLe (intAdd (intOfNat.{u} 0) (intNeg (intOfNat.{u} B)))
        (intAdd (intOfNat.{u} k) (intNeg (intOfNat.{u} B))) :=
      (intAdd_le_add_right_iff hnB (intOfNat_mem_Int.{u} 0) hk').mpr
        ((intOfNat_le_iff 0 k).mpr (by omega))
    rw [intOfNat_zero, intAdd_comm intZero_mem_Int hnB, intAdd_zero hnB] at h
    exact h
  · have h : intLe (intAdd (intOfNat.{u} k) (intNeg (intOfNat.{u} B)))
        (intAdd (intOfNat.{u} (2 * B)) (intNeg (intOfNat.{u} B))) :=
      (intAdd_le_add_right_iff hnB hk' (intOfNat_mem_Int.{u} (2 * B))).mpr
        ((intOfNat_le_iff k (2 * B)).mpr (by omega))
    have heq : intAdd (intOfNat.{u} (2 * B)) (intNeg (intOfNat.{u} B)) = intOfNat.{u} B := by
      refine intAdd_right_cancel hB (intAdd_mem_Int (intOfNat_mem_Int.{u} (2 * B)) hnB) hB ?_
      rw [intAdd_assoc (intOfNat_mem_Int.{u} (2 * B)) hnB hB,
        intAdd_comm hnB hB, intAdd_neg hB, intAdd_zero (intOfNat_mem_Int.{u} (2 * B)),
        intOfNat_add]
      exact congrArg _ (by omega)
    rw [heq] at h
    exact h

#print axioms boundedInts
#print axioms mem_boundedInts_iff
#print axioms boundedInts_subset
#print axioms shift_mem_boundedInts

theorem intOf_succ_pos {n : ZFSet.{u}} (hn : n ∈ omega.{u}) :
    intOf (succ n) empty.{u} ∈ intPositive.{u} := by
  obtain ⟨k, rfl⟩ := (mem_omega_iff n).mp hn
  rw [← ofNat_succ, ← ofNat_zero]
  exact ofNat_mem_intPositive (by omega)

/-! ## Subtraction, and the bounded-difference step -/

/-- Negation distributes over addition. Absent from `Integer.lean`, which
has `intNeg_intOf` and `intAdd_intOf` but never composes them. Both sides
reduce to the same `intOf` by those two lemmas and commutativity of `add` on
`omega`. -/
theorem intNeg_intAdd {x y : ZFSet.{u}} (hx : x ∈ Int.{u}) (hy : y ∈ Int.{u}) :
    intNeg (intAdd x y) = intAdd (intNeg x) (intNeg y) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_Int_iff x).mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_Int_iff y).mp hy
  rw [intAdd_intOf ha hb hc hd, intNeg_intOf (add_mem_omega ha hc) (add_mem_omega hb hd),
      intNeg_intOf ha hb, intNeg_intOf hc hd, intAdd_intOf hb ha hd hc]

#print axioms intNeg_intAdd
end NumberTheory

#print axioms NumberTheory.intOf_succ_pos

namespace ZFSet
export NumberTheory (Int boundedInts boundedInts_subset exists_intOfNat_of_intNonneg exists_intOfNat_of_intPositive intAdd intAdd_assoc intAdd_comm intAdd_intOf intAdd_le_add_left_iff intAdd_le_add_right_iff intAdd_left_cancel intAdd_mem_Int intAdd_mem_intPositive intAdd_mul intAdd_neg intAdd_right_cancel intAdd_zero intLe intLe_antisymm intLe_intOf intLe_neg_zero_iff intLe_ofNat intLe_refl intLe_total intLe_trans intMul intMul_add intMul_assoc intMul_comm intMul_intOf intMul_le_mul_right intMul_le_mul_right_iff intMul_left_cancel intMul_mem_Int intMul_mem_intPositive intMul_mul_comm intMul_ne_zero intMul_neg intMul_one intMul_zero intNeg intNeg_eq_zero_iff intNeg_intAdd intNeg_intNeg intNeg_intOf intNeg_mem_Int intNeg_mul intNeg_succ_add_one intNeg_zero intNonneg intNonneg_iff intOf intOfNat intOfNat_add intOfNat_eq_iff intOfNat_injective intOfNat_le_iff intOfNat_mem_Int intOfNat_mem_intPositive intOfNat_mul intOfNat_sub intOfNat_succ intOfNat_zero intOf_eq_intOf_iff intOf_mem_Int intOf_succ_pos intOne intOne_eq_intOfNat_one intOne_le_of_intPositive intOne_mem_Int intOne_mul intPositive intPositive_ne_zero intPositive_ofNat intPositive_of_intZero_le intPositive_or_neg intPositive_subset intRel intRel_isEquivRel intZero intZero_le_of_intPositive intZero_mem_Int intZero_mul int_eq_or_ne int_lt_intOfNat_mul mem_Int_iff mem_boundedInts_iff mem_intOf_iff mem_intPositive_iff mem_intRel_iff mem_omegaPairs_iff not_intPositive_intNeg_intOfNat ofNat_mem_intPositive omegaPairs one_mem_intPositive shift_mem_boundedInts)
end ZFSet
