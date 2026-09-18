/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Rings and fields.

A ring is an abelian group with a second operation on it; a field is a
commutative ring in which every non-zero element is invertible. ℚ and ℤ are
recognised as such from the arithmetic `Rational.lean` and `Integer.lean`
already prove. ℤ/nℤ is the quotient of ℤ by congruence mod `n`: a ring with `n`
elements, and a field when `n` is prime.
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
the field supplies. -/
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

/-- The four-term law for ring multiplication: `(w·x)·(y·z) = (w·y)·(x·z)`.

`opAt_interchange` says this for an abelian group; its proof uses no inverse,
so the law holds for a ring's multiplication, which is a commutative monoid. -/
theorem mulAt_interchange {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) {w x y z : ZFSet.{u}}
    (hw : w ∈ R) (hx : x ∈ R) (hy : y ∈ R) (hz : z ∈ R) :
    opAt mul (opAt mul w x) (opAt mul y z)
      = opAt mul (opAt mul w y) (opAt mul x z) := by
  rw [hR.mulAssoc _ hw _ hx _ (mulAt_mem hR hy hz),
    ← hR.mulAssoc _ hx _ hy _ hz, hR.mulComm _ hx _ hy,
    hR.mulAssoc _ hy _ hx _ hz, ← hR.mulAssoc _ hw _ hy _ (mulAt_mem hR hx hz)]

#print axioms mulAt_interchange

/-- No zero divisors, negatively, which a field gives for free.

The disjunctive form needs `DecidableVanishing` to choose a side; this one does
not, because it never chooses -- it assumes both factors nonzero and
contradicts. -/
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

/-- `natIn` on `Int` is `intOfNat`: `n`-fold repeated addition of `intOne` is
the embedded natural. `hom_natIn` carries `natIn` across a ring homomorphism,
and this reads the result as a statement about `intOfNat n`. -/
theorem natIn_eq_intOfNat :
    ∀ n : Nat, natIn NumberTheory.Int.{u} intAddOp.{u} intZero.{u} intOne.{u} n
      = intOfNat.{u} n
  | 0 => by rw [natIn, intOfNat_zero]; rfl
  | n + 1 => by
    show opAt intAddOp.{u}
        (natIn NumberTheory.Int.{u} intAddOp.{u} intZero.{u} intOne.{u} n)
          intOne.{u} = _
    rw [natIn_eq_intOfNat n, intOne_eq_intOfNat_one,
      opAt_intAddOp (intOfNat_mem_Int n) (intOfNat_mem_Int 1), ← intOfNat_add]

#print axioms Algebra.natIn_eq_intOfNat

/-- Multiples of `n`, as the image of multiplication by `n`. -/
def multiplesOf (n : ZFSet.{u}) : ZFSet.{u} :=
  imageIn (graphOn NumberTheory.Int.{u} NumberTheory.Int.{u} (fun z => intMul n z)) NumberTheory.Int.{u} NumberTheory.Int.{u}

theorem mem_multiplesOf_iff {n : ZFSet.{u}} (hn : n ∈ NumberTheory.Int.{u}) (w : ZFSet.{u}) :
    w ∈ multiplesOf n ↔ w ∈ NumberTheory.Int.{u} ∧ ∃ z, z ∈ NumberTheory.Int.{u} ∧ w = intMul n z := by
  refine Iff.trans (mem_imageIn_iff _ _ _ w) ⟨?_, ?_⟩
  · rintro ⟨hwI, z, hz, he⟩
    exact ⟨hwI, z, hz, by rwa [app_graphOn (fun m hm => intMul_mem_Int hn hm) hz] at he⟩
  · rintro ⟨hwI, z, hz, he⟩
    exact ⟨hwI, z, hz, by rwa [app_graphOn (fun m hm => intMul_mem_Int hn hm) hz]⟩

/-! ## ℤ/nℤ

The ideal gives a congruence -- `a ≡ b` when `a - b ∈ nℤ` -- so
`isGroup_congQuotient` produces the quotient group. -/

def modRel (n : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => ∃ a, a ∈ NumberTheory.Int.{u} ∧ ∃ b, b ∈ NumberTheory.Int.{u} ∧ z = opair a b ∧
        intAdd a (intNeg b) ∈ multiplesOf n) (prod NumberTheory.Int.{u} NumberTheory.Int.{u})

theorem opair_mem_modRel_iff {n a b : ZFSet.{u}} (ha : a ∈ NumberTheory.Int.{u}) (hb : b ∈ NumberTheory.Int.{u}) :
    opair a b ∈ modRel n ↔ intAdd a (intNeg b) ∈ multiplesOf n := by
  refine Iff.trans (mem_sep_iff _ _ _) ⟨?_, ?_⟩
  · rintro ⟨-, a', ha', b', hb', he, hmul⟩
    obtain ⟨rfl, rfl⟩ := opair_injective he
    exact hmul
  · intro hmul
    exact ⟨opair_mem_prod ha hb, a, ha, b, hb, rfl, hmul⟩

/-- Congruence mod `n` is a congruence for addition. Each clause comes from
writing a difference as `n·z`. -/
theorem isCongruence_modRel {n : ZFSet.{u}} (hn : n ∈ NumberTheory.Int.{u}) :
    IsCongruence (modRel n) NumberTheory.Int.{u} intAddOp.{u} := by
  constructor
  · constructor
    · intro a ha
      refine (opair_mem_modRel_iff ha ha).mpr ?_
      rw [intAdd_neg ha]
      exact (mem_multiplesOf_iff hn _).mpr
        ⟨intZero_mem_Int, intZero.{u}, intZero_mem_Int, (intMul_zero hn).symm⟩
    · intro a b ha hb hr
      obtain ⟨-, z, hz, he⟩ := (mem_multiplesOf_iff hn _).mp
        ((opair_mem_modRel_iff ha hb).mp hr)
      refine (opair_mem_modRel_iff hb ha).mpr ((mem_multiplesOf_iff hn _).mpr
        ⟨intAdd_mem_Int hb (intNeg_mem_Int ha), intNeg z, intNeg_mem_Int hz, ?_⟩)
      -- `b - a` is `-(a - b)`, and `-(n·z) = n·(-z)`
      rw [intMul_neg hn hz, ← he]
      have hstep : intAdd (intAdd a (intNeg b)) (intAdd b (intNeg a)) = intZero.{u} := by
        rw [intAdd_assoc ha (intNeg_mem_Int hb) (intAdd_mem_Int hb (intNeg_mem_Int ha)),
          ← intAdd_assoc (intNeg_mem_Int hb) hb (intNeg_mem_Int ha),
          intAdd_comm (intNeg_mem_Int hb) hb, intAdd_neg hb,
          intAdd_comm intZero_mem_Int (intNeg_mem_Int ha), intAdd_zero (intNeg_mem_Int ha),
          intAdd_neg ha]
      -- so `b - a` is the inverse of `a - b`
      have hab := intAdd_mem_Int ha (intNeg_mem_Int hb)
      have hba := intAdd_mem_Int hb (intNeg_mem_Int ha)
      have hcancel : intAdd (intNeg (intAdd a (intNeg b)))
          (intAdd (intAdd a (intNeg b)) (intAdd b (intNeg a)))
          = intAdd (intNeg (intAdd a (intNeg b))) intZero.{u} := by rw [hstep]
      rw [← intAdd_assoc (intNeg_mem_Int hab) hab hba,
        intAdd_comm (intNeg_mem_Int hab) hab, intAdd_neg hab,
        intAdd_comm intZero_mem_Int hba, intAdd_zero hba,
        intAdd_zero (intNeg_mem_Int hab)] at hcancel
      exact hcancel
    · intro a b c ha hb hc h₁ h₂
      obtain ⟨-, y, hy, hey⟩ := (mem_multiplesOf_iff hn _).mp
        ((opair_mem_modRel_iff ha hb).mp h₁)
      obtain ⟨-, z, hz, hez⟩ := (mem_multiplesOf_iff hn _).mp
        ((opair_mem_modRel_iff hb hc).mp h₂)
      refine (opair_mem_modRel_iff ha hc).mpr ((mem_multiplesOf_iff hn _).mpr
        ⟨intAdd_mem_Int ha (intNeg_mem_Int hc), intAdd y z, intAdd_mem_Int hy hz, ?_⟩)
      rw [intMul_add hn hy hz, ← hey, ← hez,
        intAdd_assoc ha (intNeg_mem_Int hb) (intAdd_mem_Int hb (intNeg_mem_Int hc)),
        ← intAdd_assoc (intNeg_mem_Int hb) hb (intNeg_mem_Int hc),
        intAdd_comm (intNeg_mem_Int hb) hb, intAdd_neg hb,
        intAdd_comm intZero_mem_Int (intNeg_mem_Int hc), intAdd_zero (intNeg_mem_Int hc)]
  · intro a ha a' ha' b hb b' hb' hr₁ hr₂
    obtain ⟨-, y, hy, hey⟩ := (mem_multiplesOf_iff hn _).mp
      ((opair_mem_modRel_iff ha ha').mp hr₁)
    obtain ⟨-, z, hz, hez⟩ := (mem_multiplesOf_iff hn _).mp
      ((opair_mem_modRel_iff hb hb').mp hr₂)
    rw [opAt_intAddOp ha hb, opAt_intAddOp ha' hb']
    refine (opair_mem_modRel_iff (intAdd_mem_Int ha hb) (intAdd_mem_Int ha' hb')).mpr
      ((mem_multiplesOf_iff hn _).mpr ⟨intAdd_mem_Int (intAdd_mem_Int ha hb)
        (intNeg_mem_Int (intAdd_mem_Int ha' hb')), intAdd y z,
        intAdd_mem_Int hy hz, ?_⟩)
    -- `(a+b) - (a'+b') = (a - a') + (b - b')`
    rw [intMul_add hn hy hz, ← hey, ← hez]
    have hneg : intNeg (intAdd a' b') = intAdd (intNeg a') (intNeg b') := by
      have hsum : intAdd (intAdd a' b') (intAdd (intNeg a') (intNeg b')) = intZero.{u} := by
        rw [intAdd_assoc ha' hb' (intAdd_mem_Int (intNeg_mem_Int ha') (intNeg_mem_Int hb')),
          ← intAdd_assoc hb' (intNeg_mem_Int ha') (intNeg_mem_Int hb'),
          intAdd_comm hb' (intNeg_mem_Int ha'),
          intAdd_assoc (intNeg_mem_Int ha') hb' (intNeg_mem_Int hb'), intAdd_neg hb',
          intAdd_zero (intNeg_mem_Int ha'), intAdd_neg ha']
      have hab := intAdd_mem_Int ha' hb'
      have hnn := intAdd_mem_Int (intNeg_mem_Int ha') (intNeg_mem_Int hb')
      have hcancel : intAdd (intNeg (intAdd a' b')) (intAdd (intAdd a' b')
          (intAdd (intNeg a') (intNeg b')))
          = intAdd (intNeg (intAdd a' b')) intZero.{u} := by rw [hsum]
      rw [← intAdd_assoc (intNeg_mem_Int hab) hab hnn,
        intAdd_comm (intNeg_mem_Int hab) hab, intAdd_neg hab,
        intAdd_comm intZero_mem_Int hnn, intAdd_zero hnn,
        intAdd_zero (intNeg_mem_Int hab)] at hcancel
      exact hcancel.symm
    rw [hneg, intAdd_assoc ha hb (intAdd_mem_Int (intNeg_mem_Int ha') (intNeg_mem_Int hb')),
      ← intAdd_assoc hb (intNeg_mem_Int ha') (intNeg_mem_Int hb'),
      intAdd_comm hb (intNeg_mem_Int ha'),
      intAdd_assoc (intNeg_mem_Int ha') hb (intNeg_mem_Int hb'),
      ← intAdd_assoc ha (intNeg_mem_Int ha') (intAdd_mem_Int hb (intNeg_mem_Int hb'))]

/-- Congruence mod `n` respects multiplication: `ab - a'b' = a(b-b') + (a-a')b'`,
and an ideal absorbs both terms. -/
theorem isCongruence_modRel_mul {n : ZFSet.{u}} (hn : n ∈ NumberTheory.Int.{u}) :
    IsCongruence (modRel n) NumberTheory.Int.{u} intMulOp.{u} := by
  refine ⟨(isCongruence_modRel hn).left, fun a ha a' ha' b hb b' hb' hr₁ hr₂ => ?_⟩
  obtain ⟨-, y, hy, hey⟩ := (mem_multiplesOf_iff hn _).mp
    ((opair_mem_modRel_iff ha ha').mp hr₁)
  obtain ⟨-, z, hz, hez⟩ := (mem_multiplesOf_iff hn _).mp
    ((opair_mem_modRel_iff hb hb').mp hr₂)
  rw [opAt_intMulOp ha hb, opAt_intMulOp ha' hb']
  refine (opair_mem_modRel_iff (intMul_mem_Int ha hb) (intMul_mem_Int ha' hb')).mpr
    ((mem_multiplesOf_iff hn _).mpr ⟨intAdd_mem_Int (intMul_mem_Int ha hb)
      (intNeg_mem_Int (intMul_mem_Int ha' hb')), intAdd (intMul a z) (intMul y b'),
      intAdd_mem_Int (intMul_mem_Int ha hz) (intMul_mem_Int hy hb'), ?_⟩)
  -- `n·(az + yb') = a·(nz) + (ny)·b' = a(b-b') + (a-a')b' = ab - a'b'`
  rw [intMul_add hn (intMul_mem_Int ha hz) (intMul_mem_Int hy hb'),
    ← intMul_assoc hn ha hz, intMul_comm hn ha, intMul_assoc ha hn hz,
    ← intMul_assoc hn hy hb', ← hey, ← hez]
  -- expand both products over the differences
  rw [intMul_add ha hb (intNeg_mem_Int hb'), intMul_neg ha hb',
    intAdd_mul ha (intNeg_mem_Int ha') hb', intNeg_mul ha' hb']
  -- `(ab + -(ab')) + (ab' + -(a'b')) = ab + -(a'b')`
  rw [intAdd_assoc (intMul_mem_Int ha hb) (intNeg_mem_Int (intMul_mem_Int ha hb'))
      (intAdd_mem_Int (intMul_mem_Int ha hb') (intNeg_mem_Int (intMul_mem_Int ha' hb'))),
    ← intAdd_assoc (intNeg_mem_Int (intMul_mem_Int ha hb')) (intMul_mem_Int ha hb')
      (intNeg_mem_Int (intMul_mem_Int ha' hb')),
    intAdd_comm (intNeg_mem_Int (intMul_mem_Int ha hb')) (intMul_mem_Int ha hb'),
    intAdd_neg (intMul_mem_Int ha hb'),
    intAdd_comm intZero_mem_Int (intNeg_mem_Int (intMul_mem_Int ha' hb')),
    intAdd_zero (intNeg_mem_Int (intMul_mem_Int ha' hb'))]

/-- ℤ/nℤ is a ring. -/
theorem isRing_intMod {n : ZFSet.{u}} (hn : n ∈ NumberTheory.Int.{u}) :
    IsRing (quotientSet (modRel n) NumberTheory.Int.{u}) (congOp (modRel n) NumberTheory.Int.{u} intAddOp.{u})
      (congOp (modRel n) NumberTheory.Int.{u} intMulOp.{u}) (cls (modRel n) NumberTheory.Int.{u} intZero.{u})
      (cls (modRel n) NumberTheory.Int.{u} intOne.{u}) :=
  isRing_congQuotient isRing_int (isCongruence_modRel hn) (isCongruence_modRel_mul hn)

/-! ## Counting `ℤ/nℤ`

Congruence between numerals is congruence in `Nat`, which is the bridge both
halves of the count need. The injective half is here: distinct numerals below
`n` land in distinct classes, so the quotient has at least `n` elements. -/

theorem intOfNat_sub_mem_multiples_iff {n j k : Nat} :
    intAdd (intOfNat.{u} j) (intNeg (intOfNat.{u} k)) ∈ multiplesOf (intOfNat.{u} n)
      ↔ ∃ p q : Nat, j + n * q = n * p + k := by
  have hdiff : intAdd (intOfNat.{u} j) (intNeg (intOfNat.{u} k))
      = intOf (ofNat.{u} j) (ofNat.{u} k) := by
    rw [intOfNat, intOfNat, intNeg_intOf (ofNat_mem_omega k) empty_mem_omega,
      intAdd_intOf (ofNat_mem_omega j) empty_mem_omega empty_mem_omega
        (ofNat_mem_omega k), add_empty, empty_add (ofNat_mem_omega k)]
  have hmulOf : ∀ p q : Nat, intMul (intOfNat.{u} n) (intOf (ofNat.{u} p) (ofNat.{u} q))
      = intOf (ofNat.{u} (n * p)) (ofNat.{u} (n * q)) := by
    intro p q
    rw [intOfNat, ← ofNat_zero, intMul_intOf (ofNat_mem_omega n) (ofNat_mem_omega 0)
      (ofNat_mem_omega p) (ofNat_mem_omega q)]
    simp only [mul_ofNat, add_ofNat]
    have e1 : n * p + 0 * q = n * p := by omega
    have e2 : n * q + 0 * p = n * q := by omega
    rw [e1, e2]
  rw [hdiff]
  constructor
  · intro hmem
    obtain ⟨-, z, hz, he⟩ := (mem_multiplesOf_iff (intOfNat_mem_Int n) _).mp hmem
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_Int_iff z).mp hz
    obtain ⟨p, rfl⟩ := (mem_omega_iff x).mp hx
    obtain ⟨q, rfl⟩ := (mem_omega_iff y).mp hy
    rw [hmulOf p q] at he
    have hadd := (intOf_eq_intOf_iff (ofNat_mem_omega j) (ofNat_mem_omega k)
      (ofNat_mem_omega (n * p)) (ofNat_mem_omega (n * q))).mp he
    rw [add_ofNat, add_ofNat] at hadd
    exact ⟨p, q, ofNat_injective hadd⟩
  · rintro ⟨p, q, he⟩
    refine (mem_multiplesOf_iff (intOfNat_mem_Int n) _).mpr
      ⟨intOf_mem_Int (ofNat_mem_omega j) (ofNat_mem_omega k),
        intOf (ofNat.{u} p) (ofNat.{u} q), intOf_mem_Int (ofNat_mem_omega p)
          (ofNat_mem_omega q), ?_⟩
    rw [hmulOf p q]
    refine (intOf_eq_intOf_iff (ofNat_mem_omega j) (ofNat_mem_omega k)
      (ofNat_mem_omega (n * p)) (ofNat_mem_omega (n * q))).mpr ?_
    rw [add_ofNat, add_ofNat]
    exact congrArg _ he

/-- Numerals below `n` are in distinct classes, so `ℤ/nℤ` has at least `n`
elements. -/
theorem cls_intOfNat_injective {n j k : Nat} (hj : j < n) (hk : k < n)
    (he : cls (modRel (intOfNat.{u} n)) NumberTheory.Int.{u} (intOfNat.{u} j)
        = cls (modRel (intOfNat.{u} n)) NumberTheory.Int.{u} (intOfNat.{u} k)) : j = k := by
  have hrel := (cls_eq_cls_iff (isCongruence_modRel (intOfNat_mem_Int n)).left
    (intOfNat_mem_Int j) (intOfNat_mem_Int k)).mp he
  obtain ⟨p, q, hpq⟩ := (intOfNat_sub_mem_multiples_iff).mp
    ((opair_mem_modRel_iff (intOfNat_mem_Int j) (intOfNat_mem_Int k)).mp hrel)
  -- `j - k` is a multiple of `n` and smaller than it, so it is zero
  rcases Nat.lt_or_ge p q with hlt | hge
  · have hstep : n * q = n * p + n * (q - p) := by
      rw [← Nat.mul_add]
      exact congrArg _ (by omega)
    have hbig : n * 1 ≤ n * (q - p) := Nat.mul_le_mul_left n (by omega)
    omega
  · have hstep : n * p = n * q + n * (p - q) := by
      rw [← Nat.mul_add]
      exact congrArg _ (by omega)
    rcases Nat.eq_or_lt_of_le hge with rfl | hlt'
    · omega
    · have hbig : n * 1 ≤ n * (p - q) := Nat.mul_le_mul_left n (by omega)
      omega

/-- Every integer is congruent to a numeral below `n`: shift by `n·b` to clear
the negative part, then divide. -/
theorem exists_cls_intOfNat {n : Nat} (hn : 0 < n) {z : ZFSet.{u}} (hz : z ∈ NumberTheory.Int.{u}) :
    ∃ k : Nat, k < n ∧ cls (modRel (intOfNat.{u} n)) NumberTheory.Int.{u} z
      = cls (modRel (intOfNat.{u} n)) NumberTheory.Int.{u} (intOfNat.{u} k) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_Int_iff z).mp hz
  obtain ⟨a, rfl⟩ := (mem_omega_iff x).mp hx
  obtain ⟨b, rfl⟩ := (mem_omega_iff y).mp hy
  -- the shifted numerator, and its remainder
  have hshift : (n - 1) * b + b = n * b := by
    rw [← Nat.succ_mul]
    exact congrArg (fun t => t * b) (by omega)
  refine ⟨(a + (n - 1) * b) % n, Nat.mod_lt _ hn, ?_⟩
  refine (cls_eq_cls_iff (isCongruence_modRel (intOfNat_mem_Int n)).left
    (intOf_mem_Int (ofNat_mem_omega a) (ofNat_mem_omega b))
    (intOfNat_mem_Int _)).mpr ?_
  refine (opair_mem_modRel_iff (intOf_mem_Int (ofNat_mem_omega a) (ofNat_mem_omega b))
    (intOfNat_mem_Int _)).mpr ?_
  -- rewrite the difference as one between numerals and use the bridge
  have hz' : intOf (ofNat.{u} a) (ofNat.{u} b)
      = intAdd (intOfNat.{u} a) (intNeg (intOfNat.{u} b)) := by
    rw [intOfNat, intOfNat, intNeg_intOf (ofNat_mem_omega b) empty_mem_omega,
      intAdd_intOf (ofNat_mem_omega a) empty_mem_omega empty_mem_omega
        (ofNat_mem_omega b), add_empty, empty_add (ofNat_mem_omega b)]
  have hcombine : intAdd (intOf (ofNat.{u} a) (ofNat.{u} b))
      (intNeg (intOfNat.{u} ((a + (n - 1) * b) % n)))
      = intAdd (intOfNat.{u} a) (intNeg (intOfNat.{u} (b + (a + (n - 1) * b) % n))) := by
    rw [hz', intOfNat, intOfNat, intOfNat, intOfNat,
      intNeg_intOf (ofNat_mem_omega b) empty_mem_omega,
      intNeg_intOf (ofNat_mem_omega ((a + (n - 1) * b) % n)) empty_mem_omega,
      intNeg_intOf (ofNat_mem_omega (b + (a + (n - 1) * b) % n)) empty_mem_omega,
      intAdd_intOf (ofNat_mem_omega a) empty_mem_omega empty_mem_omega
        (ofNat_mem_omega b),
      intAdd_intOf (add_mem_omega (ofNat_mem_omega a) empty_mem_omega)
        (add_mem_omega empty_mem_omega (ofNat_mem_omega b)) empty_mem_omega
        (ofNat_mem_omega ((a + (n - 1) * b) % n)),
      intAdd_intOf (ofNat_mem_omega a) empty_mem_omega empty_mem_omega
        (ofNat_mem_omega (b + (a + (n - 1) * b) % n))]
    simp only [add_empty]
    rw [empty_add (ofNat_mem_omega b), add_ofNat,
      empty_add (ofNat_mem_omega (b + (a + (n - 1) * b) % n))]
  rw [hcombine]
  refine (intOfNat_sub_mem_multiples_iff).mpr
    ⟨(a + (n - 1) * b) / n, b, ?_⟩
  have hdiv := Nat.div_add_mod (a + (n - 1) * b) n
  omega

/-- The bijection between `{0,…,n-1}` and the classes. -/
def numeralClasses (n : Nat) : ZFSet.{u} :=
  sep (fun z => ∃ k : Nat, k < n ∧
        z = opair (ofNat.{u} k) (cls (modRel (intOfNat.{u} n)) NumberTheory.Int.{u} (intOfNat.{u} k)))
    (prod (ofNat.{u} n) (quotientSet (modRel (intOfNat.{u} n)) NumberTheory.Int.{u}))

theorem mem_numeralClasses_iff (n : Nat) (z : ZFSet.{u}) :
    z ∈ numeralClasses.{u} n ↔
      z ∈ prod (ofNat.{u} n) (quotientSet (modRel (intOfNat.{u} n)) NumberTheory.Int.{u}) ∧
        ∃ k : Nat, k < n ∧
          z = opair (ofNat.{u} k) (cls (modRel (intOfNat.{u} n)) NumberTheory.Int.{u} (intOfNat.{u} k)) :=
  mem_sep_iff _ _ _

private theorem opair_mem_numeralClasses {n k : Nat} (hk : k < n) :
    opair (ofNat.{u} k) (cls (modRel (intOfNat.{u} n)) NumberTheory.Int.{u} (intOfNat.{u} k))
      ∈ numeralClasses.{u} n :=
  (mem_numeralClasses_iff n _).mpr
    ⟨opair_mem_prod ((mem_ofNat_iff _ n).mpr ⟨k, hk, rfl⟩)
      (cls_mem_quotientSet (intOfNat_mem_Int k)), k, hk, rfl⟩

/-- `ℤ/nℤ` has exactly `n` elements. -/
theorem equinumerous_intMod {n : Nat} (hn : 0 < n) :
    Equinumerous (ofNat.{u} n) (quotientSet (modRel (intOfNat.{u} n)) NumberTheory.Int.{u}) := by
  have hfun : IsFunction (numeralClasses.{u} n) := by
    constructor
    · intro z hz
      obtain ⟨-, k, -, he⟩ := (mem_numeralClasses_iff n z).mp hz
      exact ⟨_, _, he⟩
    · intro w v v' hv hv'
      obtain ⟨-, k, -, he⟩ := (mem_numeralClasses_iff n _).mp hv
      obtain ⟨-, k', -, he'⟩ := (mem_numeralClasses_iff n _).mp hv'
      obtain ⟨hk, rfl⟩ := opair_injective he
      obtain ⟨hk', rfl⟩ := opair_injective he'
      rw [ofNat_injective (hk.symm.trans hk')]
  have happ : ∀ k : Nat, k < n →
      app (numeralClasses.{u} n) (ofNat.{u} k)
        = cls (modRel (intOfNat.{u} n)) NumberTheory.Int.{u} (intOfNat.{u} k) :=
    fun k hk => app_eq hfun (opair_mem_numeralClasses hk)
  have hdom : domain (numeralClasses.{u} n) = ofNat.{u} n := by
    refine ext _ _ fun w => ⟨fun hw => ?_, fun hw => ?_⟩
    · obtain ⟨v, hv⟩ := (mem_domain_iff w _).mp hw
      exact mem_prod_left ((mem_numeralClasses_iff n _).mp hv).left
    · obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff w n).mp hw
      exact (mem_domain_iff _ _).mpr ⟨_, opair_mem_numeralClasses hk⟩
  have hran : range (numeralClasses.{u} n) ⊆ quotientSet (modRel (intOfNat.{u} n)) NumberTheory.Int.{u} := by
    intro v hv
    obtain ⟨w, hw⟩ := (mem_range_iff v _).mp hv
    exact mem_prod_right ((mem_numeralClasses_iff n _).mp hw).left
  refine ⟨numeralClasses.{u} n, ⟨hfun, hdom, hran, ?_⟩, ⟨hfun, hdom, hran, ?_⟩⟩
  · -- injective: distinct numerals give distinct classes
    intro w hw w' hw' he
    obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff w n).mp hw
    obtain ⟨k', hk', rfl⟩ := (mem_ofNat_iff w' n).mp hw'
    rw [happ k hk, happ k' hk'] at he
    rw [cls_intOfNat_injective hk hk' he]
  · -- surjective: every class is the class of a numeral below `n`
    intro C hC
    obtain ⟨z, hz, rfl⟩ := (mem_quotientSet_iff _ _ C).mp hC
    obtain ⟨k, hk, hcls⟩ := exists_cls_intOfNat (by omega : 0 < n) hz
    exact ⟨ofNat.{u} k, (mem_ofNat_iff _ n).mpr ⟨k, hk, rfl⟩, by rw [happ k hk, ← hcls]⟩

/-! ## ℤ/pℤ is a field

Bézout gives the inverse. For `0 < j < p` with `p` prime, `gcd p j = 1`, so
either `u·j = v·p + 1` -- and `[u]` inverts `[j]` -- or `u·p = v·j + 1`, and
`[-v]` does. `Prime.lean` proves both. -/

theorem cls_eq_iff_sub {n a b : ZFSet.{u}} (hn : n ∈ NumberTheory.Int.{u}) (ha : a ∈ NumberTheory.Int.{u})
    (hb : b ∈ NumberTheory.Int.{u}) :
    cls (modRel n) NumberTheory.Int.{u} a = cls (modRel n) NumberTheory.Int.{u} b
      ↔ intAdd a (intNeg b) ∈ multiplesOf n :=
  Iff.trans (cls_eq_cls_iff (isCongruence_modRel hn).left ha hb)
    (opair_mem_modRel_iff ha hb)

/-- ℤ/pℤ is a field for prime `p`. -/
theorem isField_intMod {p : Nat} (hp : IsPrime p) :
    IsField (quotientSet (modRel (intOfNat.{u} p)) NumberTheory.Int.{u})
      (congOp (modRel (intOfNat.{u} p)) NumberTheory.Int.{u} intAddOp.{u})
      (congOp (modRel (intOfNat.{u} p)) NumberTheory.Int.{u} intMulOp.{u})
      (cls (modRel (intOfNat.{u} p)) NumberTheory.Int.{u} intZero.{u})
      (cls (modRel (intOfNat.{u} p)) NumberTheory.Int.{u} intOne.{u}) := by
  have hpI := intOfNat_mem_Int.{u} p
  have hp2 := hp.left
  have hcl := fun a (ha : a ∈ NumberTheory.Int.{u}) b (hb : b ∈ NumberTheory.Int.{u}) => mulAt_mem isRing_int ha hb
  refine ⟨isRing_intMod hpI, ?_, ?_⟩
  · -- `0 ≠ 1` because `p ∤ 1`
    intro he
    have hsub := (cls_eq_iff_sub hpI intZero_mem_Int intOne_mem_Int).mp he
    rw [intZero, ← ofNat_zero] at hsub
    have hz : intAdd (intOfNat.{u} 0) (intNeg (intOfNat.{u} 1)) ∈ multiplesOf (intOfNat.{u} p) :=
      hsub
    obtain ⟨P, Q, hPQ⟩ := (intOfNat_sub_mem_multiples_iff).mp hz
    -- `0 + pQ = pP + 1` forces `p ∣ 1`
    rcases Nat.lt_or_ge P Q with hlt | hge
    · have hstep : p * Q = p * P + p * (Q - P) := by
        rw [← Nat.mul_add]
        exact congrArg _ (by omega)
      have hbig : p * 1 ≤ p * (Q - P) := Nat.mul_le_mul_left p (by omega)
      omega
    · have hstep : p * P = p * Q + p * (P - Q) := by
        rw [← Nat.mul_add]
        exact congrArg _ (by omega)
      rcases Nat.eq_or_lt_of_le hge with rfl | hlt'
      · omega
      · have hbig : p * 1 ≤ p * (P - Q) := Nat.mul_le_mul_left p (by omega)
        omega
  · -- every non-zero class has an inverse
    intro C hC hne
    obtain ⟨z, hz, rfl⟩ := (mem_quotientSet_iff _ _ C).mp hC
    obtain ⟨j, hj, hcls⟩ := exists_cls_intOfNat (by omega : 0 < p) hz
    rw [hcls] at hne ⊢
    have hjI := intOfNat_mem_Int.{u} j
    -- `j ≠ 0`, since the class is not zero
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · exact absurd (by rw [show intOfNat.{u} 0 = intZero.{u} from rfl]) hne
      · exact h
    -- so `p` does not divide `j`, and the gcd is one
    have hnd : ¬ Divides p j := fun hd => by
      have := divides_le hj0 hd
      omega
    have hg := gcd_eq_one_of_prime_not_divides hp hnd
    obtain ⟨u, v, hbez⟩ := bezout p j
    rw [hg] at hbez
    rcases hbez with h | h
    · -- `u·p = v·j + 1`, so `[-v]` is the inverse
      refine ⟨cls (modRel (intOfNat.{u} p)) NumberTheory.Int.{u} (intNeg (intOfNat.{u} v)),
        cls_mem_quotientSet (intNeg_mem_Int (intOfNat_mem_Int v)), ?_⟩
      rw [opAt_congOp hcl (isCongruence_modRel_mul hpI) hjI
        (intNeg_mem_Int (intOfNat_mem_Int v)), opAt_intMulOp hjI
        (intNeg_mem_Int (intOfNat_mem_Int v))]
      refine (cls_eq_iff_sub hpI (intMul_mem_Int hjI
        (intNeg_mem_Int (intOfNat_mem_Int v))) intOne_mem_Int).mpr ?_
      refine (mem_multiplesOf_iff hpI _).mpr ⟨intAdd_mem_Int (intMul_mem_Int hjI
        (intNeg_mem_Int (intOfNat_mem_Int v))) (intNeg_mem_Int intOne_mem_Int),
        intNeg (intOfNat.{u} u), intNeg_mem_Int (intOfNat_mem_Int u), ?_⟩
      -- both sides are `intOf ∅ (j·v + 1)` once `u·p = v·j + 1`
      rw [intMul_neg hjI (intOfNat_mem_Int v), intOfNat_mul,
        intMul_neg hpI (intOfNat_mem_Int u), intOfNat_mul,
        intOne, intOfNat, intOfNat, ← ofNat_zero,
        intNeg_intOf (ofNat_mem_omega (j * v)) (ofNat_mem_omega 0),
        intNeg_intOf (ofNat_mem_omega 1) (ofNat_mem_omega 0),
        intNeg_intOf (ofNat_mem_omega (p * u)) (ofNat_mem_omega 0),
        intAdd_intOf (ofNat_mem_omega 0) (ofNat_mem_omega (j * v))
          (ofNat_mem_omega 0) (ofNat_mem_omega 1), add_ofNat, add_ofNat,
        intOf_eq_intOf_iff (ofNat_mem_omega (0 + 0)) (ofNat_mem_omega (j * v + 1))
          (ofNat_mem_omega 0) (ofNat_mem_omega (p * u)), add_ofNat, add_ofNat]
      refine congrArg _ ?_
      have hcomm : v * j = j * v := Nat.mul_comm _ _
      have hcomm' : u * p = p * u := Nat.mul_comm _ _
      omega
    · -- `u·j = v·p + 1`, so `[u]` is the inverse
      refine ⟨cls (modRel (intOfNat.{u} p)) NumberTheory.Int.{u} (intOfNat.{u} u),
        cls_mem_quotientSet (intOfNat_mem_Int u), ?_⟩
      rw [opAt_congOp hcl (isCongruence_modRel_mul hpI) hjI (intOfNat_mem_Int u),
        opAt_intMulOp hjI (intOfNat_mem_Int u), intOfNat_mul]
      refine (cls_eq_iff_sub hpI (intOfNat_mem_Int (j * u)) intOne_mem_Int).mpr ?_
      rw [intOne, ← ofNat_zero]
      refine (intOfNat_sub_mem_multiples_iff).mpr ⟨v, 0, ?_⟩
      have hcomm : u * j = j * u := Nat.mul_comm _ _
      have hcomm' : v * p = p * v := Nat.mul_comm _ _
      omega


/-- Closure: a product of non-zero elements of a field is non-zero. -/
theorem mul_mem_units {R add mul zero one : ZFSet.{u}} (hF : IsField R add mul zero one) :
    ∀ x, x ∈ units R mul zero → ∀ y, y ∈ units R mul zero →
      opAt mul x y ∈ units R mul zero := by
  have hR := hF.ring
  intro x hx y hy
  obtain ⟨hxR, hxne⟩ := (mem_units_iff R mul zero x).mp hx
  obtain ⟨hyR, hyne⟩ := (mem_units_iff R mul zero y).mp hy
  refine (mem_units_iff R mul zero _).mpr ⟨mulAt_mem hR hxR hyR, fun he => ?_⟩
  obtain ⟨x', hx', hxx'⟩ := hF.inverses x hxR hxne
  -- `y = (x'·x)·y = x'·(x·y) = x'·0 = 0`
  have hstep : opAt mul x' (opAt mul x y) = opAt mul x' zero := by rw [he]
  rw [← hR.mulAssoc x' hx' x hxR y hyR, hR.mulComm x' hx' x hxR, hxx',
    hR.mulComm one hR.mem_one y hyR, hR.mul_one y hyR,
    mul_zero_of_isRing hR hx'] at hstep
  exact hyne hstep

/-- The non-zero elements of a field form a group. -/
theorem isGroup_units {R add mul zero one : ZFSet.{u}} (hF : IsField R add mul zero one) :
    IsGroup (units R mul zero) (restrictOp mul (units R mul zero)) one := by
  have hR := hF.ring
  have hsub : ∀ w, w ∈ units R mul zero → w ∈ R := fun w hw =>
    ((mem_units_iff R mul zero w).mp hw).left
  have hclosed := mul_mem_units hF
  have hdom : ∀ p, p ∈ prod (units R mul zero) (units R mul zero) → p ∈ domain mul := by
    intro p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff p _ _).mp hp
    rw [hR.mulDom]
    exact opair_mem_prod (hsub a ha) (hsub b hb)
  have happ : ∀ a, a ∈ units R mul zero → ∀ b, b ∈ units R mul zero →
      opAt (restrictOp mul (units R mul zero)) a b = opAt mul a b := fun a ha b hb =>
    opAt_restrictOp hR.mulFun hdom hclosed ha hb
  refine ⟨⟨isFunction_restrictOp hR.mulFun, restrictOp_domain hR.mulFun hdom hclosed,
    restrictOp_range, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (mem_units_iff R mul zero one).mpr ⟨hR.mem_one, fun he => hF.zero_ne_one he.symm⟩
  · intro a ha b hb c hc
    rw [happ a ha b hb, happ _ (hclosed a ha b hb) c hc, happ b hb c hc,
      happ a ha _ (hclosed b hb c hc), hR.mulAssoc a (hsub a ha) b (hsub b hb) c (hsub c hc)]
  · intro a ha
    rw [happ one ((mem_units_iff R mul zero one).mpr
      ⟨hR.mem_one, fun he => hF.zero_ne_one he.symm⟩) a ha,
      hR.mulComm one hR.mem_one a (hsub a ha), hR.mul_one a (hsub a ha)]
  · intro a ha
    rw [happ a ha one ((mem_units_iff R mul zero one).mpr
      ⟨hR.mem_one, fun he => hF.zero_ne_one he.symm⟩), hR.mul_one a (hsub a ha)]
  · intro a ha
    obtain ⟨haR, hane⟩ := (mem_units_iff R mul zero a).mp ha
    obtain ⟨b, hb, hab⟩ := hF.inverses a haR hane
    have hbne : b ≠ zero := by
      intro he
      rw [he, mul_zero_of_isRing hR haR] at hab
      exact hF.zero_ne_one hab
    refine ⟨b, (mem_units_iff R mul zero b).mpr ⟨hb, hbne⟩, ?_, ?_⟩
    · rw [happ a ha b ((mem_units_iff R mul zero b).mpr ⟨hb, hbne⟩)]
      exact hab
    · rw [happ b ((mem_units_iff R mul zero b).mpr ⟨hb, hbne⟩) a ha,
        hR.mulComm b hb a haR]
      exact hab

/-! ## Names for the pieces

The classes, their multiplication and the non-zero ones, named once. -/

def modCls (p : Nat) (z : ZFSet.{u}) : ZFSet.{u} := cls (modRel (intOfNat.{u} p)) NumberTheory.Int.{u} z

def modQuot (p : Nat) : ZFSet.{u} := quotientSet (modRel (intOfNat.{u} p)) NumberTheory.Int.{u}

def modMul (p : Nat) : ZFSet.{u} := congOp (modRel (intOfNat.{u} p)) NumberTheory.Int.{u} intMulOp.{u}

def modUnits (p : Nat) : ZFSet.{u} :=
  units (modQuot.{u} p) (modMul.{u} p) (modCls.{u} p intZero.{u})

def modUnitMul (p : Nat) : ZFSet.{u} := restrictOp (modMul.{u} p) (modUnits.{u} p)

/-- Two naturals with the same residue name the same class.

`cls_eq_iff_sub` turns class equality into a divisibility of the difference and
`intOfNat_sub_mem_multiples_iff` reads that back as a pair of natural
witnesses; the witnesses are the two quotients, and the shared remainder
cancels. -/
theorem modCls_intOfNat_congr {p j k : Nat} (h : j % p = k % p) :
    modCls.{u} p (intOfNat.{u} j) = modCls.{u} p (intOfNat.{u} k) := by
  refine (cls_eq_iff_sub (intOfNat_mem_Int p) (intOfNat_mem_Int _)
    (intOfNat_mem_Int _)).mpr ?_
  refine intOfNat_sub_mem_multiples_iff.mpr ⟨j / p, k / p, ?_⟩
  have hj := Nat.div_add_mod j p
  have hk := Nat.div_add_mod k p
  omega

#print axioms modCls_intOfNat_congr

theorem opAt_modMul {p : Nat} {a b : ZFSet.{u}} (ha : a ∈ NumberTheory.Int.{u}) (hb : b ∈ NumberTheory.Int.{u}) :
    opAt (modMul.{u} p) (modCls.{u} p a) (modCls.{u} p b) = modCls.{u} p (intMul a b) := by
  rw [modMul, modCls, modCls, modCls,
    opAt_congOp (fun x hx y hy => mulAt_mem isRing_int hx hy)
      (isCongruence_modRel_mul (intOfNat_mem_Int p)) ha hb,
    opAt_intMulOp ha hb]

theorem opAt_modUnitMul {p : Nat} (hp : IsPrime p) {A B : ZFSet.{u}}
    (hA : A ∈ modUnits.{u} p) (hB : B ∈ modUnits.{u} p) :
    opAt (modUnitMul.{u} p) A B = opAt (modMul.{u} p) A B := by
  have hpI := intOfNat_mem_Int.{u} p
  refine opAt_restrictOp (congOp_isFunction (fun x hx y hy => mulAt_mem isRing_int hx hy)
    (isCongruence_modRel_mul hpI)) (fun x hx => ?_) (mul_mem_units (isField_intMod hp))
    hA hB
  rw [modMul, congOp_domain (fun x hx y hy => mulAt_mem isRing_int hx hy)]
  obtain ⟨A', hA', B', hB', rfl⟩ := (mem_prod_iff x _ _).mp hx
  exact opair_mem_prod ((mem_units_iff _ _ _ _).mp hA').left
    ((mem_units_iff _ _ _ _).mp hB').left

/-- The units mod `p` commute, so they are a commutative monoid and can be
folded over. -/
theorem isAbelian_modUnits {p : Nat} (hp : IsPrime p) :
    IsAbelian (modUnits.{u} p) (modUnitMul.{u} p) := by
  intro A hA B hB
  rw [opAt_modUnitMul hp hA hB, opAt_modUnitMul hp hB hA]
  exact (isRing_intMod (intOfNat_mem_Int p)).mulComm A ((mem_units_iff _ _ _ _).mp hA).left
    B ((mem_units_iff _ _ _ _).mp hB).left


def intPow (z : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => intOne.{u}
  | k + 1 => intMul (intPow z k) z


theorem equinumerous_modUnits {p : Nat} (hp : IsPrime p) :
    Equinumerous (modUnits.{u} p) (ofNat.{u} (p - 1)) := by
  have hp2 := hp.left
  have hq : Equinumerous (modQuot.{u} p) (ofNat.{u} ((p - 1) + 1)) := by
    rw [show p - 1 + 1 = p by omega]
    exact equinumerous_symm (equinumerous_intMod (by omega))
  exact equinumerous_sdiff_singleton hq (cls_mem_quotientSet intZero_mem_Int)

theorem cls_intOfNat_ne_zero {p j : Nat} (hp : 2 ≤ p) (hj : 0 < j) (hjp : j < p) :
    modCls.{u} p (intOfNat.{u} j) ≠ modCls.{u} p intZero.{u} := by
  intro he
  rw [← intOfNat_zero] at he
  exact absurd (cls_intOfNat_injective hjp (by omega) he) (by omega)

theorem last_mem_modUnits {p : Nat} (hp : IsPrime p) :
    modCls.{u} p (intOfNat.{u} (p - 1)) ∈ modUnits.{u} p := by
  have hp2 := hp.left
  exact (mem_units_iff _ _ _ _).mpr ⟨cls_mem_quotientSet (intOfNat_mem_Int _),
    cls_intOfNat_ne_zero hp2 (by omega) (by omega)⟩


#print axioms isGroup_ratAdd
#print axioms isRing_rat
#print axioms isField_rat
#print axioms isRing_int
#print axioms isCongruence_modRel

#print axioms isRing_intMod
#print axioms isField_intMod
#print axioms isGroup_units
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
`intDvd_of_divides`, for a numeral cofactor, as the sign step delivers.

`intOfNat_mul` carries divisibility into `ℤ` and `intOfNat_injective` carries
it back. -/
theorem divides_of_intMul_ofNat {a b c : Nat}
    (h : intOfNat.{u} b = intMul (intOfNat.{u} a) (intOfNat.{u} c)) :
    Divides a b := by
  rw [intOfNat_mul] at h
  exact ⟨c, intOfNat_injective h⟩

#print axioms intDvd_of_divides
/-- An integer factorisation of numerals is a `Nat` divisibility.

The sign split, once: the cofactor is zero, positive, or the negation of a
positive, and only the middle case carries content -- the other two force the
dividend to vanish. Nothing is decided that is not computed. -/
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
quantifies over all of `NumberTheory.Int`, and the gap is the sign case split.
Zero gives the product zero, a positive cofactor is a numeral outright, and a
negative one makes the right side the negation of a positive numeral while the
left is a numeral -- which only both-vanishing allows.

That case split is the `natAbs` argument done inline, so `natAbs` need not
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
clauses `IsEisenstein` quantifies over. -/
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
/-- Divisibility by a numeral is decidable, at any integer. The `dec` clause
of `IsEisenstein` at `ℤ`, general rather than numeral-restricted: the dividend
normalises to a numeral by `int_eq_ofNat_or_neg` and the sign is absorbed by
`intDvd_neg_iff`, so the two cases are one. -/
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
/-- Euclid's lemma over `ℤ` at arbitrary elements. The `prime` clause of
`IsEisenstein` at the integers. Each factor normalises to a numeral by
`int_eq_ofNat_or_neg`; the sign leaves the product, and the conclusion
transports back by `intDvd_neg_iff`.

`intDvd_of_divides` states its conclusion with `opAt intMulOp` and the sign
machinery uses `intMul`, so `opAt_intMulOp` converts. -/
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
This is one application of `intDvd_of_divides`. -/
theorem cyclotomicShift_dvd_int {p : Nat} (hp : IsPrime p) {j : Nat}
    (hj : j < p - 1) :
    ∃ c, c ∈ NumberTheory.Int.{u} ∧ intOfNat.{u} (choose p (j + 1))
      = opAt intMulOp.{u} (intOfNat.{u} p) c :=
  intDvd_of_divides ((cyclotomicShift_eisenstein hp).left j hj)

#print axioms cyclotomicShift_dvd_int

#print axioms cls_intOfNat_injective
#print axioms equinumerous_intMod

/-- The size step. Writing `M = m + p` and `N = n + q`, the difference
between the two products is exactly `p * q`, so the hypothesis says
`p * q = 1`. -/
theorem natUnit_step {M m N n : Nat} (hm : m ≤ M) (hn : n ≤ N)
    (h : M * N + m * n = 1 + (M * n + m * N)) : M = m + 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, M = m + p := ⟨M - m, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, N = n + q := ⟨N - n, by omega⟩
  have e1 : (m + p) * (n + q) = m * n + m * q + p * n + p * q := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have e2 : (m + p) * n = m * n + p * n := Nat.add_mul m p n
  have e3 : m * (n + q) = m * n + m * q := Nat.mul_add m n q
  rw [e1, e2, e3] at h
  have := eq_one_of_divides_one (d := p) ⟨q, by omega⟩
  omega

/-- `|1| = 1`. -/
theorem intAbs_intOne : intAbs intOne.{u} = intOne.{u} := by
  rw [intOne, intAbs_intOf_gen (ofNat_mem_omega 1) empty_mem_omega,
    union_empty, inter_empty]

/-- A unit of `ℤ` has absolute value one.

The multiplicativity of `intAbs` splits `z * w = 1` into `|z| * |w| = 1`, and
`natUnit_step` closes it. No sign is decided: `intAbs` takes the larger and the
smaller by the lattice operations rather than by a comparison. -/
theorem intAbs_eq_one_of_unit {z : ZFSet.{u}}
    (hz : z ∈ unitsOf NumberTheory.Int.{u} intMulOp.{u} intOne.{u}) :
    intAbs z = intOne.{u} := by
  obtain ⟨hzI, w, hwI, hzw⟩ := (mem_unitsOf_iff _ _ _ _).mp hz
  rw [opAt_intMulOp hzI hwI] at hzw
  have habs : intMul (intAbs z) (intAbs w) = intOne.{u} := by
    rw [← intAbs_intMul hzI hwI, hzw, intAbs_intOne]
  obtain ⟨a', ha', b', hb', rfl⟩ := (mem_Int_iff z).mp hzI
  obtain ⟨c', hc', d', hd', rfl⟩ := (mem_Int_iff w).mp hwI
  obtain ⟨a, rfl⟩ := (mem_omega_iff a').mp ha'
  obtain ⟨b, rfl⟩ := (mem_omega_iff b').mp hb'
  obtain ⟨c, rfl⟩ := (mem_omega_iff c').mp hc'
  obtain ⟨d, rfl⟩ := (mem_omega_iff d').mp hd'
  rw [intAbs_intOf_nat a b, intAbs_intOf_nat c d,
    intMul_intOf (ofNat_mem_omega _) (ofNat_mem_omega _)
      (ofNat_mem_omega _) (ofNat_mem_omega _),
    mul_ofNat, mul_ofNat, mul_ofNat, mul_ofNat, add_ofNat, add_ofNat,
    intOne, ← ofNat_zero,
    intOf_eq_intOf_iff (ofNat_mem_omega _) (ofNat_mem_omega _)
      (ofNat_mem_omega _) (ofNat_mem_omega _), add_ofNat, add_ofNat] at habs
  have key := ofNat_injective habs
  have hM := natUnit_step (m := Nat.min a b) (M := Nat.max a b)
    (n := Nat.min c d) (N := Nat.max c d) (Nat.le_trans (Nat.min_le_left a b) (Nat.le_max_left a b))
    (Nat.le_trans (Nat.min_le_left c d) (Nat.le_max_left c d)) (by omega)
  rw [intAbs_intOf_nat a b, intOne, ← ofNat_zero,
    intOf_eq_intOf_iff (ofNat_mem_omega _) (ofNat_mem_omega _)
      (ofNat_mem_omega _) (ofNat_mem_omega _), add_ofNat, add_ofNat]
  exact congrArg ofNat (by omega)


#print axioms natUnit_step
#print axioms intAbs_intOne
#print axioms intAbs_eq_one_of_unit
#print axioms ratAdd_maps
#print axioms ratMul_maps
#print axioms intMul_maps
#print axioms opair_mem_numeralClasses
#print axioms opAt_ratAddOp
#print axioms opAt_ratMulOp
#print axioms opAt_intMulOp
#print axioms mem_multiplesOf_iff
#print axioms opair_mem_modRel_iff
#print axioms isCongruence_modRel_mul
#print axioms intOfNat_sub_mem_multiples_iff
#print axioms exists_cls_intOfNat
#print axioms mem_numeralClasses_iff
#print axioms cls_eq_iff_sub
#print axioms mul_mem_units
#print axioms opAt_modMul
#print axioms opAt_modUnitMul
#print axioms isAbelian_modUnits
#print axioms equinumerous_modUnits
#print axioms cls_intOfNat_ne_zero
#print axioms last_mem_modUnits
end Algebra

namespace ZFSet
export Algebra (cls_eq_iff_sub cls_intOfNat_injective cls_intOfNat_ne_zero cyclotomicShift_dvd_int divides_of_intMul_ofNat divides_of_intOfNat_eq_mul equinumerous_intMod equinumerous_modUnits exists_cls_intOfNat natIn_eq_intOfNat field_no_zero_divisors_ne intAbs_eq_one_of_unit intAbs_intOne intDvd_decidable intDvd_neg_iff intDvd_ofNat_decidable intDvd_of_divides intMulOp intOfNat_sub_mem_multiples_iff intPow intPrime_divides_mul intPrime_divides_mul_ofNat int_eq_ofNat_or_neg isAbelian_modUnits isCongruence_modRel isCongruence_modRel_mul isField_intMod isField_rat isGroup_ratAdd isGroup_units isRing_int isRing_intMod isRing_rat last_mem_modUnits mem_multiplesOf_iff mem_numeralClasses_iff modCls modCls_intOfNat_congr modMul modQuot modRel modUnitMul modUnits mulAt_interchange mul_mem_units mul_right_cancel_field multiplesOf natUnit_step numeralClasses opAt_intMulOp opAt_modMul opAt_modUnitMul opAt_ratAddOp opAt_ratMulOp opair_mem_modRel_iff ratAddOp ratMulOp)
end ZFSet
