/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Integral domains, and the fractions over one

`Ring.lean` has rings and fields; between them sits the integral domain,
which is what a field of fractions is built over. This file names it and
identifies the two instances the library already has the content for.

The negative form of "no zero divisors" is the one stated here, and the
choice is load-bearing rather than stylistic. Written disjunctively --
`a * b = 0 → a = 0 ∨ b = 0` -- the property needs a decision: naming which
factor vanishes is more than knowing one of them does, and
`field_no_zero_divisors` accordingly asks for `DecidableVanishing`. Written
as `a ≠ 0 → b ≠ 0 → a * b ≠ 0` it needs nothing: `field_mul_eq_zero` gives it
for any field at all.

The two forms are classically equivalent and constructively are not. The
negative one is what a denominator needs -- carried with a proof it is
nonzero, and a product of two such must again be a legitimate denominator.

It is not all the construction needs, and the section below says what else
and why: the fraction relation's transitivity is a cancellation, and
cancellation does not follow from the negative form without
double-negation elimination.
-/

import FromAxioms.Algebra.Field

universe u

open Algebra SetTheory
namespace NumberTheory

/-- An integral domain: a commutative ring with distinct zero and one in
which a product of nonzero elements is nonzero. -/
structure IsIntegralDomain (R add mul zero one : ZFSet.{u}) : Prop where
  ring : IsRing R add mul zero one
  zero_ne_one : zero ≠ one
  mul_ne_zero : ∀ a, a ∈ R → ∀ b, b ∈ R → a ≠ zero → b ≠ zero →
    opAt mul a b ≠ zero

/-- The quotient by a prime ideal is an integral domain. The section header
above has asserted this since it was written; the argument lived inside
`isField_quotient_of_prime`, where finiteness was also required and nothing
could reach the domain half on its own. -/
theorem isIntegralDomain_quotient_of_prime {I R add mul zero one : ZFSet.{u}}
    (h : IsRing R add mul zero one) (hP : IsPrimeIdeal I R add mul zero one) :
    IsIntegralDomain (quotientSet (idealRel R add zero I) R)
      (congOp (idealRel R add zero I) R add) (congOp (idealRel R add zero I) R mul)
      (cls (idealRel R add zero I) R zero) (cls (idealRel R add zero I) R one) where
  ring := isRing_quotientByIdeal h hP.left
  zero_ne_one := fun he =>
    hP.right.left ((cls_eq_zero_iff h hP.left h.mem_one).mp he.symm)
  mul_ne_zero := by
    have hI := hP.left
    intro A hA B hB hAne hBne hAB
    obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
    obtain ⟨b, hb, rfl⟩ := (mem_quotientSet_iff _ _ B).mp hB
    rw [opAt_congOp (fun x hx y hy => mulAt_mem h hx hy)
        (isCongruence_idealRel_mul h hI) ha hb,
      cls_eq_zero_iff h hI (mulAt_mem h ha hb)] at hAB
    rcases hP.right.right a ha b hb hAB with hmem | hmem
    · exact hAne ((cls_eq_zero_iff h hI ha).mpr hmem)
    · exact hBne ((cls_eq_zero_iff h hI hb).mpr hmem)

#print axioms isIntegralDomain_quotient_of_prime
/-! ## Cancellation, which is what the fraction relation needs

The negative form above is free and is not enough. Transitivity of
`a/b ~ c/d` is the cancellation step -- from `a*d = c*b` and `c*f = e*d`
conclude `a*f = e*b` -- and cancelling a nonzero factor does not follow from
`a ≠ 0 → b ≠ 0 → a*b ≠ 0`.

The gap is a double negation. Given `a*c = b*c` and `c ≠ 0`: if `a ≠ b` then
`a - b ≠ 0`, so `(a - b)*c ≠ 0`, contradicting `(a - b)*c = 0`. That yields
`¬ (a ≠ b)`, and turning it into `a = b` is exactly double-negation
elimination. The disjunctive form has no such gap -- `(a-b)*c = 0` gives
`a - b = 0 ∨ c = 0` and the second disjunct is refuted -- which is the same
overlapping-versus-decided distinction again: `field_no_zero_divisors` is
written with `DecidableVanishing` for it.

So cancellation is taken as its own property rather than derived, and the
implication that does hold runs the other way: cancellation gives the
negative form, which is how `Int` gets it (`intMul_ne_zero` is proved from
`intMul_left_cancel`). -/

/-- Cancellation: a nonzero left factor can be removed from an equation. -/
def IsCancellative (R mul zero : ZFSet.{u}) : Prop :=
  ∀ c, c ∈ R → ∀ a, a ∈ R → ∀ b, b ∈ R → c ≠ zero →
    opAt mul c a = opAt mul c b → a = b

/-- Cancellation gives the negative form, so a cancellative ring with
`0 ≠ 1` is a domain. The converse fails constructively -- see above. -/
theorem isIntegralDomain_of_cancellative {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hne : zero ≠ one)
    (hc : IsCancellative R mul zero) : IsIntegralDomain R add mul zero one where
  ring := hR
  zero_ne_one := hne
  mul_ne_zero a ha b hb ha0 hb0 hab :=
    hb0 (hc a ha b hb zero hR.addGroup.mem_e ha0
      (by rw [hab, mul_zero_of_isRing hR ha]))

/-- The disjunctive form gives cancellation, which the negative form does
not. This is the converse the docstring above says fails, holding exactly
where the double negation is paid for: `c*(a-b) = 0` names a vanishing factor,
`c` is refuted, and `a - b = 0` is an equality rather than a refutation. -/
theorem isCancellative_of_disjunctive {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one)
    (hdisj : ∀ a, a ∈ R → ∀ b, b ∈ R → opAt mul a b = zero → a = zero ∨ b = zero) :
    IsCancellative R mul zero := by
  intro c hc a ha b hb hc0 he
  have hkey : opAt mul c (opAt add a (ringNeg R add zero b)) = zero := by
    rw [hR.distrib c hc a ha _ (ringNeg_mem hR hb), ringMul_neg hR hc hb, he]
    exact ringAdd_neg hR (mulAt_mem hR hc hb)
  rcases hdisj c hc _ (addAt_mem hR ha (ringNeg_mem hR hb)) hkey with h | h
  · exact absurd h hc0
  · exact (ringSub_eq_zero_iff hR ha hb).mp h

/-- A field cancels, so `IsCancellative` never has to be assumed alongside
`IsField`. The inverse does the work in one step; the only content is the SIDE,
since `IsCancellative` is stated on the left and `mul_right_cancel_field`
cancels on the right. -/
theorem isCancellative_of_isField {R add mul zero one : ZFSet.{u}}
    (hF : IsField R add mul zero one) : IsCancellative R mul zero :=
  fun c hc a ha b hb hc0 he =>
    mul_right_cancel_field hF ha hb hc hc0
      (by rw [hF.ring.mulComm a ha c hc, hF.ring.mulComm b hb c hc]; exact he)

/-- Zero and one are distinct integers: their pair representatives differ in
the first coordinate. -/
theorem intZero_ne_intOne : intZero.{u} ≠ intOne.{u} := by
  intro he
  rw [intZero, intOne, intOf_eq_intOf_iff empty_mem_omega empty_mem_omega
    (ofNat_mem_omega 1) empty_mem_omega, add_empty, add_empty,
    ← ofNat_zero] at he
  exact Nat.noConfusion (ofNat_injective he)

/-! ## The fractions over a cancellative domain

A fraction is a pair `⟨a, b⟩` with `b` nonzero, and `a/b ~ c/d` when
`a*d = c*b`. Reflexivity and symmetry are immediate; transitivity is the
cancellation, and it is the only place any hypothesis beyond `IsRing` is
used. -/

/-- The nonzero elements of `R`. -/
def nonzeroIn (R zero : ZFSet.{u}) : ZFSet.{u} := sep (fun a => a ≠ zero) R

theorem mem_nonzeroIn_iff {R zero a : ZFSet.{u}} :
    a ∈ nonzeroIn R zero ↔ And (a ∈ R) (a ≠ zero) :=
  mem_sep_iff _ _ _

theorem nonzeroIn_subset {R zero : ZFSet.{u}} : nonzeroIn R zero ⊆ R :=
  fun _ h => (mem_nonzeroIn_iff.mp h).left

/-- Numerator over nonzero denominator. -/
def fracPairs (R zero : ZFSet.{u}) : ZFSet.{u} := prod R (nonzeroIn R zero)

theorem mem_fracPairs_iff {R zero p : ZFSet.{u}} :
    p ∈ fracPairs R zero ↔
      ∃ a, a ∈ R ∧ ∃ b, b ∈ nonzeroIn R zero ∧ p = opair a b :=
  mem_prod_iff p _ _

/-- `a/b ~ c/d` exactly when `a*d = c*b`. -/
def fracRel (R mul zero : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ a b c d, p = opair (opair a b) (opair c d) ∧
        opAt mul a d = opAt mul c b)
    (prod (fracPairs R zero) (fracPairs R zero))

theorem mem_fracRel_iff {R mul zero a b c d : ZFSet.{u}}
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero)
    (hc : c ∈ R) (hd : d ∈ nonzeroIn R zero) :
    opair (opair a b) (opair c d) ∈ fracRel R mul zero ↔
      opAt mul a d = opAt mul c b :=
  mem_pairRel_iff (opair_mem_prod ha hb) (opair_mem_prod hc hd)

/-- The fraction relation is an equivalence, and transitivity is where
cancellation is spent -- the only hypothesis beyond the ring laws. -/
theorem fracRel_isEquivRel {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hcan : IsCancellative R mul zero) :
    IsEquivRel (fracRel R mul zero) (fracPairs R zero) where
  refl p hp := by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_fracPairs_iff.mp hp
    exact (mem_fracRel_iff ha hb ha hb).mpr rfl
  symm p q hp hq hpq := by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_fracPairs_iff.mp hp
    obtain ⟨c, hc, d, hd, rfl⟩ := mem_fracPairs_iff.mp hq
    exact (mem_fracRel_iff hc hd ha hb).mpr
      ((mem_fracRel_iff ha hb hc hd).mp hpq).symm
  trans p q r hp hq hr hpq hqr := by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_fracPairs_iff.mp hp
    obtain ⟨c, hc, d, hd, rfl⟩ := mem_fracPairs_iff.mp hq
    obtain ⟨e, he, f, hf, rfl⟩ := mem_fracPairs_iff.mp hr
    have hbR := (mem_nonzeroIn_iff.mp hb).left
    have hdR := (mem_nonzeroIn_iff.mp hd).left
    have hd0 := (mem_nonzeroIn_iff.mp hd).right
    have hfR := (mem_nonzeroIn_iff.mp hf).left
    have h1 := (mem_fracRel_iff ha hb hc hd).mp hpq
    have h2 := (mem_fracRel_iff hc hd he hf).mp hqr
    refine (mem_fracRel_iff ha hb he hf).mpr ?_
    -- cancel `d` from `d * (a*f) = d * (e*b)`
    refine hcan d hdR _ (mulAt_mem hR ha hfR) _ (mulAt_mem hR he hbR) hd0 ?_
    calc opAt mul d (opAt mul a f)
        = opAt mul (opAt mul d a) f := (hR.mulAssoc d hdR a ha f hfR).symm
      _ = opAt mul (opAt mul a d) f := by rw [hR.mulComm d hdR a ha]
      _ = opAt mul (opAt mul c b) f := by rw [h1]
      _ = opAt mul c (opAt mul b f) := hR.mulAssoc c hc b hbR f hfR
      _ = opAt mul c (opAt mul f b) := by rw [hR.mulComm b hbR f hfR]
      _ = opAt mul (opAt mul c f) b := (hR.mulAssoc c hc f hfR b hbR).symm
      _ = opAt mul (opAt mul e d) b := by rw [h2]
      _ = opAt mul (opAt mul d e) b := by rw [hR.mulComm e he d hdR]
      _ = opAt mul d (opAt mul e b) := hR.mulAssoc d hdR e he b hbR

/-- The fractions of `R`: the quotient of numerator-denominator pairs. -/
def FracField (R mul zero : ZFSet.{u}) : ZFSet.{u} :=
  quotientSet (fracRel R mul zero) (fracPairs R zero)

/-- `a/b` as an element of the fraction field. -/
def fracOf (R mul zero a b : ZFSet.{u}) : ZFSet.{u} :=
  cls (fracRel R mul zero) (fracPairs R zero) (opair a b)

theorem fracOf_mem {R mul zero a b : ZFSet.{u}} (ha : a ∈ R)
    (hb : b ∈ nonzeroIn R zero) : fracOf R mul zero a b ∈ FracField R mul zero :=
  cls_mem_quotientSet (opair_mem_prod ha hb)

/-- Two fractions are equal exactly when they cross-multiply, which is
the relation the quotient is by. -/
theorem fracOf_eq_fracOf_iff {R add mul zero one a b c d : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero)
    (hc : c ∈ R) (hd : d ∈ nonzeroIn R zero) :
    fracOf R mul zero a b = fracOf R mul zero c d ↔
      opAt mul a d = opAt mul c b :=
  Iff.trans
    (cls_eq_cls_iff (fracRel_isEquivRel hR hcan)
      (opair_mem_prod ha hb) (opair_mem_prod hc hd))
    (mem_fracRel_iff ha hb hc hd)

/-! ## Multiplying fractions

`(a/b) * (c/d) = (a*c)/(b*d)`. Three hypotheses have now each done a
distinct job, which is worth naming: the ring laws rearrange the
products, the domain supplies `b*d ≠ 0` so the result is a legitimate
fraction, and cancellation was spent on the relation's transitivity. No
one of them subsumes another. -/

/-- A product of nonzero elements is a legitimate denominator. -/
theorem mulAt_mem_nonzeroIn {R add mul zero one b d : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hb : b ∈ nonzeroIn R zero) (hd : d ∈ nonzeroIn R zero) :
    opAt mul b d ∈ nonzeroIn R zero := by
  obtain ⟨hbR, hb0⟩ := mem_nonzeroIn_iff.mp hb
  obtain ⟨hdR, hd0⟩ := mem_nonzeroIn_iff.mp hd
  exact mem_nonzeroIn_iff.mpr
    ⟨mulAt_mem hdom.ring hbR hdR, hdom.mul_ne_zero b hbR d hdR hb0 hd0⟩

/-- Multiplication respects the relation, so it descends to the
quotient. Only the ring laws are used to rearrange; the domain supplies the
denominator's nonvanishing. -/
theorem fracOf_mul_congr {R add mul zero one a b c d a' b' c' d' : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero)
    (hc : c ∈ R) (hd : d ∈ nonzeroIn R zero)
    (ha' : a' ∈ R) (hb' : b' ∈ nonzeroIn R zero)
    (hc' : c' ∈ R) (hd' : d' ∈ nonzeroIn R zero)
    (h₁ : opAt mul a b' = opAt mul a' b)
    (h₂ : opAt mul c d' = opAt mul c' d) :
    fracOf R mul zero (opAt mul a c) (opAt mul b d)
      = fracOf R mul zero (opAt mul a' c') (opAt mul b' d') := by
  have hR := hdom.ring
  have hbR := (mem_nonzeroIn_iff.mp hb).left
  have hdR := (mem_nonzeroIn_iff.mp hd).left
  have hb'R := (mem_nonzeroIn_iff.mp hb').left
  have hd'R := (mem_nonzeroIn_iff.mp hd').left
  refine (fracOf_eq_fracOf_iff hR hcan (mulAt_mem hR ha hc)
    (mulAt_mem_nonzeroIn hdom hb hd) (mulAt_mem hR ha' hc')
    (mulAt_mem_nonzeroIn hdom hb' hd')).mpr ?_
  calc opAt mul (opAt mul a c) (opAt mul b' d')
      = opAt mul (opAt mul a b') (opAt mul c d') :=
        ringMul_shuffle_pair hR ha hc hb'R hd'R
    _ = opAt mul (opAt mul a' b) (opAt mul c' d) := by rw [h₁, h₂]
    _ = opAt mul (opAt mul a' c') (opAt mul b d) :=
        ringMul_shuffle_pair hR ha' hbR hc' hdR

/-! ## Adding fractions

`(a/b) + (c/d) = (a*d + c*b)/(b*d)`. The denominator is the same product as
for multiplication, so the domain does the same job; what is new is that the
numerator is a sum, and `ringRight_distrib` splits the cross-multiplied
equation into two halves that `h₁` and `h₂` close separately. -/

/-- Addition respects the relation, so it descends to the quotient. Each
half of the numerator is closed by one of the two hypotheses, after the
right-distributive split. -/
theorem fracOf_add_congr {R add mul zero one a b c d a' b' c' d' : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero)
    (hc : c ∈ R) (hd : d ∈ nonzeroIn R zero)
    (ha' : a' ∈ R) (hb' : b' ∈ nonzeroIn R zero)
    (hc' : c' ∈ R) (hd' : d' ∈ nonzeroIn R zero)
    (h₁ : opAt mul a b' = opAt mul a' b)
    (h₂ : opAt mul c d' = opAt mul c' d) :
    fracOf R mul zero
        (opAt add (opAt mul a d) (opAt mul c b)) (opAt mul b d)
      = fracOf R mul zero
        (opAt add (opAt mul a' d') (opAt mul c' b')) (opAt mul b' d') := by
  have hR := hdom.ring
  have hbR := (mem_nonzeroIn_iff.mp hb).left
  have hdR := (mem_nonzeroIn_iff.mp hd).left
  have hb'R := (mem_nonzeroIn_iff.mp hb').left
  have hd'R := (mem_nonzeroIn_iff.mp hd').left
  have had := mulAt_mem hR ha hdR
  have hcb := mulAt_mem hR hc hbR
  have ha'd' := mulAt_mem hR ha' hd'R
  have hc'b' := mulAt_mem hR hc' hb'R
  have hleft : opAt mul (opAt mul a d) (opAt mul b' d')
      = opAt mul (opAt mul a' d') (opAt mul b d) :=
    calc opAt mul (opAt mul a d) (opAt mul b' d')
        = opAt mul (opAt mul a b') (opAt mul d d') :=
          ringMul_shuffle_pair hR ha hdR hb'R hd'R
      _ = opAt mul (opAt mul a' b) (opAt mul d d') := by rw [h₁]
      _ = opAt mul (opAt mul a' b) (opAt mul d' d) := by
          rw [hR.mulComm d hdR d' hd'R]
      _ = opAt mul (opAt mul a' d') (opAt mul b d) :=
          ringMul_shuffle_pair hR ha' hbR hd'R hdR
  have hright : opAt mul (opAt mul c b) (opAt mul b' d')
      = opAt mul (opAt mul c' b') (opAt mul b d) :=
    calc opAt mul (opAt mul c b) (opAt mul b' d')
        = opAt mul (opAt mul c b) (opAt mul d' b') := by
          rw [hR.mulComm b' hb'R d' hd'R]
      _ = opAt mul (opAt mul c d') (opAt mul b b') :=
          ringMul_shuffle_pair hR hc hbR hd'R hb'R
      _ = opAt mul (opAt mul c' d) (opAt mul b b') := by rw [h₂]
      _ = opAt mul (opAt mul c' d) (opAt mul b' b) := by
          rw [hR.mulComm b hbR b' hb'R]
      _ = opAt mul (opAt mul c' b') (opAt mul d b) :=
          ringMul_shuffle_pair hR hc' hdR hb'R hbR
      _ = opAt mul (opAt mul c' b') (opAt mul b d) := by
          rw [hR.mulComm d hdR b hbR]
  refine (fracOf_eq_fracOf_iff hR hcan (addAt_mem hR had hcb)
    (mulAt_mem_nonzeroIn hdom hb hd) (addAt_mem hR ha'd' hc'b')
    (mulAt_mem_nonzeroIn hdom hb' hd')).mpr ?_
  rw [ringRight_distrib hR had hcb (mulAt_mem hR hb'R hd'R),
    ringRight_distrib hR ha'd' hc'b' (mulAt_mem hR hbR hdR), hleft, hright]

/-! ## Inverses

A class is zero exactly when its numerator is, and that is an equivalence
rather than a decision -- so "this class is nonzero" hands back
`a ≠ zero` with nothing spent, and `b/a` is then a legitimate fraction. -/

/-- `one` is a legitimate denominator, since a domain has `0 ≠ 1`. -/
theorem one_mem_nonzeroIn {R add mul zero one : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one) :
    one ∈ nonzeroIn R zero :=
  mem_nonzeroIn_iff.mpr ⟨hdom.ring.mem_one, fun he => hdom.zero_ne_one he.symm⟩

/-- A fraction is zero exactly when its numerator is. An equivalence, so
the negation transfers in both directions and no vanishing is decided. -/
theorem fracOf_eq_zero_iff {R add mul zero one a b : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero) :
    fracOf R mul zero a b = fracOf R mul zero zero one ↔ a = zero := by
  have hR := hdom.ring
  have hbR := (mem_nonzeroIn_iff.mp hb).left
  refine Iff.trans (fracOf_eq_fracOf_iff hR hcan ha hb hR.addGroup.mem_e
    (one_mem_nonzeroIn hdom)) ?_
  rw [hR.mul_one a ha, ringZero_mul hR hbR]

/-- Every nonzero class has an inverse, and the witness is the fraction
turned over. The nonzero hypothesis is on the class; `fracOf_eq_zero_iff`
turns it into `a ≠ zero` with nothing spent, so `b/a` is a legitimate fraction.
-/
theorem fracOf_mul_inv {R add mul zero one a b : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero)
    (hne : fracOf R mul zero a b ≠ fracOf R mul zero zero one) :
    And (a ∈ nonzeroIn R zero)
      (fracOf R mul zero (opAt mul a b) (opAt mul b a)
        = fracOf R mul zero one one) := by
  have hR := hdom.ring
  have hbR := (mem_nonzeroIn_iff.mp hb).left
  have ha0 : a ≠ zero := fun he =>
    hne ((fracOf_eq_zero_iff hdom hcan ha hb).mpr he)
  have haN : a ∈ nonzeroIn R zero := mem_nonzeroIn_iff.mpr ⟨ha, ha0⟩
  refine ⟨haN, ?_⟩
  have hone := one_mem_nonzeroIn hdom
  refine (fracOf_eq_fracOf_iff hR hcan (mulAt_mem hR ha hbR)
    (mulAt_mem_nonzeroIn hdom hb haN) hR.mem_one hone).mpr ?_
  rw [hR.mul_one _ (mulAt_mem hR ha hbR),
    ringOne_mul hR (mulAt_mem hR hbR ha), hR.mulComm a ha b hbR]

/-! ## The operations

Following `Rational.lean`: an operation quantifies into the classes rather
than selecting representatives, stating its condition as membership in the
class of the result of those representatives. Well-definedness is then one
equality of classes -- `fracOf_mul_congr`, `fracOf_add_congr` -- rather than
an equation replayed in every proof. -/

theorem fracOf_subset (R mul zero a b : ZFSet.{u}) :
    fracOf R mul zero a b ⊆ fracPairs R zero := cls_subset _ _ _

theorem mem_FracField_iff {R mul zero : ZFSet.{u}} (r : ZFSet.{u}) :
    r ∈ FracField R mul zero ↔
      ∃ a, a ∈ R ∧ ∃ b, b ∈ nonzeroIn R zero ∧ r = fracOf R mul zero a b := by
  refine Iff.trans (mem_quotientSet_iff _ _ r) ⟨?_, ?_⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_fracPairs_iff.mp hp
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨opair a b, opair_mem_prod ha hb, rfl⟩

theorem mem_fracOf_iff {R mul zero a b : ZFSet.{u}}
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero) (p : ZFSet.{u}) :
    p ∈ fracOf R mul zero a b ↔
      ∃ c, c ∈ R ∧ ∃ d, d ∈ nonzeroIn R zero ∧ p = opair c d ∧
        opAt mul a d = opAt mul c b := by
  refine Iff.trans (mem_cls_iff _ _ _ p) ⟨?_, ?_⟩
  · rintro ⟨hp, hrel⟩
    obtain ⟨c, hc, d, hd, rfl⟩ := mem_fracPairs_iff.mp hp
    exact ⟨c, hc, d, hd, rfl, (mem_fracRel_iff ha hb hc hd).mp hrel⟩
  · rintro ⟨c, hc, d, hd, rfl, hcross⟩
    exact ⟨opair_mem_prod hc hd, (mem_fracRel_iff ha hb hc hd).mpr hcross⟩

/-- Multiplication of classes. -/
def fracMul (R mul zero r s : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ a b c d, opair a b ∈ r ∧ opair c d ∈ s ∧
        p ∈ fracOf R mul zero (opAt mul a c) (opAt mul b d))
    (fracPairs R zero)

/-- Addition of classes. -/
def fracAdd (R add mul zero r s : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ a b c d, opair a b ∈ r ∧ opair c d ∈ s ∧
        p ∈ fracOf R mul zero
          (opAt add (opAt mul a d) (opAt mul c b)) (opAt mul b d))
    (fracPairs R zero)

/-- Multiplication computes on representatives, which is where
`fracOf_mul_congr` is consumed. -/
theorem fracMul_fracOf {R add mul zero one a b c d : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero)
    (hc : c ∈ R) (hd : d ∈ nonzeroIn R zero) :
    fracMul R mul zero (fracOf R mul zero a b) (fracOf R mul zero c d)
      = fracOf R mul zero (opAt mul a c) (opAt mul b d) := by
  have hR := hdom.ring
  refine ext _ _ fun p => ?_
  refine Iff.trans (mem_sep_iff _ p _) ⟨?_, ?_⟩
  · rintro ⟨-, a', b', c', d', h₁, h₂, hmem⟩
    obtain ⟨a'', ha'', b'', hb'', he₁, r₁⟩ :=
      (mem_fracOf_iff ha hb _).mp h₁
    obtain ⟨rfl, rfl⟩ := opair_injective he₁
    obtain ⟨c'', hc'', d'', hd'', he₂, r₂⟩ :=
      (mem_fracOf_iff hc hd _).mp h₂
    obtain ⟨rfl, rfl⟩ := opair_injective he₂
    rwa [← fracOf_mul_congr hdom hcan ha hb hc hd ha'' hb'' hc'' hd'' r₁ r₂]
      at hmem
  · intro hmem
    exact ⟨fracOf_subset _ _ _ _ _ p hmem, a, b, c, d,
      mem_cls_self (fracRel_isEquivRel hR hcan) (opair_mem_prod ha hb),
      mem_cls_self (fracRel_isEquivRel hR hcan) (opair_mem_prod hc hd), hmem⟩

/-- Addition computes on representatives, consuming
`fracOf_add_congr`. -/
theorem fracAdd_fracOf {R add mul zero one a b c d : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero)
    (hc : c ∈ R) (hd : d ∈ nonzeroIn R zero) :
    fracAdd R add mul zero (fracOf R mul zero a b) (fracOf R mul zero c d)
      = fracOf R mul zero
          (opAt add (opAt mul a d) (opAt mul c b)) (opAt mul b d) := by
  have hR := hdom.ring
  refine ext _ _ fun p => ?_
  refine Iff.trans (mem_sep_iff _ p _) ⟨?_, ?_⟩
  · rintro ⟨-, a', b', c', d', h₁, h₂, hmem⟩
    obtain ⟨a'', ha'', b'', hb'', he₁, r₁⟩ :=
      (mem_fracOf_iff ha hb _).mp h₁
    obtain ⟨rfl, rfl⟩ := opair_injective he₁
    obtain ⟨c'', hc'', d'', hd'', he₂, r₂⟩ :=
      (mem_fracOf_iff hc hd _).mp h₂
    obtain ⟨rfl, rfl⟩ := opair_injective he₂
    rwa [← fracOf_add_congr hdom hcan ha hb hc hd ha'' hb'' hc'' hd'' r₁ r₂]
      at hmem
  · intro hmem
    exact ⟨fracOf_subset _ _ _ _ _ p hmem, a, b, c, d,
      mem_cls_self (fracRel_isEquivRel hR hcan) (opair_mem_prod ha hb),
      mem_cls_self (fracRel_isEquivRel hR hcan) (opair_mem_prod hc hd), hmem⟩

theorem fracMul_mem {R add mul zero one r s : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (hr : r ∈ FracField R mul zero) (hs : s ∈ FracField R mul zero) :
    fracMul R mul zero r s ∈ FracField R mul zero := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_FracField_iff _).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_FracField_iff _).mp hs
  rw [fracMul_fracOf hdom hcan ha hb hc hd]
  exact fracOf_mem (mulAt_mem hdom.ring ha hc)
    (mulAt_mem_nonzeroIn hdom hb hd)

theorem fracAdd_mem {R add mul zero one r s : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (hr : r ∈ FracField R mul zero) (hs : s ∈ FracField R mul zero) :
    fracAdd R add mul zero r s ∈ FracField R mul zero := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_FracField_iff _).mp hr
  obtain ⟨c, hc, d, hd, rfl⟩ := (mem_FracField_iff _).mp hs
  rw [fracAdd_fracOf hdom hcan ha hb hc hd]
  have hR := hdom.ring
  exact fracOf_mem
    (addAt_mem hR (mulAt_mem hR ha (mem_nonzeroIn_iff.mp hd).left)
      (mulAt_mem hR hc (mem_nonzeroIn_iff.mp hb).left))
    (mulAt_mem_nonzeroIn hdom hb hd)

/-! ## The operation graphs

`IsRing` and `IsField` are stated over set-level function graphs applied
with `opAt`, so the Lean-level `fracAdd` and `fracMul` have to be packaged
as sets before anything can be claimed about the structure. The pattern is
`Field.lean`'s for `ℚ`: a `graphOn` over the square, a `maps` lemma for the
codomain, and an `opAt` computation lemma. -/

def fracAddOp (R add mul zero : ZFSet.{u}) : ZFSet.{u} :=
  graphOn (prod (FracField R mul zero) (FracField R mul zero))
    (FracField R mul zero) (fun z => fracAdd R add mul zero (fst z) (snd z))

def fracMulOp (R mul zero : ZFSet.{u}) : ZFSet.{u} :=
  graphOn (prod (FracField R mul zero) (FracField R mul zero))
    (FracField R mul zero) (fun z => fracMul R mul zero (fst z) (snd z))

private theorem fracAdd_maps {R add mul zero one : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero) {z : ZFSet.{u}}
    (hz : z ∈ prod (FracField R mul zero) (FracField R mul zero)) :
    fracAdd R add mul zero (fst z) (snd z) ∈ FracField R mul zero := by
  obtain ⟨r, hr, s, hs, rfl⟩ := (mem_prod_iff z _ _).mp hz
  rw [fst_opair, snd_opair]
  exact fracAdd_mem hdom hcan hr hs

private theorem fracMul_maps {R add mul zero one : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero) {z : ZFSet.{u}}
    (hz : z ∈ prod (FracField R mul zero) (FracField R mul zero)) :
    fracMul R mul zero (fst z) (snd z) ∈ FracField R mul zero := by
  obtain ⟨r, hr, s, hs, rfl⟩ := (mem_prod_iff z _ _).mp hz
  rw [fst_opair, snd_opair]
  exact fracMul_mem hdom hcan hr hs

theorem opAt_fracAddOp {R add mul zero one r s : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (hr : r ∈ FracField R mul zero) (hs : s ∈ FracField R mul zero) :
    opAt (fracAddOp R add mul zero) r s = fracAdd R add mul zero r s := by
  rw [opAt, fracAddOp,
    app_graphOn (fun _ hm => fracAdd_maps hdom hcan hm) (opair_mem_prod hr hs),
    fst_opair, snd_opair]

theorem opAt_fracMulOp {R add mul zero one r s : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (hr : r ∈ FracField R mul zero) (hs : s ∈ FracField R mul zero) :
    opAt (fracMulOp R mul zero) r s = fracMul R mul zero r s := by
  rw [opAt, fracMulOp,
    app_graphOn (fun _ hm => fracMul_maps (one := one) hdom hcan hm)
      (opair_mem_prod hr hs),
    fst_opair, snd_opair]

/-! ## Negation

`-(a/b) = (-a)/b`, and the congruence is `ringNeg_mul` applied to both
sides of the cross-multiplication. The denominator is untouched, so unlike
addition and multiplication this one needs nothing from the domain. -/

/-- Negation of classes. -/
def fracNeg (R add mul zero r : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ∃ a b, opair a b ∈ r ∧
        p ∈ fracOf R mul zero (ringNeg R add zero a) b)
    (fracPairs R zero)

/-- Negation respects the relation. Only the ring laws are used: the
denominator is carried through unchanged, so the domain is not consulted. -/
theorem fracOf_neg_congr {R add mul zero one a b a' b' : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero)
    (ha' : a' ∈ R) (hb' : b' ∈ nonzeroIn R zero)
    (h₁ : opAt mul a b' = opAt mul a' b) :
    fracOf R mul zero (ringNeg R add zero a) b
      = fracOf R mul zero (ringNeg R add zero a') b' := by
  have hbR := (mem_nonzeroIn_iff.mp hb).left
  have hb'R := (mem_nonzeroIn_iff.mp hb').left
  refine (fracOf_eq_fracOf_iff hR hcan (ringNeg_mem hR ha) hb
    (ringNeg_mem hR ha') hb').mpr ?_
  rw [ringNeg_mul hR ha hb'R, ringNeg_mul hR ha' hbR, h₁]

/-- Negation computes on representatives. -/
theorem fracNeg_fracOf {R add mul zero one a b : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero) :
    fracNeg R add mul zero (fracOf R mul zero a b)
      = fracOf R mul zero (ringNeg R add zero a) b := by
  refine ext _ _ fun p => ?_
  refine Iff.trans (mem_sep_iff _ p _) ⟨?_, ?_⟩
  · rintro ⟨-, a', b', h₁, hmem⟩
    obtain ⟨a'', ha'', b'', hb'', he₁, r₁⟩ := (mem_fracOf_iff ha hb _).mp h₁
    obtain ⟨rfl, rfl⟩ := opair_injective he₁
    rwa [← fracOf_neg_congr hR hcan ha hb ha'' hb'' r₁] at hmem
  · intro hmem
    exact ⟨fracOf_subset _ _ _ _ _ p hmem, a, b,
      mem_cls_self (fracRel_isEquivRel hR hcan) (opair_mem_prod ha hb), hmem⟩

theorem fracNeg_mem {R add mul zero one r : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hcan : IsCancellative R mul zero)
    (hr : r ∈ FracField R mul zero) :
    fracNeg R add mul zero r ∈ FracField R mul zero := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_FracField_iff _).mp hr
  rw [fracNeg_fracOf hR hcan ha hb]
  exact fracOf_mem (ringNeg_mem hR ha) hb

/-! ## The unit classes, and the three short laws

`0` and `1` of the fraction field are `0/1` and `1/1`. The identity, the
inverse and the multiplicative unit are each one cross-multiplication after
the computation lemmas; associativity and distributivity are the long ones
and come after. -/

/-- The zero class, `0/1`.

Both spellings are live -- `isField_frac` states the field's zero as `fracZero`,
while `fracOf_eq_zero_iff` and `fracEmbed_ne_zero_of_ne_zero` state theirs as
`fracOf .. zero one` -- and the crossing is definitional, so which one a goal
carries is not a fact about the mathematics.

`rw` crosses it in BOTH directions when the def is NAMED: `rw [fracZero]`
unfolds, `rw [← fracZero]` folds. What does NOT cross is the IMPLICIT trailing
`rfl` of a rewrite, which runs at reducible transparency where a plain `def` is
opaque -- so a goal left as `fracOf .. zero one = fracZero ..` by some other
rewrite needs `rfl`, `exact`, or a naming rewrite, and not the rewrite that
produced it. -/
def fracZero (R mul zero one : ZFSet.{u}) : ZFSet.{u} :=
  fracOf R mul zero zero one

/-- The unit class, `1/1`. -/
def fracOne (R mul zero one : ZFSet.{u}) : ZFSet.{u} :=
  fracOf R mul zero one one

theorem fracZero_mem {R add mul zero one : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one) :
    fracZero R mul zero one ∈ FracField R mul zero :=
  fracOf_mem hdom.ring.addGroup.mem_e (one_mem_nonzeroIn hdom)

theorem fracOne_mem {R add mul zero one : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one) :
    fracOne R mul zero one ∈ FracField R mul zero :=
  fracOf_mem hdom.ring.mem_one (one_mem_nonzeroIn hdom)

/-- Zero is the additive identity. -/
theorem fracAdd_fracZero {R add mul zero one a b : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero) :
    fracAdd R add mul zero (fracOf R mul zero a b) (fracZero R mul zero one)
      = fracOf R mul zero a b := by
  have hR := hdom.ring
  have hbR := (mem_nonzeroIn_iff.mp hb).left
  have hz := hR.addGroup.mem_e
  have hone := one_mem_nonzeroIn hdom
  rw [fracZero, fracAdd_fracOf hdom hcan ha hb hz hone]
  refine (fracOf_eq_fracOf_iff hR hcan
    (addAt_mem hR (mulAt_mem hR ha hR.mem_one) (mulAt_mem hR hz hbR))
    (mulAt_mem_nonzeroIn hdom hb hone) ha hb).mpr ?_
  rw [hR.mul_one a ha, ringZero_mul hR hbR, ringAdd_zero hR ha,
    hR.mul_one b hbR]

/-- Every class has an additive inverse. The denominator squares and the
numerator cancels, and `0/(b*b) = 0/1` because both cross-products vanish. -/
theorem fracAdd_fracNeg {R add mul zero one a b : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero) :
    fracAdd R add mul zero (fracOf R mul zero a b)
        (fracNeg R add mul zero (fracOf R mul zero a b))
      = fracZero R mul zero one := by
  have hR := hdom.ring
  have hbR := (mem_nonzeroIn_iff.mp hb).left
  have hz := hR.addGroup.mem_e
  have hnaR := ringNeg_mem hR ha
  rw [fracNeg_fracOf hR hcan ha hb, fracAdd_fracOf hdom hcan ha hb hnaR hb,
    fracZero]
  refine (fracOf_eq_fracOf_iff hR hcan
    (addAt_mem hR (mulAt_mem hR ha hbR) (mulAt_mem hR hnaR hbR))
    (mulAt_mem_nonzeroIn hdom hb hb) hz (one_mem_nonzeroIn hdom)).mpr ?_
  rw [ringNeg_mul hR ha hbR, ringAdd_neg hR (mulAt_mem hR ha hbR),
    ringZero_mul hR (mulAt_mem hR hbR hbR), hR.mul_one zero hz]

/-- One is the multiplicative identity. -/
theorem fracMul_fracOne {R add mul zero one a b : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero) :
    fracMul R mul zero (fracOf R mul zero a b) (fracOne R mul zero one)
      = fracOf R mul zero a b := by
  have hR := hdom.ring
  have hbR := (mem_nonzeroIn_iff.mp hb).left
  have hone := one_mem_nonzeroIn hdom
  rw [fracOne, fracMul_fracOf hdom hcan ha hb hR.mem_one hone]
  refine (fracOf_eq_fracOf_iff hR hcan (mulAt_mem hR ha hR.mem_one)
    (mulAt_mem_nonzeroIn hdom hb hone) ha hb).mpr ?_
  rw [hR.mul_one a ha, hR.mul_one b hbR]

/-! ## Commutativity, and associativity of multiplication

Three more laws, each one cross-multiplication after the computation
lemmas. Associativity of addition and distributivity are the long ones and
follow separately. -/

/-- Multiplication of classes is commutative. -/
theorem fracMul_comm {R add mul zero one a b c d : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero)
    (hc : c ∈ R) (hd : d ∈ nonzeroIn R zero) :
    fracMul R mul zero (fracOf R mul zero a b) (fracOf R mul zero c d)
      = fracMul R mul zero (fracOf R mul zero c d) (fracOf R mul zero a b) := by
  have hR := hdom.ring
  have hbR := (mem_nonzeroIn_iff.mp hb).left
  have hdR := (mem_nonzeroIn_iff.mp hd).left
  rw [fracMul_fracOf hdom hcan ha hb hc hd,
    fracMul_fracOf hdom hcan hc hd ha hb,
    hR.mulComm c hc a ha, hR.mulComm d hdR b hbR]

/-- Addition of classes is commutative. -/
theorem fracAdd_comm {R add mul zero one a b c d : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero)
    (hc : c ∈ R) (hd : d ∈ nonzeroIn R zero) :
    fracAdd R add mul zero (fracOf R mul zero a b) (fracOf R mul zero c d)
      = fracAdd R add mul zero (fracOf R mul zero c d) (fracOf R mul zero a b) := by
  have hR := hdom.ring
  have hbR := (mem_nonzeroIn_iff.mp hb).left
  have hdR := (mem_nonzeroIn_iff.mp hd).left
  rw [fracAdd_fracOf hdom hcan ha hb hc hd,
    fracAdd_fracOf hdom hcan hc hd ha hb,
    ringAdd_comm hR (mulAt_mem hR hc hbR) (mulAt_mem hR ha hdR),
    hR.mulComm d hdR b hbR]

/-- Multiplication of classes is associative, by associativity in the
numerator and the denominator separately. -/
theorem fracMul_assoc {R add mul zero one a b c d e f : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero)
    (hc : c ∈ R) (hd : d ∈ nonzeroIn R zero)
    (he : e ∈ R) (hf : f ∈ nonzeroIn R zero) :
    fracMul R mul zero
        (fracMul R mul zero (fracOf R mul zero a b) (fracOf R mul zero c d))
        (fracOf R mul zero e f)
      = fracMul R mul zero (fracOf R mul zero a b)
        (fracMul R mul zero (fracOf R mul zero c d) (fracOf R mul zero e f)) := by
  have hR := hdom.ring
  have hbR := (mem_nonzeroIn_iff.mp hb).left
  have hdR := (mem_nonzeroIn_iff.mp hd).left
  have hfR := (mem_nonzeroIn_iff.mp hf).left
  rw [fracMul_fracOf hdom hcan ha hb hc hd,
    fracMul_fracOf hdom hcan (mulAt_mem hR ha hc)
      (mulAt_mem_nonzeroIn hdom hb hd) he hf,
    fracMul_fracOf hdom hcan hc hd he hf,
    fracMul_fracOf hdom hcan ha hb (mulAt_mem hR hc he)
      (mulAt_mem_nonzeroIn hdom hd hf),
    hR.mulAssoc a ha c hc e he, hR.mulAssoc b hbR d hdR f hfR]

/-- Addition of classes is associative. The long one: both sides split
by right-distributivity into three products, and the three match pairwise
after one associativity and one commutation each. The denominators are the
same triple product associated the two ways. -/
theorem fracAdd_assoc {R add mul zero one a b c d e f : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero)
    (hc : c ∈ R) (hd : d ∈ nonzeroIn R zero)
    (he : e ∈ R) (hf : f ∈ nonzeroIn R zero) :
    fracAdd R add mul zero
        (fracAdd R add mul zero (fracOf R mul zero a b) (fracOf R mul zero c d))
        (fracOf R mul zero e f)
      = fracAdd R add mul zero (fracOf R mul zero a b)
        (fracAdd R add mul zero (fracOf R mul zero c d) (fracOf R mul zero e f)) := by
  have hR := hdom.ring
  have hbR := (mem_nonzeroIn_iff.mp hb).left
  have hdR := (mem_nonzeroIn_iff.mp hd).left
  have hfR := (mem_nonzeroIn_iff.mp hf).left
  have had := mulAt_mem hR ha hdR
  have hcb := mulAt_mem hR hc hbR
  have hcf := mulAt_mem hR hc hfR
  have hed := mulAt_mem hR he hdR
  -- the three numerator pieces
  have p1 : opAt mul (opAt mul a d) f = opAt mul a (opAt mul d f) :=
    hR.mulAssoc a ha d hdR f hfR
  have p2 : opAt mul (opAt mul c b) f = opAt mul (opAt mul c f) b :=
    calc opAt mul (opAt mul c b) f
        = opAt mul c (opAt mul b f) := hR.mulAssoc c hc b hbR f hfR
      _ = opAt mul c (opAt mul f b) := by rw [hR.mulComm b hbR f hfR]
      _ = opAt mul (opAt mul c f) b := (hR.mulAssoc c hc f hfR b hbR).symm
  have p3 : opAt mul e (opAt mul b d) = opAt mul (opAt mul e d) b :=
    calc opAt mul e (opAt mul b d)
        = opAt mul e (opAt mul d b) := by rw [hR.mulComm b hbR d hdR]
      _ = opAt mul (opAt mul e d) b := (hR.mulAssoc e he d hdR b hbR).symm
  have hnum : opAt add
        (opAt mul (opAt add (opAt mul a d) (opAt mul c b)) f)
        (opAt mul e (opAt mul b d))
      = opAt add (opAt mul a (opAt mul d f))
        (opAt mul (opAt add (opAt mul c f) (opAt mul e d)) b) :=
    calc opAt add (opAt mul (opAt add (opAt mul a d) (opAt mul c b)) f)
          (opAt mul e (opAt mul b d))
        = opAt add (opAt add (opAt mul (opAt mul a d) f)
            (opAt mul (opAt mul c b) f)) (opAt mul e (opAt mul b d)) := by
          rw [ringRight_distrib hR had hcb hfR]
      _ = opAt add (opAt mul (opAt mul a d) f)
            (opAt add (opAt mul (opAt mul c b) f)
              (opAt mul e (opAt mul b d))) :=
          ringAdd_assoc hR (mulAt_mem hR had hfR) (mulAt_mem hR hcb hfR)
            (mulAt_mem hR he (mulAt_mem hR hbR hdR))
      _ = opAt add (opAt mul a (opAt mul d f))
            (opAt add (opAt mul (opAt mul c f) b)
              (opAt mul (opAt mul e d) b)) := by rw [p1, p2, p3]
      _ = opAt add (opAt mul a (opAt mul d f))
            (opAt mul (opAt add (opAt mul c f) (opAt mul e d)) b) := by
          rw [ringRight_distrib hR hcf hed hbR]
  have hden : opAt mul (opAt mul b d) f = opAt mul b (opAt mul d f) :=
    hR.mulAssoc b hbR d hdR f hfR
  rw [fracAdd_fracOf hdom hcan ha hb hc hd,
    fracAdd_fracOf hdom hcan (addAt_mem hR had hcb)
      (mulAt_mem_nonzeroIn hdom hb hd) he hf,
    fracAdd_fracOf hdom hcan hc hd he hf,
    fracAdd_fracOf hdom hcan ha hb (addAt_mem hR hcf hed)
      (mulAt_mem_nonzeroIn hdom hd hf),
    hnum, hden]

/-! ## Distributivity

The last algebraic law, and the only one whose two sides do not share a
denominator: `a/b * (c/d + e/f)` lands over `b*(d*f)` while the expanded sum
lands over `(b*d)*(b*f)`. So it cannot be closed by rewriting
representatives the way the others were, and wants a scaling lemma to bring
the two over a common denominator first. -/

/-- Scaling numerator and denominator leaves the class alone. -/
theorem fracOf_scale {R add mul zero one a b m : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero) (hm : m ∈ nonzeroIn R zero)
    (hbm : opAt mul b m ∈ nonzeroIn R zero) :
    fracOf R mul zero a b
      = fracOf R mul zero (opAt mul a m) (opAt mul b m) := by
  have hbR := (mem_nonzeroIn_iff.mp hb).left
  have hmR := (mem_nonzeroIn_iff.mp hm).left
  refine (fracOf_eq_fracOf_iff hR hcan ha hb (mulAt_mem hR ha hmR) hbm).mpr ?_
  calc opAt mul a (opAt mul b m)
      = opAt mul a (opAt mul m b) := by rw [hR.mulComm b hbR m hmR]
    _ = opAt mul (opAt mul a m) b := (hR.mulAssoc a ha m hmR b hbR).symm

/-- Multiplication distributes over addition on the quotient. -/
theorem fracMul_add_distrib {R add mul zero one a b c d e f : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hb : b ∈ nonzeroIn R zero)
    (hc : c ∈ R) (hd : d ∈ nonzeroIn R zero)
    (he : e ∈ R) (hf : f ∈ nonzeroIn R zero) :
    fracMul R mul zero (fracOf R mul zero a b)
        (fracAdd R add mul zero (fracOf R mul zero c d) (fracOf R mul zero e f))
      = fracAdd R add mul zero
        (fracMul R mul zero (fracOf R mul zero a b) (fracOf R mul zero c d))
        (fracMul R mul zero (fracOf R mul zero a b) (fracOf R mul zero e f)) := by
  have hR := hdom.ring
  have hbR := (mem_nonzeroIn_iff.mp hb).left
  have hdR := (mem_nonzeroIn_iff.mp hd).left
  have hfR := (mem_nonzeroIn_iff.mp hf).left
  have hcf := mulAt_mem hR hc hfR
  have hed := mulAt_mem hR he hdR
  have hdf := mulAt_mem_nonzeroIn hdom hd hf
  have hac := mulAt_mem hR ha hc
  have hae := mulAt_mem hR ha he
  have hbd := mulAt_mem_nonzeroIn hdom hb hd
  have hbf := mulAt_mem_nonzeroIn hdom hb hf
  rw [fracAdd_fracOf hdom hcan hc hd he hf,
    fracMul_fracOf hdom hcan ha hb (addAt_mem hR hcf hed) hdf,
    fracMul_fracOf hdom hcan ha hb hc hd,
    fracMul_fracOf hdom hcan ha hb he hf,
    fracAdd_fracOf hdom hcan hac hbd hae hbf]
  -- scale the left by `b` so both sides sit over `(b*d)*(b*f)`
  rw [fracOf_scale hR hcan
    (mulAt_mem hR ha (addAt_mem hR hcf hed))
    (mulAt_mem_nonzeroIn hdom hb hdf) hb
    (mulAt_mem_nonzeroIn hdom (mulAt_mem_nonzeroIn hdom hb hdf) hb)]
  have hden : opAt mul (opAt mul b (opAt mul d f)) b
      = opAt mul (opAt mul b d) (opAt mul b f) :=
    calc opAt mul (opAt mul b (opAt mul d f)) b
        = opAt mul b (opAt mul (opAt mul d f) b) :=
          hR.mulAssoc b hbR _ (mulAt_mem hR hdR hfR) b hbR
      _ = opAt mul b (opAt mul b (opAt mul d f)) := by
          rw [hR.mulComm _ (mulAt_mem hR hdR hfR) b hbR]
      _ = opAt mul (opAt mul b b) (opAt mul d f) :=
          (hR.mulAssoc b hbR b hbR _ (mulAt_mem hR hdR hfR)).symm
      _ = opAt mul (opAt mul b d) (opAt mul b f) :=
          (ringMul_shuffle_pair hR hbR hdR hbR hfR).symm
  have hnum : opAt mul (opAt mul a (opAt add (opAt mul c f) (opAt mul e d))) b
      = opAt add (opAt mul (opAt mul a c) (opAt mul b f))
        (opAt mul (opAt mul a e) (opAt mul b d)) :=
    calc opAt mul (opAt mul a (opAt add (opAt mul c f) (opAt mul e d))) b
        = opAt mul (opAt add (opAt mul a (opAt mul c f))
            (opAt mul a (opAt mul e d))) b := by
          rw [hR.distrib a ha _ hcf _ hed]
      _ = opAt add (opAt mul (opAt mul a (opAt mul c f)) b)
            (opAt mul (opAt mul a (opAt mul e d)) b) :=
          ringRight_distrib hR (mulAt_mem hR ha hcf) (mulAt_mem hR ha hed) hbR
      _ = opAt add (opAt mul (opAt mul a c) (opAt mul b f))
            (opAt mul (opAt mul a e) (opAt mul b d)) := by
          rw [← hR.mulAssoc a ha c hc f hfR, ← hR.mulAssoc a ha e he d hdR,
            hR.mulAssoc _ hac f hfR b hbR, hR.mulAssoc _ hae d hdR b hbR,
            hR.mulComm f hfR b hbR, hR.mulComm d hdR b hbR]
  rw [hnum, hden]

/-! ## The structure

Every law above is stated on representatives; the interfaces are stated over
the graphs. Each field below is therefore the same three steps: destructure
the classes with `mem_FracField_iff`, rewrite the graph application with
`opAt_frac*Op`, and apply the representative law. -/

theorem isGroup_fracAdd {R add mul zero one : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero) :
    IsGroup (FracField R mul zero) (fracAddOp R add mul zero)
      (fracZero R mul zero one) where
  isFun := graphOn_isFunction _ _ _
  dom := graphOn_domain (fun _ hm => fracAdd_maps hdom hcan hm)
  ran := graphOn_range
  mem_e := fracZero_mem hdom
  assoc r hr s hs t ht := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_FracField_iff _).mp hr
    obtain ⟨c, hc, d, hd, rfl⟩ := (mem_FracField_iff _).mp hs
    obtain ⟨e, he, f, hf, rfl⟩ := (mem_FracField_iff _).mp ht
    rw [opAt_fracAddOp hdom hcan (fracOf_mem ha hb) (fracOf_mem hc hd),
      opAt_fracAddOp hdom hcan (fracAdd_mem hdom hcan
        (fracOf_mem ha hb) (fracOf_mem hc hd)) (fracOf_mem he hf),
      opAt_fracAddOp hdom hcan (fracOf_mem hc hd) (fracOf_mem he hf),
      opAt_fracAddOp hdom hcan (fracOf_mem ha hb)
        (fracAdd_mem hdom hcan (fracOf_mem hc hd) (fracOf_mem he hf))]
    exact fracAdd_assoc hdom hcan ha hb hc hd he hf
  left_id r hr := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_FracField_iff _).mp hr
    rw [opAt_fracAddOp hdom hcan (fracZero_mem hdom) (fracOf_mem ha hb),
      fracZero, fracAdd_comm hdom hcan hdom.ring.addGroup.mem_e
        (one_mem_nonzeroIn hdom) ha hb]
    exact fracAdd_fracZero hdom hcan ha hb
  right_id r hr := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_FracField_iff _).mp hr
    rw [opAt_fracAddOp hdom hcan (fracOf_mem ha hb) (fracZero_mem hdom)]
    exact fracAdd_fracZero hdom hcan ha hb
  inverses r hr := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_FracField_iff _).mp hr
    refine ⟨fracNeg R add mul zero (fracOf R mul zero a b),
      fracNeg_mem hdom.ring hcan (fracOf_mem ha hb), ?_, ?_⟩
    · rw [opAt_fracAddOp hdom hcan (fracOf_mem ha hb)
        (fracNeg_mem hdom.ring hcan (fracOf_mem ha hb))]
      exact fracAdd_fracNeg hdom hcan ha hb
    · rw [opAt_fracAddOp hdom hcan
        (fracNeg_mem hdom.ring hcan (fracOf_mem ha hb)) (fracOf_mem ha hb),
        fracNeg_fracOf hdom.ring hcan ha hb,
        fracAdd_comm hdom hcan (ringNeg_mem hdom.ring ha) hb ha hb,
        ← fracNeg_fracOf hdom.ring hcan ha hb]
      exact fracAdd_fracNeg hdom hcan ha hb

theorem isRing_frac {R add mul zero one : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero) :
    IsRing (FracField R mul zero) (fracAddOp R add mul zero)
      (fracMulOp R mul zero) (fracZero R mul zero one)
      (fracOne R mul zero one) where
  addGroup := isGroup_fracAdd hdom hcan
  addComm r hr s hs := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_FracField_iff _).mp hr
    obtain ⟨c, hc, d, hd, rfl⟩ := (mem_FracField_iff _).mp hs
    rw [opAt_fracAddOp hdom hcan (fracOf_mem ha hb) (fracOf_mem hc hd),
      opAt_fracAddOp hdom hcan (fracOf_mem hc hd) (fracOf_mem ha hb)]
    exact fracAdd_comm hdom hcan ha hb hc hd
  mulFun := graphOn_isFunction _ _ _
  mulDom := graphOn_domain (fun _ hm => fracMul_maps (one := one) hdom hcan hm)
  mulRan := graphOn_range
  mulAssoc r hr s hs t ht := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_FracField_iff _).mp hr
    obtain ⟨c, hc, d, hd, rfl⟩ := (mem_FracField_iff _).mp hs
    obtain ⟨e, he, f, hf, rfl⟩ := (mem_FracField_iff _).mp ht
    rw [opAt_fracMulOp (one := one) hdom hcan (fracOf_mem ha hb)
        (fracOf_mem hc hd),
      opAt_fracMulOp (one := one) hdom hcan (fracMul_mem hdom hcan
        (fracOf_mem ha hb) (fracOf_mem hc hd)) (fracOf_mem he hf),
      opAt_fracMulOp (one := one) hdom hcan (fracOf_mem hc hd)
        (fracOf_mem he hf),
      opAt_fracMulOp (one := one) hdom hcan (fracOf_mem ha hb)
        (fracMul_mem hdom hcan (fracOf_mem hc hd) (fracOf_mem he hf))]
    exact fracMul_assoc hdom hcan ha hb hc hd he hf
  mulComm r hr s hs := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_FracField_iff _).mp hr
    obtain ⟨c, hc, d, hd, rfl⟩ := (mem_FracField_iff _).mp hs
    rw [opAt_fracMulOp (one := one) hdom hcan (fracOf_mem ha hb)
        (fracOf_mem hc hd),
      opAt_fracMulOp (one := one) hdom hcan (fracOf_mem hc hd)
        (fracOf_mem ha hb)]
    exact fracMul_comm hdom hcan ha hb hc hd
  mem_one := fracOne_mem hdom
  mul_one r hr := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_FracField_iff _).mp hr
    rw [opAt_fracMulOp (one := one) hdom hcan (fracOf_mem ha hb)
      (fracOne_mem hdom)]
    exact fracMul_fracOne hdom hcan ha hb
  distrib r hr s hs t ht := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_FracField_iff _).mp hr
    obtain ⟨c, hc, d, hd, rfl⟩ := (mem_FracField_iff _).mp hs
    obtain ⟨e, he, f, hf, rfl⟩ := (mem_FracField_iff _).mp ht
    rw [opAt_fracAddOp hdom hcan (fracOf_mem hc hd) (fracOf_mem he hf),
      opAt_fracMulOp (one := one) hdom hcan (fracOf_mem ha hb)
        (fracAdd_mem hdom hcan (fracOf_mem hc hd) (fracOf_mem he hf)),
      opAt_fracMulOp (one := one) hdom hcan (fracOf_mem ha hb)
        (fracOf_mem hc hd),
      opAt_fracMulOp (one := one) hdom hcan (fracOf_mem ha hb)
        (fracOf_mem he hf),
      opAt_fracAddOp hdom hcan
        (fracMul_mem hdom hcan (fracOf_mem ha hb) (fracOf_mem hc hd))
        (fracMul_mem hdom hcan (fracOf_mem ha hb) (fracOf_mem he hf))]
    exact fracMul_add_distrib hdom hcan ha hb hc hd he hf

/-- The fractions over a cancellative integral domain form a field.
The inverse is the fraction turned over, and the hypothesis that a class is
nonzero yields its numerator's nonvanishing through an equivalence rather
than a decision, so nothing here branches. -/
theorem isField_frac {R add mul zero one : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero) :
    IsField (FracField R mul zero) (fracAddOp R add mul zero)
      (fracMulOp R mul zero) (fracZero R mul zero one)
      (fracOne R mul zero one) where
  ring := isRing_frac hdom hcan
  zero_ne_one := by
    intro he
    have hz := hdom.ring.addGroup.mem_e
    have hone := one_mem_nonzeroIn hdom
    rw [fracZero, fracOne] at he
    have hcross := (fracOf_eq_fracOf_iff hdom.ring hcan hz hone
      hdom.ring.mem_one hone).mp he
    rw [hdom.ring.mul_one zero hz,
      hdom.ring.mul_one one hdom.ring.mem_one] at hcross
    exact hdom.zero_ne_one hcross
  inverses r hr hne := by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_FracField_iff _).mp hr
    obtain ⟨haN, hinv⟩ := fracOf_mul_inv hdom hcan ha hb (by rwa [fracZero] at hne)
    refine ⟨fracOf R mul zero b a, fracOf_mem
      (mem_nonzeroIn_iff.mp hb).left haN, ?_⟩
    rw [opAt_fracMulOp (one := one) hdom hcan (fracOf_mem ha hb)
        (fracOf_mem (mem_nonzeroIn_iff.mp hb).left haN),
      fracMul_fracOf hdom hcan ha hb (mem_nonzeroIn_iff.mp hb).left haN,
      fracOne]
    exact hinv

/-! ## `Rat` is the fraction field of `Int`, up to isomorphism

`Rat` is built with a positive denominator and `FracField Int` with a
merely nonzero one, so they are not the same construction.
They are isomorphic, and the bridge is what lets generic fraction-field
results reach `Rat` without changing a statement everything downstream
rewrites with. -/

/-- The quotient by a prime ideal has the DISJUNCTIVE no-zero-divisor
property, which `isIntegralDomain_quotient_of_prime` computes and discards.

The negative form it returns (`mul_ne_zero`) cannot yield cancellation
constructively -- that step is double-negation elimination, as `Fraction.lean`
records above `IsCancellative`.  The disjunction can, through
`isCancellative_of_disjunctive`, and the prime ideal supplies it directly:
`IsPrimeIdeal`'s third clause IS this statement, one `cls_eq_zero_iff` away. -/
theorem disjunctive_quotient_of_prime {I R add mul zero one : ZFSet.{u}}
    (h : IsRing R add mul zero one) (hP : IsPrimeIdeal I R add mul zero one) :
    ∀ A, A ∈ quotientSet (idealRel R add zero I) R →
      ∀ B, B ∈ quotientSet (idealRel R add zero I) R →
      opAt (congOp (idealRel R add zero I) R mul) A B
          = cls (idealRel R add zero I) R zero →
      A = cls (idealRel R add zero I) R zero ∨
        B = cls (idealRel R add zero I) R zero := by
  have hI := hP.left
  intro A hA B hB hAB
  obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
  obtain ⟨b, hb, rfl⟩ := (mem_quotientSet_iff _ _ B).mp hB
  rw [opAt_congOp (fun x hx y hy => mulAt_mem h hx hy)
      (isCongruence_idealRel_mul h hI) ha hb,
    cls_eq_zero_iff h hI (mulAt_mem h ha hb)] at hAB
  rcases hP.right.right a ha b hb hAB with hmem | hmem
  · exact Or.inl ((cls_eq_zero_iff h hI ha).mpr hmem)
  · exact Or.inr ((cls_eq_zero_iff h hI hb).mpr hmem)

#print axioms disjunctive_quotient_of_prime


/-- The quotient by a prime ideal is CANCELLATIVE, which the domain form
cannot give: `isIntegralDomain_quotient_of_prime` returns the negative
`mul_ne_zero`, and crossing from that to cancellation is double-negation
elimination.  The disjunction crosses it, and the prime ideal supplies one. -/
theorem isCancellative_quotient_of_prime {I R add mul zero one : ZFSet.{u}}
    (h : IsRing R add mul zero one) (hP : IsPrimeIdeal I R add mul zero one) :
    IsCancellative (quotientSet (idealRel R add zero I) R)
      (congOp (idealRel R add zero I) R mul)
      (cls (idealRel R add zero I) R zero) :=
  isCancellative_of_disjunctive (isRing_quotientByIdeal h hP.left)
    (disjunctive_quotient_of_prime h hP)

#print axioms isCancellative_quotient_of_prime
theorem fracAdd_fracOf_same {R add mul zero one a c d : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (ha : a ∈ R) (hc : c ∈ R) (hd : d ∈ nonzeroIn R zero) :
    fracAdd R add mul zero (fracOf R mul zero a d) (fracOf R mul zero c d)
      = fracOf R mul zero (opAt add a c) d := by
  have hR := hdom.ring
  have hdR : d ∈ R := (mem_nonzeroIn_iff.mp hd).left
  rw [fracAdd_fracOf hdom hcan ha hd hc hd]
  refine (fracOf_eq_fracOf_iff hR hcan
    (addAt_mem hR (mulAt_mem hR ha hdR) (mulAt_mem hR hc hdR))
    (mulAt_mem_nonzeroIn hdom hd hd)
    (addAt_mem hR ha hc) hd).mpr ?_
  rw [ringRight_distrib hR (mulAt_mem hR ha hdR) (mulAt_mem hR hc hdR) hdR,
    hR.mulAssoc _ ha _ hdR _ hdR, hR.mulAssoc _ hc _ hdR _ hdR]
  exact (ringRight_distrib hR ha hc (mulAt_mem hR hdR hdR)).symm



/-- Clearing one denominator, over any domain. -/
theorem pb_clear_denom {R add mul zero one r : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (hr : r ∈ FracField R mul zero) :
    ∃ b, b ∈ nonzeroIn R zero ∧ ∃ a, a ∈ R ∧
      opAt (fracMulOp R mul zero) (fracOf R mul zero b one) r
        = fracOf R mul zero a one := by
  have hR := hdom.ring
  have hone := one_mem_nonzeroIn hdom
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_FracField_iff r).mp hr
  have hbR : b ∈ R := nonzeroIn_subset _ hb
  have honeR : one ∈ R := nonzeroIn_subset _ hone
  refine ⟨b, hb, a, ha, ?_⟩
  rw [opAt_fracMulOp hdom hcan (fracOf_mem hbR hone) (fracOf_mem ha hb),
      fracMul_fracOf hdom hcan hbR hone ha hb]
  refine (fracOf_eq_fracOf_iff hR hcan (mulAt_mem hR hbR ha)
    (mulAt_mem_nonzeroIn hdom hone hb) ha hone).mpr ?_
  rw [hR.mul_one _ (mulAt_mem hR hbR ha), hR.mulComm _ honeR _ hbR,
      hR.mul_one _ hbR, hR.mulComm _ hbR _ ha]

/-- The embedding is multiplicative: `b*c` over one is the product of the two. -/
theorem pb_embed_mul {R add mul zero one b c : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    (hb : b ∈ R) (hc : c ∈ R) :
    fracOf R mul zero (opAt mul b c) one
      = opAt (fracMulOp R mul zero) (fracOf R mul zero b one)
          (fracOf R mul zero c one) := by
  -- only DENOMINATORS must be non-zero; a numerator needs `R` alone, which is
  -- what lets this serve both the scalar and the numerator side below
  have hR := hdom.ring
  have hone := one_mem_nonzeroIn hdom
  have honeR : one ∈ R := nonzeroIn_subset _ hone
  rw [opAt_fracMulOp hdom hcan (fracOf_mem hb hone) (fracOf_mem hc hone),
      fracMul_fracOf hdom hcan hb hone hc hone, hR.mul_one _ honeR]

/-- A COMMON DENOMINATOR FOR FINITELY MANY FRACTIONS, OVER ANY DOMAIN.

`exists_common_denom` (in `Rational.lean`) is this for `Z ⊂ Q`; the argument is the same
bounded induction -- one more denominator at each step -- and uses nothing of
`Z`. Stated over `opAt (fracMulOp ..)` rather than `fracMul` so the FIELD's own
ring structure supplies associativity on abstract elements: `fracMul_assoc` is
stated over `fracOf` forms and cannot reach a `T i` that is not one. -/
theorem pb_common_denom {R add mul zero one : ZFSet.{u}}
    (hdom : IsIntegralDomain R add mul zero one)
    (hcan : IsCancellative R mul zero)
    {T : Nat → ZFSet.{u}} :
    ∀ d : Nat, (∀ i : Nat, i < d → T i ∈ FracField R mul zero) →
      ∃ b, b ∈ nonzeroIn R zero ∧
        ∀ i : Nat, i < d → ∃ a, a ∈ R ∧
          opAt (fracMulOp R mul zero) (fracOf R mul zero b one) (T i)
            = fracOf R mul zero a one := by
  have hR := hdom.ring
  have hone := one_mem_nonzeroIn hdom
  have hFF := (isField_frac hdom hcan).ring
  intro d
  induction d with
  | zero => exact fun _ => ⟨one, hone, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ k ih =>
      intro hmem
      obtain ⟨b, hb, hall⟩ := ih (fun i hi => hmem i (Nat.lt_succ_of_lt hi))
      obtain ⟨c, hc, a0, ha0, hca⟩ :=
        pb_clear_denom hdom hcan (hmem k (Nat.lt_succ_self k))
      -- annotate: `fracOf_mem`'s `mul` is not determined by its arguments
      have hbF : fracOf R mul zero b one ∈ FracField R mul zero :=
        fracOf_mem (nonzeroIn_subset _ hb) hone
      have hcF : fracOf R mul zero c one ∈ FracField R mul zero :=
        fracOf_mem (nonzeroIn_subset _ hc) hone
      refine ⟨opAt mul b c, mulAt_mem_nonzeroIn hdom hb hc, fun i hi => ?_⟩
      rcases Nat.lt_or_ge i k with hik | hik
      · obtain ⟨a, ha, hai⟩ := hall i hik
        refine ⟨opAt mul c a, mulAt_mem hR (nonzeroIn_subset _ hc) ha, ?_⟩
        rw [pb_embed_mul hdom hcan (nonzeroIn_subset _ hb) (nonzeroIn_subset _ hc),
            hFF.mulComm _ hbF _ hcF,
            hFF.mulAssoc _ hcF _ hbF _ (hmem i (Nat.lt_succ_of_lt hik)), hai,
            ← pb_embed_mul hdom hcan (nonzeroIn_subset _ hc) ha]
      · have hik' : i = k := Nat.le_antisymm (Nat.lt_succ_iff.mp hi) hik
        subst hik'
        refine ⟨opAt mul b a0, mulAt_mem hR (nonzeroIn_subset _ hb) ha0, ?_⟩
        rw [pb_embed_mul hdom hcan (nonzeroIn_subset _ hb) (nonzeroIn_subset _ hc),
            hFF.mulAssoc _ hbF _ hcF _ (hmem i (Nat.lt_succ_self i)), hca,
            ← pb_embed_mul hdom hcan (nonzeroIn_subset _ hb) ha0]

/-- THE EMBEDDING'S PREIMAGE, AS A TERM -- the generic `intOfRat`.

`intOfRat` (in `Rational.lean`) is this for `Z ⊂ Q`, and its docstring already names the
technique: a definite description via `theOnly`. The same argument works over
any domain, because `a ↦ a/1` is INJECTIVE and so the preimage, where it exists,
is unique -- the separation is a singleton and `sUnion` opens it.

This is the third time today the tower's answer to *turn `∀i, ∃a, P i a` into a
FUNCTION* has been a definite description rather than a choice: `polyQuotBy` for
the exact quotient, `intOfRat` here, and `theOnly` itself underneath both. In a
SET-THEORETIC development that move is free; reaching for a recursion or for
choice is the type-theorist's instinct and the expensive one. -/
noncomputable def fracPre (R mul zero one x : ZFSet.{u}) : ZFSet.{u} :=
  theOnly (fun a => x = fracOf R mul zero a one) R

end NumberTheory


#print axioms NumberTheory.isIntegralDomain_of_cancellative
#print axioms NumberTheory.intZero_ne_intOne
#print axioms NumberTheory.isCancellative_of_isField
#print axioms NumberTheory.mem_fracRel_iff
#print axioms NumberTheory.fracRel_isEquivRel
#print axioms NumberTheory.fracOf_mem
#print axioms NumberTheory.fracOf_eq_fracOf_iff
#print axioms NumberTheory.mulAt_mem_nonzeroIn
#print axioms NumberTheory.fracOf_mul_congr
#print axioms NumberTheory.fracOf_add_congr
#print axioms NumberTheory.one_mem_nonzeroIn
#print axioms NumberTheory.fracOf_eq_zero_iff
#print axioms NumberTheory.fracOf_mul_inv
#print axioms NumberTheory.mem_FracField_iff
#print axioms NumberTheory.mem_fracOf_iff
#print axioms NumberTheory.fracMul_fracOf
#print axioms NumberTheory.fracAdd_fracOf
#print axioms NumberTheory.fracMul_mem
#print axioms NumberTheory.fracAdd_mem
#print axioms NumberTheory.opAt_fracAddOp
#print axioms NumberTheory.opAt_fracMulOp
#print axioms NumberTheory.fracOf_neg_congr
#print axioms NumberTheory.fracNeg_fracOf
#print axioms NumberTheory.fracNeg_mem
#print axioms NumberTheory.fracZero_mem
#print axioms NumberTheory.fracOne_mem
#print axioms NumberTheory.fracAdd_fracZero
#print axioms NumberTheory.fracAdd_fracNeg
#print axioms NumberTheory.fracMul_fracOne
#print axioms NumberTheory.fracMul_comm
#print axioms NumberTheory.fracAdd_comm
#print axioms NumberTheory.fracMul_assoc
#print axioms NumberTheory.fracAdd_assoc
#print axioms NumberTheory.fracOf_scale
#print axioms NumberTheory.fracMul_add_distrib
#print axioms NumberTheory.isGroup_fracAdd
#print axioms NumberTheory.isRing_frac
#print axioms NumberTheory.isField_frac
#print axioms NumberTheory.pb_clear_denom
#print axioms NumberTheory.pb_embed_mul
#print axioms NumberTheory.pb_common_denom
#print axioms NumberTheory.fracPre
#print axioms NumberTheory.fracAdd_fracOf_same

namespace ZFSet
export NumberTheory (FracField IsCancellative IsIntegralDomain disjunctive_quotient_of_prime fracAdd fracAddOp fracAdd_assoc fracAdd_comm fracAdd_fracNeg fracAdd_fracOf fracAdd_fracOf_same fracAdd_fracZero fracAdd_mem fracMul fracMulOp fracMul_add_distrib fracMul_assoc fracMul_comm fracMul_fracOf fracMul_fracOne fracMul_mem fracNeg fracNeg_fracOf fracNeg_mem fracOf fracOf_add_congr fracOf_eq_fracOf_iff fracOf_eq_zero_iff fracOf_mem fracOf_mul_congr fracOf_mul_inv fracOf_neg_congr fracOf_scale fracOf_subset fracOne fracOne_mem fracPairs fracPre fracRel fracRel_isEquivRel fracZero fracZero_mem intZero_ne_intOne isCancellative_of_disjunctive isCancellative_of_isField isCancellative_quotient_of_prime isField_frac isGroup_fracAdd isIntegralDomain_of_cancellative isIntegralDomain_quotient_of_prime isRing_frac mem_FracField_iff mem_fracOf_iff mem_fracPairs_iff mem_fracRel_iff mem_nonzeroIn_iff mulAt_mem_nonzeroIn nonzeroIn nonzeroIn_subset one_mem_nonzeroIn opAt_fracAddOp opAt_fracMulOp pb_clear_denom pb_common_denom pb_embed_mul)
end ZFSet
