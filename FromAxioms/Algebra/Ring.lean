/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Rings, ideals, and their homomorphisms.

A ring is an abelian group with a second set function on it. `IsRing` carries
`mulComm`, so everything here is about COMMUTATIVE rings: calculating in one,
quotienting by an ideal, subrings, homomorphisms and the first isomorphism
theorem. `Field.lean` builds on it with the fields themselves and with `ℚ` and
`ℤ/nℤ` as the running examples.

Every ring here is commutative. Whether commutativity should be split off
into a mixin or kept as the scope of this development is open.
-/

import FromAxioms.Algebra.FinProd
import FromAxioms.NumberTheory.Prime

universe u

open NumberTheory SetTheory
namespace Algebra

/-- A ring with unit, NOT assumed commutative. `IsRing` below is the
commutative one, so the base arrives beside it rather than replacing it.
A theorem generalises by
changing its hypothesis from `IsRing` to `IsRingNC`, and its callers by writing
`hR.toNC` --- one theorem at a time, each move a real widening rather than a
rename.

TWO AXIOMS ARE NEW HERE, and they are exactly what commutativity was supplying
for free: `one_mul` beside `mul_one`, and `distribRight` beside the left
distributivity `IsRing` calls `distrib`. That is the whole content of the
split. -/
structure IsRingNC (R add mul zero one : ZFSet.{u}) : Prop where
  addGroup : IsGroup R add zero
  addComm : IsAbelian R add
  mulFun : IsFunction mul
  mulDom : domain mul = prod R R
  mulRan : range mul ⊆ R
  mulAssoc : ∀ a, a ∈ R → ∀ b, b ∈ R → ∀ c, c ∈ R →
    opAt mul (opAt mul a b) c = opAt mul a (opAt mul b c)
  mem_one : one ∈ R
  mul_one : ∀ a, a ∈ R → opAt mul a one = a
  one_mul : ∀ a, a ∈ R → opAt mul one a = a
  distrib : ∀ a, a ∈ R → ∀ b, b ∈ R → ∀ c, c ∈ R →
    opAt mul a (opAt add b c) = opAt add (opAt mul a b) (opAt mul a c)
  distribRight : ∀ a, a ∈ R → ∀ b, b ∈ R → ∀ c, c ∈ R →
    opAt mul (opAt add a b) c = opAt add (opAt mul a c) (opAt mul b c)

/-- A commutative ring with unit, over set functions. -/
structure IsRing (R add mul zero one : ZFSet.{u}) : Prop where
  addGroup : IsGroup R add zero
  addComm : IsAbelian R add
  mulFun : IsFunction mul
  mulDom : domain mul = prod R R
  mulRan : range mul ⊆ R
  mulAssoc : ∀ a, a ∈ R → ∀ b, b ∈ R → ∀ c, c ∈ R →
    opAt mul (opAt mul a b) c = opAt mul a (opAt mul b c)
  mulComm : ∀ a, a ∈ R → ∀ b, b ∈ R → opAt mul a b = opAt mul b a
  mem_one : one ∈ R
  mul_one : ∀ a, a ∈ R → opAt mul a one = a
  distrib : ∀ a, a ∈ R → ∀ b, b ∈ R → ∀ c, c ∈ R →
    opAt mul a (opAt add b c) = opAt add (opAt mul a b) (opAt mul a c)


/-- Every commutative ring is a ring, which is the direction that makes
`IsRingNC` usable: a theorem generalised onto the base is still available to
every existing caller, who writes `hR.toNC`.

The two derivations are the split's whole content. `one_mul` is `mul_one` read
through commutativity, and `distribRight` is the left distributivity with three
commutations around it. Nothing else in `IsRing` changes meaning. -/
theorem IsRing.toNC {R add mul zero one : ZFSet.{u}}
    (h : IsRing R add mul zero one) : IsRingNC R add mul zero one where
  addGroup := h.addGroup
  addComm := h.addComm
  mulFun := h.mulFun
  mulDom := h.mulDom
  mulRan := h.mulRan
  mulAssoc := h.mulAssoc
  mem_one := h.mem_one
  mul_one := h.mul_one
  one_mul := fun a ha => by
    rw [h.mulComm _ h.mem_one _ ha]; exact h.mul_one _ ha
  distrib := h.distrib
  distribRight := fun a ha b hb c hc => by
    rw [h.mulComm _ (opAt_mem h.addGroup ha hb) _ hc, h.distrib _ hc _ ha _ hb,
      h.mulComm _ hc _ ha, h.mulComm _ hc _ hb]

#print axioms Algebra.IsRing.toNC
#print axioms IsRing

/-- Multiplication lands in the ring, over the non-commutative base.

`mulAt_mem` reads only `mulFun`, `mulDom` and `mulRan`, which `IsRingNC` has
verbatim, so this is the same proof at a weaker hypothesis. -/
theorem mulAt_mem_nc {R add mul zero one a b : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) :
    opAt mul a b ∈ R :=
  h.mulRan _ (app_mem_range h.mulFun (by rw [h.mulDom]; exact opair_mem_prod ha hb))

/-- `a · 0 = 0` without commutativity.

`a·0 = a·(0+0) = a·0 + a·0`, then cancel in the additive group. Only LEFT
distributivity is spent, which `IsRingNC` calls `distrib` exactly as `IsRing`
does. -/
theorem mul_zero_of_isRingNC {R add mul zero one a : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) :
    opAt mul a zero = zero := by
  have hz := h.addGroup.mem_e
  have hstep : opAt mul a zero = opAt add (opAt mul a zero) (opAt mul a zero) := by
    have hd := h.distrib a ha zero hz zero hz
    rwa [h.addGroup.left_id zero hz] at hd
  obtain ⟨b, hb, hab, hba⟩ := h.addGroup.inverses _ (mulAt_mem_nc h ha hz)
  have hcancel : opAt add b (opAt mul a zero)
      = opAt add b (opAt add (opAt mul a zero) (opAt mul a zero)) := by rw [← hstep]
  rw [hba, ← h.addGroup.assoc b hb _ (mulAt_mem_nc h ha hz) _ (mulAt_mem_nc h ha hz),
    hba, h.addGroup.left_id _ (mulAt_mem_nc h ha hz)] at hcancel
  exact hcancel.symm

/-- `0 · a = 0` without commutativity, and this one is a REAL widening
rather than the same proof at a weaker hypothesis.

`ringZero_mul` gets this from `mul_zero_of_isRing` by commuting the product,
which is unavailable here. The mirror argument uses RIGHT distributivity:
`0·a = (0+0)·a = 0·a + 0·a`, then the same cancellation. `distribRight` is one
of the two axioms the split adds, and this is its use. -/
theorem zero_mul_of_isRingNC {R add mul zero one a : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) :
    opAt mul zero a = zero := by
  have hz := h.addGroup.mem_e
  have hstep : opAt mul zero a = opAt add (opAt mul zero a) (opAt mul zero a) := by
    have hd := h.distribRight zero hz zero hz a ha
    rwa [h.addGroup.left_id zero hz] at hd
  obtain ⟨b, hb, hab, hba⟩ := h.addGroup.inverses _ (mulAt_mem_nc h hz ha)
  have hcancel : opAt add b (opAt mul zero a)
      = opAt add b (opAt add (opAt mul zero a) (opAt mul zero a)) := by rw [← hstep]
  rw [hba, ← h.addGroup.assoc b hb _ (mulAt_mem_nc h hz ha) _ (mulAt_mem_nc h hz ha),
    hba, h.addGroup.left_id _ (mulAt_mem_nc h hz ha)] at hcancel
  exact hcancel.symm

/-- A semiring, which is what a module's scalars are actually required
to be.

`IsRingNC` dropped `mulComm` from `IsRing`; this drops ADDITIVE INVERSES as
well. The additive part is a commutative monoid rather than an abelian group,
so `IsCommMonoid R add zero` replaces `addGroup` and `addComm` together.

`zeroMul` AND `mulZero` ARE AXIOMS HERE, AND THAT IS NOT AN OVERSIGHT. In a
ring they are theorems -- `zero_mul_of_isRingNC` proves `0·a = 0` from
`(0+0)·a = 0·a + 0·a` and CANCELLING, which needs the additive inverse. A
semiring has no inverse to cancel with, so the absorption has to be assumed.
Deriving it from the other fields is an error rather than a simplification.

Every `IsRingNC` is an `IsSemiring` -- see `IsRingNC.toSemiring`. -/
structure IsSemiring (R add mul zero one : ZFSet.{u}) : Prop where
  addMonoid : IsCommMonoid R add zero
  mulFun : IsFunction mul
  mulDom : domain mul = prod R R
  mulRan : range mul ⊆ R
  mulAssoc : ∀ a, a ∈ R → ∀ b, b ∈ R → ∀ c, c ∈ R →
    opAt mul (opAt mul a b) c = opAt mul a (opAt mul b c)
  mem_one : one ∈ R
  mul_one : ∀ a, a ∈ R → opAt mul a one = a
  one_mul : ∀ a, a ∈ R → opAt mul one a = a
  zeroMul : ∀ a, a ∈ R → opAt mul zero a = zero
  mulZero : ∀ a, a ∈ R → opAt mul a zero = zero
  distrib : ∀ a, a ∈ R → ∀ b, b ∈ R → ∀ c, c ∈ R →
    opAt mul a (opAt add b c) = opAt add (opAt mul a b) (opAt mul a c)
  distribRight : ∀ a, a ∈ R → ∀ b, b ∈ R → ∀ c, c ∈ R →
    opAt mul (opAt add a b) c = opAt add (opAt mul a c) (opAt mul b c)

/-- Every non-commutative ring is a semiring, so `IsSemiring` is a
WIDENING rather than a second notion standing beside the first.

The additive group becomes a commutative monoid by `isCommMonoid_of_isGroup`,
and the two absorption axioms -- which a semiring must assume -- are here the
theorems `zero_mul_of_isRingNC` and `mul_zero_of_isRingNC`, proved by
cancelling, which a semiring cannot do, so this direction is the only one that
goes through. -/
theorem IsRingNC.toSemiring {R add mul zero one : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) : IsSemiring R add mul zero one where
  addMonoid := isCommMonoid_of_isGroup h.addGroup h.addComm
  mulFun := h.mulFun
  mulDom := h.mulDom
  mulRan := h.mulRan
  mulAssoc := h.mulAssoc
  mem_one := h.mem_one
  mul_one := h.mul_one
  one_mul := h.one_mul
  zeroMul := fun a ha => zero_mul_of_isRingNC h ha
  mulZero := fun a ha => mul_zero_of_isRingNC h ha
  distrib := h.distrib
  distribRight := h.distribRight

#print axioms Algebra.IsSemiring
#print axioms Algebra.IsRingNC.toSemiring

/-- Multiplication stays in the carrier, over a semiring. The three
function clauses `IsSemiring` shares with `IsRingNC` are all this needs, so it
is `mulAt_mem_nc`'s proof verbatim at the weaker hypothesis. -/
theorem mulAt_mem_semi {R add mul zero one a b : ZFSet.{u}}
    (h : IsSemiring R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) :
    opAt mul a b ∈ R :=
  h.mulRan _ (app_mem_range h.mulFun (by rw [h.mulDom]; exact opair_mem_prod ha hb))

/-- Addition stays in the carrier, over a semiring -- closure of the
additive COMMUTATIVE MONOID, which is all a semiring's addition is. -/
theorem addAt_mem_semi {R add mul zero one a b : ZFSet.{u}}
    (h : IsSemiring R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) :
    opAt add a b ∈ R :=
  h.addMonoid.ran _ (app_mem_range h.addMonoid.isFun
    (by rw [h.addMonoid.dom]; exact opair_mem_prod ha hb))

#print axioms Algebra.mulAt_mem_semi
#print axioms Algebra.addAt_mem_semi


/-- `1 · a = a` without commutativity -- an AXIOM of `IsRingNC` rather
than a theorem. `ringOne_mul` derives it by commuting `mul_one`, which is
exactly the derivation `IsRing.toNC` performs once so that everything past
this point can simply ask for it. -/
theorem ringOne_mul_nc {R add mul zero one a : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) :
    opAt mul one a = a := h.one_mul a ha

/-- `(a + b)·c = a·c + b·c` without commutativity -- likewise an axiom
here. `ringRight_distrib` gets it from the left law with three commutations;
`distribRight` is the other half of what the split adds. -/
theorem ringRight_distrib_nc {R add mul zero one a b c : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) :
    opAt mul (opAt add a b) c = opAt add (opAt mul a c) (opAt mul b c) :=
  h.distribRight a ha b hb c hc

#print axioms Algebra.mulAt_mem_nc
#print axioms Algebra.mul_zero_of_isRingNC
#print axioms Algebra.zero_mul_of_isRingNC

/-! ### The additive helpers on the non-commutative base

`IsRingNC` keeps `addGroup` and `addComm` verbatim -- the split drops
MULTIPLICATIVE commutativity only -- so each of these is its commutative
twin's proof unchanged. They are migrated first because they block the most:
`addAt_mem` alone stands under 31 further lemmas, and the additive family
together under about ninety. -/

theorem addAt_mem_nc {R add mul zero one a b : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) :
    opAt add a b ∈ R := opAt_mem h.addGroup ha hb

theorem ringAdd_zero_nc {R add mul zero one a : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) :
    opAt add a zero = a := h.addGroup.right_id a ha

theorem ringZero_add_nc {R add mul zero one a : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) :
    opAt add zero a = a := h.addGroup.left_id a ha

theorem ringAdd_comm_nc {R add mul zero one a b : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) :
    opAt add a b = opAt add b a := h.addComm a ha b hb

theorem ringAdd_assoc_nc {R add mul zero one a b c : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) :
    opAt add (opAt add a b) c = opAt add a (opAt add b c) :=
  h.addGroup.assoc a ha b hb c hc

#print axioms Algebra.addAt_mem_nc
#print axioms Algebra.ringAdd_zero_nc
#print axioms Algebra.ringZero_add_nc
#print axioms Algebra.ringAdd_comm_nc
#print axioms Algebra.ringAdd_assoc_nc
#print axioms Algebra.ringOne_mul_nc
#print axioms Algebra.ringRight_distrib_nc

/-- A field: a ring where every element other than `zero` has an inverse. -/
structure IsField (R add mul zero one : ZFSet.{u}) : Prop where
  ring : IsRing R add mul zero one
  zero_ne_one : zero ≠ one
  inverses : ∀ a, a ∈ R → a ≠ zero → ∃ b, b ∈ R ∧ opAt mul a b = one

theorem mulAt_mem {R add mul zero one a b : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) : opAt mul a b ∈ R :=
  mulAt_mem_nc h.toNC ha hb

/-! ## Ideals, and ℤ

The third word of the 1871 row. `nℤ` is the image of multiplication by `n`,
which is how it inherits closure -- the same move `Group.lean` makes for the
even integers. -/

def IsIdeal (I R add mul zero : ZFSet.{u}) : Prop :=
  I ⊆ R ∧ zero ∈ I ∧ (∀ a, a ∈ I → ∀ b, b ∈ I → opAt add a b ∈ I) ∧
    (∀ a, a ∈ I → ∃ b, b ∈ I ∧ opAt add a b = zero) ∧
    (∀ r, r ∈ R → ∀ a, a ∈ I → opAt mul r a ∈ I)

theorem ideal_subset {I R add mul zero : ZFSet.{u}} (hI : IsIdeal I R add mul zero) :
    I ⊆ R := hI.left

theorem ideal_mem_zero {I R add mul zero : ZFSet.{u}} (hI : IsIdeal I R add mul zero) :
    zero ∈ I := hI.right.left

theorem ideal_add {I R add mul zero a b : ZFSet.{u}} (hI : IsIdeal I R add mul zero)
    (ha : a ∈ I) (hb : b ∈ I) : opAt add a b ∈ I := hI.right.right.left a ha b hb

theorem ideal_inverse {I R add mul zero a : ZFSet.{u}} (hI : IsIdeal I R add mul zero)
    (ha : a ∈ I) : ∃ b, b ∈ I ∧ opAt add a b = zero := hI.right.right.right.left a ha

/-- An ideal absorbs multiplication by anything in the ring. -/
theorem ideal_absorbs {I R add mul zero r a : ZFSet.{u}} (hI : IsIdeal I R add mul zero)
    (hr : r ∈ R) (ha : a ∈ I) : opAt mul r a ∈ I := hI.right.right.right.right r hr a ha


theorem mul_zero_of_isRing {R add mul zero one a : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (ha : a ∈ R) : opAt mul a zero = zero :=
  mul_zero_of_isRingNC hR.toNC ha

def units (R mul zero : ZFSet.{u}) : ZFSet.{u} := R \ singleton zero

/-! ## Quotient rings

A relation that is a congruence for both operations gives a ring on the
classes. The additive half is `isGroup_congQuotient`; the multiplicative half
is the same `congOp`, so `congOp_isFunction` was stated for a closed operation
rather than a group's. -/

theorem isRing_congQuotient {r R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hadd : IsCongruence r R add)
    (hmul : IsCongruence r R mul) :
    IsRing (quotientSet r R) (congOp r R add) (congOp r R mul)
      (cls r R zero) (cls r R one) where
  addGroup := isGroup_congQuotient hR.addGroup hadd
  addComm A hA B hB := by
    obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
    obtain ⟨b, hb, rfl⟩ := (mem_quotientSet_iff _ _ B).mp hB
    rw [opAt_congOp (fun a ha b hb => opAt_mem hR.addGroup ha hb) hadd ha hb,
      opAt_congOp (fun a ha b hb => opAt_mem hR.addGroup ha hb) hadd hb ha,
      hR.addComm a ha b hb]
  mulFun := congOp_isFunction (fun a ha b hb => mulAt_mem hR ha hb) hmul
  mulDom := congOp_domain (fun a ha b hb => mulAt_mem hR ha hb)
  mulRan := congOp_range
  mulAssoc A hA B hB C hC := by
    obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
    obtain ⟨b, hb, rfl⟩ := (mem_quotientSet_iff _ _ B).mp hB
    obtain ⟨c, hc, rfl⟩ := (mem_quotientSet_iff _ _ C).mp hC
    have hcl := fun a (ha : a ∈ R) b (hb : b ∈ R) => mulAt_mem hR ha hb
    rw [opAt_congOp hcl hmul ha hb, opAt_congOp hcl hmul (mulAt_mem hR ha hb) hc,
      opAt_congOp hcl hmul hb hc, opAt_congOp hcl hmul ha (mulAt_mem hR hb hc),
      hR.mulAssoc a ha b hb c hc]
  mulComm A hA B hB := by
    obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
    obtain ⟨b, hb, rfl⟩ := (mem_quotientSet_iff _ _ B).mp hB
    have hcl := fun a (ha : a ∈ R) b (hb : b ∈ R) => mulAt_mem hR ha hb
    rw [opAt_congOp hcl hmul ha hb, opAt_congOp hcl hmul hb ha, hR.mulComm a ha b hb]
  mem_one := cls_mem_quotientSet hR.mem_one
  mul_one A hA := by
    obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
    rw [opAt_congOp (fun a ha b hb => mulAt_mem hR ha hb) hmul ha hR.mem_one,
      hR.mul_one a ha]
  distrib A hA B hB C hC := by
    obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
    obtain ⟨b, hb, rfl⟩ := (mem_quotientSet_iff _ _ B).mp hB
    obtain ⟨c, hc, rfl⟩ := (mem_quotientSet_iff _ _ C).mp hC
    have hclm := fun a (ha : a ∈ R) b (hb : b ∈ R) => mulAt_mem hR ha hb
    have hcla := fun a (ha : a ∈ R) b (hb : b ∈ R) => opAt_mem hR.addGroup ha hb
    rw [opAt_congOp hcla hadd hb hc, opAt_congOp hclm hmul ha (hcla b hb c hc),
      opAt_congOp hclm hmul ha hb, opAt_congOp hclm hmul ha hc,
      opAt_congOp hcla hadd (hclm a ha b hb) (hclm a ha c hc), hR.distrib a ha b hb c hc]

/-! ## Calculating in a ring

The structure gives associativity, commutativity, a unit and one distributive
law; everything else a calculation needs has to be derived, and without a `ring`
tactic each step is a rewrite. These are the steps. -/

theorem addAt_mem {R add mul zero one a b : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) : opAt add a b ∈ R :=
  addAt_mem_nc h.toNC ha hb

theorem ringAdd_assoc {R add mul zero one a b c : ZFSet.{u}}
    (h : IsRing R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) :
    opAt add (opAt add a b) c = opAt add a (opAt add b c) :=
  ringAdd_assoc_nc h.toNC ha hb hc

theorem ringAdd_comm {R add mul zero one a b : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) : opAt add a b = opAt add b a :=
  ringAdd_comm_nc h.toNC ha hb

theorem ringAdd_zero {R add mul zero one a : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) : opAt add a zero = a :=
  ringAdd_zero_nc h.toNC ha

theorem ringZero_add {R add mul zero one a : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) : opAt add zero a = a :=
  ringZero_add_nc h.toNC ha

theorem ringAdd_left_comm {R add mul zero one a b c : ZFSet.{u}}
    (h : IsRing R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) :
    opAt add a (opAt add b c) = opAt add b (opAt add a c) := by
  rw [← ringAdd_assoc h ha hb hc, ringAdd_comm h ha hb, ringAdd_assoc h hb ha hc]

theorem ringZero_mul {R add mul zero one a : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) : opAt mul zero a = zero := by
  exact zero_mul_of_isRingNC h.toNC ha

theorem ringOne_mul {R add mul zero one a : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) : opAt mul one a = a :=
  ringOne_mul_nc h.toNC ha

theorem ringRight_distrib {R add mul zero one a b c : ZFSet.{u}}
    (h : IsRing R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) :
    opAt mul (opAt add a b) c = opAt add (opAt mul a c) (opAt mul b c) :=
  ringRight_distrib_nc h.toNC ha hb hc

/-- Additive inverse. -/
def ringNeg (R add zero a : ZFSet.{u}) : ZFSet.{u} := ginv R add zero a

/-- Negation lands in the ring, over the non-commutative base. Additive only,
so `addGroup` carries it unchanged. -/
theorem ringNeg_mem_nc {R add mul zero one a : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) :
    ringNeg R add zero a ∈ R := ginv_mem h.addGroup ha

/-- `-a + a = 0`, over the non-commutative base. -/
theorem ringNeg_add_nc {R add mul zero one a : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) :
    opAt add (ringNeg R add zero a) a = zero := opAt_ginv h.addGroup ha

/-- `a + -a = 0`, over the non-commutative base. ADDITIVE commutativity is
still available -- `IsRingNC` keeps `addComm`; it is only the MULTIPLICATIVE
`mulComm` that the split drops. -/
theorem ringAdd_neg_nc {R add mul zero one a : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) :
    opAt add a (ringNeg R add zero a) = zero := by
  rw [h.addComm _ ha _ (ringNeg_mem_nc h ha)]
  exact ringNeg_add_nc h ha

/-- `a·(-b) = -(a·b)` without commutativity. The original proof already
avoided `mulComm`: `a·b + a·(-b) = a·(b + -b) = a·0 = 0` identifies `a·(-b)`
as the additive inverse. Only LEFT distributivity is spent. -/
theorem ringMul_neg_nc {R add mul zero one a b : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) :
    opAt mul a (ringNeg R add zero b) = ringNeg R add zero (opAt mul a b) := by
  refine inv_unique h.addGroup (mulAt_mem_nc h ha hb)
    (mulAt_mem_nc h ha (ringNeg_mem_nc h hb))
    (ringNeg_mem_nc h (mulAt_mem_nc h ha hb)) ?_
    (ringNeg_add_nc h (mulAt_mem_nc h ha hb))
  rw [← h.distrib a ha b hb _ (ringNeg_mem_nc h hb), ringAdd_neg_nc h hb,
    mul_zero_of_isRingNC h ha]

/-- `(-a)·b = -(a·b)` without commutativity, and this is the REAL widening
of the four above.

`ringNeg_mul` reaches this by commuting into `ringMul_neg`, which the
non-commutative base cannot do. The mirror argument runs on the other side:
`a·b + (-a)·b = (a + -a)·b = 0·b = 0`, so `(-a)·b` is the additive inverse of
`a·b`. It spends `distribRight` and `zero_mul_of_isRingNC` -- the axiom the
split adds and the lemma it makes provable. The commutative development
got this for free; the non-commutative one has to earn it. -/
theorem ringNeg_mul_nc {R add mul zero one a b : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) :
    opAt mul (ringNeg R add zero a) b = ringNeg R add zero (opAt mul a b) := by
  refine inv_unique h.addGroup (mulAt_mem_nc h ha hb)
    (mulAt_mem_nc h (ringNeg_mem_nc h ha) hb)
    (ringNeg_mem_nc h (mulAt_mem_nc h ha hb)) ?_
    (ringNeg_add_nc h (mulAt_mem_nc h ha hb))
  rw [← h.distribRight a ha _ (ringNeg_mem_nc h ha) b hb, ringAdd_neg_nc h ha,
    zero_mul_of_isRingNC h hb]

#print axioms Algebra.ringNeg_mem_nc
#print axioms Algebra.ringNeg_add_nc
#print axioms Algebra.ringAdd_neg_nc
#print axioms Algebra.ringMul_neg_nc
#print axioms Algebra.ringNeg_mul_nc

/-- `(-1)·a = -a` without commutativity.

`ringNegOne_mul` commutes into `ringMul_neg`; here the mirror lemma
`ringNeg_mul_nc` applies on the correct side already, and `one_mul` -- an
axiom of `IsRingNC` rather than a derived fact -- finishes it. -/
theorem ringNegOne_mul_nc {R add mul zero one a : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) :
    opAt mul (ringNeg R add zero one) a = ringNeg R add zero a := by
  rw [ringNeg_mul_nc h h.mem_one ha, h.one_mul _ ha]

#print axioms Algebra.ringNegOne_mul_nc

theorem ringNeg_mem {R add mul zero one a : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) : ringNeg R add zero a ∈ R :=
  ringNeg_mem_nc h.toNC ha

theorem ringNeg_add {R add mul zero one a : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) : opAt add (ringNeg R add zero a) a = zero :=
  ringNeg_add_nc h.toNC ha

theorem ringAdd_neg {R add mul zero one a : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) : opAt add a (ringNeg R add zero a) = zero :=
  ringAdd_neg_nc h.toNC ha


/-- Subtraction detects equality: `x - a = 0` exactly when `x = a`. -/
theorem ringSub_eq_zero_iff {R add mul zero one x a : ZFSet.{u}}
    (h : IsRing R add mul zero one) (hx : x ∈ R) (ha : a ∈ R) :
    opAt add x (ringNeg R add zero a) = zero ↔ x = a := by
  constructor
  · intro he
    have he' : opAt add (ringNeg R add zero a) x = zero := by
      rw [ringAdd_comm h (ringNeg_mem h ha) hx]
      exact he
    exact inv_unique h.addGroup (ringNeg_mem h ha) hx ha he' (ringAdd_neg h ha)
  · intro he
    rw [he]
    exact ringAdd_neg h ha

/-- A field has no zero divisors. -/
theorem field_mul_eq_zero {R add mul zero one u v : ZFSet.{u}}
    (hF : IsField R add mul zero one) (hu : u ∈ R) (hv : v ∈ R)
    (he : opAt mul u v = zero) (hune : u ≠ zero) : v = zero := by
  have h := hF.ring
  obtain ⟨w, hw, huw⟩ := hF.inverses u hu hune
  have hstep : opAt mul w (opAt mul u v) = v := by
    rw [← h.mulAssoc w hw u hu v hv, h.mulComm w hw u hu, huw, ringOne_mul h hv]
  rw [he, mul_zero_of_isRing h hw] at hstep
  exact hstep.symm

/-! ## Subtraction, and the identities a quotient needs

`ringAdd_shuffle_pair` is the INTERCHANGE law -- `Located.lean` states
the same statement as `realLAdd_interchange`, and a reader who knows it
by that word finds nothing here without this line. -/

theorem ringAdd_shuffle_pair {R add mul zero one a b c d : ZFSet.{u}}
    (h : IsRing R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) (hd : d ∈ R) :
    opAt add (opAt add a b) (opAt add c d)
      = opAt add (opAt add a c) (opAt add b d) := by
  rw [ringAdd_assoc h ha hb (addAt_mem h hc hd), ← ringAdd_assoc h hb hc hd,
    ringAdd_comm h hb hc, ringAdd_assoc h hc hb hd,
    ← ringAdd_assoc h ha hc (addAt_mem h hb hd)]

theorem ringNeg_neg {R add mul zero one a : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) : ringNeg R add zero (ringNeg R add zero a) = a :=
  ginv_ginv h.addGroup ha

theorem ringNeg_addAt {R add mul zero one a b : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) :
    ringNeg R add zero (opAt add a b)
      = opAt add (ringNeg R add zero a) (ringNeg R add zero b) := by
  have hna := ringNeg_mem h ha
  have hnb := ringNeg_mem h hb
  refine inv_unique h.addGroup (addAt_mem h ha hb)
    (ringNeg_mem h (addAt_mem h ha hb)) (addAt_mem h hna hnb)
    (ringAdd_neg h (addAt_mem h ha hb)) ?_
  rw [ringAdd_shuffle_pair h hna hnb ha hb, ringNeg_add h ha, ringNeg_add h hb,
    ringAdd_zero h h.addGroup.mem_e]

theorem ringMul_neg {R add mul zero one a b : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) :
    opAt mul a (ringNeg R add zero b) = ringNeg R add zero (opAt mul a b) :=
  ringMul_neg_nc h.toNC ha hb


/-- `(-1) * a = -a`. The twin of `ringMul_neg` in the other direction: that
moves a negation OUT of a product, this puts the unit's negation IN as a
factor, so a negated element can be handled by a multiplicative law. -/
theorem ringNegOne_mul {R add mul zero one a : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (ha : a ∈ R) :
    opAt mul (ringNeg R add zero one) a = ringNeg R add zero a :=
  ringNegOne_mul_nc hR.toNC ha

#print axioms ringNegOne_mul

theorem ringNeg_mul {R add mul zero one a b : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) :
    opAt mul (ringNeg R add zero a) b = ringNeg R add zero (opAt mul a b) :=
  ringNeg_mul_nc h.toNC ha hb

/-- `a - b`, spelled out. -/
def ringSub (R add zero a b : ZFSet.{u}) : ZFSet.{u} := opAt add a (ringNeg R add zero b)

/-- Subtraction lands in the ring, over the non-commutative base.
`a - b` is `a + (-b)`, so this is additive and `addGroup` carries it. -/
theorem ringSub_mem_nc {R add mul zero one a b : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) :
    ringSub R add zero a b ∈ R :=
  opAt_mem h.addGroup ha (ringNeg_mem_nc h hb)

#print axioms Algebra.ringSub_mem_nc

/-- Double negation cancels, over the non-commutative base. Purely a
group fact, so `addGroup` carries it unchanged. -/
theorem ringNeg_neg_nc {R add mul zero one a : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) :
    ringNeg R add zero (ringNeg R add zero a) = a :=
  ginv_ginv h.addGroup ha

/-- `a - a = 0`, over the non-commutative base. -/
theorem ringSub_self_nc {R add mul zero one a : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) :
    ringSub R add zero a a = zero := ringAdd_neg_nc h ha

/-- Differences compose: `(a-b) + (b-c) = a-c`, over the non-commutative
base. Associativity, the inverse law and the additive unit -- every step is a
group fact, so this needed nothing from the split beyond the additive helpers
already moved. -/
theorem ringSub_trans_nc {R add mul zero one a b c : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) :
    opAt add (ringSub R add zero a b) (ringSub R add zero b c)
      = ringSub R add zero a c := by
  rw [ringSub, ringSub, ringSub, ringAdd_assoc_nc h ha (ringNeg_mem_nc h hb)
      (addAt_mem_nc h hb (ringNeg_mem_nc h hc)),
    ← ringAdd_assoc_nc h (ringNeg_mem_nc h hb) hb (ringNeg_mem_nc h hc),
    ringNeg_add_nc h hb, ringZero_add_nc h (ringNeg_mem_nc h hc)]

#print axioms Algebra.ringNeg_neg_nc
#print axioms Algebra.ringSub_self_nc
#print axioms Algebra.ringSub_trans_nc

/-- `(a+b) + (c+d) = (a+c) + (b+d)`, over the non-commutative base.
Additive commutativity is what shuffles the middle pair, and `IsRingNC` keeps
it -- the split touches the multiplicative side only. -/
theorem ringAdd_shuffle_pair_nc {R add mul zero one a b c d : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R)
    (hd : d ∈ R) :
    opAt add (opAt add a b) (opAt add c d)
      = opAt add (opAt add a c) (opAt add b d) := by
  rw [ringAdd_assoc_nc h ha hb (addAt_mem_nc h hc hd),
    ← ringAdd_assoc_nc h hb hc hd, ringAdd_comm_nc h hb hc,
    ringAdd_assoc_nc h hc hb hd, ← ringAdd_assoc_nc h ha hc (addAt_mem_nc h hb hd)]

/-- Negation distributes over a sum, over the non-commutative base:
`-(a+b) = (-a) + (-b)`. The additive group is abelian here, so the sum of the
inverses IS the inverse of the sum, identified by `inv_unique`. -/
theorem ringNeg_addAt_nc {R add mul zero one a b : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) :
    ringNeg R add zero (opAt add a b)
      = opAt add (ringNeg R add zero a) (ringNeg R add zero b) := by
  have hna := ringNeg_mem_nc h ha
  have hnb := ringNeg_mem_nc h hb
  refine inv_unique h.addGroup (addAt_mem_nc h ha hb)
    (ringNeg_mem_nc h (addAt_mem_nc h ha hb)) (addAt_mem_nc h hna hnb)
    (ringAdd_neg_nc h (addAt_mem_nc h ha hb)) ?_
  rw [ringAdd_shuffle_pair_nc h hna hnb ha hb, ringNeg_add_nc h ha,
    ringNeg_add_nc h hb, ringAdd_zero_nc h h.addGroup.mem_e]

/-- Negating a difference swaps it: `-(a-b) = b-a`, over the
non-commutative base. -/
theorem ringSub_swap_nc {R add mul zero one a b : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) :
    ringNeg R add zero (ringSub R add zero a b) = ringSub R add zero b a := by
  rw [ringSub, ringNeg_addAt_nc h ha (ringNeg_mem_nc h hb), ringNeg_neg_nc h hb,
    ringSub, ringAdd_comm_nc h (ringNeg_mem_nc h ha) hb]

#print axioms Algebra.ringAdd_shuffle_pair_nc
#print axioms Algebra.ringNeg_addAt_nc
#print axioms Algebra.ringSub_swap_nc

/-- A difference of sums splits across both summands, over the
non-commutative base:
`(a+b) - (a'+b') = (a-a') + (b-b')`.

Negation over the sum, then the abelian shuffle. Both are additive, so this
is its commutative twin's proof with the helpers renamed -- and it is the
last piece `isCongruence_idealRel_add` was waiting on. -/
theorem ringSub_addAt_nc {R add mul zero one a a' b b' : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (ha : a ∈ R) (ha' : a' ∈ R) (hb : b ∈ R)
    (hb' : b' ∈ R) :
    ringSub R add zero (opAt add a b) (opAt add a' b')
      = opAt add (ringSub R add zero a a') (ringSub R add zero b b') := by
  show opAt add (opAt add a b) (ringNeg R add zero (opAt add a' b'))
    = opAt add (opAt add a (ringNeg R add zero a'))
      (opAt add b (ringNeg R add zero b'))
  rw [ringNeg_addAt_nc h ha' hb',
    ringAdd_shuffle_pair_nc h ha hb (ringNeg_mem_nc h ha') (ringNeg_mem_nc h hb')]

#print axioms Algebra.ringSub_addAt_nc

theorem ringSub_def (R add zero a b : ZFSet.{u}) :
    ringSub R add zero a b = opAt add a (ringNeg R add zero b) := rfl

theorem ringSub_mem {R add mul zero one a b : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) : ringSub R add zero a b ∈ R :=
  ringSub_mem_nc h.toNC ha hb

theorem ringSub_self {R add mul zero one a : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) : ringSub R add zero a a = zero :=
  ringSub_self_nc h.toNC ha


theorem ringSub_swap {R add mul zero one a b : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) :
    ringNeg R add zero (ringSub R add zero a b) = ringSub R add zero b a :=
  ringSub_swap_nc h.toNC ha hb

theorem ringSub_trans {R add mul zero one a b c : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) :
    opAt add (ringSub R add zero a b) (ringSub R add zero b c) = ringSub R add zero a c :=
  ringSub_trans_nc h.toNC ha hb hc

/-- The difference of two products, split across both factors.

NOT the `opAt` spelling of `ringSub_mul`, despite the suffix: `ringSub_mul` is
right distributivity, `(a - b) * c = a*c - b*c`, at ONE product. This is the
two-product identity, and the `At` here does not mean what it means in
`addAt_mem` or `opAt_polyAddOp`. Named so a reader who found either can reach
the other. -/
theorem ringSub_mulAt {R add mul zero one a a' b b' : ZFSet.{u}}
    (h : IsRing R add mul zero one) (ha : a ∈ R) (ha' : a' ∈ R) (hb : b ∈ R) (hb' : b' ∈ R) :
    ringSub R add zero (opAt mul a b) (opAt mul a' b')
      = opAt add (opAt mul a (ringSub R add zero b b'))
        (opAt mul (ringSub R add zero a a') b') := by
  show opAt add (opAt mul a b) (ringNeg R add zero (opAt mul a' b'))
    = opAt add (opAt mul a (opAt add b (ringNeg R add zero b')))
      (opAt mul (opAt add a (ringNeg R add zero a')) b')
  rw [h.distrib a ha b hb _ (ringNeg_mem h hb'),
    ringRight_distrib h ha (ringNeg_mem h ha') hb', ringMul_neg h ha hb',
    ringNeg_mul h ha' hb',
    ringAdd_assoc h (mulAt_mem h ha hb) (ringNeg_mem h (mulAt_mem h ha hb'))
      (addAt_mem h (mulAt_mem h ha hb') (ringNeg_mem h (mulAt_mem h ha' hb'))),
    ← ringAdd_assoc h (ringNeg_mem h (mulAt_mem h ha hb')) (mulAt_mem h ha hb')
      (ringNeg_mem h (mulAt_mem h ha' hb')),
    ringNeg_add h (mulAt_mem h ha hb'),
    ringZero_add h (ringNeg_mem h (mulAt_mem h ha' hb'))]

/-! ## Adding an element to itself

`gpow` iterates any operation, so the additive iterate is `gpow add zero`. These
are its laws, and they are what the binomial theorem needs. -/

/-- The additive ladder: `a` added to itself `k` times.

The lemmas below are stated about `gpow`. Restating them breaks every
downstream `rw` that matches on `gpow`, because `rw` matches syntactically
while a definition unfolds only for typechecking; migrating those call sites is
queued separately. `ringNsmul_def` is the bridge. -/
def ringNsmul (add zero a : ZFSet.{u}) (k : Nat) : ZFSet.{u} := gpow add zero a k

/-- The ladder is the iterate, by definition. -/
theorem ringNsmul_def (add zero a : ZFSet.{u}) (k : Nat) :
    ringNsmul add zero a k = gpow add zero a k := rfl

/-- The multiplicative ladder: `x` multiplied by itself `k` times, named
in six lemmas below and, until now, defined in none. -/
def ringPow (mul one x : ZFSet.{u}) (k : Nat) : ZFSet.{u} := gpow mul one x k

/-- The ladder is the iterate, by definition. -/
theorem ringPow_def (mul one x : ZFSet.{u}) (k : Nat) :
    ringPow mul one x k = gpow mul one x k := rfl

/-- `(-1)^k` is `1` or `-1`, by the parity of `k`. The step is
`(-1)·(-1) = 1`, which is double negation and needs no invertibility -- so this
holds in any ring, and a determinant's sign alternation is what wants it. -/
theorem ringNegOne_pow {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) :
    ∀ k : Nat, ringPow mul one (ringNeg R add zero one) k
      = (if k % 2 = 0 then one else ringNeg R add zero one)
  | 0 => rfl
  | k + 1 => by
    have hn1 : ringNeg R add zero one ∈ R := ringNeg_mem hR hR.mem_one
    show opAt mul (ringPow mul one (ringNeg R add zero one) k)
        (ringNeg R add zero one) = _
    rw [ringNegOne_pow hR k]
    by_cases h : k % 2 = 0
    · rw [if_pos h, if_neg (by omega : ¬((k + 1) % 2 = 0))]
      exact ringOne_mul hR hn1
    · rw [if_neg h, if_pos (by omega : (k + 1) % 2 = 0),
        ringMul_neg hR hn1 hR.mem_one, hR.mul_one _ hn1]
      exact ringNeg_neg hR hR.mem_one

#print axioms ringNegOne_pow

theorem ringNsmul_mem {R add mul zero one a : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) : ∀ k : Nat, gpow add zero a k ∈ R :=
  gpow_mem h.addGroup ha

/-- Unfolding the iterated sum by one. Definitional: nothing about a ring, or
about `a` belonging to it, is consulted. -/
theorem ringNsmul_succ {add zero a : ZFSet.{u}} (k : Nat) :
    gpow add zero a (k + 1) = opAt add (gpow add zero a k) a := rfl

/-- `n` copies of `zero` is `zero`. The additive twin of
`gpow_zero_eq_zero`, which is multiplicative (`0^(m+1) = 0`); the additive one
had no name until a coefficientwise map needed it to send zero to zero. -/
theorem ringNsmul_zero {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    ∀ k : Nat, gpow add zero zero k = zero
  | 0 => rfl
  | k + 1 => by
    show opAt add (gpow add zero zero k) zero = zero
    rw [ringNsmul_zero hR k]
    exact ringAdd_zero hR hR.addGroup.mem_e

/-- Zero to any positive power is zero. The multiplicative twin of
`ringNsmul_zero` above. The BASE is zero, not the exponent -- `gpow_zero` is
left free for the exponent-zero lemma, which is what that name means elsewhere. -/
theorem gpow_zero_eq_zero {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) :
    ∀ m : Nat, gpow mul one zero (m + 1) = zero
  | 0 => by
    show opAt mul one zero = zero
    exact mul_zero_of_isRing hR hR.mem_one
  | m + 1 => by
    show opAt mul (gpow mul one zero (m + 1)) zero = zero
    rw [gpow_zero_eq_zero hR m]
    exact mul_zero_of_isRing hR hR.addGroup.mem_e

#print axioms gpow_zero_eq_zero

#print axioms ringNsmul_zero
#print axioms isRing_congQuotient
end Algebra
namespace ZFSet
export Algebra (IsField IsIdeal IsRing IsRingNC IsSemiring addAt_mem addAt_mem_nc addAt_mem_semi field_mul_eq_zero gpow_zero_eq_zero ideal_absorbs ideal_add ideal_inverse ideal_mem_zero ideal_subset isRing_congQuotient mulAt_mem mulAt_mem_nc mulAt_mem_semi mul_zero_of_isRing mul_zero_of_isRingNC ringAdd_assoc ringAdd_assoc_nc ringAdd_comm ringAdd_comm_nc ringAdd_left_comm ringAdd_neg ringAdd_neg_nc ringAdd_shuffle_pair ringAdd_shuffle_pair_nc ringAdd_zero ringAdd_zero_nc ringMul_neg ringMul_neg_nc ringNeg ringNegOne_mul ringNegOne_mul_nc ringNegOne_pow ringNeg_add ringNeg_addAt ringNeg_addAt_nc ringNeg_add_nc ringNeg_mem ringNeg_mem_nc ringNeg_mul ringNeg_mul_nc ringNeg_neg ringNeg_neg_nc ringNsmul ringNsmul_def ringNsmul_mem ringNsmul_succ ringNsmul_zero ringOne_mul ringOne_mul_nc ringPow ringPow_def ringRight_distrib ringRight_distrib_nc ringSub ringSub_addAt_nc ringSub_def ringSub_eq_zero_iff ringSub_mem ringSub_mem_nc ringSub_mulAt ringSub_self ringSub_self_nc ringSub_swap ringSub_swap_nc ringSub_trans ringSub_trans_nc ringZero_add ringZero_add_nc ringZero_mul units zero_mul_of_isRingNC)
end ZFSet
