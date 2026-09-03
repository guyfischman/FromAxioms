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
classes. The additive half is `isGroup_congQuotient`; the multiplicative half is
the same `congOp`, so `congOp_isFunction` was stated for a closed
operation rather than a group's. -/

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
group fact, so this needed nothing from the split beyond the
additive helpers already moved. -/
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

theorem ringNsmul_sum {R add mul zero one a : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) (j : Nat) :
    ∀ k : Nat, gpow add zero a (j + k)
      = opAt add (gpow add zero a j) (gpow add zero a k) :=
  gpow_add h.addGroup ha j
theorem ringNsmul_mul {R add mul zero one a b : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) :
    ∀ k : Nat, gpow add zero (opAt mul a b) k = opAt mul (gpow add zero a k) b
  | 0 => (ringZero_mul h hb).symm
  | k + 1 => by
    show opAt add (gpow add zero (opAt mul a b) k) (opAt mul a b)
      = opAt mul (opAt add (gpow add zero a k) a) b
    rw [ringNsmul_mul h ha hb k, ringRight_distrib h (ringNsmul_mem h ha k) ha hb]

/-! ## The additive iterate over a semiring

`IsRing` reaches these through its additive GROUP; a semiring has only a
commutative monoid, and each proof below routes through the `_bare` or
`_of_commMonoid` form that already asks for no more than that. They exist
because the binomial theorem is a semiring theorem --- `add_pow` holds in
`Nat`, which has no negation --- and `binomTerm` carries its coefficient as an
additive iterate.

Asked by statement before writing, and the queries returned SAME SHAPE only,
never an exact type: PROVES-CHECKED: ringNsmul_mem_semi, ringNsmul_sum_semi,
ringNsmul_mul_semi, ringPow_mem_semi, isCommSemiring_of_isRing.
The same sweep found `IsCommMonoid.toMonoid` ALREADY PROVED (FinProd.lean 53)
and surfaced `gpow_add_of_commMonoid`, so two of these are one-liners
rather than the ports they were sized as. -/

theorem ringNsmul_mem_semi {R add mul zero one a : ZFSet.{u}}
    (h : IsSemiring R add mul zero one) (ha : a ∈ R) :
    ∀ k : Nat, gpow add zero a k ∈ R :=
  gpow_mem_bare h.addMonoid.toMonoid ha

#print axioms Algebra.ringNsmul_mem_semi

theorem ringNsmul_sum_semi {R add mul zero one a : ZFSet.{u}}
    (h : IsSemiring R add mul zero one) (ha : a ∈ R) (j k : Nat) :
    gpow add zero a (j + k) = opAt add (gpow add zero a j) (gpow add zero a k) :=
  gpow_add_of_commMonoid h.addMonoid ha j k

#print axioms Algebra.ringNsmul_sum_semi

/-- `k·(ab) = (k·a)b` over a semiring. The ring proof reaches for
`ringZero_mul` and `ringRight_distrib`, which are THEOREMS there and AXIOMS
here (`zeroMul`, `distribRight`) --- the inversion that makes dropping
inverses cheap rather than costly. -/
theorem ringNsmul_mul_semi {R add mul zero one a b : ZFSet.{u}}
    (h : IsSemiring R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) :
    ∀ k : Nat, gpow add zero (opAt mul a b) k = opAt mul (gpow add zero a k) b
  | 0 => (h.zeroMul _ hb).symm
  | k + 1 => by
    show opAt add (gpow add zero (opAt mul a b) k) (opAt mul a b)
      = opAt mul (opAt add (gpow add zero a k) a) b
    rw [ringNsmul_mul_semi h ha hb k,
      h.distribRight _ (ringNsmul_mem_semi h ha k) _ ha _ hb]

#print axioms Algebra.ringNsmul_mul_semi

theorem ringPow_mem_semi {R add mul zero one x : ZFSet.{u}}
    (h : IsSemiring R add mul zero one) (hx : x ∈ R) :
    ∀ k : Nat, gpow mul one x k ∈ R
  | 0 => h.mem_one
  | k + 1 => mulAt_mem_semi h (ringPow_mem_semi h hx k) hx

#print axioms Algebra.ringPow_mem_semi

/-- A commutative semiring. `IsSemiring` states no `mulComm`, and the
binomial theorem is false without one, so the widening that reaches `add_pow`
needs the commutativity back as its own field rather than as a ring's. -/
structure IsCommSemiring (R add mul zero one : ZFSet.{u}) : Prop where
  semiring : IsSemiring R add mul zero one
  mulComm : ∀ a, a ∈ R → ∀ b, b ∈ R → opAt mul a b = opAt mul b a

/-- Every commutative ring is a commutative semiring, so the `_semi` forms
are a WIDENING rather than a second theory standing beside the first --- the same relation `IsRingNC.toSemiring` gives one level down. -/
theorem isCommSemiring_of_isRing {R add mul zero one : ZFSet.{u}}
    (h : IsRing R add mul zero one) : IsCommSemiring R add mul zero one where
  semiring := h.toNC.toSemiring
  mulComm := h.mulComm

#print axioms Algebra.isCommSemiring_of_isRing

/-! ## A finite domain is a field

No division algorithm is needed: in a finite ring the powers of an element must
repeat, and with no zero divisors that forces a power of it to be `1`. -/

theorem ringPow_mem {R add mul zero one x : ZFSet.{u}} (h : IsRing R add mul zero one)
    (hx : x ∈ R) : ∀ k : Nat, gpow mul one x k ∈ R
  | 0 => h.mem_one
  | k + 1 => mulAt_mem h (ringPow_mem h hx k) hx
  -- the NC form proves the same recursion; kept separate so this one stays
  -- usable at `IsRing` without a `.toNC` at every call site

theorem ringPow_succ (mul one x : ZFSet.{u}) (k : Nat) :
    gpow mul one x (k + 1) = opAt mul (gpow mul one x k) x := rfl

theorem ringPow_add {R add mul zero one x : ZFSet.{u}} (h : IsRing R add mul zero one)
    (hx : x ∈ R) (i : Nat) :
    ∀ j : Nat, gpow mul one x (i + j) = opAt mul (gpow mul one x i) (gpow mul one x j)
  | 0 => (h.mul_one _ (ringPow_mem h hx i)).symm
  | j + 1 => by
    show opAt mul (gpow mul one x (i + j)) x
      = opAt mul (gpow mul one x i) (opAt mul (gpow mul one x j) x)
    rw [ringPow_add h hx i j,
      h.mulAssoc _ (ringPow_mem h hx i) _ (ringPow_mem h hx j) _ hx]

theorem ringOne_pow {R add mul zero one : ZFSet.{u}} (h : IsRing R add mul zero one) :
    ∀ k : Nat, gpow mul one one k = one
  | 0 => rfl
  | k + 1 => by
    show opAt mul (gpow mul one one k) one = one
    rw [h.mul_one _ (ringPow_mem h h.mem_one k), ringOne_pow h k]

/-- The additive inverse is determined: anything summing to zero with `a` is
`ringNeg a`. -/
theorem ringNeg_eq_of_add_zero {R add mul zero one a b : ZFSet.{u}}
    (h : IsRing R add mul zero one) (ha : a ∈ R) (hb : b ∈ R)
    (hab : opAt add a b = zero) : ringNeg R add zero a = b :=
  (op_left_cancel h.addGroup ha hb (ringNeg_mem h ha)
    (hab.trans (ringAdd_neg h ha).symm)).symm

/-- `(a + b) - b = a`. -/
theorem ringAdd_sub_cancel {R add mul zero one a b : ZFSet.{u}}
    (h : IsRing R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) :
    ringSub R add zero (opAt add a b) b = a := by
  show opAt add (opAt add a b) (ringNeg R add zero b) = a
  rw [ringAdd_assoc h ha hb (ringNeg_mem h hb), ringAdd_neg h hb, ringAdd_zero h ha]


/-- The image of a natural number in a ring, by repeated addition -- the idiom
`binomTerm` uses, so no characteristic map and no `NumberTheory.Int` embedding. -/
noncomputable def natIn (R add zero one : ZFSet.{u}) (n : Nat) : ZFSet.{u} :=
  gpow add zero one n

theorem ringMul_shuffle_pair {R add mul zero one a b c d : ZFSet.{u}}
    (h : IsRing R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) (hd : d ∈ R) :
    opAt mul (opAt mul a b) (opAt mul c d)
      = opAt mul (opAt mul a c) (opAt mul b d) := by
  rw [h.mulAssoc _ ha _ hb _ (mulAt_mem h hc hd), ← h.mulAssoc _ hb _ hc _ hd,
    h.mulComm _ hb _ hc, h.mulAssoc _ hc _ hb _ hd,
    ← h.mulAssoc _ ha _ hc _ (mulAt_mem h hb hd)]


theorem ringPow_mul {R add mul zero one x : ZFSet.{u}} (h : IsRing R add mul zero one)
    (hx : x ∈ R) (i : Nat) :
    ∀ j : Nat, gpow mul one x (i * j) = gpow mul one (gpow mul one x i) j
  | 0 => by rw [Nat.mul_zero]; rfl
  | j + 1 => by
    show gpow mul one x (i * (j + 1)) = opAt mul (gpow mul one (gpow mul one x i) j) _
    rw [← ringPow_mul h hx i j, show i * (j + 1) = i * j + i from Nat.mul_succ i j,
      ringPow_add h hx (i * j) i]

theorem ringMul_sub {R add mul zero one a b c : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) :
    opAt mul a (ringSub R add zero b c) = ringSub R add zero (opAt mul a b) (opAt mul a c) := by
  show opAt mul a (opAt add b (ringNeg R add zero c))
    = opAt add (opAt mul a b) (ringNeg R add zero (opAt mul a c))
  rw [h.distrib a ha b hb _ (ringNeg_mem h hc), ringMul_neg h ha hc]

/-- And the left twin. `ringMul_sub` distributes a subtraction on the RIGHT
of a product; this is the same law on the left. They are different lemmas and
neither follows from the other without commutativity, which a caller holding a
one-sided distributive law does not necessarily have.

Named because the asymmetry is a trap: a reader who finds `ringMul_sub` by
searching for sub and mul has found the other one. -/
theorem ringSub_mul {R add mul zero one a b c : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R) :
    opAt mul (ringSub R add zero a b) c = ringSub R add zero (opAt mul a c) (opAt mul b c) := by
  show opAt mul (opAt add a (ringNeg R add zero b)) c
    = opAt add (opAt mul a c) (ringNeg R add zero (opAt mul b c))
  rw [ringRight_distrib h ha (ringNeg_mem h hb) hc, ringNeg_mul h hb hc]

#print axioms ringSub_mul

/-! ## Homomorphisms -/

/-- A ring homomorphism is a homomorphism of the additive groups that also
carries `×` and `1`. Stating it as `IsHom ∧ _` rather than restating `IsHom`'s
clauses is what lets the group lemmas apply to it directly. Callers use the
named projections below rather than the nesting. -/
def IsRingHom (h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂ : ZFSet.{u}) : Prop :=
  IsHom h R₁ add₁ R₂ add₂ ∧
    (∀ a, a ∈ R₁ → ∀ b, b ∈ R₁ → app h (opAt mul₁ a b) = opAt mul₂ (app h a) (app h b)) ∧
    app h one₁ = one₂

theorem hom_add {h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂ a b : ZFSet.{u}}
    (hh : IsRingHom h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂) (ha : a ∈ R₁) (hb : b ∈ R₁) :
    app h (opAt add₁ a b) = opAt add₂ (app h a) (app h b) :=
  hh.left.right.right.right a ha b hb

theorem hom_mul {h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂ a b : ZFSet.{u}}
    (hh : IsRingHom h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂) (ha : a ∈ R₁) (hb : b ∈ R₁) :
    app h (opAt mul₁ a b) = opAt mul₂ (app h a) (app h b) :=
  hh.right.left a ha b hb

/-- The additive and multiplicative laws in the explicit-argument form the
extension theory uses: `IsRingHom` was a flat conjunction before the group
homomorphism was factored out, and its users pass the elements. -/
theorem hom_add' {h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂ : ZFSet.{u}}
    (hh : IsRingHom h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂) :
    ∀ a, a ∈ R₁ → ∀ b, b ∈ R₁ →
      app h (opAt add₁ a b) = opAt add₂ (app h a) (app h b) :=
  fun _ ha _ hb => hom_add hh ha hb

theorem hom_mul' {h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂ : ZFSet.{u}}
    (hh : IsRingHom h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂) :
    ∀ a, a ∈ R₁ → ∀ b, b ∈ R₁ →
      app h (opAt mul₁ a b) = opAt mul₂ (app h a) (app h b) :=
  fun _ ha _ hb => hom_mul hh ha hb

theorem hom_one {h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂ : ZFSet.{u}}
    (hh : IsRingHom h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂) : app h one₁ = one₂ :=
  hh.right.right

theorem hom_app_mem {h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂ a : ZFSet.{u}}
    (hh : IsRingHom h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂) (ha : a ∈ R₁) : app h a ∈ R₂ :=
  app_mem_of_isHom hh.left ha

/-! A ring hom out of a FIELD kills nothing --- that is `hom_ne_zero`, in
`SetTheory/Extension.lean`, and NOT here. -/

/-- Vanishing is decidable: the hypothesis degree needs.

Sited here rather than beside the first degree argument that wanted it. Its body
is carrier and zero -- no degree, no polynomial, nothing from the file it was
declared in -- and fifteen files across the polynomial, field and geometry towers
take it as a hypothesis. A subject-free predicate placed at its first consumer is
invisible to the second. -/
def DecidableVanishing (R zero : ZFSet.{u}) : Prop :=
  ∀ a, a ∈ R → a = zero ∨ a ≠ zero

/-- Vanishing is STABLE: a doubly negated vanishing is a vanishing.

Strictly weaker than `DecidableVanishing`, which hands over a disjunction, and
an argument by REFUTATION needs it -- a proof that `a ≠ zero` is absurd gives
`¬ a ≠ zero` and nothing more, and stability is exactly the step from there to
the equation.

The distinction is not idle at the carriers this tower cares about.
`DecidableVanishing RealL` is floored at `WLPO`, while stability holds for the
located reals outright (`stableVanishing_realL`), because not-apart is equal. So
a theorem stating a decision where it only refutes charges a principle it does
not spend. -/
def StableVanishing (R zero : ZFSet.{u}) : Prop :=
  ∀ a, a ∈ R → ¬ a ≠ zero → a = zero

/-- A decision is stable: the disjunction settles the doubly negated form. -/
theorem stableVanishing_of_decidableVanishing {R zero : ZFSet.{u}}
    (hdec : DecidableVanishing R zero) : StableVanishing R zero := by
  intro a ha hnn
  rcases hdec a ha with h | h
  · exact h
  · exact absurd h hnn

/-- An injective homomorphism: the copy of `R₁` inside `R₂`. -/
def IsEmbedding (h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂ : ZFSet.{u}) : Prop :=
  IsRingHom h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂ ∧
    ∀ a, a ∈ R₁ → ∀ b, b ∈ R₁ → app h a = app h b → a = b

theorem hom_zero {h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ zero₁ zero₂ one₂ : ZFSet.{u}}
    (hh : IsRingHom h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂)
    (h₁ : IsRing R₁ add₁ mul₁ zero₁ one₁) (h₂ : IsRing R₂ add₂ mul₂ zero₂ one₂) :
    app h zero₁ = zero₂ := by
  have hz := hom_app_mem hh h₁.addGroup.mem_e
  have hstep := hom_add hh h₁.addGroup.mem_e h₁.addGroup.mem_e
  rw [ringAdd_zero h₁ h₁.addGroup.mem_e] at hstep
  refine op_left_cancel h₂.addGroup hz hz h₂.addGroup.mem_e ?_
  rw [ringAdd_zero h₂ hz]
  exact hstep.symm

theorem hom_pow {h R₁ add₁ mul₁ zero₁ one₁ R₂ add₂ mul₂ one₂ a : ZFSet.{u}}
    (hh : IsRingHom h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂)
    (h₁ : IsRing R₁ add₁ mul₁ zero₁ one₁) (ha : a ∈ R₁) :
    ∀ k : Nat, app h (gpow mul₁ one₁ a k) = gpow mul₂ one₂ (app h a) k
  | 0 => hom_one hh
  | k + 1 => by
    show app h (opAt mul₁ (gpow mul₁ one₁ a k) a) = opAt mul₂ (gpow mul₂ one₂ (app h a) k) _
    rw [hom_mul hh (ringPow_mem h₁ ha k) ha, hom_pow hh h₁ ha k]

/-! ### The identity embedding

A ring is an extension of itself, and saying so needs a homomorphism whose
underlying set of pairs is the identity graph. `imageIn_id` is the clause that
makes the statement about `R` rather than about a copy of it: without it, *`R`
embeds in `R` with basis `{1}`* would be a claim about `imageIn (idOn R) R R`,
which reads as true while naming a different set. -/

theorem isRingHom_id {R add mul zero one : ZFSet.{u}} (h : IsRing R add mul zero one) :
    IsRingHom (idOn R) R add mul one R add mul one := by
  refine ⟨⟨graphOn_isFunction R R _, graphOn_domain (fun _ hm => hm), ?_, ?_⟩, ?_, ?_⟩
  · intro b hb
    obtain ⟨a, hab⟩ := (mem_range_iff b _).mp hb
    obtain ⟨-, n, hn, he⟩ := (mem_graphOn_iff R R _ _).mp hab
    obtain ⟨-, rfl⟩ := opair_injective he
    exact hn
  · intro a ha b hb
    rw [app_idOn (opAt_mem h.addGroup ha hb), app_idOn ha, app_idOn hb]
  · intro a ha b hb
    rw [app_idOn (mulAt_mem h ha hb), app_idOn ha, app_idOn hb]
  · exact app_idOn h.mem_one

theorem isEmbedding_id {R add mul zero one : ZFSet.{u}} (h : IsRing R add mul zero one) :
    IsEmbedding (idOn R) R add mul one R add mul one :=
  ⟨isRingHom_id h, fun _ ha _ hb he => (app_idOn ha).symm.trans (he.trans (app_idOn hb))⟩

/-- The image of the identity is the ring itself,not a copy of it. -/
theorem imageIn_id (R : ZFSet.{u}) : imageIn (idOn R) R R = R :=
  ext _ _ fun v => ⟨fun hv => ((mem_imageIn_iff _ R R v).mp hv).left,
    fun hv => (mem_imageIn_iff _ R R v).mpr ⟨hv, v, hv, (app_idOn hv).symm⟩⟩

/-- A finite commutative ring with no zero divisors is a field. -/
theorem isField_of_finite_domain {R add mul zero one : ZFSet.{u}}
    (h : IsRing R add mul zero one) (hne : zero ≠ one)
    (hdisj : ∀ a, a ∈ R → ∀ b, b ∈ R → opAt mul a b = zero → a = zero ∨ b = zero)
    {n : Nat} (hfin : Equinumerous R (ofNat.{u} n)) : IsField R add mul zero one := by
  refine ⟨h, hne, fun a ha hane => ?_⟩
  -- powers of a non-zero element never vanish
  have hpowne : ∀ k : Nat, gpow mul one a k ≠ zero := by
    intro k
    induction k with
    | zero => exact fun he => hne he.symm
    | succ i ih =>
      intro he
      rcases hdisj _ (ringPow_mem h ha i) _ ha he with h' | h'
      · exact ih h'
      · exact hane h'
  obtain ⟨j, k, hjk, hpow⟩ := exists_repeat_of_finite (F := fun k => gpow mul one a k)
    (ringPow_mem h ha) hfin
  -- `a^j·(a^(k-j) - 1) = 0`, and the first factor is non-zero
  have hsplit : opAt mul (gpow mul one a j) (ringSub R add zero (gpow mul one a (k - j)) one)
      = zero := by
    rw [ringMul_sub h (ringPow_mem h ha j) (ringPow_mem h ha (k - j)) h.mem_one,
      ← ringPow_add h ha j (k - j), show j + (k - j) = k by omega, ← hpow,
      h.mul_one _ (ringPow_mem h ha j), ringSub_self h (ringPow_mem h ha j)]
  have hunit : gpow mul one a (k - j) = one := by
    rcases hdisj _ (ringPow_mem h ha j) _ (ringSub_mem h (ringPow_mem h ha (k - j)) h.mem_one)
      hsplit with h' | h'
    · exact absurd h' (hpowne j)
    · exact (ringSub_eq_zero_iff h (ringPow_mem h ha (k - j)) h.mem_one).mp h'
  refine ⟨gpow mul one a (k - j - 1), ringPow_mem h ha _, ?_⟩
  have hstep : gpow mul one a (k - j) = opAt mul (gpow mul one a (k - j - 1)) a := by
    obtain ⟨m, hm⟩ : ∃ m, k - j = m + 1 := ⟨k - j - 1, by omega⟩
    rw [hm, show m + 1 - 1 = m by omega]
    rfl
  rw [hstep] at hunit
  rw [h.mulComm a ha _ (ringPow_mem h ha (k - j - 1))]
  exact hunit

/-! ## The quotient by an ideal -/

def ringMultiples (R mul a : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun w => ∃ y, y ∈ R ∧ w = opAt mul a y) R

theorem mem_ringMultiples_iff (R mul a w : ZFSet.{u}) :
    w ∈ ringMultiples R mul a ↔ w ∈ R ∧ ∃ y, y ∈ R ∧ w = opAt mul a y :=
  mem_sep_iff _ _ _

/-! `ringMultiples_natIn_mul_unit` --- a unit numeral factor is invisible to the
ideal --- belongs beside these two and is sited instead beside
`ringMultiples_unit_mul`, some nine thousand lines below, which it cites. -/

theorem isIdeal_ringMultiples {R add mul zero one a : ZFSet.{u}}
    (h : IsRing R add mul zero one) (ha : a ∈ R) :
    IsIdeal (ringMultiples R mul a) R add mul zero := by
  refine ⟨fun w hw => ((mem_ringMultiples_iff _ _ _ w).mp hw).left,
    (mem_ringMultiples_iff _ _ _ _).mpr ⟨h.addGroup.mem_e, zero, h.addGroup.mem_e,
      (mul_zero_of_isRing h ha).symm⟩, ?_, ?_, ?_⟩
  · intro u hu v hv
    obtain ⟨huR, y, hy, rfl⟩ := (mem_ringMultiples_iff _ _ _ u).mp hu
    obtain ⟨hvR, z, hz, rfl⟩ := (mem_ringMultiples_iff _ _ _ v).mp hv
    exact (mem_ringMultiples_iff _ _ _ _).mpr ⟨addAt_mem h huR hvR, opAt add y z,
      addAt_mem h hy hz, (h.distrib a ha y hy z hz).symm⟩
  · intro u hu
    obtain ⟨huR, y, hy, rfl⟩ := (mem_ringMultiples_iff _ _ _ u).mp hu
    refine ⟨opAt mul a (ringNeg R add zero y), (mem_ringMultiples_iff _ _ _ _).mpr
      ⟨mulAt_mem h ha (ringNeg_mem h hy), ringNeg R add zero y, ringNeg_mem h hy, rfl⟩, ?_⟩
    rw [← h.distrib a ha y hy _ (ringNeg_mem h hy), ringAdd_neg h hy,
      mul_zero_of_isRing h ha]
  · intro r hr u hu
    obtain ⟨huR, y, hy, rfl⟩ := (mem_ringMultiples_iff _ _ _ u).mp hu
    exact (mem_ringMultiples_iff _ _ _ _).mpr ⟨mulAt_mem h hr huR, opAt mul r y,
      mulAt_mem h hr hy, by
        rw [← h.mulAssoc r hr a ha y hy, h.mulComm r hr a ha, h.mulAssoc a ha r hr y hy]⟩


/-- An ideal is closed under negation, over the non-commutative base.

The proof never touched commutativity -- it identifies the additive inverse
supplied by `ideal_inverse` with `ringNeg` and reads off membership. This is
the first of the IDEAL lemmas to move, and it is representative: of 215
ideal-family results stated over `IsRing`, 188 carry commutativity without
spending it, so they move by hypothesis change alone once the additive
helpers exist on the weaker base. -/
theorem ideal_neg_mem_nc {I R add mul zero one a : ZFSet.{u}}
    (h : IsRingNC R add mul zero one)
    (hI : IsIdeal I R add mul zero) (ha : a ∈ I) : ringNeg R add zero a ∈ I := by
  obtain ⟨b, hb, hab⟩ := ideal_inverse hI ha
  have haR : a ∈ R := ideal_subset hI _ ha
  have hbe : b = ringNeg R add zero a :=
    inv_unique h.addGroup haR (ideal_subset hI _ hb) (ringNeg_mem_nc h haR) hab
      (ringNeg_add_nc h haR)
  rw [← hbe]
  exact hb

#print axioms Algebra.ideal_neg_mem_nc

theorem ideal_neg_mem {I R add mul zero one a : ZFSet.{u}} (h : IsRing R add mul zero one)
    (hI : IsIdeal I R add mul zero) (ha : a ∈ I) : ringNeg R add zero a ∈ I :=
  ideal_neg_mem_nc h.toNC hI ha

def idealRel (R add zero I : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => ∃ a, a ∈ R ∧ ∃ b, b ∈ R ∧ z = opair a b ∧ ringSub R add zero a b ∈ I)
    (prod R R)

theorem opair_mem_idealRel_iff {R add zero I a b : ZFSet.{u}} (ha : a ∈ R) (hb : b ∈ R) :
    opair a b ∈ idealRel R add zero I ↔ ringSub R add zero a b ∈ I := by
  refine Iff.trans (mem_sep_iff _ _ _) ⟨?_, ?_⟩
  · rintro ⟨-, a', -, b', -, he, hmem⟩
    obtain ⟨rfl, rfl⟩ := opair_injective he
    exact hmem
  · exact fun hmem => ⟨opair_mem_prod ha hb, a, ha, b, hb, rfl, hmem⟩

/-- Congruence modulo an ideal, for ADDITION, over the non-commutative
base.

Reflexivity is `a - a = 0`, symmetry is `-(a-b) = b-a`, transitivity is
`(a-b) + (b-c) = a-c`, and compatibility is the difference of sums splitting
across both summands. Every one of those is a fact about the additive group,
which `IsRingNC` keeps unchanged -- so the additive half of the quotient
construction never needed a commutative ring.

The MULTIPLICATIVE half is a different matter: `isCongruence_idealRel_mul`
spends `mulComm` moving `(a-a')·b'` to the side `IsIdeal` absorbs on, and
that is the left/right question rather than a rename. -/
theorem isCongruence_idealRel_add_nc {I R add mul zero one : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) (hI : IsIdeal I R add mul zero) :
    IsCongruence (idealRel R add zero I) R add := by
  refine ⟨⟨fun a ha => (opair_mem_idealRel_iff ha ha).mpr (by
      rw [ringSub_self_nc h ha]; exact ideal_mem_zero hI), fun a b ha hb hr => ?_,
    fun a b c ha hb hc hab hbc => ?_⟩, fun a ha a' ha' b hb b' hb' hr₁ hr₂ => ?_⟩
  · refine (opair_mem_idealRel_iff hb ha).mpr ?_
    rw [← ringSub_swap_nc h ha hb]
    exact ideal_neg_mem_nc h hI ((opair_mem_idealRel_iff ha hb).mp hr)
  · refine (opair_mem_idealRel_iff ha hc).mpr ?_
    rw [← ringSub_trans_nc h ha hb hc]
    exact ideal_add hI ((opair_mem_idealRel_iff ha hb).mp hab)
      ((opair_mem_idealRel_iff hb hc).mp hbc)
  · refine (opair_mem_idealRel_iff (addAt_mem_nc h ha hb)
      (addAt_mem_nc h ha' hb')).mpr ?_
    rw [ringSub_addAt_nc h ha ha' hb hb']
    exact ideal_add hI ((opair_mem_idealRel_iff ha ha').mp hr₁)
      ((opair_mem_idealRel_iff hb hb').mp hr₂)

#print axioms Algebra.isCongruence_idealRel_add_nc

theorem isCongruence_idealRel_add {I R add mul zero one : ZFSet.{u}}
    (h : IsRing R add mul zero one) (hI : IsIdeal I R add mul zero) :
    IsCongruence (idealRel R add zero I) R add :=
  isCongruence_idealRel_add_nc h.toNC hI

theorem isCongruence_idealRel_mul {I R add mul zero one : ZFSet.{u}}
    (h : IsRing R add mul zero one) (hI : IsIdeal I R add mul zero) :
    IsCongruence (idealRel R add zero I) R mul := by
  refine ⟨(isCongruence_idealRel_add h hI).left, fun a ha a' ha' b hb b' hb' hr₁ hr₂ => ?_⟩
  refine (opair_mem_idealRel_iff (mulAt_mem h ha hb) (mulAt_mem h ha' hb')).mpr ?_
  rw [ringSub_mulAt h ha ha' hb hb']
  refine ideal_add hI (ideal_absorbs hI ha
    ((opair_mem_idealRel_iff hb hb').mp hr₂)) ?_
  rw [h.mulComm _ (ringSub_mem h ha ha') _ hb']
  exact ideal_absorbs hI hb' ((opair_mem_idealRel_iff ha ha').mp hr₁)

/-- The quotient of a ring by an ideal is a ring. -/
theorem isRing_quotientByIdeal {I R add mul zero one : ZFSet.{u}}
    (h : IsRing R add mul zero one) (hI : IsIdeal I R add mul zero) :
    IsRing (quotientSet (idealRel R add zero I) R)
      (congOp (idealRel R add zero I) R add) (congOp (idealRel R add zero I) R mul)
      (cls (idealRel R add zero I) R zero) (cls (idealRel R add zero I) R one) :=
  isRing_congQuotient h (isCongruence_idealRel_add h hI) (isCongruence_idealRel_mul h hI)

/-! ## Subrings

A subset containing `zero` and `one` and closed under addition, negation and
multiplication is a ring under the restricted operations. The restricted
operation has the same pairs; only the ambient product shrinks. -/

structure IsSubring (S R add mul zero one : ZFSet.{u}) : Prop where
  sub : S ⊆ R
  mem_zero : zero ∈ S
  mem_one : one ∈ S
  add_closed : ∀ a, a ∈ S → ∀ b, b ∈ S → opAt add a b ∈ S
  mul_closed : ∀ a, a ∈ S → ∀ b, b ∈ S → opAt mul a b ∈ S
  neg_closed : ∀ a, a ∈ S → ringNeg R add zero a ∈ S

/-- A homomorphism carries negation, which the image needs to be a subring. -/
theorem hom_neg {h R₁ add₁ mul₁ zero₁ one₁ R₂ add₂ mul₂ zero₂ one₂ a : ZFSet.{u}}
    (hh : IsRingHom h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂)
    (h₁ : IsRing R₁ add₁ mul₁ zero₁ one₁) (h₂ : IsRing R₂ add₂ mul₂ zero₂ one₂)
    (ha : a ∈ R₁) :
    app h (ringNeg R₁ add₁ zero₁ a) = ringNeg R₂ add₂ zero₂ (app h a) := by
  refine op_left_cancel h₂.addGroup (hom_app_mem hh ha)
    (hom_app_mem hh (ringNeg_mem h₁ ha)) (ringNeg_mem h₂ (hom_app_mem hh ha)) ?_
  rw [← hom_add hh ha (ringNeg_mem h₁ ha), ringAdd_neg h₁ ha, hom_zero hh h₁ h₂,
    ringAdd_neg h₂ (hom_app_mem hh ha)]

/-- The image of a ring homomorphism is a subring. -/
theorem isSubring_imageIn {h R₁ add₁ mul₁ zero₁ one₁ R₂ add₂ mul₂ zero₂ one₂ : ZFSet.{u}}
    (hh : IsRingHom h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂)
    (h₁ : IsRing R₁ add₁ mul₁ zero₁ one₁) (h₂ : IsRing R₂ add₂ mul₂ zero₂ one₂) :
    IsSubring (imageIn h R₁ R₂) R₂ add₂ mul₂ zero₂ one₂ := by
  have hmem : ∀ a, a ∈ R₁ → app h a ∈ imageIn h R₁ R₂ := fun a ha =>
    (mem_imageIn_iff h R₁ R₂ _).mpr ⟨hom_app_mem hh ha, a, ha, rfl⟩
  refine ⟨fun w hw => ((mem_imageIn_iff h R₁ R₂ w).mp hw).left, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hom_zero hh h₁ h₂]
    exact hmem _ h₁.addGroup.mem_e
  · rw [← hom_one hh]
    exact hmem _ h₁.mem_one
  · intro a ha b hb
    obtain ⟨-, x, hx, rfl⟩ := (mem_imageIn_iff h R₁ R₂ a).mp ha
    obtain ⟨-, y, hy, rfl⟩ := (mem_imageIn_iff h R₁ R₂ b).mp hb
    rw [← hom_add hh hx hy]
    exact hmem _ (addAt_mem h₁ hx hy)
  · intro a ha b hb
    obtain ⟨-, x, hx, rfl⟩ := (mem_imageIn_iff h R₁ R₂ a).mp ha
    obtain ⟨-, y, hy, rfl⟩ := (mem_imageIn_iff h R₁ R₂ b).mp hb
    rw [← hom_mul hh hx hy]
    exact hmem _ (mulAt_mem h₁ hx hy)
  · intro a ha
    obtain ⟨-, x, hx, rfl⟩ := (mem_imageIn_iff h R₁ R₂ a).mp ha
    rw [← hom_neg hh h₁ h₂ hx]
    exact hmem _ (ringNeg_mem h₁ hx)

/-- The image of a SUBRING is a subring of the codomain.

`isSubring_imageIn` takes the image of the whole ring; a tower needs the image
of a subring, and the closure conditions come from the subring's rather than
the ring's. The negation clause is the one that is not symmetric: `ringNeg` is
computed in the AMBIENT ring on each side, so it goes through `hom_neg` at the
source's ring and not at the subring. -/
theorem isSubring_imageIn_of_subring
    {h R₁ add₁ mul₁ zero₁ one₁ R₂ add₂ mul₂ zero₂ one₂ K : ZFSet.{u}}
    (hh : IsRingHom h R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂)
    (h₁ : IsRing R₁ add₁ mul₁ zero₁ one₁) (h₂ : IsRing R₂ add₂ mul₂ zero₂ one₂)
    (hK : IsSubring K R₁ add₁ mul₁ zero₁ one₁) :
    IsSubring (imageIn h K R₂) R₂ add₂ mul₂ zero₂ one₂ := by
  have hmem : ∀ a, a ∈ K → app h a ∈ imageIn h K R₂ := fun a ha =>
    (mem_imageIn_iff h K R₂ _).mpr ⟨hom_app_mem hh (hK.sub a ha), a, ha, rfl⟩
  refine ⟨fun w hw => ((mem_imageIn_iff h K R₂ w).mp hw).left, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hom_zero hh h₁ h₂]
    exact hmem _ hK.mem_zero
  · rw [← hom_one hh]
    exact hmem _ hK.mem_one
  · intro a ha b hb
    obtain ⟨-, x, hx, rfl⟩ := (mem_imageIn_iff h K R₂ a).mp ha
    obtain ⟨-, y, hy, rfl⟩ := (mem_imageIn_iff h K R₂ b).mp hb
    rw [← hom_add hh (hK.sub x hx) (hK.sub y hy)]
    exact hmem _ (hK.add_closed x hx y hy)
  · intro a ha b hb
    obtain ⟨-, x, hx, rfl⟩ := (mem_imageIn_iff h K R₂ a).mp ha
    obtain ⟨-, y, hy, rfl⟩ := (mem_imageIn_iff h K R₂ b).mp hb
    rw [← hom_mul hh (hK.sub x hx) (hK.sub y hy)]
    exact hmem _ (hK.mul_closed x hx y hy)
  · intro a ha
    obtain ⟨-, x, hx, rfl⟩ := (mem_imageIn_iff h K R₂ a).mp ha
    rw [← hom_neg hh h₁ h₂ (hK.sub x hx)]
    exact hmem _ (hK.neg_closed x hx)

theorem opAt_subring_add {S R add mul zero one a b : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hS : IsSubring S R add mul zero one)
    (ha : a ∈ S) (hb : b ∈ S) : opAt (restrictOp add S) a b = opAt add a b :=
  opAt_restrictOp hR.addGroup.isFun
    (fun x hx => by
      obtain ⟨c, hc, d, hd, rfl⟩ := (mem_prod_iff x _ _).mp hx
      rw [hR.addGroup.dom]
      exact opair_mem_prod (hS.sub _ hc) (hS.sub _ hd))
    hS.add_closed ha hb

theorem opAt_subring_mul {S R add mul zero one a b : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hS : IsSubring S R add mul zero one)
    (ha : a ∈ S) (hb : b ∈ S) : opAt (restrictOp mul S) a b = opAt mul a b :=
  opAt_restrictOp hR.mulFun
    (fun x hx => by
      obtain ⟨c, hc, d, hd, rfl⟩ := (mem_prod_iff x _ _).mp hx
      rw [hR.mulDom]
      exact opair_mem_prod (hS.sub _ hc) (hS.sub _ hd))
    hS.mul_closed ha hb

/-- A subring is a ring. -/
theorem isRing_subring {S R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hS : IsSubring S R add mul zero one) :
    IsRing S (restrictOp add S) (restrictOp mul S) zero one := by
  have hdomAdd : ∀ x, x ∈ prod S S → x ∈ domain add := fun x hx => by
    obtain ⟨c, hc, d, hd, rfl⟩ := (mem_prod_iff x _ _).mp hx
    rw [hR.addGroup.dom]
    exact opair_mem_prod (hS.sub _ hc) (hS.sub _ hd)
  have hdomMul : ∀ x, x ∈ prod S S → x ∈ domain mul := fun x hx => by
    obtain ⟨c, hc, d, hd, rfl⟩ := (mem_prod_iff x _ _).mp hx
    rw [hR.mulDom]
    exact opair_mem_prod (hS.sub _ hc) (hS.sub _ hd)
  have hA : ∀ {a b : ZFSet.{u}}, a ∈ S → b ∈ S → opAt (restrictOp add S) a b = opAt add a b :=
    fun ha hb => opAt_subring_add hR hS ha hb
  have hM : ∀ {a b : ZFSet.{u}}, a ∈ S → b ∈ S → opAt (restrictOp mul S) a b = opAt mul a b :=
    fun ha hb => opAt_subring_mul hR hS ha hb
  refine ⟨⟨⟨isFunction_restrictOp hR.addGroup.isFun,
      restrictOp_domain hR.addGroup.isFun hdomAdd hS.add_closed, restrictOp_range,
      hS.mem_zero, ?_, ?_, ?_⟩, ?_⟩, ?_, isFunction_restrictOp hR.mulFun,
    restrictOp_domain hR.mulFun hdomMul hS.mul_closed, restrictOp_range, ?_, ?_,
    hS.mem_one, ?_, ?_⟩
  · intro a ha b hb c hc
    rw [hA ha hb, hA (hS.add_closed a ha b hb) hc, hA hb hc, hA ha (hS.add_closed b hb c hc)]
    exact ringAdd_assoc hR (hS.sub _ ha) (hS.sub _ hb) (hS.sub _ hc)
  · intro a ha
    rw [hA hS.mem_zero ha]
    exact ringZero_add hR (hS.sub _ ha)
  · intro a ha
    rw [hA ha hS.mem_zero]
    exact ringAdd_zero hR (hS.sub _ ha)
  · intro a ha
    refine ⟨ringNeg R add zero a, hS.neg_closed a ha, ?_, ?_⟩
    · rw [hA ha (hS.neg_closed a ha)]
      exact ringAdd_neg hR (hS.sub _ ha)
    · rw [hA (hS.neg_closed a ha) ha]
      exact ringNeg_add hR (hS.sub _ ha)
  · intro a ha b hb
    rw [hA ha hb, hA hb ha]
    exact ringAdd_comm hR (hS.sub _ ha) (hS.sub _ hb)
  · intro a ha b hb c hc
    rw [hM ha hb, hM (hS.mul_closed a ha b hb) hc, hM hb hc, hM ha (hS.mul_closed b hb c hc)]
    exact hR.mulAssoc _ (hS.sub _ ha) _ (hS.sub _ hb) _ (hS.sub _ hc)
  · intro a ha b hb
    rw [hM ha hb, hM hb ha]
    exact hR.mulComm _ (hS.sub _ ha) _ (hS.sub _ hb)
  · intro a ha
    rw [hM ha hS.mem_one]
    exact hR.mul_one _ (hS.sub _ ha)
  · intro a ha b hb c hc
    rw [hA hb hc, hM ha (hS.add_closed b hb c hc), hM ha hb, hM ha hc,
      hA (hS.mul_closed a ha b hb) (hS.mul_closed a ha c hc)]
    exact hR.distrib _ (hS.sub _ ha) _ (hS.sub _ hb) _ (hS.sub _ hc)

/-- The image of a field under an embedding is a field, with the ambient
operations restricted to it.

The inverse of an image is the image of the inverse, and injectivity is what
turns `app e a ≠ zero₂` back into `a ≠ zero₁` -- so nothing is chosen and the
ambient ring is not required to be a field. -/
theorem isField_imageIn_of_embedding
    {e R₁ add₁ mul₁ zero₁ one₁ R₂ add₂ mul₂ zero₂ one₂ : ZFSet.{u}}
    (h₁ : IsField R₁ add₁ mul₁ zero₁ one₁) (h₂ : IsRing R₂ add₂ mul₂ zero₂ one₂)
    (he : IsEmbedding e R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂) :
    IsField (imageIn e R₁ R₂) (restrictOp add₂ (imageIn e R₁ R₂))
      (restrictOp mul₂ (imageIn e R₁ R₂)) zero₂ one₂ := by
  have hsub := isSubring_imageIn he.left h₁.ring h₂
  refine ⟨isRing_subring h₂ hsub, ?_, ?_⟩
  · intro hzo
    refine h₁.zero_ne_one (he.right _ h₁.ring.addGroup.mem_e _ h₁.ring.mem_one ?_)
    rw [hom_zero he.left h₁.ring h₂, hom_one he.left, hzo]
  · intro x hx hne
    obtain ⟨-, a, ha, rfl⟩ := (mem_imageIn_iff _ _ _ _).mp hx
    have hane : a ≠ zero₁ := by
      intro hz
      exact hne (by rw [hz, hom_zero he.left h₁.ring h₂])
    obtain ⟨b, hb, hab⟩ := h₁.inverses a ha hane
    have hbi : app e b ∈ imageIn e R₁ R₂ :=
      (mem_imageIn_iff _ _ _ _).mpr ⟨hom_app_mem he.left hb, b, hb, rfl⟩
    refine ⟨app e b, hbi, ?_⟩
    rw [opAt_subring_mul h₂ hsub hx hbi, ← hom_mul' he.left a ha b hb, hab,
      hom_one he.left]

/-- Deciding vanishing transports along an embedding, through injectivity
rather than through any decision: an image vanishes exactly when its preimage
does. -/
theorem decidableVanishing_imageIn_of_embedding
    {e R₁ add₁ mul₁ zero₁ one₁ R₂ add₂ mul₂ zero₂ one₂ : ZFSet.{u}}
    (h₁ : IsRing R₁ add₁ mul₁ zero₁ one₁) (h₂ : IsRing R₂ add₂ mul₂ zero₂ one₂)
    (he : IsEmbedding e R₁ add₁ mul₁ one₁ R₂ add₂ mul₂ one₂)
    (hdec : DecidableVanishing R₁ zero₁) :
    DecidableVanishing (imageIn e R₁ R₂) zero₂ := by
  intro x hx
  obtain ⟨-, a, ha, rfl⟩ := (mem_imageIn_iff _ _ _ _).mp hx
  rcases hdec a ha with hz | hne
  · exact Or.inl (by rw [hz, hom_zero he.left h₁ h₂])
  · refine Or.inr (fun heq => hne (he.right a ha _ h₁.addGroup.mem_e ?_))
    rw [heq, hom_zero he.left h₁ h₂]

/-! ## The characteristic

The additive order of `one` in a finite field. It is prime, because a proper
factorisation would give a product of two non-zero elements equal to zero. -/

/-- Negating zero gives zero, over the non-commutative base. Purely a
statement about the additive group, which `IsRingNC` leaves untouched. -/
theorem ringNeg_zero_nc {R add mul zero one : ZFSet.{u}}
    (h : IsRingNC R add mul zero one) :
    ringNeg R add zero zero = zero :=
  inv_unique h.addGroup h.addGroup.mem_e (ringNeg_mem_nc h h.addGroup.mem_e)
    h.addGroup.mem_e (ringAdd_neg_nc h h.addGroup.mem_e)
    (ringAdd_zero_nc h h.addGroup.mem_e)

#print axioms Algebra.ringNeg_zero_nc
/-! ## Prime ideals

The quotient by a prime ideal has no zero divisors, so when it is also finite it
is a field. That is the field criterion this development uses -- no division
algorithm anywhere. -/

def IsPrimeIdeal (I R add mul zero one : ZFSet.{u}) : Prop :=
  IsIdeal I R add mul zero ∧ one ∉ I ∧
    ∀ a, a ∈ R → ∀ b, b ∈ R → opAt mul a b ∈ I → a ∈ I ∨ b ∈ I


theorem ringNeg_zero {R add mul zero one : ZFSet.{u}} (h : IsRing R add mul zero one) :
    ringNeg R add zero zero = zero :=
  ringNeg_zero_nc h.toNC

theorem ringNsmul_add {R add mul zero one a b : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) :
    ∀ k : Nat, gpow add zero (opAt add a b) k
      = opAt add (gpow add zero a k) (gpow add zero b k) :=
  gpow_opAt h.addGroup h.addComm ha hb
theorem ringSub_zero {R add mul zero one a : ZFSet.{u}} (h : IsRing R add mul zero one)
    (ha : a ∈ R) : ringSub R add zero a zero = a := by
  show opAt add a (ringNeg R add zero zero) = a
  rw [ringNeg_zero h, ringAdd_zero h ha]

/-- A class is zero exactly when its representative is in the ideal. -/
theorem cls_eq_zero_iff {I R add mul zero one a : ZFSet.{u}} (h : IsRing R add mul zero one)
    (hI : IsIdeal I R add mul zero) (ha : a ∈ R) :
    cls (idealRel R add zero I) R a = cls (idealRel R add zero I) R zero ↔ a ∈ I := by
  refine Iff.trans (cls_eq_cls_iff (isCongruence_idealRel_add h hI).left ha
    h.addGroup.mem_e) ?_
  rw [opair_mem_idealRel_iff ha h.addGroup.mem_e, ringSub_zero h ha]

/-! ## The first isomorphism theorem -/

/-- The quotient by a prime ideal is a field, if it is finite. -/
theorem isField_quotient_of_prime {I R add mul zero one : ZFSet.{u}}
    (h : IsRing R add mul zero one) (hP : IsPrimeIdeal I R add mul zero one)
    {n : Nat} (hfin : Equinumerous (quotientSet (idealRel R add zero I) R) (ofNat.{u} n)) :
    IsField (quotientSet (idealRel R add zero I) R)
      (congOp (idealRel R add zero I) R add) (congOp (idealRel R add zero I) R mul)
      (cls (idealRel R add zero I) R zero) (cls (idealRel R add zero I) R one) := by
  have hI := hP.left
  have hQ := isRing_quotientByIdeal h hI
  refine isField_of_finite_domain hQ (fun he => hP.right.left ?_) (fun A hA B hB hAB => ?_) hfin
  · exact (cls_eq_zero_iff h hI h.mem_one).mp he.symm
  · obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
    obtain ⟨b, hb, rfl⟩ := (mem_quotientSet_iff _ _ B).mp hB
    rw [opAt_congOp (fun x hx y hy => mulAt_mem h hx hy) (isCongruence_idealRel_mul h hI) ha hb,
      cls_eq_zero_iff h hI (mulAt_mem h ha hb)] at hAB
    rcases hP.right.right a ha b hb hAB with hmem | hmem
    · exact Or.inl ((cls_eq_zero_iff h hI ha).mpr hmem)
    · exact Or.inr ((cls_eq_zero_iff h hI hb).mpr hmem)

/-! ## Audit -/

#print axioms ringNsmul_zero
#print axioms ringNsmul_add
#print axioms ringNsmul_mul
#print axioms isField_of_finite_domain
#print axioms isField_quotient_of_prime
#print axioms isIdeal_ringMultiples
#print axioms isRing_quotientByIdeal
#print axioms isSubring_imageIn
#print axioms isSubring_imageIn_of_subring

#print axioms isField_imageIn_of_embedding
#print axioms decidableVanishing_imageIn_of_embedding
#print axioms stableVanishing_of_decidableVanishing
#print axioms isRing_congQuotient
#print axioms isRingHom_id
#print axioms isEmbedding_id
#print axioms imageIn_id

/-- The pairwise combinations of two subsets under one operation:
`{ a op b : a ∈ I, b ∈ J }`, carved out of `R`.

Named once because it IS one construction. `idealSum` and `idealProdGens` were
written separately -- the same body with `add` in one and `mul` in the other.
The operation was already a parameter in both; only the name suggested
otherwise. -/
def pairwiseOp (R op I J : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun w => ∃ a, a ∈ I ∧ ∃ b, b ∈ J ∧ w = opAt op a b) R

/-- `I + J`, the pairwise sums. -/
def idealSum (R add I J : ZFSet.{u}) : ZFSet.{u} := pairwiseOp R add I J

/-- And back, where the unit enters: `a ∈ (a)` needs `a = a·1`. -/
theorem mem_ringMultiples_self {R add mul zero one a : ZFSet.{u}}
    (h : IsRing R add mul zero one) (ha : a ∈ R) :
    a ∈ ringMultiples R mul a :=
  (mem_ringMultiples_iff _ _ _ _).mpr ⟨ha, one, h.mem_one, (h.mul_one a ha).symm⟩

/-! ## Maximal ideals -/

/-- The ideal generated by `S`: everything in every ideal that contains `S`. -/
def genIdeal (R add mul zero S : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun x => ∀ I, I ∈ powerset R -> IsIdeal I R add mul zero -> S ⊆ I -> x ∈ I) R

/-! ## The product of two ideals -/

/-- The products `ab` with `a ∈ I` and `b ∈ J`, before any sums are taken --
`pairwiseOp` at the multiplication. -/
def idealProdGens (R mul I J : ZFSet.{u}) : ZFSet.{u} := pairwiseOp R mul I J

/-- `I · J`. -/
def idealProd (R add mul zero I J : ZFSet.{u}) : ZFSet.{u} :=
  genIdeal R add mul zero (idealProdGens R mul I J)

/-! ## Invertibility, and the one hypothesis that makes the monoid a group

Everything above is a commutative MONOID. What separates it from the class
GROUP is inverses, and the hypothesis that supplies them has a name.

An ideal is invertible when some ideal multiplies it into a non-zero principal
ideal. That is weaker than the fractional-ideal definition and is all the class
group needs: a principal ideal is the identity class, so `I · J` principal means
`cls I` and `cls J` are inverse.

This section reduces the class set is a group to exactly one property, and
that property is now proved for a Dedekind domain. `isInvertibleIdeal_top` and
`isInvertibleIdeal_of_maximal_subset` are here; the maximal case is
`isInvertibleIdeal_of_isMaximalIdeal`, the general one
`isInvertibleIdeal_of_primeProductList` and
`isInvertibleIdeal_of_primeProduct_dedekind`, both in `Integral.lean`. The
class inverse is then `cls_inverse_of_invertible` applied to one of those --
one line, so it is composed at the point of use rather than named again.

No norm is involved. The route is the determinant trick on a stabilised
span and then an induction on the length of a prime product; the only
arithmetic input is the domain clause. What it costs is the maximal case's
three decisions and one further disjunction -- for an ideal above the one being
proved, either `one` is in it or a maximal ideal lies above it. -/

/-- Some ideal carries `I` into a non-zero principal ideal. -/
def IsInvertibleIdeal (R add mul zero I : ZFSet.{u}) : Prop :=
  ∃ J, IsIdeal J R add mul zero ∧ ∃ c, c ∈ R ∧ c ≠ zero ∧
    idealProd R add mul zero I J = ringMultiples R mul c

#print axioms pairwiseOp
#print axioms idealSum
#print axioms genIdeal
#print axioms idealProd
#print axioms IsInvertibleIdeal
/-! ### What a Bezout pair does to a vector

Row 1870. The identity is a statement about matrices; the decomposition needs
it as a statement about a VECTOR. Applying it to `v` writes `D^e v` as a sum of
two vectors, and the point of the whole construction is that each summand is
killed by one of the two factors --- so the sum is a splitting into the two
generalised eigenspaces, up to the accumulated power of `D`.

Each summand dies for the same reason: the coefficient in front commutes past
the power that must reach `v`, leaving `L^k * M^m` innermost, where the
hypothesis applies. That is the fourth and last use of the commutation
conjuncts, and the one they were introduced for. -/

/-- `restrictLeft` agrees with the operation when the left factor is a
subring.

The four-line discharge this replaces was written once in `GeomTower.lean` and
three times in `CycIntegrallyClosed.lean`, each time with the same two side
conditions: the domain clause from `hR.mulDom` and closure from `mulAt_mem`.
Both follow from `IsRing` and `IsSubring` alone, so no caller was supplying
anything its hypotheses did not already carry. -/
theorem opAt_restrictLeft_of_isSubring {S R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hSub : IsSubring S R add mul zero one)
    {c w : ZFSet.{u}} (hc : c ∈ S) (hw : w ∈ R) :
    opAt (restrictLeft mul S R) c w = opAt mul c w :=
  opAt_restrictLeft hR.mulFun
    (fun z hz => by
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff z _ _).mp hz
      rw [hR.mulDom]; exact opair_mem_prod (hSub.sub _ ha) hb)
    (fun a ha b hb => mulAt_mem hR (hSub.sub _ ha) hb) hc hw

/-- The subring restriction, quantified.

`opAt_restrictLeft_of_isSubring` at both arguments, which seven proofs in
`CycIntegrallyClosed.lean` restate as a four-line `have` before using it. Eta
expansion, no mathematics: the value of the name is that the STATEMENT stops
being written out. -/
theorem opAt_restrictLeft_bridge {S R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hSub : IsSubring S R add mul zero one) :
    ∀ a, a ∈ S → ∀ b, b ∈ R →
      opAt (restrictLeft mul S R) a b = opAt mul a b :=
  fun _ ha _ hb => opAt_restrictLeft_of_isSubring hR hSub ha hb

#print axioms opAt_restrictLeft_of_isSubring

/-- Every entry of `powerList` lies in the ring.

The four-line discharge this replaces stands at the head of four proofs --- once
in `GeomTower.lean`, three times in `CycIntegrallyClosed.lean` --- and in every
one it feeds `isSubmodule_spanSet` and `exists_coeffs_len_of_mem_spanSet`, which
both demand exactly this membership. It asks nothing of the subring: `IsRing`
and `x ∈ R` are the whole of it, so the four copies could each be
written without reference to their surroundings. -/
theorem powerList_subset_ring {R add mul zero one x : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hx : x ∈ R) (d : Nat) :
    ∀ v, v ∈ powerList mul one x d → v ∈ R := by
  intro v hv
  obtain ⟨i, _, he⟩ := (mem_powerList d v).mp hv
  exact he ▸ ringPow_mem hR hx i

#print axioms powerList_subset_ring

end Algebra
#print axioms Algebra.StableVanishing
namespace ZFSet
export Algebra (DecidableVanishing IsCommSemiring IsEmbedding IsField IsIdeal IsInvertibleIdeal IsPrimeIdeal IsRing IsRingHom IsRingNC IsSemiring IsSubring StableVanishing addAt_mem addAt_mem_nc addAt_mem_semi cls_eq_zero_iff decidableVanishing_imageIn_of_embedding field_mul_eq_zero genIdeal gpow_zero_eq_zero hom_add hom_add' hom_app_mem hom_mul hom_mul' hom_neg hom_one hom_pow hom_zero idealProd idealProdGens idealRel idealSum ideal_absorbs ideal_add ideal_inverse ideal_mem_zero ideal_neg_mem ideal_neg_mem_nc ideal_subset imageIn_id isCommSemiring_of_isRing isCongruence_idealRel_add isCongruence_idealRel_add_nc isCongruence_idealRel_mul isEmbedding_id isField_imageIn_of_embedding isField_of_finite_domain isField_quotient_of_prime isIdeal_ringMultiples isRingHom_id isRing_congQuotient isRing_quotientByIdeal isRing_subring isSubring_imageIn isSubring_imageIn_of_subring mem_ringMultiples_iff mem_ringMultiples_self mulAt_mem mulAt_mem_nc mulAt_mem_semi mul_zero_of_isRing mul_zero_of_isRingNC natIn opAt_restrictLeft_of_isSubring opAt_subring_add opAt_subring_mul opair_mem_idealRel_iff pairwiseOp powerList_subset_ring ringAdd_assoc ringAdd_assoc_nc ringAdd_comm ringAdd_comm_nc ringAdd_left_comm ringAdd_neg ringAdd_neg_nc ringAdd_shuffle_pair ringAdd_shuffle_pair_nc ringAdd_sub_cancel ringAdd_zero ringAdd_zero_nc ringMul_neg ringMul_neg_nc ringMul_shuffle_pair ringMul_sub ringMultiples ringNeg ringNegOne_mul ringNegOne_mul_nc ringNegOne_pow ringNeg_add ringNeg_addAt ringNeg_addAt_nc ringNeg_add_nc ringNeg_eq_of_add_zero ringNeg_mem ringNeg_mem_nc ringNeg_mul ringNeg_mul_nc ringNeg_neg ringNeg_neg_nc ringNeg_zero ringNeg_zero_nc ringNsmul ringNsmul_add ringNsmul_def ringNsmul_mem ringNsmul_mem_semi ringNsmul_mul ringNsmul_mul_semi ringNsmul_succ ringNsmul_sum ringNsmul_sum_semi ringNsmul_zero ringOne_mul ringOne_mul_nc ringOne_pow ringPow ringPow_add ringPow_def ringPow_mem ringPow_mem_semi ringPow_mul ringPow_succ ringRight_distrib ringRight_distrib_nc ringSub ringSub_addAt_nc ringSub_def ringSub_eq_zero_iff ringSub_mem ringSub_mem_nc ringSub_mul ringSub_mulAt ringSub_self ringSub_self_nc ringSub_swap ringSub_swap_nc ringSub_trans ringSub_trans_nc ringSub_zero ringZero_add ringZero_add_nc ringZero_mul stableVanishing_of_decidableVanishing units zero_mul_of_isRingNC)
end ZFSet
