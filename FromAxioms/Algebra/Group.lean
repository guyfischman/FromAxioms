/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Groups.

The algebra track opens here, at Cayley's 1854 row: a group is a set `G`
together with a set function `op : G × G → G`, an identity, associativity and
inverses. Stating it over set functions rather than Lean functions is the same
choice `Relation.lean` makes for injections: only a set function
can be quantified over inside the theory, which is what "the set of all groups
on `G`" would need.

`Integer.lean` has had an abelian group in it since it was written --
`intAdd`, `intZero`, `intNeg`, with associativity, identity and inverses all
proved. What is new here is only the recognition: packaging the operation as a
set of pairs and reading the existing lemmas through `app`.

Everything is `[propext, Quot.sound]`. Nothing about groups needs a decision:
the operation is given, not chosen.
-/

import FromAxioms.Core.CoreShim
import FromAxioms.SetTheory.Cardinal

universe u

open Core NumberTheory SetTheory
namespace Algebra

/-- A monoid: associative, with a two-sided identity. No inverses.

`IsGroup` extends this, so a group IS a monoid with inverses and the order
arithmetic below is stated where it belongs. Every proof in that family uses
`assoc`, `left_id` and `right_id` only, which the kernel checks. -/
structure IsMonoid (M op e : ZFSet.{u}) : Prop where
  isFun : IsFunction op
  dom : domain op = prod M M
  ran : range op ⊆ M
  mem_e : e ∈ M
  assoc : ∀ a, a ∈ M → ∀ b, b ∈ M → ∀ c, c ∈ M →
    opAt op (opAt op a b) c = opAt op a (opAt op b c)
  left_id : ∀ a, a ∈ M → opAt op e a = a
  right_id : ∀ a, a ∈ M → opAt op a e = a

theorem opAt_mem_bare {M op e a b : ZFSet.{u}} (h : IsMonoid M op e)
    (ha : a ∈ M) (hb : b ∈ M) : opAt op a b ∈ M :=
  h.ran _ (app_mem_range h.isFun (by rw [h.dom]; exact opair_mem_prod ha hb))


/-- A group: a set, a binary set function on it, and an identity element. -/
structure IsGroup (G op e : ZFSet.{u}) extends IsMonoid G op e : Prop where
  inverses : ∀ a, a ∈ G → ∃ b, b ∈ G ∧ opAt op a b = e ∧ opAt op b a = e

/-- Forget the inverses. `IsGroup` extends `IsMonoid`, so this is a projection
rather than a construction; the fields are named one by one because the
parent's are inherited flat and callers reach for this by name. -/
theorem IsGroup.toMonoid {G op e : ZFSet.{u}} (h : IsGroup G op e) :
    IsMonoid G op e :=
  { isFun := h.isFun, dom := h.dom, ran := h.ran, mem_e := h.mem_e,
    assoc := h.assoc, left_id := h.left_id, right_id := h.right_id }

/-- The operation lands in `G`, which the axioms use constantly. -/
theorem opAt_mem {G op e a b : ZFSet.{u}} (h : IsGroup G op e) (ha : a ∈ G)
    (hb : b ∈ G) : opAt op a b ∈ G :=
  h.ran _ (app_mem_range h.isFun (by rw [h.dom]; exact opair_mem_prod ha hb))

/-- Inverses are unique, so "the" inverse is well defined -- extracted from a
singleton rather than chosen. -/
theorem inv_unique {G op e a b c : ZFSet.{u}} (h : IsGroup G op e) (ha : a ∈ G)
    (hb : b ∈ G) (hc : c ∈ G) (h₁ : opAt op a b = e) (h₂ : opAt op c a = e) :
    b = c := by
  have hstep : opAt op (opAt op c a) b = opAt op c (opAt op a b) := h.assoc c hc a ha b hb
  rw [h₁, h₂, h.left_id b hb, h.right_id c hc] at hstep
  exact hstep

/-! ## Abelian groups -/

def IsAbelian (G op : ZFSet.{u}) : Prop :=
  ∀ a, a ∈ G → ∀ b, b ∈ G → opAt op a b = opAt op b a

/-! ## ℤ under addition

The operation is `graphOn` of the Lean-level `intAdd` composed with the pair
projections, so `app` computes and the `Integer.lean` lemmas apply directly. -/

def intAddOp : ZFSet.{u} :=
  graphOn (prod NumberTheory.Int.{u} NumberTheory.Int.{u}) NumberTheory.Int.{u} (fun z => intAdd (fst z) (snd z))

private theorem intAdd_maps {z : ZFSet.{u}} (hz : z ∈ prod NumberTheory.Int.{u} NumberTheory.Int.{u}) :
    intAdd (fst z) (snd z) ∈ NumberTheory.Int.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff z _ _).mp hz
  rw [fst_opair, snd_opair]
  exact intAdd_mem_Int ha hb

theorem opAt_intAddOp {a b : ZFSet.{u}} (ha : a ∈ NumberTheory.Int.{u}) (hb : b ∈ NumberTheory.Int.{u}) :
    opAt intAddOp.{u} a b = intAdd a b := by
  rw [opAt, intAddOp, app_graphOn (fun _ hm => intAdd_maps hm) (opair_mem_prod ha hb),
    fst_opair, snd_opair]

/-- ℤ is a group under addition. -/
theorem isGroup_intAdd : IsGroup NumberTheory.Int.{u} intAddOp.{u} intZero.{u} where
  isFun := graphOn_isFunction _ _ _
  dom := graphOn_domain (fun _ hm => intAdd_maps hm)
  ran := by
    intro v hv
    obtain ⟨w, hw⟩ := (mem_range_iff v _).mp hv
    exact mem_prod_right (graphOn_subset _ _ _ _ hw)
  mem_e := intZero_mem_Int
  assoc a ha b hb c hc := by
    rw [opAt_intAddOp ha hb, opAt_intAddOp (intAdd_mem_Int ha hb) hc,
      opAt_intAddOp hb hc, opAt_intAddOp ha (intAdd_mem_Int hb hc)]
    exact intAdd_assoc ha hb hc
  left_id a ha := by
    rw [opAt_intAddOp intZero_mem_Int ha, intAdd_comm intZero_mem_Int ha, intAdd_zero ha]
  right_id a ha := by
    rw [opAt_intAddOp ha intZero_mem_Int, intAdd_zero ha]
  inverses a ha := by
    refine ⟨intNeg a, intNeg_mem_Int ha, ?_, ?_⟩
    · rw [opAt_intAddOp ha (intNeg_mem_Int ha)]
      exact intAdd_neg ha
    · rw [opAt_intAddOp (intNeg_mem_Int ha) ha,
        intAdd_comm (intNeg_mem_Int ha) ha]
      exact intAdd_neg ha

theorem isAbelian_intAdd : IsAbelian NumberTheory.Int.{u} intAddOp.{u} := by
  intro a ha b hb
  rw [opAt_intAddOp ha hb, opAt_intAddOp hb ha]
  exact intAdd_comm ha hb

/-! ## Subgroups and homomorphisms

A subgroup is a subset containing the identity and closed under the operation
and inverses; a homomorphism is a set function that commutes with the two
operations. The theorem that ties them is that an image is a subgroup -- which
is how `2ℤ` arrives below, without a separate closure argument. -/

def IsSubgroup (H G op e : ZFSet.{u}) : Prop :=
  H ⊆ G ∧ e ∈ H ∧ (∀ a, a ∈ H → ∀ b, b ∈ H → opAt op a b ∈ H) ∧
    (∀ a, a ∈ H → ∃ b, b ∈ H ∧ opAt op a b = e ∧ opAt op b a = e)

def IsHom (f G₁ op₁ G₂ op₂ : ZFSet.{u}) : Prop :=
  IsFunction f ∧ domain f = G₁ ∧ range f ⊆ G₂ ∧
    ∀ a, a ∈ G₁ → ∀ b, b ∈ G₁ → app f (opAt op₁ a b) = opAt op₂ (app f a) (app f b)

/-- The clause a proof actually reaches for: a homomorphism carries the
operation. The other three are `.left`, `.right.left` and `.right.right.left`,
which a reader can still count. -/
theorem isHom_op {f G₁ op₁ G₂ op₂ a b : ZFSet.{u}} (h : IsHom f G₁ op₁ G₂ op₂)
    (ha : a ∈ G₁) (hb : b ∈ G₁) :
    app f (opAt op₁ a b) = opAt op₂ (app f a) (app f b) := h.right.right.right a ha b hb

theorem app_mem_of_isHom {f G₁ op₁ G₂ op₂ a : ZFSet.{u}} (h : IsHom f G₁ op₁ G₂ op₂)
    (ha : a ∈ G₁) : app f a ∈ G₂ :=
  h.right.right.left _ (app_mem_range h.left (by rw [h.right.left]; exact ha))

/-- A homomorphism sends the identity to the identity: `f e · f e = f e`, and
cancelling on the left leaves `f e = e'`. -/
theorem hom_id {f G₁ op₁ e₁ G₂ op₂ e₂ : ZFSet.{u}} (h₁ : IsGroup G₁ op₁ e₁)
    (h₂ : IsGroup G₂ op₂ e₂) (h : IsHom f G₁ op₁ G₂ op₂) : app f e₁ = e₂ := by
  have hfe : app f e₁ ∈ G₂ := app_mem_of_isHom h h₁.mem_e
  obtain ⟨b, hb, hab, hba⟩ := h₂.inverses _ hfe
  have hstep : app f (opAt op₁ e₁ e₁) = opAt op₂ (app f e₁) (app f e₁) :=
    isHom_op h h₁.mem_e h₁.mem_e
  rw [h₁.left_id e₁ h₁.mem_e] at hstep
  -- multiply both sides by the inverse of `f e₁`
  have hcancel : opAt op₂ b (app f e₁) = opAt op₂ b (opAt op₂ (app f e₁) (app f e₁)) := by
    rw [← hstep]
  rw [hba, ← h₂.assoc b hb _ hfe _ hfe, hba, h₂.left_id _ hfe] at hcancel
  exact hcancel.symm

/-! ## Quotients by a congruence

A congruence is an equivalence relation the operation respects. Its classes then
carry an operation, built by separation -- representatives appear inside the
formula, never as a choice -- and the quotient is a group. `fibreRel` is the
instance a homomorphism supplies; `modRel` below is the instance `nℤ` supplies,
and the two give the first isomorphism theorem and `ℤ/nℤ` from one proof. -/

def IsCongruence (r G op : ZFSet.{u}) : Prop :=
  IsEquivRel r G ∧ ∀ a, a ∈ G → ∀ a', a' ∈ G → ∀ b, b ∈ G → ∀ b', b' ∈ G →
    opair a a' ∈ r → opair b b' ∈ r → opair (opAt op a b) (opAt op a' b') ∈ r

#print axioms IsGroup

def congOp (r G op : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => ∃ a, a ∈ G ∧ ∃ b, b ∈ G ∧
        z = opair (opair (cls r G a) (cls r G b)) (cls r G (opAt op a b)))
    (prod (prod (quotientSet r G) (quotientSet r G)) (quotientSet r G))

/-- Single-valuedness is the congruence property. The operation only has to
be closed, not to be a group's, so `Field.lean` reuses this for multiplication.
-/
theorem congOp_isFunction {r G op : ZFSet.{u}}
    (hclosed : ∀ a, a ∈ G → ∀ b, b ∈ G → opAt op a b ∈ G)
    (hr : IsCongruence r G op) : IsFunction (congOp r G op) := by
  constructor
  · intro z hz
    obtain ⟨-, a, ha, b, hb, he⟩ := (mem_sep_iff _ z _).mp hz
    exact ⟨_, _, he⟩
  · intro p v v' hv hv'
    obtain ⟨-, a, ha, b, hb, he⟩ := (mem_sep_iff _ _ _).mp hv
    obtain ⟨-, a', ha', b', hb', he'⟩ := (mem_sep_iff _ _ _).mp hv'
    obtain ⟨hpair, rfl⟩ := opair_injective he
    obtain ⟨hpair', rfl⟩ := opair_injective he'
    obtain ⟨hca, hcb⟩ := opair_injective (hpair.symm.trans hpair')
    exact (cls_eq_cls_iff hr.left (hclosed a ha b hb) (hclosed a' ha' b' hb')).mpr
      (hr.right a ha a' ha' b hb b' hb'
        ((cls_eq_cls_iff hr.left ha ha').mp hca)
        ((cls_eq_cls_iff hr.left hb hb').mp hcb))

theorem opAt_congOp {r G op a b : ZFSet.{u}}
    (hclosed : ∀ a, a ∈ G → ∀ b, b ∈ G → opAt op a b ∈ G)
    (hr : IsCongruence r G op) (ha : a ∈ G) (hb : b ∈ G) :
    opAt (congOp r G op) (cls r G a) (cls r G b) = cls r G (opAt op a b) :=
  app_eq (congOp_isFunction hclosed hr) ((mem_sep_iff _ _ _).mpr
    ⟨opair_mem_prod (opair_mem_prod (cls_mem_quotientSet ha) (cls_mem_quotientSet hb))
      (cls_mem_quotientSet (hclosed a ha b hb)), a, ha, b, hb, rfl⟩)

/-- The domain and range of the induced operation, which the ring case needs
separately. -/
theorem congOp_domain {r G op : ZFSet.{u}}
    (hclosed : ∀ a, a ∈ G → ∀ b, b ∈ G → opAt op a b ∈ G) :
    domain (congOp r G op) = prod (quotientSet r G) (quotientSet r G) := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨v, hv⟩ := (mem_domain_iff p _).mp hp
    obtain ⟨hprod, -⟩ := (mem_sep_iff _ _ _).mp hv
    exact mem_prod_left hprod
  · obtain ⟨A, hA, B, hB, rfl⟩ := (mem_prod_iff p _ _).mp hp
    obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
    obtain ⟨b, hb, rfl⟩ := (mem_quotientSet_iff _ _ B).mp hB
    exact (mem_domain_iff _ _).mpr ⟨_, (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod (opair_mem_prod hA hB)
        (cls_mem_quotientSet (hclosed a ha b hb)), a, ha, b, hb, rfl⟩⟩

theorem congOp_range {r G op : ZFSet.{u}} :
    range (congOp r G op) ⊆ quotientSet r G := by
  intro v hv
  obtain ⟨p, hp⟩ := (mem_range_iff v _).mp hv
  obtain ⟨hprod, -⟩ := (mem_sep_iff _ _ _).mp hp
  exact mem_prod_right hprod

/-- The quotient by a congruence is a group. -/
theorem isGroup_congQuotient {r G op e : ZFSet.{u}} (h₁ : IsGroup G op e)
    (hr : IsCongruence r G op) :
    IsGroup (quotientSet r G) (congOp r G op) (cls r G e) where
  isFun := congOp_isFunction (fun a ha b hb => opAt_mem h₁ ha hb) hr
  dom := congOp_domain (fun a ha b hb => opAt_mem h₁ ha hb)
  ran := congOp_range
  mem_e := cls_mem_quotientSet h₁.mem_e
  assoc A hA B hB C hC := by
    obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
    obtain ⟨b, hb, rfl⟩ := (mem_quotientSet_iff _ _ B).mp hB
    obtain ⟨c, hc, rfl⟩ := (mem_quotientSet_iff _ _ C).mp hC
    rw [opAt_congOp (fun a ha b hb => opAt_mem h₁ ha hb) hr ha hb, opAt_congOp (fun a ha b hb => opAt_mem h₁ ha hb) hr (opAt_mem h₁ ha hb) hc,
      opAt_congOp (fun a ha b hb => opAt_mem h₁ ha hb) hr hb hc, opAt_congOp (fun a ha b hb => opAt_mem h₁ ha hb) hr ha (opAt_mem h₁ hb hc),
      h₁.assoc a ha b hb c hc]
  left_id A hA := by
    obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
    rw [opAt_congOp (fun a ha b hb => opAt_mem h₁ ha hb) hr h₁.mem_e ha, h₁.left_id a ha]
  right_id A hA := by
    obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
    rw [opAt_congOp (fun a ha b hb => opAt_mem h₁ ha hb) hr ha h₁.mem_e, h₁.right_id a ha]
  inverses A hA := by
    obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
    obtain ⟨b, hb, hab, hba⟩ := h₁.inverses a ha
    refine ⟨cls r G b, cls_mem_quotientSet hb, ?_, ?_⟩
    · rw [opAt_congOp (fun a ha b hb => opAt_mem h₁ ha hb) hr ha hb, hab]
    · rw [opAt_congOp (fun a ha b hb => opAt_mem h₁ ha hb) hr hb ha, hba]

/-! ## Cosets

`a ~ b` when `b = a·h` for some `h` in the subgroup. The relation is an
equivalence, and left translation puts the subgroup in bijection with each of
its classes -- so all cosets are the same size, which is the half of Lagrange's
theorem that does not need counting. -/

theorem op_left_cancel {G op e a b c : ZFSet.{u}} (h : IsGroup G op e) (ha : a ∈ G)
    (hb : b ∈ G) (hc : c ∈ G) (he : opAt op a b = opAt op a c) : b = c := by
  obtain ⟨a', ha', haa', ha'a⟩ := h.inverses a ha
  have hstep : opAt op (opAt op a' a) b = opAt op (opAt op a' a) c := by
    rw [h.assoc a' ha' a ha b hb, h.assoc a' ha' a ha c hc, he]
  rw [ha'a, h.left_id b hb, h.left_id c hc] at hstep
  exact hstep

def cosetRel (H G op : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => ∃ a, a ∈ G ∧ ∃ b, b ∈ G ∧ z = opair a b ∧
        ∃ h, h ∈ H ∧ b = opAt op a h) (prod G G)

theorem opair_mem_cosetRel_iff {H G op a b : ZFSet.{u}} (ha : a ∈ G) (hb : b ∈ G) :
    opair a b ∈ cosetRel H G op ↔ ∃ h, h ∈ H ∧ b = opAt op a h := by
  refine Iff.trans (mem_sep_iff _ _ _) ⟨?_, ?_⟩
  · rintro ⟨-, a', ha', b', hb', he, hh⟩
    obtain ⟨rfl, rfl⟩ := opair_injective he
    exact hh
  · rintro ⟨h, hh, he⟩
    exact ⟨opair_mem_prod ha hb, a, ha, b, hb, rfl, h, hh, he⟩

theorem isEquivRel_cosetRel {H G op e : ZFSet.{u}} (hG : IsGroup G op e)
    (hH : IsSubgroup H G op e) : IsEquivRel (cosetRel H G op) G where
  refl a ha := (opair_mem_cosetRel_iff ha ha).mpr
    ⟨e, hH.right.left, (hG.right_id a ha).symm⟩
  symm a b ha hb hab := by
    obtain ⟨h, hh, rfl⟩ := (opair_mem_cosetRel_iff ha hb).mp hab
    obtain ⟨h', hh', hhh', -⟩ := hH.right.right.right h hh
    refine (opair_mem_cosetRel_iff hb ha).mpr ⟨h', hh', ?_⟩
    rw [hG.assoc a ha h (hH.left h hh) h' (hH.left h' hh'), hhh', hG.right_id a ha]
  trans a b c ha hb hc hab hbc := by
    obtain ⟨h, hh, rfl⟩ := (opair_mem_cosetRel_iff ha hb).mp hab
    obtain ⟨h', hh', rfl⟩ := (opair_mem_cosetRel_iff hb hc).mp hbc
    refine (opair_mem_cosetRel_iff ha hc).mpr
      ⟨opAt op h h', hH.right.right.left h hh h' hh', ?_⟩
    exact hG.assoc a ha h (hH.left h hh) h' (hH.left h' hh')

/-! ## The inverse as a set function, and a section of the quotient

Two things Lagrange's counting step needs. The inverse map is definable because
inverses are unique (`inv_unique`), so no choice is involved; the section comes
from `finite_choice`, which is a theorem. -/

def invMap (G op e : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => ∃ a, a ∈ G ∧ ∃ b, b ∈ G ∧ z = opair a b ∧
        opAt op a b = e ∧ opAt op b a = e) (prod G G)

theorem invMap_isFunction {G op e : ZFSet.{u}} (h : IsGroup G op e) :
    IsFunction (invMap G op e) := by
  constructor
  · intro z hz
    obtain ⟨-, a, -, b, -, he, -⟩ := (mem_sep_iff _ z _).mp hz
    exact ⟨_, _, he⟩
  · intro a b b' hb hb'
    obtain ⟨-, c, hc, d, hd, he, hcd, hdc⟩ := (mem_sep_iff _ _ _).mp hb
    obtain ⟨-, c', hc', d', hd', he', hcd', hdc'⟩ := (mem_sep_iff _ _ _).mp hb'
    obtain ⟨rfl, rfl⟩ := opair_injective he
    obtain ⟨rfl, rfl⟩ := opair_injective he'
    exact inv_unique h hc hd hd' hcd hdc'

theorem app_invMap {G op e a : ZFSet.{u}} (h : IsGroup G op e) (ha : a ∈ G) :
    app (invMap G op e) a ∈ G ∧ opAt op a (app (invMap G op e) a) = e ∧
      opAt op (app (invMap G op e) a) a = e := by
  obtain ⟨b, hb, hab, hba⟩ := h.inverses a ha
  have he : app (invMap G op e) a = b :=
    app_eq (invMap_isFunction h) ((mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod ha hb, a, ha, b, hb, rfl, hab, hba⟩)
  rw [he]
  exact ⟨hb, hab, hba⟩

/-- A section of the quotient map, given that there are finitely many
cosets. `finite_choice` supplies it -- no axiom. -/
theorem exists_coset_section {H G op e : ZFSet.{u}} (hG : IsGroup G op e)
    (hH : IsSubgroup H G op e)
    (hfin : IsFinite (quotientSet (cosetRel H G op) G)) :
    ∃ s, IsFunction s ∧ domain s = quotientSet (cosetRel H G op) G ∧
      ∀ C, C ∈ quotientSet (cosetRel H G op) G → app s C ∈ C := by
  have hid : ∀ C, C ∈ quotientSet (cosetRel H G op) G →
      app (idOn (quotientSet (cosetRel H G op) G)) C = C := fun C hC => app_idOn hC
  obtain ⟨s, hs, hsdom, hsspec⟩ := finite_choice hfin
    (isInjection_idOn _).left (isInjection_idOn _).right.left (fun C hC => by
      rw [hid C hC]
      obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ C).mp hC
      exact ⟨a, mem_cls_self (isEquivRel_cosetRel hG hH) ha⟩)
  refine ⟨s, hs, hsdom, fun C hC => ?_⟩
  have := hsspec C hC
  rwa [hid C hC] at this

/-! ## Lagrange

`a ↦ ⟨aH, s(aH)⁻¹·a⟩` is a bijection `G → (G/H) × H`, with inverse
`⟨C, h⟩ ↦ s C · h`. Everything it needs is now in place, and the second
component lands in `H` for the reason the coset relation was set up to give:
`s(aH) = a·h`, so `s(aH)⁻¹·a = h⁻¹`. -/

theorem cls_eq_of_mem {r x a b : ZFSet.{u}} (h : IsEquivRel r x) (ha : a ∈ x)
    (hb : b ∈ cls r x a) : cls r x b = cls r x a :=
  (cls_eq_cls_iff h ((mem_cls_iff r x a b).mp hb).left ha).mpr
    (h.symm a b ha ((mem_cls_iff r x a b).mp hb).left ((mem_cls_iff r x a b).mp hb).right)

theorem lagrange_component {H G op e a b : ZFSet.{u}} (hG : IsGroup G op e)
    (hH : IsSubgroup H G op e) (ha : a ∈ G)
    (hsa : b ∈ cls (cosetRel H G op) G a) :
    opAt op (app (invMap G op e) b) a ∈ H := by
  have hbG : b ∈ G := ((mem_cls_iff _ _ _ b).mp hsa).left
  obtain ⟨h, hh, hba⟩ := (opair_mem_cosetRel_iff ha hbG).mp
    ((mem_cls_iff _ _ _ b).mp hsa).right
  obtain ⟨h', hh', hhh', hh'h⟩ := hH.right.right.right h hh
  have hhG := hH.left h hh
  have hh'G := hH.left h' hh'
  obtain ⟨hbinvG, hbb, hbb'⟩ := app_invMap hG hbG
  -- `a = b·h'`, and then `b⁻¹·a = h'`
  have hab : opAt op b h' = a := by
    rw [hba, hG.assoc a ha h hhG h' hh'G, hhh', hG.right_id a ha]
  have hfinal : opAt op (app (invMap G op e) b) a = h' := by
    rw [← hab, ← hG.assoc (app (invMap G op e) b) hbinvG b hbG h' hh'G, hbb',
      hG.left_id h' hh'G]
  rw [hfinal]
  exact hh'

/-- Lagrange's theorem, as a bijection: `G` is equinumerous with
`(G/H) × H`. -/
theorem equinumerous_prod_quotient {H G op e s : ZFSet.{u}} (hG : IsGroup G op e)
    (hH : IsSubgroup H G op e)
    (hsspec : ∀ C, C ∈ quotientSet (cosetRel H G op) G → app s C ∈ C) :
    Equinumerous G (prod (quotientSet (cosetRel H G op) G) H) := by
  have hrel := isEquivRel_cosetRel hG hH
  have hmem : ∀ a, a ∈ G → app s (cls (cosetRel H G op) G a) ∈ cls (cosetRel H G op) G a :=
    fun a ha => hsspec _ (cls_mem_quotientSet ha)
  have hmaps : ∀ a, a ∈ G →
      opair (cls (cosetRel H G op) G a)
        (opAt op (app (invMap G op e) (app s (cls (cosetRel H G op) G a))) a)
      ∈ prod (quotientSet (cosetRel H G op) G) H := fun a ha =>
    opair_mem_prod (cls_mem_quotientSet ha) (lagrange_component hG hH ha (hmem a ha))
  have happ : ∀ a, a ∈ G →
      app (graphOn G (prod (quotientSet (cosetRel H G op) G) H)
        (fun a => opair (cls (cosetRel H G op) G a)
          (opAt op (app (invMap G op e) (app s (cls (cosetRel H G op) G a))) a))) a
      = opair (cls (cosetRel H G op) G a)
          (opAt op (app (invMap G op e) (app s (cls (cosetRel H G op) G a))) a) :=
    fun a ha => app_graphOn hmaps ha
  refine ⟨_, ⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range, ?_⟩,
    ⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range, ?_⟩⟩
  · -- injective: equal classes give the same `s`, and then left cancellation
    intro a ha b hb he
    rw [happ a ha, happ b hb] at he
    obtain ⟨hcls, hcomp⟩ := opair_injective he
    rw [hcls] at hcomp
    obtain ⟨hinvG, -, -⟩ := app_invMap hG (((mem_cls_iff _ _ _ _).mp (hmem b hb)).left)
    exact op_left_cancel hG hinvG ha hb hcomp
  · -- surjective: `⟨C, h⟩` is the image of `s C · h`
    intro p hp
    obtain ⟨C, hC, h, hh, rfl⟩ := (mem_prod_iff p _ _).mp hp
    obtain ⟨c, hc, rfl⟩ := (mem_quotientSet_iff _ _ C).mp hC
    have hsc := hsspec _ hC
    have hscG : app s (cls (cosetRel H G op) G c) ∈ G :=
      ((mem_cls_iff _ _ _ _).mp hsc).left
    have hhG := hH.left h hh
    refine ⟨opAt op (app s (cls (cosetRel H G op) G c)) h,
      opAt_mem hG hscG hhG, ?_⟩
    rw [happ _ (opAt_mem hG hscG hhG)]
    -- the class is unchanged, so `s` returns the same representative
    have hclseq : cls (cosetRel H G op) G (opAt op (app s (cls (cosetRel H G op) G c)) h)
        = cls (cosetRel H G op) G c := by
      refine cls_eq_of_mem hrel hc ?_
      refine (mem_cls_iff _ _ _ _).mpr ⟨opAt_mem hG hscG hhG, ?_⟩
      obtain ⟨h₀, hh₀, hsc₀⟩ := (opair_mem_cosetRel_iff hc hscG).mp
        ((mem_cls_iff _ _ _ _).mp hsc).right
      refine (opair_mem_cosetRel_iff hc (opAt_mem hG hscG hhG)).mpr
        ⟨opAt op h₀ h, hH.right.right.left h₀ hh₀ h hh, ?_⟩
      rw [hsc₀, hG.assoc c hc h₀ (hH.left h₀ hh₀) h hhG]
    rw [hclseq]
    -- and the second component is `h` again
    obtain ⟨hinvG, hbb, hbb'⟩ := app_invMap hG hscG
    refine congrArg _ ?_
    rw [← hG.assoc (app (invMap G op e) (app s (cls (cosetRel H G op) G c))) hinvG
      (app s (cls (cosetRel H G op) G c)) hscG h hhG, hbb', hG.left_id h hhG]

/-- Lagrange's theorem. If a group has finitely many cosets of `H` and `H`
is finite, the group is finite and its order is the product. Every hypothesis is
about finiteness; nothing here is classical. -/
theorem lagrange {H G op e : ZFSet.{u}} (hG : IsGroup G op e)
    (hH : IsSubgroup H G op e) {k m : Nat}
    (hq : Equinumerous (quotientSet (cosetRel H G op) G) (ofNat.{u} k))
    (hHfin : Equinumerous H (ofNat.{u} m)) :
    Equinumerous G (ofNat.{u} (k * m)) := by
  obtain ⟨s, -, -, hsspec⟩ := exists_coset_section hG hH ⟨k, hq⟩
  refine equinumerous_trans (equinumerous_prod_quotient hG hH hsspec) ?_
  refine equinumerous_trans (equinumerous_prod hq hHfin) (equinumerous_prod_ofNat k m)

/-! ## Lagrange, constructively

The hypotheses `lagrange` needs are `|G/H| = k` and `|H| = m`. Both follow from
what a constructive algebraist would actually assume: `G` finite and membership
in `H` detachable. Detachability makes `H` finite and makes the
coset relation decidable, which makes the quotient a finite image
(`isFinite_imageIn`). -/

theorem quotientSet_eq_image (H G op : ZFSet.{u}) :
    imageIn (clsMap (cosetRel H G op) G) G (quotientSet (cosetRel H G op) G)
      = quotientSet (cosetRel H G op) G := by
  refine ext _ _ fun C => ⟨fun hC => (mem_imageIn_iff _ _ _ C).mp hC |>.left, fun hC => ?_⟩
  obtain ⟨a, ha, rfl⟩ := (mem_quotientSet_iff _ _ C).mp hC
  exact (mem_imageIn_iff _ G _ _).mpr ⟨hC, a, ha, (app_clsMap ha).symm⟩

/-- Detachable membership in `H` decides the coset relation, hence equality of
classes. -/
theorem cls_eq_or_ne_of_detachable {H G op e : ZFSet.{u}} (hG : IsGroup G op e)
    (hH : IsSubgroup H G op e)
    (hdet : ∀ a, a ∈ G → a ∈ H ∨ a ∉ H) {a b : ZFSet.{u}} (ha : a ∈ G) (hb : b ∈ G) :
    cls (cosetRel H G op) G a = cls (cosetRel H G op) G b ∨
      cls (cosetRel H G op) G a ≠ cls (cosetRel H G op) G b := by
  obtain ⟨hinvG, hinv, hinv'⟩ := app_invMap hG ha
  -- `a ~ b` exactly when `a⁻¹·b ∈ H`
  have hiff : opair a b ∈ cosetRel H G op ↔ opAt op (app (invMap G op e) a) b ∈ H := by
    constructor
    · rintro hr
      obtain ⟨h, hh, rfl⟩ := (opair_mem_cosetRel_iff ha hb).mp hr
      have hhG := hH.left h hh
      rw [← hG.assoc (app (invMap G op e) a) hinvG a ha h hhG, hinv',
        hG.left_id h hhG]
      exact hh
    · intro hmem
      refine (opair_mem_cosetRel_iff ha hb).mpr ⟨_, hmem, ?_⟩
      rw [← hG.assoc a ha (app (invMap G op e) a) hinvG b hb, hinv,
        hG.left_id b hb]
  rcases hdet _ (opAt_mem hG hinvG hb) with h | h
  · exact Or.inl ((cls_eq_cls_iff (isEquivRel_cosetRel hG hH) ha hb).mpr (hiff.mpr h))
  · exact Or.inr fun he => h (hiff.mp
      ((cls_eq_cls_iff (isEquivRel_cosetRel hG hH) ha hb).mp he))

/-- Lagrange, with constructive hypotheses: `G` finite and `H` detachable. -/
theorem lagrange_of_detachable {H G op e : ZFSet.{u}} (hG : IsGroup G op e)
    (hH : IsSubgroup H G op e) {n : Nat} (hGfin : Equinumerous G (ofNat.{u} n))
    (hdet : ∀ a, a ∈ G → a ∈ H ∨ a ∉ H) :
    ∃ k m : Nat, Equinumerous (quotientSet (cosetRel H G op) G) (ofNat.{u} k) ∧
      Equinumerous H (ofNat.{u} m) ∧ Equinumerous G (ofNat.{u} (k * m)) := by
  -- `H` is finite because it is detachable
  obtain ⟨m, hm⟩ := isFinite_of_detachable n H G hH.left hGfin hdet
  -- and the quotient is a finite image, because the relation is decidable
  have himg : IsFinite (imageIn (clsMap (cosetRel H G op) G) G (quotientSet (cosetRel H G op) G)) := by
    refine isFinite_imageIn n G _ _ hGfin (fun a ha b hb => ?_)
      (fun a ha => by rw [app_clsMap ha]; exact cls_mem_quotientSet ha)
    rw [app_clsMap ha, app_clsMap hb]
    exact cls_eq_or_ne_of_detachable hG hH hdet ha hb
  rw [quotientSet_eq_image] at himg
  obtain ⟨k, hk⟩ := himg
  exact ⟨k, m, hk, hm, lagrange hG hH hk hm⟩

/-! ## Powers, and finite order

`a^k` is a `Nat`-indexed iteration, so it is a Lean-level family; `natSeq` turns
it into a set function and pigeonhole does the rest. In a finite group the
powers must repeat, and cancelling gives `a^m = e` for some `m > 0` -- every
element has finite order, with no axiom. -/

def gpow (op e a : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => e
  | k + 1 => opAt op (gpow op e a k) a

/-! ### The order arithmetic, over a monoid

Every proof below uses `assoc`, `left_id` and `right_id`. The group forms that
follow are one-liners through `IsGroup.toMonoid`.

`gpow_inj_below` is NOT here, because it is proved by CANCELLATION, which is
where inverses are genuinely used. It weakens to a monoid only with the extra
hypothesis that some power is the identity, which is a different theorem rather
than the same one at lower cost. -/

theorem gpow_mem_bare {M op e a : ZFSet.{u}} (hM : IsMonoid M op e) (ha : a ∈ M) :
    ∀ k : Nat, gpow op e a k ∈ M
  | 0 => hM.mem_e
  | k + 1 => opAt_mem_bare hM (gpow_mem_bare hM ha k) ha

theorem gpow_add_bare {M op e a : ZFSet.{u}} (hM : IsMonoid M op e) (ha : a ∈ M)
    (j : Nat) :
    ∀ k : Nat, gpow op e a (j + k) = opAt op (gpow op e a j) (gpow op e a k)
  | 0 => by
    show gpow op e a j = opAt op (gpow op e a j) e
    rw [hM.right_id _ (gpow_mem_bare hM ha j)]
  | k + 1 => by
    show opAt op (gpow op e a (j + k)) a
      = opAt op (gpow op e a j) (opAt op (gpow op e a k) a)
    rw [gpow_add_bare hM ha j k,
      hM.assoc _ (gpow_mem_bare hM ha j) _ (gpow_mem_bare hM ha k) a ha]

theorem gpow_one_bare {M op e a : ZFSet.{u}} (hM : IsMonoid M op e) (ha : a ∈ M) :
    gpow op e a 1 = a := by
  show opAt op (gpow op e a 0) a = a
  exact hM.left_id _ ha

theorem gpow_id_bare {M op e : ZFSet.{u}} (hM : IsMonoid M op e) :
    ∀ k : Nat, gpow op e e k = e
  | 0 => rfl
  | k + 1 => by
    show opAt op (gpow op e e k) e = e
    rw [gpow_id_bare hM k, hM.right_id _ hM.mem_e]

theorem gpow_mul_bare {M op e a : ZFSet.{u}} (hM : IsMonoid M op e) (ha : a ∈ M)
    (j : Nat) :
    ∀ k : Nat, gpow op e a (j * k) = gpow op e (gpow op e a j) k
  | 0 => by rw [Nat.mul_zero]; rfl
  | k + 1 => by
    show gpow op e a (j * (k + 1))
      = opAt op (gpow op e (gpow op e a j) k) (gpow op e a j)
    rw [Nat.mul_succ, gpow_add_bare hM ha (j * k) j, gpow_mul_bare hM ha j k]

theorem gpow_mul_eq_id_bare {M op e a : ZFSet.{u}} (hM : IsMonoid M op e)
    (ha : a ∈ M) {m : Nat} (hme : gpow op e a m = e) :
    ∀ j : Nat, gpow op e a (j * m) = e
  | 0 => by
    rw [Nat.zero_mul]
    rfl
  | i + 1 => by
    rw [Nat.succ_mul, gpow_add_bare hM ha (i * m) m,
      gpow_mul_eq_id_bare hM ha hme i, hme, hM.left_id _ hM.mem_e]

theorem gpow_mod_bare {M op e a : ZFSet.{u}} (hM : IsMonoid M op e) (ha : a ∈ M)
    {m : Nat} (hm : 0 < m) (hme : gpow op e a m = e) :
    ∀ k : Nat, gpow op e a k = gpow op e a (k % m) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    rcases Nat.lt_or_ge k m with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
    · have hstep : gpow op e a k = gpow op e a (k - m) := by
        have he : gpow op e a (m + (k - m)) = gpow op e a k := by
          rw [show m + (k - m) = k by omega]
        rw [← he, gpow_add_bare hM ha m (k - m), hme,
          hM.left_id _ (gpow_mem_bare hM ha _)]
      rw [hstep, ih (k - m) (by omega), ← Nat.mod_eq_sub_mod hge]

theorem gpow_mem {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G) :
    ∀ k : Nat, gpow op e a k ∈ G :=
  gpow_mem_bare hG.toMonoid ha
theorem gpow_add {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G) (j : Nat) :
    ∀ k : Nat, gpow op e a (j + k) = opAt op (gpow op e a j) (gpow op e a k) :=
  gpow_add_bare hG.toMonoid ha j

/-- The interchange law: `(w·x)·(y·z) = (w·y)·(x·z)` in an abelian group.

The four-term rearrangement that every "add componentwise, then split each
component" argument needs -- and writing it as an inline chain of associativity
and commutativity rewrites is how such a proof becomes six brittle steps whose
order nobody can predict. Named once, it is one rewrite at each call site. -/
theorem opAt_interchange {G op e : ZFSet.{u}} (hG : IsGroup G op e)
    (hab : IsAbelian G op) {w x y z : ZFSet.{u}}
    (hw : w ∈ G) (hx : x ∈ G) (hy : y ∈ G) (hz : z ∈ G) :
    opAt op (opAt op w x) (opAt op y z)
      = opAt op (opAt op w y) (opAt op x z) := by
  rw [hG.assoc _ hw _ hx _ (opAt_mem hG hy hz),
    ← hG.assoc _ hx _ hy _ hz, hab _ hx _ hy,
    hG.assoc _ hy _ hx _ hz, ← hG.assoc _ hw _ hy _ (opAt_mem hG hx hz)]

#print axioms opAt_interchange

theorem gpow_id {G op e : ZFSet.{u}} (hG : IsGroup G op e) :
    ∀ k : Nat, gpow op e e k = e
  | 0 => rfl
  | k + 1 => by
    show opAt op (gpow op e e k) e = e
    rw [gpow_id hG k, hG.right_id e hG.mem_e]

theorem gpow_mul {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G) (j : Nat) :
    ∀ k : Nat, gpow op e a (j * k) = gpow op e (gpow op e a j) k :=
  gpow_mul_bare hG.toMonoid ha j
/-- Pigeonhole for a sequence in a finite set, WITH THE BOUND. Two of the
first `n+1` values coincide, and the later index is one of those `n+1`.

THE BOUND WAS PROVED HERE AND DISCARDED, AND THE DOCSTRING KNEW. The old
statement returned `∃ j k, j < k ∧ F j = F k` while the sentence above it said
two of the first `n+1` values --- the prose was right and the type was weaker.
`exists_pair_or_inj` hands back `hj : j < n + 1` and `hk : k < n + 1`, and both
branches of the final `rcases` dropped them.

IT IS NOT A COSMETIC STRENGTHENING. Dirichlet's theorem is this lemma with
the bound: the difference of the two indices is the approximation's denominator,
so `k <= n` is the whole quantitative content, and an unbounded collision carries
none of it. `exists_dirichlet_collision` (`PolyRing`) was rewritten onto the weak
form and inherited the defect --- true, green, and unusable by its own consumer.

`exists_repeat_of_finite` below is this with the bound forgotten, for the callers
that never wanted it.
-/
theorem exists_repeat_of_finite_lt {G : ZFSet.{u}} {F : Nat → ZFSet.{u}}
    (hmaps : ∀ k : Nat, F k ∈ G) {n : Nat} (hGfin : Equinumerous G (ofNat.{u} n)) :
    ∃ j k : Nat, j < k ∧ k < n + 1 ∧ F j = F k := by
  have hnotinj : ¬ ∀ j k : Nat, j < n + 1 → k < n + 1 → F j = F k → j = k := by
    intro hinj
    have hdom : Dominates (ofNat.{u} (n + 1)) (ofNat.{u} n) := by
      refine dominates_trans ⟨graphOn (ofNat.{u} (n + 1)) G (natFun G F),
        graphOn_isFunction _ _ _, graphOn_domain (fun w hw => ?_), graphOn_range,
        fun w hw w' hw' he => ?_⟩ (dominates_of_equinumerous hGfin)
      · obtain ⟨k, -, rfl⟩ := (mem_ofNat_iff w (n + 1)).mp hw
        rw [natFun_ofNat hmaps k]
        exact hmaps k
      · obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff w (n + 1)).mp hw
        obtain ⟨k', hk', rfl⟩ := (mem_ofNat_iff w' (n + 1)).mp hw'
        rw [app_graphOn (fun m hm => by
              obtain ⟨i, -, rfl⟩ := (mem_ofNat_iff m (n + 1)).mp hm
              rw [natFun_ofNat hmaps i]; exact hmaps i) hw,
            app_graphOn (fun m hm => by
              obtain ⟨i, -, rfl⟩ := (mem_ofNat_iff m (n + 1)).mp hm
              rw [natFun_ofNat hmaps i]; exact hmaps i) hw',
            natFun_ofNat hmaps k, natFun_ofNat hmaps k'] at he
        rw [hinj k k' hk hk' he]
    have := dominates_ofNat_le _ _ hdom
    omega
  rcases exists_pair_or_inj (P := fun j k => F j = F k)
    (fun j k => eq_or_ne_of_finite hGfin (hmaps j) (hmaps k)) (n + 1) with
    ⟨j, k, hj, hk, hne, hjk⟩ | hinj
  · rcases Nat.lt_or_ge j k with hlt | hge
    · exact ⟨j, k, hlt, hk, hjk⟩
    · exact ⟨k, j, by omega, hj, hjk.symm⟩
  · exact absurd hinj hnotinj

#print axioms exists_repeat_of_finite_lt

/-- Pigeonhole for a sequence in a finite set. Two of the first `n+1` values
coincide. The bound on the later index is available from
`exists_repeat_of_finite_lt`; this is the form for callers that do not need it. -/
theorem exists_repeat_of_finite {G : ZFSet.{u}} {F : Nat → ZFSet.{u}}
    (hmaps : ∀ k : Nat, F k ∈ G) {n : Nat} (hGfin : Equinumerous G (ofNat.{u} n)) :
    ∃ j k : Nat, j < k ∧ F j = F k :=
  let ⟨j, k, hlt, _, hjk⟩ := exists_repeat_of_finite_lt hmaps hGfin
  ⟨j, k, hlt, hjk⟩

/-- Every element of a finite group has finite order. The powers cannot all
be distinct, and cancelling a repetition leaves the identity. -/
theorem exists_gpow_eq_id {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G)
    {n : Nat} (hGfin : Equinumerous G (ofNat.{u} n)) :
    ∃ m : Nat, 0 < m ∧ gpow op e a m = e := by
  -- the powers, as a set function on `ω`
  have hmaps : ∀ k : Nat, gpow op e a k ∈ G := gpow_mem hG ha
  -- if they were distinct on `{0,…,n}` we would inject `n+1` points into `n`
  have hnotinj : ¬ ∀ j k : Nat, j < n + 1 → k < n + 1 →
      gpow op e a j = gpow op e a k → j = k := by
    intro hinj
    have hdom : Dominates (ofNat.{u} (n + 1)) (ofNat.{u} n) := by
      refine dominates_trans ⟨graphOn (ofNat.{u} (n + 1)) G (natFun G (gpow op e a)),
        graphOn_isFunction _ _ _, graphOn_domain (fun w hw => ?_), graphOn_range,
        fun w hw w' hw' he => ?_⟩ (dominates_of_equinumerous hGfin)
      · obtain ⟨k, -, rfl⟩ := (mem_ofNat_iff w (n + 1)).mp hw
        rw [natFun_ofNat hmaps k]
        exact hmaps k
      · obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff w (n + 1)).mp hw
        obtain ⟨k', hk', rfl⟩ := (mem_ofNat_iff w' (n + 1)).mp hw'
        rw [app_graphOn (fun m hm => by
              obtain ⟨i, -, rfl⟩ := (mem_ofNat_iff m (n + 1)).mp hm
              rw [natFun_ofNat hmaps i]; exact hmaps i) hw,
            app_graphOn (fun m hm => by
              obtain ⟨i, -, rfl⟩ := (mem_ofNat_iff m (n + 1)).mp hm
              rw [natFun_ofNat hmaps i]; exact hmaps i) hw',
            natFun_ofNat hmaps k, natFun_ofNat hmaps k'] at he
        rw [hinj k k' hk hk' he]
    have := dominates_ofNat_le _ _ hdom
    omega
  -- so two powers agree; cancelling the common prefix leaves the identity
  rcases exists_pair_or_inj (P := fun j k => gpow op e a j = gpow op e a k)
    (fun j k => eq_or_ne_of_finite hGfin (hmaps j) (hmaps k)) (n + 1) with
    ⟨j, k, hj, hk, hne, hjk⟩ | hinj
  · -- put the smaller index first
    rcases Nat.lt_or_ge j k with hlt | hge
    · refine ⟨k - j, by omega, ?_⟩
      have hsum : gpow op e a (j + (k - j)) = gpow op e a j := by
        rw [show j + (k - j) = k by omega, ← hjk]
      rw [gpow_add hG ha j (k - j)] at hsum
      have hid : opAt op (gpow op e a j) (gpow op e a (k - j))
          = opAt op (gpow op e a j) e := by
        rw [hsum, hG.right_id _ (hmaps j)]
      exact op_left_cancel hG (hmaps j) (hmaps (k - j)) hG.mem_e hid
    · refine ⟨j - k, by omega, ?_⟩
      have hsum : gpow op e a (k + (j - k)) = gpow op e a k := by
        rw [show k + (j - k) = j by omega, hjk]
      rw [gpow_add hG ha k (j - k)] at hsum
      have hid : opAt op (gpow op e a k) (gpow op e a (j - k))
          = opAt op (gpow op e a k) e := by
        rw [hsum, hG.right_id _ (hmaps k)]
      exact op_left_cancel hG (hmaps k) (hmaps (j - k)) hG.mem_e hid
  · exact absurd hinj hnotinj

/-- The first power is the element, as a fact about `gpow` alone. -/
theorem gpow_one {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G) :
    gpow op e a 1 = a := hG.left_id a ha

/-- In an abelian group the power of a product is the product of the powers. -/
theorem gpow_opAt {G op e a b : ZFSet.{u}} (hG : IsGroup G op e) (hab : IsAbelian G op)
    (ha : a ∈ G) (hb : b ∈ G) :
    ∀ k : Nat, gpow op e (opAt op a b) k = opAt op (gpow op e a k) (gpow op e b k)
  | 0 => (hG.left_id e hG.mem_e).symm
  | k + 1 => by
    have hak := gpow_mem hG ha k
    have hbk := gpow_mem hG hb k
    show opAt op (gpow op e (opAt op a b) k) (opAt op a b)
      = opAt op (opAt op (gpow op e a k) a) (opAt op (gpow op e b k) b)
    rw [gpow_opAt hG hab ha hb k,
      hG.assoc _ hak _ hbk _ (opAt_mem hG ha hb),
      ← hG.assoc _ hbk _ ha _ hb,
      hab _ hbk _ ha,
      hG.assoc _ ha _ hbk _ hb,
      ← hG.assoc _ hak _ ha _ (opAt_mem hG hbk hb)]

/-! ## Divisibility of exponents -/

/-- Powers repeat with period `m` once `a^m = e`. -/
theorem gpow_mod {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G) {m : Nat}
    (hm : 0 < m) (hme : gpow op e a m = e) :
    ∀ k : Nat, gpow op e a k = gpow op e a (k % m) :=
  gpow_mod_bare hG.toMonoid ha hm hme
/-! ## The cyclic subgroup, and `a^|G| = e`

`⟨a⟩` is the image of `ω` under `k ↦ a^k`. With `a^m = e` for the least such
`m`, its elements are exactly the powers below `m`, so it has `m` of them;
Lagrange then divides `m` into `|G|` and `a^|G| = e` follows. -/

def cyclic (G op e a : ZFSet.{u}) : ZFSet.{u} :=
  imageIn (natSeq G (gpow op e a)) omega.{u} G

theorem mem_cyclic_iff {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G)
    (w : ZFSet.{u}) : w ∈ cyclic G op e a ↔ w ∈ G ∧ ∃ k : Nat, w = gpow op e a k := by
  refine Iff.trans (mem_imageIn_iff _ _ _ w) ⟨?_, ?_⟩
  · rintro ⟨hwG, n, hn, he⟩
    obtain ⟨k, rfl⟩ := (mem_omega_iff n).mp hn
    exact ⟨hwG, k, by rwa [app_natSeq (gpow_mem hG ha) k] at he⟩
  · rintro ⟨hwG, k, rfl⟩
    exact ⟨hwG, ofNat.{u} k, ofNat_mem_omega k, by rw [app_natSeq (gpow_mem hG ha) k]⟩

theorem isSubgroup_cyclic {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G)
    {m : Nat} (hm : 0 < m) (hme : gpow op e a m = e) :
    IsSubgroup (cyclic G op e a) G op e := by
  refine ⟨imageIn_subset _ _ _, ?_, ?_, ?_⟩
  · exact (mem_cyclic_iff hG ha e).mpr ⟨hG.mem_e, 0, rfl⟩
  · rintro x hx y hy
    obtain ⟨-, j, rfl⟩ := (mem_cyclic_iff hG ha x).mp hx
    obtain ⟨-, k, rfl⟩ := (mem_cyclic_iff hG ha y).mp hy
    exact (mem_cyclic_iff hG ha _).mpr
      ⟨opAt_mem hG (gpow_mem hG ha j) (gpow_mem hG ha k), j + k,
        (gpow_add hG ha j k).symm⟩
  · rintro x hx
    obtain ⟨-, k, rfl⟩ := (mem_cyclic_iff hG ha x).mp hx
    -- the inverse is the power that completes a full period
    refine ⟨gpow op e a (m - k % m), (mem_cyclic_iff hG ha _).mpr
      ⟨gpow_mem hG ha _, m - k % m, rfl⟩, ?_, ?_⟩
    · rw [gpow_mod hG ha hm hme k, ← gpow_add hG ha (k % m) (m - k % m),
        show k % m + (m - k % m) = m by have := Nat.mod_lt k hm; omega, hme]
    · rw [gpow_mod hG ha hm hme k, ← gpow_add hG ha (m - k % m) (k % m),
        show m - k % m + k % m = m by have := Nat.mod_lt k hm; omega, hme]

/-- With `m` least, the powers below `m` are distinct, so `⟨a⟩` has `m`
elements. -/
theorem equinumerous_cyclic {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G)
    {m : Nat} (hm : 0 < m) (hme : gpow op e a m = e)
    (hleast : ∀ k, k < m → 0 < k → gpow op e a k ≠ e) :
    Equinumerous (ofNat.{u} m) (cyclic G op e a) := by
  have hmaps : ∀ w, w ∈ ofNat.{u} m → natFun G (gpow op e a) w ∈ cyclic G op e a := by
    intro w hw
    obtain ⟨k, -, rfl⟩ := (mem_ofNat_iff w m).mp hw
    rw [natFun_ofNat (gpow_mem hG ha) k]
    exact (mem_cyclic_iff hG ha _).mpr ⟨gpow_mem hG ha k, k, rfl⟩
  have happ : ∀ k : Nat, k < m →
      app (graphOn (ofNat.{u} m) (cyclic G op e a) (natFun G (gpow op e a))) (ofNat.{u} k)
        = gpow op e a k := by
    intro k hk
    rw [app_graphOn hmaps ((mem_ofNat_iff _ m).mpr ⟨k, hk, rfl⟩),
      natFun_ofNat (gpow_mem hG ha) k]
  -- distinctness below `m`: a coincidence would give a smaller period
  have hinj : ∀ j, j < m → ∀ k, k < m → gpow op e a j = gpow op e a k → j = k := by
    intro j hj k hk he
    rcases Nat.lt_or_ge j k with hlt | hge
    · exfalso
      have hcancel : gpow op e a (k - j) = e := by
        have hsum : gpow op e a (j + (k - j)) = gpow op e a j := by
          rw [show j + (k - j) = k by omega, ← he]
        rw [gpow_add hG ha j (k - j)] at hsum
        exact op_left_cancel hG (gpow_mem hG ha j) (gpow_mem hG ha _) hG.mem_e
          (by rw [hsum, hG.right_id _ (gpow_mem hG ha j)])
      exact hleast (k - j) (by omega) (by omega) hcancel
    · rcases Nat.eq_or_lt_of_le hge with heq | hlt
      · omega
      · exfalso
        have hcancel : gpow op e a (j - k) = e := by
          have hsum : gpow op e a (k + (j - k)) = gpow op e a k := by
            rw [show k + (j - k) = j by omega, he]
          rw [gpow_add hG ha k (j - k)] at hsum
          exact op_left_cancel hG (gpow_mem hG ha k) (gpow_mem hG ha _) hG.mem_e
            (by rw [hsum, hG.right_id _ (gpow_mem hG ha k)])
        exact hleast (j - k) (by omega) (by omega) hcancel
  refine ⟨_, ⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range, ?_⟩,
    ⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range, ?_⟩⟩
  · intro w hw w' hw' he
    obtain ⟨j, hj, rfl⟩ := (mem_ofNat_iff w m).mp hw
    obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff w' m).mp hw'
    rw [happ j hj, happ k hk] at he
    rw [hinj j hj k hk he]
  · intro v hv
    obtain ⟨-, k, rfl⟩ := (mem_cyclic_iff hG ha v).mp hv
    refine ⟨ofNat.{u} (k % m), (mem_ofNat_iff _ m).mpr ⟨k % m, Nat.mod_lt k hm, rfl⟩, ?_⟩
    rw [happ (k % m) (Nat.mod_lt k hm), ← gpow_mod hG ha hm hme k]

/-- Membership in `⟨a⟩` is decidable, because it is a bounded search over the
powers below the period. -/
theorem cyclic_detachable {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G)
    {n : Nat} (hGfin : Equinumerous G (ofNat.{u} n)) {m : Nat} (hm : 0 < m)
    (hme : gpow op e a m = e) (w : ZFSet.{u}) (hw : w ∈ G) :
    w ∈ cyclic G op e a ∨ w ∉ cyclic G op e a := by
  rcases exists_lt_or_not (Q := fun k => w = gpow op e a k)
    (fun k => eq_or_ne_of_finite hGfin hw (gpow_mem hG ha k)) m with ⟨k, -, hk⟩ | hno
  · exact Or.inl ((mem_cyclic_iff hG ha w).mpr ⟨hw, k, hk⟩)
  · refine Or.inr fun hmem => ?_
    obtain ⟨-, k, hk⟩ := (mem_cyclic_iff hG ha w).mp hmem
    exact hno (k % m) (Nat.mod_lt k hm) (by rw [hk, gpow_mod hG ha hm hme k])

/-! ## The order of an element

The least positive exponent returning the identity. It is the size of the
cyclic subgroup the element generates, so Lagrange makes it divide the order of
the group -- and `gpow_card_eq_id`, which Fermat and Euler are instances of,
falls out of that. -/

def IsOrderOf (m : Nat) (op e a : ZFSet.{u}) : Prop :=
  0 < m ∧ gpow op e a m = e ∧ ∀ k, k < m → 0 < k → gpow op e a k ≠ e

theorem gpow_eq_id_iff_bare {M op e a : ZFSet.{u}} (hM : IsMonoid M op e)
    (ha : a ∈ M) {m : Nat} (hm : IsOrderOf m op e a) (k : Nat) :
    gpow op e a k = e ↔ k % m = 0 := by
  constructor
  · intro hk
    rcases Nat.eq_zero_or_pos (k % m) with h | h
    · exact h
    · exact absurd (by rw [← gpow_mod_bare hM ha hm.left hm.right.left k]; exact hk)
        (hm.right.right (k % m) (Nat.mod_lt k hm.left) h)
  · intro hk
    have hsplit : k = (k / m) * m := by
      have := Nat.div_add_mod k m
      rw [hk, Nat.mul_comm] at this
      omega
    rw [hsplit]
    exact gpow_mul_eq_id_bare hM ha hm.right.left _

theorem exists_order {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G)
    {n : Nat} (hGfin : Equinumerous G (ofNat.{u} n)) : ∃ m : Nat, IsOrderOf m op e a := by
  obtain ⟨m₀, hm₀, hme₀⟩ := exists_gpow_eq_id hG ha hGfin
  obtain ⟨m, ⟨hmpos, hmid⟩, hleast⟩ := exists_least
    (Q := fun k => 0 < k ∧ gpow op e a k = e)
    (fun k => by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact Or.inr (fun h => by omega)
      · rcases eq_or_ne_of_finite hGfin (gpow_mem hG ha k) hG.mem_e with h | h
        · exact Or.inl ⟨hk, h⟩
        · exact Or.inr (fun hc => h hc.right)) m₀ ⟨hm₀, hme₀⟩
  exact ⟨m, hmpos, hmid, fun k hk hk0 he => hleast k hk ⟨hk0, he⟩⟩

/-- Whole periods return the identity. -/
theorem gpow_mul_eq_id {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G)
    {m : Nat} (hme : gpow op e a m = e) : ∀ j : Nat, gpow op e a (j * m) = e :=
  gpow_mul_eq_id_bare hG.toMonoid ha hme
/-- An exponent returns the identity exactly when the order divides it. -/
theorem gpow_eq_id_iff {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G)
    {m : Nat} (hm : IsOrderOf m op e a) (k : Nat) :
    gpow op e a k = e ↔ k % m = 0 :=
  gpow_eq_id_iff_bare hG.toMonoid ha hm k
theorem gpow_inj_below {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G)
    {m : Nat} (hleast : ∀ k, k < m → 0 < k → gpow op e a k ≠ e) :
    ∀ j, j < m → ∀ k, k < m → gpow op e a j = gpow op e a k → j = k := by
  intro j hj k hk he
  rcases Nat.lt_or_ge j k with hlt | hge
  · exfalso
    have hcancel : gpow op e a (k - j) = e := by
      have hsum : gpow op e a (j + (k - j)) = gpow op e a j := by
        rw [show j + (k - j) = k by omega, ← he]
      rw [gpow_add hG ha j (k - j)] at hsum
      exact op_left_cancel hG (gpow_mem hG ha j) (gpow_mem hG ha _) hG.mem_e
        (by rw [hsum, hG.right_id _ (gpow_mem hG ha j)])
    exact hleast (k - j) (by omega) (by omega) hcancel
  · rcases Nat.eq_or_lt_of_le hge with heq | hlt
    · omega
    · exfalso
      have hcancel : gpow op e a (j - k) = e := by
        have hsum : gpow op e a (k + (j - k)) = gpow op e a k := by
          rw [show k + (j - k) = j by omega, he]
        rw [gpow_add hG ha k (j - k)] at hsum
        exact op_left_cancel hG (gpow_mem hG ha k) (gpow_mem hG ha _) hG.mem_e
          (by rw [hsum, hG.right_id _ (gpow_mem hG ha k)])
      exact hleast (j - k) (by omega) (by omega) hcancel

/-- The cyclic subgroup generated by an element has exactly `order` elements. -/
theorem equinumerous_cyclic_order {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G)
    {m : Nat} (hm : IsOrderOf m op e a) : Equinumerous (ofNat.{u} m) (cyclic G op e a) :=
  equinumerous_cyclic hG ha hm.left hm.right.left hm.right.right

/-- The order of an element divides the order of the group -- Lagrange
applied to the subgroup it generates. -/
theorem order_divides_card {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G)
    {n : Nat} (hGfin : Equinumerous G (ofNat.{u} n)) {m : Nat} (hm : IsOrderOf m op e a) :
    ∃ k : Nat, n = k * m := by
  obtain ⟨k, m', hq, hm', hprod⟩ := lagrange_of_detachable hG
    (isSubgroup_cyclic hG ha hm.left hm.right.left) hGfin
    (fun g hg => cyclic_detachable hG ha hGfin hm.left hm.right.left g hg)
  have hmm : m = m' :=
    card_unique (equinumerous_symm (equinumerous_cyclic_order hG ha hm)) hm'
  exact ⟨k, by rw [hmm]; exact card_unique hGfin hprod⟩

/-! ## Restricting an operation

A binary operation restricted to a closed subset. The pairs are the same; only
the ambient product shrinks, so `app` is unchanged where it is defined. -/

/-- Carving a function down to the pairs lying in a product leaves a function. -/
theorem isFunction_sep_prod {op A B : ZFSet.{u}} (hop : IsFunction op) :
    IsFunction (sep (fun z => z ∈ op) (prod A B)) := by
  constructor
  · intro z hz
    obtain ⟨hprod, -⟩ := (mem_sep_iff _ z _).mp hz
    obtain ⟨p, hp, v, hv, rfl⟩ := (mem_prod_iff z _ _).mp hprod
    exact ⟨p, v, rfl⟩
  · intro p v v' hv hv'
    exact hop.right p v v' ((mem_sep_iff _ _ _).mp hv).right
      ((mem_sep_iff _ _ _).mp hv').right

def restrictOp (op S : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => z ∈ op) (prod (prod S S) S)

theorem opAt_restrictOp {op S a b : ZFSet.{u}} (hop : IsFunction op)
    (hdom : ∀ x, x ∈ prod S S → x ∈ domain op)
    (hclosed : ∀ x, x ∈ S → ∀ y, y ∈ S → opAt op x y ∈ S)
    (ha : a ∈ S) (hb : b ∈ S) : opAt (restrictOp op S) a b = opAt op a b := by
  have hmem : opair (opair a b) (opAt op a b) ∈ restrictOp op S :=
    (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod (opair_mem_prod ha hb) (hclosed a ha b hb),
      opair_app_mem hop (hdom _ (opair_mem_prod ha hb))⟩
  have hfun : IsFunction (restrictOp op S) := isFunction_sep_prod hop
  exact app_eq hfun hmem

theorem isFunction_restrictOp {op S : ZFSet.{u}} (hop : IsFunction op) :
    IsFunction (restrictOp op S) := isFunction_sep_prod hop

theorem restrictOp_domain {op S : ZFSet.{u}} (hop : IsFunction op)
    (hdom : ∀ x, x ∈ prod S S → x ∈ domain op)
    (hclosed : ∀ x, x ∈ S → ∀ y, y ∈ S → opAt op x y ∈ S) :
    domain (restrictOp op S) = prod S S := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨v, hv⟩ := (mem_domain_iff p _).mp hp
    exact mem_prod_left ((mem_sep_iff _ _ _).mp hv).left
  · obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff p _ _).mp hp
    exact (mem_domain_iff _ _).mpr ⟨opAt op a b, (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod (opair_mem_prod ha hb) (hclosed a ha b hb),
        opair_app_mem hop (hdom _ (opair_mem_prod ha hb))⟩⟩

theorem restrictOp_range {op S : ZFSet.{u}} : range (restrictOp op S) ⊆ S := by
  intro v hv
  obtain ⟨p, hp⟩ := (mem_range_iff v _).mp hv
  exact mem_prod_right ((mem_sep_iff _ _ _).mp hp).left

/-! ## Restricting one side

The same restriction with the left factor cut down further: an action of `S` on
`T` carved out of an operation on the ambient set. -/

def restrictLeft (op S T : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => z ∈ op) (prod (prod S T) T)

theorem isFunction_restrictLeft {op S T : ZFSet.{u}} (hop : IsFunction op) :
    IsFunction (restrictLeft op S T) := isFunction_sep_prod hop

theorem opAt_restrictLeft {op S T a b : ZFSet.{u}} (hop : IsFunction op)
    (hdom : ∀ x, x ∈ prod S T → x ∈ domain op)
    (hclosed : ∀ x, x ∈ S → ∀ y, y ∈ T → opAt op x y ∈ T)
    (ha : a ∈ S) (hb : b ∈ T) : opAt (restrictLeft op S T) a b = opAt op a b :=
  app_eq (isFunction_restrictLeft hop)
    ((mem_sep_iff _ _ _).mpr ⟨opair_mem_prod (opair_mem_prod ha hb) (hclosed a ha b hb),
      opair_app_mem hop (hdom _ (opair_mem_prod ha hb))⟩)

theorem restrictLeft_domain {op S T : ZFSet.{u}} (hop : IsFunction op)
    (hdom : ∀ x, x ∈ prod S T → x ∈ domain op)
    (hclosed : ∀ x, x ∈ S → ∀ y, y ∈ T → opAt op x y ∈ T) :
    domain (restrictLeft op S T) = prod S T := by
  refine ext _ _ fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · obtain ⟨v, hv⟩ := (mem_domain_iff q _).mp hq
    exact mem_prod_left ((mem_sep_iff _ _ _).mp hv).left
  · obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff q _ _).mp hq
    exact (mem_domain_iff _ _).mpr ⟨opAt op a b, (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod (opair_mem_prod ha hb) (hclosed a ha b hb),
        opair_app_mem hop (hdom _ (opair_mem_prod ha hb))⟩⟩

theorem restrictLeft_range {op S T : ZFSet.{u}} : range (restrictLeft op S T) ⊆ T := by
  intro v hv
  obtain ⟨q, hq⟩ := (mem_range_iff v _).mp hv
  exact mem_prod_right ((mem_sep_iff _ _ _).mp hq).left

/-! ## Audit

Nothing classical, and nothing new proved about `ℤ`: the group axioms are the
`Integer.lean` lemmas read through `app`. -/

#print axioms opAt_mem
#print axioms inv_unique
#print axioms isGroup_intAdd
#print axioms isAbelian_intAdd
#print axioms hom_id
#print axioms isGroup_congQuotient
#print axioms isEquivRel_cosetRel
#print axioms invMap_isFunction
#print axioms exists_coset_section
#print axioms equinumerous_prod_quotient
#print axioms lagrange
#print axioms lagrange_of_detachable
#print axioms exists_gpow_eq_id
#print axioms gpow_mod
#print axioms isSubgroup_cyclic
#print axioms equinumerous_cyclic
#print axioms order_divides_card
#print axioms gpow_eq_id_iff
#print axioms opAt_restrictOp
#print axioms gpow_opAt
#print axioms gpow_one

#print axioms gpow_inj_below
-- Cons at the head, so the recursion matches `Distinct`'s own: a list built by
-- appending needs a separate lemma before its head clause can be reached.

/-- An element whose order is the group's size generates the group. The
cyclic subgroup it spans is contained and equinumerous, so it is everything --
no construction, just a count. -/
theorem cyclic_eq_of_order_card {G op e a : ZFSet.{u}} (hG : IsGroup G op e) (ha : a ∈ G)
    {n : Nat} (hfin : Equinumerous G (ofNat.{u} n)) (hord : IsOrderOf n op e a) :
    cyclic G op e a = G := by
  refine subset_eq_of_card_eq (fun w hw => ((mem_cyclic_iff hG ha w).mp hw).left)
    (equinumerous_symm (equinumerous_cyclic_order hG ha hord)) hfin

#print axioms cyclic_eq_of_order_card


/-- The first `n` powers of `a`, top first: `a^(n-1) … a^0`.

`(below n).map` rather than its own recursion -- the recursion IS `below`'s, and
writing it twice is what stranded the generic in `Lebesgue.lean`.
The cons shape survives: `below (n+1)` reduces to
`n :: below n` and `List.map` reduces on a cons, so anything matching on the
head still does. -/
def powerList (op e a : ZFSet.{u}) (n : Nat) : List ZFSet.{u} :=
  (below n).map (gpow op e a)

theorem mem_powerList {op e a : ZFSet.{u}} (n : Nat) (x : ZFSet.{u}) :
    x ∈ powerList op e a n ↔ ∃ i, i < n ∧ gpow op e a i = x := by
  simp only [powerList, List.mem_map, mem_below]

theorem length_powerList (op e a : ZFSet.{u}) (n : Nat) :
    (powerList op e a n).length = n := by
  rw [powerList, List.length_map, length_below]

#print axioms powerList
#print axioms mem_powerList
#print axioms length_powerList
#print axioms IsMonoid
#print axioms opAt_mem_bare
#print axioms gpow_mem_bare
#print axioms gpow_add_bare
#print axioms gpow_one_bare
#print axioms gpow_id_bare
#print axioms gpow_mul_bare
#print axioms gpow_mul_eq_id_bare
#print axioms gpow_mod_bare
#print axioms gpow_eq_id_iff_bare
#print axioms intAdd_maps

#print axioms IsGroup.toMonoid
#print axioms opAt_intAddOp
#print axioms isHom_op
#print axioms app_mem_of_isHom
#print axioms congOp_isFunction
#print axioms opAt_congOp
#print axioms congOp_domain
#print axioms congOp_range
#print axioms op_left_cancel
#print axioms opair_mem_cosetRel_iff
#print axioms app_invMap
#print axioms cls_eq_of_mem
#print axioms lagrange_component
#print axioms quotientSet_eq_image
#print axioms cls_eq_or_ne_of_detachable
#print axioms gpow_mem
#print axioms gpow_add
#print axioms gpow_id
#print axioms gpow_mul
#print axioms exists_repeat_of_finite
#print axioms mem_cyclic_iff
#print axioms cyclic_detachable
#print axioms exists_order
#print axioms gpow_mul_eq_id
#print axioms equinumerous_cyclic_order
#print axioms isFunction_sep_prod
#print axioms isFunction_restrictOp
#print axioms restrictOp_domain
#print axioms restrictOp_range
#print axioms isFunction_restrictLeft
#print axioms opAt_restrictLeft
#print axioms restrictLeft_domain
#print axioms restrictLeft_range
end Algebra

namespace ZFSet
export Algebra (IsAbelian IsCongruence IsGroup IsHom IsMonoid IsOrderOf IsSubgroup app_invMap app_mem_of_isHom cls_eq_of_mem cls_eq_or_ne_of_detachable congOp congOp_domain congOp_isFunction congOp_range cosetRel cyclic cyclic_detachable cyclic_eq_of_order_card equinumerous_cyclic equinumerous_cyclic_order equinumerous_prod_quotient exists_coset_section exists_gpow_eq_id exists_order exists_repeat_of_finite gpow gpow_add gpow_add_bare gpow_eq_id_iff gpow_eq_id_iff_bare gpow_id gpow_id_bare gpow_inj_below gpow_mem gpow_mem_bare gpow_mod gpow_mod_bare gpow_mul gpow_mul_bare gpow_mul_eq_id gpow_mul_eq_id_bare gpow_one gpow_one_bare gpow_opAt hom_id intAddOp invMap invMap_isFunction inv_unique isAbelian_intAdd isEquivRel_cosetRel isFunction_restrictLeft isFunction_restrictOp isFunction_sep_prod isGroup_congQuotient isGroup_intAdd isHom_op isSubgroup_cyclic lagrange lagrange_component lagrange_of_detachable length_powerList mem_cyclic_iff mem_powerList opAt_congOp opAt_intAddOp opAt_interchange opAt_mem opAt_mem_bare opAt_restrictLeft opAt_restrictOp op_left_cancel opair_mem_cosetRel_iff order_divides_card powerList quotientSet_eq_image restrictLeft restrictLeft_domain restrictLeft_range restrictOp restrictOp_domain restrictOp_range)
end ZFSet
