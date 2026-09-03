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

import FromAxioms.NumberTheory.Integer
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
follow are one-liners through `IsGroup.toMonoid`. -/

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

/-- Pigeonhole for a sequence in a finite set. Two of the first `n+1` values
coincide. -/
theorem exists_repeat_of_finite {G : ZFSet.{u}} {F : Nat → ZFSet.{u}}
    (hmaps : ∀ k : Nat, F k ∈ G) {n : Nat} (hGfin : Equinumerous G (ofNat.{u} n)) :
    ∃ j k : Nat, j < k ∧ F j = F k := by
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
    · exact ⟨j, k, hlt, hjk⟩
    · exact ⟨k, j, by omega, hjk.symm⟩
  · exact absurd hinj hnotinj

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

/-! ## The cyclic subgroup, and `a^|G| = e`

`⟨a⟩` is the image of `ω` under `k ↦ a^k`. With `a^m = e` for the least such
`m`, its elements are exactly the powers below `m`, so it has `m` of them;
Lagrange then divides `m` into `|G|` and `a^|G| = e` follows. -/

def cyclic (G op e a : ZFSet.{u}) : ZFSet.{u} :=
  imageIn (natSeq G (gpow op e a)) omega.{u} G

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
#print axioms isGroup_congQuotient
#print axioms invMap_isFunction
#print axioms opAt_restrictOp
#print axioms gpow_opAt
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
end Algebra

namespace ZFSet
export Algebra (IsAbelian IsCongruence IsGroup IsHom IsMonoid app_invMap app_mem_of_isHom congOp congOp_domain congOp_isFunction congOp_range cyclic exists_repeat_of_finite gpow gpow_add gpow_add_bare gpow_id gpow_mem gpow_mem_bare gpow_opAt intAddOp invMap invMap_isFunction inv_unique isAbelian_intAdd isFunction_restrictLeft isFunction_restrictOp isFunction_sep_prod isGroup_congQuotient isGroup_intAdd isHom_op length_powerList mem_powerList opAt_congOp opAt_intAddOp opAt_interchange opAt_mem opAt_mem_bare opAt_restrictLeft opAt_restrictOp op_left_cancel powerList restrictLeft restrictLeft_domain restrictLeft_range restrictOp restrictOp_domain restrictOp_range)
end ZFSet
