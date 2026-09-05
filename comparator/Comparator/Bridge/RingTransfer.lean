/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
A LEAN COMMUTATIVE RING, TRANSPORTED ONTO ITS ENCODED CARRIER --- with NO
finiteness anywhere.

`TypeTransfer` answers can the carrier be encoded --- `encodeSet α` is a ZFSet
whose members are exactly the encodings of `α`'s elements. This answers the
question after it: can a STRUCTURE be carried across, the way `natOpSet` carries
one onto a finite carrier?

IT CAN, AND IT IS ONE INGREDIENT SHORTER THAN THE FINITE CASE. `natOpSet` had to
do its arithmetic inside a `Prop`, because reading a natural back out of `omega`
is an existential in the tower and so not a function there. Here `decode` is an
honest Lean function --- the inverse of `encode` on the carrier, junk off it ---
because choice is available on this side of the pair. So an operation is a plain
`graphOn`, and its computation rule `opAt_opSet` is one rewrite.

WHAT IT REPLACES. Before this, an algebraic row whose carrier was not finite had
no route at all, and three were blocked on that reading. The pair for such a row
is now: encode the carrier, transport the ring, apply the tower's theorem, read
the conclusion back. The remaining cost per row is whatever structure sits ABOVE
the ring --- polynomials, an automorphism group, a family of intermediate fields
--- not the ring itself.

CHOICE, ON THE RIGHT SIDE. `decode` uses `Exists.choose` and the encoding uses
mathlib's `WellOrderingRel`. This is the mathlib half of a comparator pair,
where choice is a theorem; nothing here is re-exported into `FromAxioms` and no
tower declaration changes.

Verified as `.agent/chains/probe-ring-onto-encoded.lean`.
-/
import Comparator.Bridge.TypeTransfer
import Mathlib.Algebra.Ring.Defs

open SetTheory NumberTheory Algebra Comparator.TypeTransfer
open scoped Classical

namespace Comparator.RingTransfer

variable {α : Type} [CommRing α]

/-- The inverse of `encode` on the carrier. Total, with a junk value off it,
which is never reached: every obligation below is discharged at an `encode a`. -/
noncomputable def decode (z : ZFSet.{0}) : α :=
  if h : ∃ a : α, z = encode a then h.choose else 0

theorem decode_encode (a : α) : decode (encode a) = a := by
  rw [decode, dif_pos ⟨a, rfl⟩]
  exact encode_injective
    (Exists.choose_spec (⟨a, rfl⟩ : ∃ b : α, encode a = encode b)).symm

/-- A Lean binary operation, as a ZFSet operation on the encoded carrier. -/
noncomputable def opSet (op : α → α → α) : ZFSet.{0} :=
  graphOn (prod (encodeSet α) (encodeSet α)) (encodeSet α)
    (fun z => encode (op (decode (fst z)) (decode (snd z))))

theorem opSet_maps (op : α → α → α) :
    ∀ z, z ∈ prod (encodeSet α) (encodeSet α) →
      encode (op (decode (fst z)) (decode (snd z))) ∈ encodeSet α :=
  fun _ _ => encode_mem _

/-- THE COMPUTATION RULE. Every ring axiom reduces through this to `α`'s own. -/
theorem opAt_opSet (op : α → α → α) (a b : α) :
    opAt (opSet op) (encode a) (encode b) = encode (op a b) := by
  rw [opSet, opAt,
    app_graphOn (opSet_maps op) (opair_mem_prod (encode_mem a) (encode_mem b)),
    fst_opair, snd_opair, decode_encode, decode_encode]

/-- The operation is defined on the whole square of the carrier. Factored out
because `IsRing` asks for it twice, as `dom` and as `mulDom`. -/
theorem domain_opSet (op : α → α → α) :
    domain (opSet op) = prod (encodeSet α) (encodeSet α) := by
  apply SetTheory.ext
  intro z
  constructor
  · intro hz
    obtain ⟨y, hy⟩ := (mem_domain_iff _ _).mp hz
    rw [opSet] at hy
    exact mem_prod_left ((mem_graphOn_iff _ _ _ _).mp hy).left
  · intro hz
    refine (mem_domain_iff _ _).mpr
      ⟨encode (op (decode (fst z)) (decode (snd z))), ?_⟩
    rw [opSet]
    exact (mem_graphOn_iff _ _ _ _).mpr
      ⟨opair_mem_prod hz (opSet_maps op z hz), z, hz, rfl⟩

theorem range_opSet (op : α → α → α) : range (opSet op) ⊆ encodeSet α := by
  intro y hy
  obtain ⟨x, hx⟩ := (mem_range_iff _ _).mp hy
  rw [opSet] at hx
  exact mem_prod_right ((mem_graphOn_iff _ _ _ _).mp hx).left

/-- The carrier and the two operations form a ring. Each field is `α`'s own
axiom read through the computation rule; nothing about `α` is assumed beyond
`CommRing`, and in particular nothing is finite. -/
theorem isRing_transported :
    IsRing (encodeSet α) (opSet (α := α) (· + ·)) (opSet (α := α) (· * ·))
      (encode (0 : α)) (encode (1 : α)) where
  addGroup :=
    { isFun := graphOn_isFunction _ _ _
      dom := domain_opSet _
      ran := range_opSet _
      mem_e := encode_mem _
      assoc := by
        intro a ha b hb c hc
        obtain ⟨x, rfl⟩ := exists_of_mem_encodeSet ha
        obtain ⟨y, rfl⟩ := exists_of_mem_encodeSet hb
        obtain ⟨z, rfl⟩ := exists_of_mem_encodeSet hc
        rw [opAt_opSet, opAt_opSet, opAt_opSet, opAt_opSet, _root_.add_assoc]
      left_id := by
        intro a ha
        obtain ⟨x, rfl⟩ := exists_of_mem_encodeSet ha
        rw [opAt_opSet, _root_.zero_add]
      right_id := by
        intro a ha
        obtain ⟨x, rfl⟩ := exists_of_mem_encodeSet ha
        rw [opAt_opSet, _root_.add_zero]
      inverses := by
        intro a ha
        obtain ⟨x, rfl⟩ := exists_of_mem_encodeSet ha
        refine ⟨encode (-x), encode_mem _, ?_, ?_⟩
        · rw [opAt_opSet, _root_.add_neg_cancel]
        · rw [opAt_opSet, _root_.neg_add_cancel] }
  addComm := by
    intro a ha b hb
    obtain ⟨x, rfl⟩ := exists_of_mem_encodeSet ha
    obtain ⟨y, rfl⟩ := exists_of_mem_encodeSet hb
    rw [opAt_opSet, opAt_opSet, _root_.add_comm]
  mulFun := graphOn_isFunction _ _ _
  mulDom := domain_opSet _
  mulRan := range_opSet _
  mulAssoc := by
    intro a ha b hb c hc
    obtain ⟨x, rfl⟩ := exists_of_mem_encodeSet ha
    obtain ⟨y, rfl⟩ := exists_of_mem_encodeSet hb
    obtain ⟨z, rfl⟩ := exists_of_mem_encodeSet hc
    rw [opAt_opSet, opAt_opSet, opAt_opSet, opAt_opSet, _root_.mul_assoc]
  mulComm := by
    intro a ha b hb
    obtain ⟨x, rfl⟩ := exists_of_mem_encodeSet ha
    obtain ⟨y, rfl⟩ := exists_of_mem_encodeSet hb
    rw [opAt_opSet, opAt_opSet, _root_.mul_comm]
  mem_one := encode_mem _
  mul_one := by
    intro a ha
    obtain ⟨x, rfl⟩ := exists_of_mem_encodeSet ha
    rw [opAt_opSet, _root_.mul_one]
  distrib := by
    intro a ha b hb c hc
    obtain ⟨x, rfl⟩ := exists_of_mem_encodeSet ha
    obtain ⟨y, rfl⟩ := exists_of_mem_encodeSet hb
    obtain ⟨z, rfl⟩ := exists_of_mem_encodeSet hc
    -- five rewrites at four different instantiations, so `rw` cannot do it in
    -- one pass: `simp only` applies the rule wherever it matches
    simp only [opAt_opSet]
    rw [_root_.mul_add]

end Comparator.RingTransfer
