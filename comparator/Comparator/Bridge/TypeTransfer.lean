/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
ANY Lean type as a ZFSet, injectively --- the encoding three rows were blocked
on today for being impossible.

WHY IT LOOKED IMPOSSIBLE. `natOpSet` transports a FINITE type into the tower by
using its enumeration, and there is no enumeration for an infinite one. Reading
that as no encoding exists is the mistake: it says the finite instrument does
not reach, not that nothing does.

WHY IT IS POSSIBLE. This tree's pre-sets are the standard construction,

    inductive PSet : Type (u+1) | mk (α : Type u) (A : α → PSet)

so ANY `Type u` may index one. What is needed is an INJECTIVE `α → ZFSet`, and
the classical construction is Mostowski's collapse: well-order `α`, then send
`a` to the set of images of its strict predecessors.

WHERE THE PRICE SITS, AND WHY IT IS THE RIGHT SIDE. The well-ordering is
mathlib's `WellOrderingRel`, so this needs choice --- and this file is the
mathlib side of a comparator pair, where choice is available and the tower's
floor does not apply. Nothing here is re-exported into `FromAxioms`, and no
`FromAxioms` declaration changes.

WHAT THIS GIVES AND WHAT IT DOES NOT. It gives the CARRIER: `encodeSet α` is a
ZFSet whose members are exactly the encodings of `α`'s elements, and distinct
elements stay distinct. It does NOT by itself give a transported STRUCTURE ---
an operation still has to be carried across, the way `natOpSet` carries one for
a finite carrier and `graphOn` carries a unary map. So a row blocked on "the
carrier cannot be encoded" is unblocked by this; a row whose remaining work is
transporting a large structure still has that work.
-/
import Mathlib.SetTheory.Cardinal.Order
import FromAxioms

namespace Comparator.TypeTransfer

variable {α : Type}

/-- Mostowski's collapse of the well-ordering: `a` goes to the set of images of
its strict predecessors.

Written with `WellFounded.fix` rather than `termination_by`: the latter wants a
measure into a type Lean already knows to be well-founded, and there is none to
offer --- the well-order IS this recursion's justification, so it is passed
directly. -/
noncomputable def emb : α → PSet.{0} :=
  (WellOrderingRel.isWellOrder (α := α)).toIsWellFounded.wf.fix
    (fun a rec => ⟨{b : α // WellOrderingRel b a}, fun b => rec b.1 b.2⟩)

/-- The unfolding equation, which `fix` does not give definitionally. -/
theorem emb_eq (a : α) :
    emb a = ⟨{b : α // WellOrderingRel b a}, fun b => emb b.1⟩ :=
  WellFounded.fix_eq _ _ _

/-- A predecessor's image is a member. -/
theorem emb_mem_of_lt {a b : α} (h : WellOrderingRel b a) : emb b ∈ emb a := by
  rw [emb_eq a]
  exact ⟨⟨b, h⟩, PSet.Equiv.refl _⟩

/-- And every member is a predecessor's image. -/
theorem exists_of_mem_emb {a : α} {w : PSet.{0}} (h : w ∈ emb a) :
    ∃ b : α, WellOrderingRel b a ∧ PSet.Equiv w (emb b) := by
  rw [emb_eq a] at h
  obtain ⟨i, hi⟩ := h
  exact ⟨i.1, i.2, hi⟩

/-- THE POINT: the collapse is injective up to `Equiv`.

Well-founded induction plus trichotomy. If `a < b` then `emb a` is a member of
`emb b`, so an equivalence between them puts `emb a` inside ITSELF, and the
predecessor witnessing that contradicts the induction hypothesis together with
irreflexivity. The `b < a` branch is the same move one step further out: its
witness lies below `b`, hence below `a` by transitivity, so the induction
applies. -/
theorem emb_injective : ∀ a b : α, PSet.Equiv (emb a) (emb b) → a = b := by
  have hwo := WellOrderingRel.isWellOrder (α := α)
  intro a
  induction a using (hwo.toIsWellFounded.wf).induction with
  | _ a ih =>
    intro b hab
    rcases trichotomous_of (WellOrderingRel : α → α → Prop) a b with hlt | heq | hgt
    · exfalso
      have hself : emb a ∈ emb a :=
        (PSet.mem_congr_right hab (emb a)).mpr (emb_mem_of_lt hlt)
      obtain ⟨c, hc, hce⟩ := exists_of_mem_emb hself
      have hca : c = a := ih c hc a (PSet.Equiv.symm hce)
      rw [hca] at hc
      exact irrefl_of (WellOrderingRel : α → α → Prop) a hc
    · exact heq
    · exfalso
      have hself : emb b ∈ emb b :=
        (PSet.mem_congr_right hab (emb b)).mp (emb_mem_of_lt hgt)
      obtain ⟨c, hc, hce⟩ := exists_of_mem_emb hself
      have hca : WellOrderingRel c a := trans_of _ hc hgt
      have hcb : c = b := ih c hca b (PSet.Equiv.symm hce)
      rw [hcb] at hc
      exact irrefl_of (WellOrderingRel : α → α → Prop) b hc

/-! ### At the ZFSet level -/

/-- The type's element, as a ZFSet. -/
noncomputable def encode (a : α) : ZFSet.{0} := SetTheory.mk (emb a)

/-- The type ITSELF, as a ZFSet: the set of all the encodings. This is the
carrier a transported structure would live on. -/
noncomputable def encodeSet (α : Type) : ZFSet.{0} := SetTheory.mk ⟨α, emb⟩

theorem encode_mem (a : α) : encode a ∈ encodeSet α := ⟨a, PSet.Equiv.refl _⟩

/-- Every member of the carrier is an encoded element, so the ZFSet is a
faithful copy of the type rather than merely containing one. -/
theorem exists_of_mem_encodeSet {z : ZFSet.{0}} (hz : z ∈ encodeSet α) :
    ∃ a : α, z = encode a := by
  induction z using Quotient.inductionOn with
  | _ w =>
    obtain ⟨a, ha⟩ := hz
    exact ⟨a, Quotient.sound ha⟩

/-- And distinct elements stay distinct. -/
theorem encode_injective {a b : α} (h : encode a = encode b) : a = b :=
  emb_injective a b (Quotient.exact h)

end Comparator.TypeTransfer
