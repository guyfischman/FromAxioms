/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Ordinal addition and multiplication.

    α + β = α ∪ { α + γ | γ ∈ β }          α · β = ⋃ { α·γ + α | γ ∈ β }

Both are stated uniformly, with no split into zero, successor and limit. That is
not a stylistic preference: "β is zero, a successor, or a limit" is not decidable,
so a definition by those cases would need the decision as data and cost choice.
The uniform recursions above have the usual equations as
theorems instead.

The recursion is structural at the pre-set level, exactly as `PSet.V` is:
a pre-set is an index type with a family, so `{ α + γ | γ ∈ β }`
is indexed by `β`'s own index type and needs no replacement. The union with `α`
is a sum of index types.
-/

import FromAxioms.Algebra.Algebra
import FromAxioms.NumberTheory.Natural
import FromAxioms.SetTheory.Hierarchy

universe u

namespace PSet

/-- `α + β`, indexed by `α`'s members and `β`'s. -/
def ordAdd (x : PSet.{u}) : PSet.{u} → PSet.{u}
  | ⟨β, B⟩ => ⟨Sum (Idx x) β, fun s => Sum.elim (Fam x) (fun b => ordAdd x (B b)) s⟩

theorem ordAdd_congr : ∀ {x x' y y' : PSet.{u}}, Equiv x x' → Equiv y y' →
    Equiv (ordAdd x y) (ordAdd x' y')
  | x, x', ⟨β, B⟩, ⟨β', B'⟩, hx, hy => by
    refine (equiv_iff_ext _ _).mpr fun w => ⟨?_, ?_⟩
    · rintro ⟨s, hs⟩
      cases s with
      | inl a =>
        obtain ⟨a', ha'⟩ := ((equiv_iff x x').mp hx).left a
        exact ⟨Sum.inl a', hs.trans ha'⟩
      | inr b =>
        obtain ⟨b', hb'⟩ := ((equiv_iff _ _).mp hy).left b
        exact ⟨Sum.inr b', hs.trans (ordAdd_congr hx hb')⟩
    · rintro ⟨s, hs⟩
      cases s with
      | inl a' =>
        obtain ⟨a, ha⟩ := ((equiv_iff x x').mp hx).right a'
        exact ⟨Sum.inl a, hs.trans ha.symm⟩
      | inr b' =>
        obtain ⟨b, hb⟩ := ((equiv_iff _ _).mp hy).right b'
        exact ⟨Sum.inr b, hs.trans (ordAdd_congr hx hb).symm⟩

theorem mem_ordAdd_iff (w x : PSet.{u}) : ∀ y : PSet.{u},
    w ∈ ordAdd x y ↔ w ∈ x ∨ ∃ z : PSet.{u}, z ∈ y ∧ Equiv w (ordAdd x z)
  | ⟨β, B⟩ => by
    constructor
    · rintro ⟨s, hs⟩
      cases s with
      | inl a => exact Or.inl ⟨a, hs⟩
      | inr b => exact Or.inr ⟨B b, ⟨b, Equiv.refl _⟩, hs⟩
    · rintro (⟨a, ha⟩ | ⟨z, ⟨b, hzb⟩, hw⟩)
      · exact ⟨Sum.inl a, ha⟩
      · exact ⟨Sum.inr b, hw.trans (ordAdd_congr (Equiv.refl x) hzb)⟩

/-- `α · β`, the union of the stages `α·γ + α`. -/
def ordMul (x : PSet.{u}) : PSet.{u} → PSet.{u}
  | ⟨β, B⟩ => sUnion ⟨β, fun b => ordAdd (ordMul x (B b)) x⟩

theorem ordMul_congr : ∀ {x x' y y' : PSet.{u}}, Equiv x x' → Equiv y y' →
    Equiv (ordMul x y) (ordMul x' y')
  | x, x', ⟨β, B⟩, ⟨β', B'⟩, hx, hy => by
    refine sUnion_congr ?_
    refine (equiv_iff_ext _ _).mpr fun w => ⟨?_, ?_⟩
    · rintro ⟨b, hw⟩
      obtain ⟨b', hb'⟩ := ((equiv_iff _ _).mp hy).left b
      exact ⟨b', hw.trans (ordAdd_congr (ordMul_congr hx hb') hx)⟩
    · rintro ⟨b', hw⟩
      obtain ⟨b, hb⟩ := ((equiv_iff _ _).mp hy).right b'
      exact ⟨b, hw.trans (ordAdd_congr (ordMul_congr hx hb) hx).symm⟩

theorem mem_ordMul_iff (w x : PSet.{u}) : ∀ y : PSet.{u},
    w ∈ ordMul x y ↔ ∃ z : PSet.{u}, z ∈ y ∧ w ∈ ordAdd (ordMul x z) x
  | ⟨β, B⟩ => by
    refine Iff.trans (mem_sUnion_iff w _) ⟨?_, ?_⟩
    · rintro ⟨v, ⟨b, hv⟩, hw⟩
      exact ⟨B b, ⟨b, Equiv.refl _⟩, (mem_congr_right hv w).mp hw⟩
    · rintro ⟨z, ⟨b, hzb⟩, hw⟩
      refine ⟨ordAdd (ordMul x (B b)) x, ⟨b, Equiv.refl _⟩, ?_⟩
      exact (mem_congr_right (ordAdd_congr (ordMul_congr (Equiv.refl x) hzb)
        (Equiv.refl x)) w).mp hw

/-- `α ^ β = 1 ∪ ⋃ { α^γ · α | γ ∈ β }`. The `1` is `insert ∅`, which is what
makes the empty exponent come out right without a case. -/
def ordPow (x : PSet.{u}) : PSet.{u} → PSet.{u}
  | ⟨β, B⟩ => insert empty (sUnion ⟨β, fun b => ordMul (ordPow x (B b)) x⟩)

theorem ordPow_congr : ∀ {x x' y y' : PSet.{u}}, Equiv x x' → Equiv y y' →
    Equiv (ordPow x y) (ordPow x' y')
  | x, x', ⟨β, B⟩, ⟨β', B'⟩, hx, hy => by
    refine insert_congr (Equiv.refl _) (sUnion_congr ?_)
    refine (equiv_iff_ext _ _).mpr fun w => ⟨?_, ?_⟩
    · rintro ⟨b, hw⟩
      obtain ⟨b', hb'⟩ := ((equiv_iff _ _).mp hy).left b
      exact ⟨b', hw.trans (ordMul_congr (ordPow_congr hx hb') hx)⟩
    · rintro ⟨b', hw⟩
      obtain ⟨b, hb⟩ := ((equiv_iff _ _).mp hy).right b'
      exact ⟨b, hw.trans (ordMul_congr (ordPow_congr hx hb) hx).symm⟩

theorem mem_ordPow_iff (w x : PSet.{u}) : ∀ y : PSet.{u},
    w ∈ ordPow x y ↔ Equiv w empty ∨ ∃ z : PSet.{u}, z ∈ y ∧ w ∈ ordMul (ordPow x z) x
  | ⟨β, B⟩ => by
    refine Iff.trans (mem_insert_iff w empty _) ⟨?_, ?_⟩
    · rintro (h | h)
      · exact Or.inl h
      · obtain ⟨v, ⟨b, hv⟩, hw⟩ := (mem_sUnion_iff w _).mp h
        exact Or.inr ⟨B b, ⟨b, Equiv.refl _⟩, (mem_congr_right hv w).mp hw⟩
    · rintro (h | ⟨z, ⟨b, hzb⟩, hw⟩)
      · exact Or.inl h
      · refine Or.inr ((mem_sUnion_iff w _).mpr ⟨ordMul (ordPow x (B b)) x,
          ⟨b, Equiv.refl _⟩, ?_⟩)
        exact (mem_congr_right (ordMul_congr (ordPow_congr (Equiv.refl x) hzb)
          (Equiv.refl x)) w).mp hw

/-- The rank: one more than the ranks below. Structural, like `V`. -/
def rank : PSet.{u} → PSet.{u}
  | ⟨α, A⟩ => sUnion ⟨α, fun a => succ (rank (A a))⟩

theorem rank_congr : ∀ {x y : PSet.{u}}, Equiv x y → Equiv (rank x) (rank y)
  | ⟨α, A⟩, ⟨β, B⟩, h => by
    refine sUnion_congr ?_
    refine (equiv_iff_ext _ _).mpr fun w => ⟨?_, ?_⟩
    · rintro ⟨a, hw⟩
      obtain ⟨b, hb⟩ := ((equiv_iff _ _).mp h).left a
      exact ⟨b, hw.trans (insert_congr (rank_congr hb) (rank_congr hb))⟩
    · rintro ⟨b, hw⟩
      obtain ⟨a, ha⟩ := ((equiv_iff _ _).mp h).right b
      exact ⟨a, hw.trans (insert_congr (rank_congr ha) (rank_congr ha)).symm⟩

end PSet

open NumberTheory
namespace SetTheory

/-- Ordinal addition on sets. -/
def ordAdd : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} :=
  Quotient.lift₂ (fun x y => mk (PSet.ordAdd x y))
    (fun _ _ _ _ hx hy => Quotient.sound (PSet.ordAdd_congr hx hy))

/-- Ordinal multiplication on sets. -/
def ordMul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} :=
  Quotient.lift₂ (fun x y => mk (PSet.ordMul x y))
    (fun _ _ _ _ hx hy => Quotient.sound (PSet.ordMul_congr hx hy))

theorem mem_ordAdd_iff (w x y : ZFSet.{u}) :
    w ∈ ordAdd x y ↔ w ∈ x ∨ ∃ z : ZFSet.{u}, z ∈ y ∧ w = ordAdd x z := by
  refine Quotient.inductionOn₃ w x y (fun w x y => ?_)
  refine Iff.trans (PSet.mem_ordAdd_iff w x y) ⟨?_, ?_⟩
  · rintro (h | ⟨z, hz, hw⟩)
    · exact Or.inl h
    · exact Or.inr ⟨mk z, hz, Quotient.sound hw⟩
  · rintro (h | ⟨z, hz, hw⟩)
    · exact Or.inl h
    · obtain ⟨z, rfl⟩ := Quotient.exists_rep z
      exact Or.inr ⟨z, hz, Quotient.exact hw⟩

theorem mem_ordMul_iff (w x y : ZFSet.{u}) :
    w ∈ ordMul x y ↔ ∃ z : ZFSet.{u}, z ∈ y ∧ w ∈ ordAdd (ordMul x z) x := by
  refine Quotient.inductionOn₃ w x y (fun w x y => ?_)
  refine Iff.trans (PSet.mem_ordMul_iff w x y) ⟨?_, ?_⟩
  · rintro ⟨z, hz, hw⟩
    exact ⟨mk z, hz, hw⟩
  · rintro ⟨z, hz, hw⟩
    obtain ⟨z, rfl⟩ := Quotient.exists_rep z
    exact ⟨z, hz, hw⟩

/-! ## The equations

Zero, successor and limit are not cases of the definition; they are theorems
about it. -/

@[simp] theorem ordAdd_empty (x : ZFSet.{u}) : ordAdd x empty.{u} = x := by
  refine ext _ _ fun w => Iff.trans (mem_ordAdd_iff w x empty.{u}) ⟨?_, Or.inl⟩
  rintro (h | ⟨z, hz, -⟩)
  · exact h
  · exact absurd hz (not_mem_empty z)

@[simp] theorem ordMul_empty (x : ZFSet.{u}) : ordMul x empty.{u} = empty.{u} :=
  ext _ _ fun w => ⟨fun hw => by
      obtain ⟨z, hz, -⟩ := (mem_ordMul_iff w x empty.{u}).mp hw
      exact absurd hz (not_mem_empty z),
    fun hw => absurd hw (not_mem_empty w)⟩

/-! ## Rank

The stage at which a set first appears. `V` says every set appears somewhere;
`rank` names where. -/

def rank : ZFSet.{u} → ZFSet.{u} :=
  Quotient.lift (fun x => mk (PSet.rank x)) (fun _ _ h => Quotient.sound (PSet.rank_congr h))

/-- Ordinal exponentiation on sets. -/
def ordPow : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} :=
  Quotient.lift₂ (fun x y => mk (PSet.ordPow x y))
    (fun _ _ _ _ hx hy => Quotient.sound (PSet.ordPow_congr hx hy))

theorem mem_ordPow_iff (w x y : ZFSet.{u}) :
    w ∈ ordPow x y ↔ w = empty.{u} ∨ ∃ z : ZFSet.{u}, z ∈ y ∧ w ∈ ordMul (ordPow x z) x := by
  refine Quotient.inductionOn₃ w x y (fun w x y => ?_)
  refine Iff.trans (PSet.mem_ordPow_iff w x y) ⟨?_, ?_⟩
  · rintro (h | ⟨z, hz, hw⟩)
    · exact Or.inl (Quotient.sound h)
    · exact Or.inr ⟨mk z, hz, hw⟩
  · rintro (h | ⟨z, hz, hw⟩)
    · exact Or.inl (Quotient.exact h)
    · obtain ⟨z, rfl⟩ := Quotient.exists_rep z
      exact Or.inr ⟨z, hz, hw⟩

/-- Zero exponent: the answer is `1`, with no case in the definition. -/
@[simp] theorem ordPow_empty (x : ZFSet.{u}) : ordPow x empty.{u} = ofNat.{u} 1 := by
  refine ext _ _ fun w => Iff.trans (mem_ordPow_iff w x empty.{u}) ⟨?_, ?_⟩
  · rintro (rfl | ⟨z, hz, -⟩)
    · exact mem_succ_self empty.{u}
    · exact absurd hz (not_mem_empty z)
  · intro hw
    rcases (mem_succ_iff w empty.{u}).mp hw with rfl | h
    · exact Or.inl rfl
    · exact absurd h (not_mem_empty w)

/-! ## `ε₀`

The tower `ω, ω^ω, …` is a `Nat`-indexed family of sets with no bound to
separate over, so `natSeq` cannot build it. At pre-set level it needs no bound:
a family indexed by `ULift Nat` is a pre-set, exactly as for `V`.
-/

def tower : Nat → ZFSet.{u}
  | 0 => omega
  | n + 1 => ordPow omega (tower n)

#print axioms PSet.ordAdd_congr
#print axioms mem_ordAdd_iff
#print axioms ordPow_empty
end SetTheory

namespace ZFSet
export SetTheory (mem_ordAdd_iff mem_ordMul_iff mem_ordPow_iff ordAdd ordAdd_empty ordMul ordMul_empty ordPow ordPow_empty rank tower)
end ZFSet
