/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Arithmetic on ω.

Addition and multiplication are defined set-theoretically, by structural
recursion on the pre-set:

    x + y = x ∪ { x + z | z ∈ y }
    x * y = ⋃ { (x * z) + x | z ∈ y }

Recursing on the pre-set keeps both computable and choice-free. The
alternative -- inverting `ofNat` to reach a `Nat` and adding there -- needs
`Classical.choice`, because extracting a provably-unique natural has no analogue
of the union-of-singleton trick that keeps `SetTheory.app` choice-free.

`mul_ofNat` needs strong induction and the order structure of the numerals
(`mem_ofNat_iff`): the union is correct because its terms are nested, which the
recursion alone does not give.
-/

import FromAxioms.SetTheory.Relation

universe u

namespace PSet

def add : PSet.{u} → PSet.{u} → PSet.{u}
  | ⟨α, A⟩, ⟨β, B⟩ => ⟨Sum α β, fun i =>
      match i with
      | .inl a => A a
      | .inr b => add ⟨α, A⟩ (B b)⟩

theorem mem_add_iff (w : PSet.{u}) : ∀ x y : PSet.{u},
    w ∈ add x y ↔ w ∈ x ∨ ∃ b : Idx y, Equiv w (add x (Fam y b))
  | ⟨_, _⟩, ⟨_, _⟩ => by
    simp only [add]
    constructor
    · rintro ⟨i, h⟩
      cases i with
      | inl a => exact Or.inl ⟨a, h⟩
      | inr b => exact Or.inr ⟨b, h⟩
    · rintro (⟨a, h⟩ | ⟨b, h⟩)
      · exact ⟨.inl a, h⟩
      · exact ⟨.inr b, h⟩

theorem add_congr : ∀ (y y' : PSet.{u}) {x x' : PSet.{u}},
    Equiv x x' → Equiv y y' → Equiv (add x y) (add x' y')
  | ⟨_, B⟩, ⟨_, B'⟩, ⟨_, A⟩, ⟨_, A'⟩, hx, hy => by
    obtain ⟨hx₁, hx₂⟩ := id hx
    obtain ⟨hy₁, hy₂⟩ := id hy
    simp only [add]
    refine And.intro ?_ ?_
    · rintro (a | b)
      · obtain ⟨a', ha⟩ := hx₁ a
        exact ⟨.inl a', ha⟩
      · obtain ⟨b', hb⟩ := hy₁ b
        exact ⟨.inr b', add_congr (B b) (B' b') hx hb⟩
    · rintro (a' | b')
      · obtain ⟨a, ha⟩ := hx₂ a'
        exact ⟨.inl a, ha⟩
      · obtain ⟨b, hb⟩ := hy₂ b'
        exact ⟨.inr b, add_congr (B b) (B' b') hx hb⟩

def mul : PSet.{u} → PSet.{u} → PSet.{u}
  | ⟨α, A⟩, ⟨β, B⟩ => sUnion ⟨β, fun b => add (mul ⟨α, A⟩ (B b)) ⟨α, A⟩⟩

theorem mem_mul_iff (w : PSet.{u}) : ∀ x y : PSet.{u},
    w ∈ mul x y ↔ ∃ b : Idx y, w ∈ add (mul x (Fam y b)) x
  | ⟨_, _⟩, ⟨_, _⟩ => by
    simp only [mul]
    refine Iff.trans (mem_sUnion_iff w _) ?_
    constructor
    · rintro ⟨z, ⟨b, hz⟩, hw⟩
      exact ⟨b, (mem_congr_right hz w).mp hw⟩
    · rintro ⟨b, hw⟩
      exact ⟨_, ⟨b, Equiv.refl _⟩, hw⟩

theorem mul_congr : ∀ (y y' : PSet.{u}) {x x' : PSet.{u}},
    Equiv x x' → Equiv y y' → Equiv (mul x y) (mul x' y')
  | ⟨_, B⟩, ⟨_, B'⟩, x, x', hx, hy => by
    obtain ⟨hy₁, hy₂⟩ := id hy
    refine (equiv_iff_ext _ _).mpr fun w => ?_
    refine Iff.trans (mem_mul_iff w _ _) (Iff.trans ?_ (mem_mul_iff w _ _).symm)
    constructor
    · rintro ⟨b, hw⟩
      obtain ⟨b', hb⟩ := hy₁ b
      exact ⟨b', (mem_congr_right
        (add_congr _ _ (mul_congr (B b) (B' b') hx hb) hx) w).mp hw⟩
    · rintro ⟨b', hw⟩
      obtain ⟨b, hb⟩ := hy₂ b'
      exact ⟨b, (mem_congr_right
        (add_congr _ _ (mul_congr (B b) (B' b') hx hb) hx) w).mpr hw⟩

end PSet

open Algebra SetTheory
namespace NumberTheory

def add : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} :=
  Quotient.lift₂ (fun x y => mk (PSet.add x y))
    (fun _ _ _ _ hx hy => Quotient.sound (PSet.add_congr _ _ hx hy))

def mul : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} :=
  Quotient.lift₂ (fun x y => mk (PSet.mul x y))
    (fun _ _ _ _ hx hy => Quotient.sound (PSet.mul_congr _ _ hx hy))

theorem mem_mul_iff (w x y : ZFSet.{u}) :
    w ∈ mul x y ↔ ∃ z, z ∈ y ∧ w ∈ add (mul x z) x := by
  refine Quotient.inductionOn₃ w x y (fun w x y => ?_)
  refine Iff.trans (PSet.mem_mul_iff w x y) ?_
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨mk (PSet.Fam y b), ⟨b, PSet.Equiv.refl _⟩, hb⟩
  · rintro ⟨z, hz, hw⟩
    obtain ⟨z, rfl⟩ := Quotient.exists_rep z
    obtain ⟨b, hb⟩ := hz
    exact ⟨b, (PSet.mem_congr_right
      (PSet.add_congr _ _ (PSet.mul_congr _ _ (PSet.Equiv.refl x) hb)
        (PSet.Equiv.refl x)) w).mp hw⟩

theorem mem_add_iff (w x y : ZFSet.{u}) :
    w ∈ add x y ↔ w ∈ x ∨ ∃ z, z ∈ y ∧ w = add x z := by
  refine Quotient.inductionOn₃ w x y (fun w x y => ?_)
  refine Iff.trans (PSet.mem_add_iff w x y) ?_
  constructor
  · rintro (h | ⟨b, hb⟩)
    · exact Or.inl h
    · exact Or.inr ⟨mk (PSet.Fam y b), ⟨b, PSet.Equiv.refl _⟩, mk_eq_mk.mpr hb⟩
  · rintro (h | ⟨z, hz, he⟩)
    · exact Or.inl h
    · obtain ⟨z, rfl⟩ := Quotient.exists_rep z
      obtain ⟨b, hb⟩ := hz
      exact Or.inr ⟨b, mk_eq_mk.mp
        (he.trans (Quotient.sound (PSet.add_congr _ _ (PSet.Equiv.refl x) hb)))⟩

/-! ## The recursion equations -/

@[simp] theorem add_empty (x : ZFSet.{u}) : add x empty.{u} = x :=
  ext _ _ fun w => by
    refine Iff.trans (mem_add_iff w x empty) ⟨?_, Or.inl⟩
    rintro (h | ⟨z, hz, _⟩)
    · exact h
    · exact absurd hz (not_mem_empty z)

/-- The recursive definition of `+`, second clause. -/
theorem add_succ (x y : ZFSet.{u}) : add x (succ y) = succ (add x y) :=
  ext _ _ fun w => by
    refine Iff.trans (mem_add_iff w x (succ y)) ?_
    refine Iff.trans ?_ (mem_succ_iff w (add x y)).symm
    constructor
    · rintro (h | ⟨z, hz, rfl⟩)
      · exact Or.inr ((mem_add_iff _ x y).mpr (Or.inl h))
      · rcases (mem_succ_iff z y).mp hz with rfl | hzy
        · exact Or.inl rfl
        · exact Or.inr ((mem_add_iff _ x y).mpr (Or.inr ⟨z, hzy, rfl⟩))
    · rintro (rfl | h)
      · exact Or.inr ⟨y, mem_succ_self y, rfl⟩
      · rcases (mem_add_iff w x y).mp h with h | ⟨z, hz, rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨z, (mem_succ_iff z y).mpr (Or.inr hz), rfl⟩

@[simp] theorem mul_empty (x : ZFSet.{u}) : mul x empty.{u} = empty.{u} :=
  ext _ _ fun w => by
    refine Iff.trans (mem_mul_iff w x empty) ?_
    exact ⟨fun ⟨z, hz, _⟩ => absurd hz (not_mem_empty z),
           fun h => absurd h (not_mem_empty w)⟩

/-! ## Agreement with `ofNat`, and the laws -/

@[simp] theorem add_ofNat (m : Nat) : ∀ n : Nat,
    add (ofNat.{u} m) (ofNat.{u} n) = ofNat.{u} (m + n)
  | 0 => add_empty _
  | n + 1 => by
    rw [ofNat_succ n, add_succ, add_ofNat m n, ← ofNat_succ (m + n)]
    rfl

theorem mul_ofNat (m : Nat) : ∀ n : Nat,
    mul (ofNat.{u} m) (ofNat.{u} n) = ofNat.{u} (m * n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    refine ext _ _ fun w => ?_
    refine Iff.trans (mem_mul_iff w _ _) (Iff.trans ?_ (mem_ofNat_iff w (m * n)).symm)
    constructor
    · rintro ⟨z, hz, hw⟩
      obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff z n).mp hz
      rw [ih k hk, add_ofNat] at hw
      obtain ⟨j, hj, rfl⟩ := (mem_ofNat_iff _ (m * k + m)).mp hw
      refine ⟨j, ?_, rfl⟩
      have hle : m * (k + 1) ≤ m * n := Nat.mul_le_mul (Nat.le_refl m) hk
      rw [Nat.mul_succ] at hle
      omega
    · rintro ⟨j, hj, rfl⟩
      cases n with
      | zero => rw [Nat.mul_zero] at hj; exact absurd hj (Nat.not_lt_zero _)
      | succ n' =>
        refine ⟨ofNat n', (mem_ofNat_iff _ (n' + 1)).mpr ⟨n', Nat.lt_succ_self _, rfl⟩, ?_⟩
        rw [ih n' (Nat.lt_succ_self _), add_ofNat]
        rw [Nat.mul_succ] at hj
        exact (mem_ofNat_iff _ (m * n' + m)).mpr ⟨j, hj, rfl⟩

theorem add_mem_omega {x y : ZFSet.{u}} (hx : x ∈ omega.{u}) (hy : y ∈ omega.{u}) :
    add x y ∈ omega.{u} := by
  obtain ⟨m, rfl⟩ := (mem_omega_iff x).mp hx
  obtain ⟨n, rfl⟩ := (mem_omega_iff y).mp hy
  rw [add_ofNat]; exact ofNat_mem_omega _

@[simp] theorem empty_add {x : ZFSet.{u}} (hx : x ∈ omega.{u}) : add empty.{u} x = x := by
  obtain ⟨n, rfl⟩ := (mem_omega_iff x).mp hx
  rw [← ofNat_zero, add_ofNat, Nat.zero_add]

theorem add_comm {x y : ZFSet.{u}} (hx : x ∈ omega.{u}) (hy : y ∈ omega.{u}) :
    add x y = add y x := by
  obtain ⟨m, rfl⟩ := (mem_omega_iff x).mp hx
  obtain ⟨n, rfl⟩ := (mem_omega_iff y).mp hy
  rw [add_ofNat, add_ofNat, Nat.add_comm]

theorem add_assoc {x y z : ZFSet.{u}} (hx : x ∈ omega.{u}) (hy : y ∈ omega.{u})
    (hz : z ∈ omega.{u}) : add (add x y) z = add x (add y z) := by
  obtain ⟨m, rfl⟩ := (mem_omega_iff x).mp hx
  obtain ⟨n, rfl⟩ := (mem_omega_iff y).mp hy
  obtain ⟨k, rfl⟩ := (mem_omega_iff z).mp hz
  rw [add_ofNat, add_ofNat, add_ofNat, add_ofNat, Nat.add_assoc]

theorem mul_mem_omega {x y : ZFSet.{u}} (hx : x ∈ omega.{u}) (hy : y ∈ omega.{u}) :
    mul x y ∈ omega.{u} := by
  obtain ⟨m, rfl⟩ := (mem_omega_iff x).mp hx
  obtain ⟨n, rfl⟩ := (mem_omega_iff y).mp hy
  rw [mul_ofNat]; exact ofNat_mem_omega _

theorem mul_comm {x y : ZFSet.{u}} (hx : x ∈ omega.{u}) (hy : y ∈ omega.{u}) :
    mul x y = mul y x := by
  obtain ⟨m, rfl⟩ := (mem_omega_iff x).mp hx
  obtain ⟨n, rfl⟩ := (mem_omega_iff y).mp hy
  rw [mul_ofNat, mul_ofNat, Nat.mul_comm]

#print axioms add
#print axioms add_succ
#print axioms add_ofNat
#print axioms add_assoc
#print axioms mul_ofNat
end NumberTheory

namespace ZFSet
export NumberTheory (add add_assoc add_comm add_empty add_mem_omega add_ofNat add_succ empty_add mem_add_iff mem_mul_iff mul mul_comm mul_empty mul_mem_omega mul_ofNat)
end ZFSet
