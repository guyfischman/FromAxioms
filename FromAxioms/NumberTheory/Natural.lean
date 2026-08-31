/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The natural numbers, as sets.

`omega` was constructed in `PSet.lean` as the von Neumann naturals -- `0 = ∅`
and `n+1 = n ∪ {n}` -- and shown to contain `∅` and be closed under successor.
That is the axiom of infinity. It is not yet arithmetic.

This file proves `omega` satisfies the Peano axioms:

  P1  `∅ ∈ omega`                        already proved, in `PSet.lean`
  P2  closure under `succ`               already proved, in `PSet.lean`
  P3  `succ n ≠ ∅`                       `succ_ne_empty`
  P4  `succ` is injective                `succ_injective`
  P5  induction                          `omega_induction`

and that `ofNat : Nat → ZFSet` is injective with image exactly `omega` -- so the
sets in `omega` are in bijection with Lean's `Nat`, and this really is ℕ rather
than something that merely resembles it.

## The one that needs foundation

P3 and P5 are routine. P4 draws on the earlier work. Suppose
`succ m = succ n`. Since `m ∈ succ m`, we get `m ∈ succ n`, hence `m = n` or
`m ∈ n`; symmetrically `n = m` or `n ∈ m`. The bad case is `m ∈ n` and
`n ∈ m` -- a two-step membership cycle. Ruling it out is exactly what
regularity is for, and `not_mem_mem` below derives it from ∈-induction.

Not needed: no transitivity of the naturals, and no restriction to `omega`.
`succ_injective` holds for arbitrary sets, because the cycle is impossible for
arbitrary sets.

## Cost

All of it is `[propext, Quot.sound]` -- the quotient, and nothing more.
Peano arithmetic here is choice-free, including P4, because the constructive
half of regularity (`inductionOn`) is what P4 actually uses. `Classical.choice`
was needed for the existence form of regularity, which never appears below.
-/

import FromAxioms.SetTheory.Regularity

universe u

open SetTheory
namespace NumberTheory

/-! ## `Nat` and `omega` are the same thing -/

/-- The von Neumann numeral of a Lean natural. -/
def ofNat (n : Nat) : ZFSet.{u} := mk (PSet.ofNat n)

/-- Both hold by `rfl`: the quotient's `insert` computes on representatives, so
the `ZFSet` recursion and the `PSet` recursion are the same recursion. -/
@[simp] theorem ofNat_zero : ofNat.{u} 0 = empty.{u} := rfl

@[simp] theorem ofNat_succ (n : Nat) : ofNat.{u} (n + 1) = succ (ofNat.{u} n) := rfl

theorem ofNat_mem_omega (n : Nat) : ofNat.{u} n ∈ omega.{u} :=
  ⟨ULift.up n, PSet.Equiv.refl _⟩

/-- `omega` is exactly the image of `ofNat` -- every member is a numeral and
every numeral is a member. -/
theorem mem_omega_iff (x : ZFSet.{u}) : x ∈ omega.{u} ↔ ∃ n : Nat, x = ofNat.{u} n := by
  refine Quotient.inductionOn x (fun x => ?_)
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n.down, mk_eq_mk.mpr hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨ULift.up n, mk_eq_mk.mp hn⟩

/-! ## P3: zero is not a successor -/

theorem mem_succ_self (x : ZFSet.{u}) : x ∈ succ x :=
  (mem_insert_iff x x x).mpr (Or.inl rfl)

theorem mem_succ_iff (w x : ZFSet.{u}) : w ∈ succ x ↔ w = x ∨ w ∈ x :=
  mem_insert_iff w x x

/-- P3 of the Peano axioms: no successor is empty. -/
theorem succ_ne_empty (x : ZFSet.{u}) : succ x ≠ empty.{u} :=
  fun h => not_mem_empty x (h ▸ mem_succ_self x)

/-! ## P4: the successor is injective

The two-cycle lemma first. This is foundation doing real work: nothing about
the definition of membership forbids `x ∈ y ∈ x`, and only well-foundedness
rules it out. -/

/-- No two-step membership cycle. Proved by ∈-induction on `x`: the inductive
hypothesis applies to `y`, which is a member of `x`, and then contradicts
itself. -/
theorem not_mem_mem : ∀ x y : ZFSet.{u}, x ∈ y → y ∈ x → False :=
  inductionOn (motive := fun x => ∀ y : ZFSet.{u}, x ∈ y → y ∈ x → False)
    (fun x ih y hxy hyx => ih y hyx x hyx hxy)

/-- P4. Note there is no hypothesis that `m` or `n` lies in `omega`: the
argument works for arbitrary sets. -/
theorem succ_injective {m n : ZFSet.{u}} (h : succ m = succ n) : m = n := by
  have hm : m ∈ succ n := h ▸ mem_succ_self m
  have hn : n ∈ succ m := h ▸ mem_succ_self n
  rcases (mem_succ_iff m n).mp hm with h₁ | h₁
  · exact h₁
  · rcases (mem_succ_iff n m).mp hn with h₂ | h₂
    · exact h₂.symm
    · exact (not_mem_mem m n h₁ h₂).elim

/-! ## `omega` really is ℕ

`mem_omega_iff` gave surjectivity of `ofNat` onto `omega`; injectivity makes it
a bijection. So the set-theoretic naturals and Lean's inductive `Nat` carry the
same information, which is the sense in which this construction has arrived
somewhere rather than merely restated its starting point. -/

/-- The `show ... from` casts are load-bearing: `ofNat (n+1) = ofNat 0` and
`succ (ofNat n) = empty` are definitionally equal, but `absurd` will not unfold
`ofNat` on its own to see it. -/
theorem ofNat_injective : ∀ {m n : Nat}, ofNat.{u} m = ofNat.{u} n → m = n
  | 0,     0,     _ => rfl
  | 0,     n + 1, h =>
    absurd (show succ (ofNat.{u} n) = empty.{u} from h.symm) (succ_ne_empty _)
  | m + 1, 0,     h =>
    absurd (show succ (ofNat.{u} m) = empty.{u} from h) (succ_ne_empty _)
  | _ + 1, _ + 1, h => congrArg (· + 1) (ofNat_injective (succ_injective h))

/-- The order structure of the numerals: `ofNat n` is exactly `{0, …, n-1}`. -/
theorem mem_ofNat_iff (w : ZFSet.{u}) : ∀ n : Nat,
    w ∈ ofNat.{u} n ↔ ∃ k, k < n ∧ w = ofNat.{u} k
  | 0 => by
    rw [ofNat_zero]
    exact ⟨fun h => absurd h (not_mem_empty w), fun ⟨_, hk, _⟩ => absurd hk (Nat.not_lt_zero _)⟩
  | n + 1 => by
    rw [ofNat_succ, mem_succ_iff]
    constructor
    · rintro (rfl | h)
      · exact ⟨n, Nat.lt_succ_self n, rfl⟩
      · obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff w n).mp h
        exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
      · exact Or.inr ((mem_ofNat_iff _ n).mpr ⟨k, h, rfl⟩)
      · exact Or.inl rfl

/-- Order on the numerals is inclusion. Choice-free: the case split is on
`Nat`, where `≤` is decidable. -/
theorem ofNat_subset_iff (m n : Nat) : ofNat.{u} m ⊆ ofNat.{u} n ↔ m ≤ n := by
  constructor
  · intro h
    rcases Nat.lt_or_ge n m with hlt | hle
    · exact absurd (h _ ((mem_ofNat_iff _ m).mpr ⟨n, hlt, rfl⟩)) (not_mem_self _)
    · exact hle
  · intro h w hw
    obtain ⟨k, hk, rfl⟩ := (mem_ofNat_iff w m).mp hw
    exact (mem_ofNat_iff _ n).mpr ⟨k, Nat.lt_of_lt_of_le hk h, rfl⟩

#print axioms succ_ne_empty     -- P3
#print axioms not_mem_mem       -- foundation, in the form P4 needs
#print axioms succ_injective    -- P4
#print axioms ofNat_injective
#print axioms mem_omega_iff
end NumberTheory

namespace ZFSet
export NumberTheory (mem_ofNat_iff mem_omega_iff mem_succ_iff mem_succ_self not_mem_mem ofNat ofNat_injective ofNat_mem_omega ofNat_subset_iff ofNat_succ ofNat_zero succ_injective succ_ne_empty)
end ZFSet
