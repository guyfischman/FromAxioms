/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The algebra of sets.

Binary union, intersection, difference and singletons, plus the standard laws
relating them. None of this needs new machinery: every operation is a few lines
from `sUnion`, `pair` and `sep`, which `ZFSet.lean` already provides.

    singleton x = insert x ∅          union x y = ⋃₀ {x, y}
    inter x y   = { w ∈ x | w ∈ y }   sdiff x y = { w ∈ x | w ∉ y }

Every proof below has the same shape: apply `ext`, rewrite membership on both
sides, and discharge the propositional core.
-/

import FromAxioms.SetTheory.ZFSet

universe u v

open SetTheory
namespace Algebra

/-! ## Singletons -/

def singleton (x : ZFSet.{u}) : ZFSet.{u} := insert x empty

@[simp] theorem mem_singleton_iff (w x : ZFSet.{u}) : w ∈ singleton x ↔ w = x := by
  refine Iff.trans (mem_insert_iff w x empty) ?_
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h (not_mem_empty w)
  · exact Or.inl

theorem mem_singleton_self (x : ZFSet.{u}) : x ∈ singleton x :=
  (mem_singleton_iff x x).mpr rfl

theorem singleton_injective {x y : ZFSet.{u}} (h : singleton x = singleton y) : x = y :=
  (mem_singleton_iff x y).mp (h ▸ mem_singleton_self x)

/-! ## Union, intersection, difference

Registered against Lean's `Union`/`Inter`/`SDiff` classes so the laws below can
be stated with `∪`, `∩` and `\` rather than as nested applications. -/

def union (x y : ZFSet.{u}) : ZFSet.{u} := sUnion (pair x y)

def inter (x y : ZFSet.{u}) : ZFSet.{u} := sep (fun w => w ∈ y) x

def sdiff (x y : ZFSet.{u}) : ZFSet.{u} := sep (fun w => w ∉ y) x

instance : Union ZFSet.{u} := ⟨union⟩
instance : Inter ZFSet.{u} := ⟨inter⟩
instance : SDiff ZFSet.{u} := ⟨sdiff⟩

@[simp] theorem mem_union_iff (w x y : ZFSet.{u}) : w ∈ x ∪ y ↔ w ∈ x ∨ w ∈ y := by
  refine Iff.trans (mem_sUnion_iff w (pair x y)) ?_
  constructor
  · rintro ⟨z, hz, hwz⟩
    rcases (mem_pair_iff z x y).mp hz with rfl | rfl
    · exact Or.inl hwz
    · exact Or.inr hwz
  · rintro (h | h)
    · exact ⟨x, (mem_pair_iff x x y).mpr (Or.inl rfl), h⟩
    · exact ⟨y, (mem_pair_iff y x y).mpr (Or.inr rfl), h⟩

@[simp] theorem mem_inter_iff (w x y : ZFSet.{u}) : w ∈ x ∩ y ↔ w ∈ x ∧ w ∈ y :=
  mem_sep_iff (fun w => w ∈ y) w x

@[simp] theorem mem_sdiff_iff (w x y : ZFSet.{u}) : w ∈ x \ y ↔ w ∈ x ∧ w ∉ y :=
  mem_sep_iff (fun w => w ∉ y) w x

/-! ## The laws

`ext` reduces each to a propositional identity, which `simp` then closes using
the membership lemmas above. -/


@[simp] theorem union_self (x : ZFSet.{u}) : x ∪ x = x :=
  ext _ _ fun z => by simp

@[simp] theorem union_empty (x : ZFSet.{u}) : x ∪ empty.{u} = x :=
  ext _ _ fun z => by simp

@[simp] theorem empty_union (x : ZFSet.{u}) : empty.{u} ∪ x = x :=
  ext _ _ fun z => by simp

@[simp] theorem inter_self (x : ZFSet.{u}) : x ∩ x = x :=
  ext _ _ fun z => by simp

@[simp] theorem inter_empty (x : ZFSet.{u}) : x ∩ empty.{u} = empty.{u} :=
  ext _ _ fun z => by simp

@[simp] theorem empty_inter (x : ZFSet.{u}) : empty.{u} ∩ x = empty.{u} :=
  ext _ _ fun z => by simp

/-! ### Absorption -/

@[simp] theorem union_inter_cancel (x y : ZFSet.{u}) : x ∪ x ∩ y = x :=
  ext _ _ fun w => by
    simp only [mem_union_iff, mem_inter_iff]
    exact ⟨fun h => h.elim id And.left, Or.inl⟩

@[simp] theorem inter_union_cancel (x y : ZFSet.{u}) : x ∩ (x ∪ y) = x :=
  ext _ _ fun w => by
    simp only [mem_union_iff, mem_inter_iff]
    exact ⟨And.left, fun h => ⟨h, Or.inl h⟩⟩

/-! ### Difference, and relative De Morgan

`ZFSet` has no complement -- there is no universal set -- so De Morgan appears
in its relative form, with `x \ ·` playing the part of negation. -/

@[simp] theorem sdiff_self (x : ZFSet.{u}) : x \ x = empty.{u} :=
  ext _ _ fun w => by simp

@[simp] theorem sdiff_empty (x : ZFSet.{u}) : x \ empty.{u} = x :=
  ext _ _ fun w => by simp

@[simp] theorem empty_sdiff (x : ZFSet.{u}) : empty.{u} \ x = empty.{u} :=
  ext _ _ fun w => by simp

/-- A subset and its complement cover, once membership in the subset is decided.
The decision is a hypothesis rather than `em`, so the caller says where it comes
from. -/
theorem union_sdiff_self {x y : ZFSet.{u}} (hsub : ∀ w, w ∈ y → w ∈ x)
    (hdet : ∀ w, w ∈ x → w ∈ y ∨ w ∉ y) : x = y ∪ (x \ y) := by
  refine ext _ _ fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · rcases hdet w hw with h | h
    · exact (mem_union_iff _ _ _).mpr (Or.inl h)
    · exact (mem_union_iff _ _ _).mpr (Or.inr ((mem_sdiff_iff _ _ _).mpr ⟨hw, h⟩))
  · rcases (mem_union_iff _ _ _).mp hw with h | h
    · exact hsub w h
    · exact ((mem_sdiff_iff _ _ _).mp h).left

#print axioms union
/-! ### Difference against itself -/

/-- Removing `x` from anything already inside `x` leaves nothing. -/
@[simp] theorem sdiff_sdiff_left_self (x y : ZFSet.{u}) : (x \ y) \ x = empty.{u} :=
  ext _ _ fun w => by
    simp only [mem_sdiff_iff, not_mem_empty, iff_false]
    rintro ⟨⟨h, _⟩, h'⟩
    exact h' h

/-! ### Subset characterizations -/

@[simp] theorem empty_subset (x : ZFSet.{u}) : empty.{u} ⊆ x :=
  fun w hw => absurd hw (not_mem_empty w)

theorem sdiff_subset (x y : ZFSet.{u}) : x \ y ⊆ x :=
  fun _ h => ((mem_sdiff_iff _ x y).mp h).left

@[simp] theorem sUnion_singleton (x : ZFSet.{u}) : sUnion (singleton x) = x :=
  ext _ _ fun w => by
    simp only [mem_sUnion_iff, mem_singleton_iff]
    exact ⟨fun ⟨_, hz, hw⟩ => hz ▸ hw, fun hw => ⟨x, rfl, hw⟩⟩

/-! ### The degenerate cases

Written down because they are what a model asks for first: `V ω`'s closure
proofs and the two-element structure both needed `⋃ ∅`, and it was being proved
inline each time. -/

@[simp] theorem sUnion_empty : sUnion empty.{u} = empty.{u} := by
  refine ext _ _ fun w => ⟨fun hw => ?_, fun hw => absurd hw (not_mem_empty w)⟩
  obtain ⟨y, hy, -⟩ := (mem_sUnion_iff w _).mp hw
  exact absurd hy (not_mem_empty y)

@[simp] theorem powerset_empty : powerset empty.{u} = singleton empty.{u} :=
  ext _ _ fun w => Iff.trans (mem_powerset_iff w _)
    (Iff.trans ⟨fun h => ext _ _ fun t => ⟨fun ht => h t ht, fun ht =>
        absurd ht (not_mem_empty t)⟩,
      fun h t ht => absurd (h ▸ ht) (not_mem_empty t)⟩
      (mem_singleton_iff w _).symm)

@[simp] theorem sep_empty (p : ZFSet.{u} → Prop) : sep p empty.{u} = empty.{u} :=
  ext _ _ fun w => ⟨fun hw => absurd ((mem_sep_iff _ _ _).mp hw).left
    (not_mem_empty w), fun hw => absurd hw (not_mem_empty w)⟩

/-! ## Audit -/

#print axioms mem_union_iff
#print axioms empty_subset
#print axioms union_sdiff_self
#print axioms sdiff_sdiff_left_self

/-- The union of the first `n` blocks of an enumerated family. -/
def unionUpto (F : Nat → ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => empty
  | n + 1 => unionUpto F n ∪ F n

theorem mem_unionUpto_iff (F : Nat → ZFSet.{u}) :
    ∀ n : Nat, ∀ w, w ∈ unionUpto F n ↔ ∃ i, i < n ∧ w ∈ F i
  | 0, w => by
    refine ⟨fun h => absurd h (not_mem_empty w), ?_⟩
    rintro ⟨i, hi, -⟩
    exact absurd hi (Nat.not_lt_zero i)
  | n + 1, w => by
    refine Iff.trans (mem_union_iff _ _ _) ⟨?_, ?_⟩
    · rintro (h | h)
      · obtain ⟨i, hi, hw⟩ := (mem_unionUpto_iff F n w).mp h
        exact ⟨i, by omega, hw⟩
      · exact ⟨n, Nat.lt_succ_self n, h⟩
    · rintro ⟨i, hi, hw⟩
      rcases Nat.lt_or_ge i n with hlt | hge
      · exact Or.inl ((mem_unionUpto_iff F n w).mpr ⟨i, hlt, hw⟩)
      · have : i = n := by omega
        exact Or.inr (this ▸ hw)

#print axioms unionUpto
#print axioms mem_unionUpto_iff
/-- The unique element carved out of `S` by `P`, as a definite description.

`sep` collects the elements with the property and `sUnion` opens the singleton,
so when the property holds of exactly one element this NAMES it. Nothing is
chosen: uniqueness makes the separation a singleton, and `sUnion_singleton` is
an equation rather than a selection, so no `Classical.choice` and no representative-picking operator
enter. That is the difference between a definite description and a choice
function, and it is why the second was removed from this development.

Off by itself, `theOnly` is whatever `sUnion (sep P S)` happens to be -- `∅` when
nothing has the property, and the union of the candidates when several do. The
spec below is what makes it a description, and it takes the uniqueness as a
hypothesis rather than assuming it. -/
def theOnly (P : ZFSet.{u} → Prop) (S : ZFSet.{u}) : ZFSet.{u} := sUnion (sep P S)

theorem sep_eq_singleton {P : ZFSet.{u} → Prop} {S a : ZFSet.{u}}
    (ha : a ∈ S) (hPa : P a) (huniq : ∀ b, b ∈ S → P b → b = a) :
    sep P S = singleton a :=
  ext _ _ fun w => Iff.intro
    (fun hw => by
      obtain ⟨hwS, hwP⟩ := (mem_sep_iff P w S).mp hw
      rw [huniq w hwS hwP]
      exact mem_singleton_self a)
    (fun hw => by
      rw [(mem_singleton_iff w a).mp hw]
      exact (mem_sep_iff P a S).mpr ⟨ha, hPa⟩)

/-- The description names the element, given that there is exactly one. -/
theorem theOnly_eq {P : ZFSet.{u} → Prop} {S a : ZFSet.{u}}
    (ha : a ∈ S) (hPa : P a) (huniq : ∀ b, b ∈ S → P b → b = a) :
    theOnly P S = a := by
  rw [theOnly, sep_eq_singleton ha hPa huniq, sUnion_singleton]

#print axioms sep_eq_singleton
#print axioms theOnly
#print axioms theOnly_eq
end Algebra
#print axioms Algebra.empty_inter
#print axioms Algebra.empty_sdiff
#print axioms Algebra.inter_union_cancel
#print axioms Algebra.powerset_empty
#print axioms Algebra.sep_empty
#print axioms Algebra.union_inter_cancel
#print axioms Algebra.empty_union
#print axioms Algebra.inter_empty
#print axioms Algebra.inter_self
#print axioms Algebra.union_empty
#print axioms Algebra.union_self
namespace ZFSet
export Algebra (empty_inter empty_sdiff empty_subset empty_union inter inter_empty inter_self inter_union_cancel mem_inter_iff mem_sdiff_iff mem_singleton_iff mem_singleton_self mem_unionUpto_iff mem_union_iff powerset_empty sUnion_empty sUnion_singleton sdiff sdiff_empty sdiff_sdiff_left_self sdiff_self sdiff_subset sep_empty sep_eq_singleton singleton singleton_injective theOnly theOnly_eq union unionUpto union_empty union_inter_cancel union_sdiff_self union_self)
end ZFSet
