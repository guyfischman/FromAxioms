/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Counting a disjoint union.

`equinumerous_union_disjoint` counts TWO disjoint blocks. Every counting
argument over a partition wants that iterated, and this is it.

The statement is a divisibility invariant rather than a sum. Writing the
sum of the block sizes needs a `Nat`-valued fold over a family, which the
library's `setFold` -- which folds `ZFSet` operations -- does not give. The
arguments that want this do not need the sum: they need to know a prime divides
the total. Carrying divisibility through the induction never forms a sum at
all, so the missing fold is not missing for anything.

Stated generally rather than beside the argument that wanted it first. A
counting lemma buried in a group-theory file is a lemma nothing else can find.
-/

import FromAxioms.SetTheory.Cardinal

universe u

open Algebra NumberTheory SetTheory
namespace Combinatorics

/-- A disjoint union of blocks whose sizes a prime divides has a size that
prime divides. No sum is ever formed: the divisibility is carried as an
invariant through the induction, so this avoids the `Nat`-valued fold over a
family the library does not have. -/
theorem dvd_card_unionUpto {p : Nat} (F : Nat → ZFSet.{u}) :
    ∀ n : Nat,
    (∀ i, i < n → ∃ m, Equinumerous (F i) (ofNat.{u} m) ∧ p ∣ m) →
    (∀ i j, i < n → j < n → i ≠ j → ∀ w, w ∈ F i → w ∉ F j) →
    ∃ N, Equinumerous (unionUpto F n) (ofNat.{u} N) ∧ p ∣ N
  | 0, _, _ => ⟨0, equinumerous_refl _, ⟨0, by omega⟩⟩
  | n + 1, hsize, hdisj => by
    obtain ⟨N, hN, hpN⟩ := dvd_card_unionUpto F n
      (fun i hi => hsize i (by omega))
      (fun i j hi hj hne => hdisj i j (by omega) (by omega) hne)
    obtain ⟨m, hm, hpm⟩ := hsize n (Nat.lt_succ_self n)
    refine ⟨N + m, ?_, ?_⟩
    · refine equinumerous_union_disjoint m N _ _ hN hm (fun w hw => ?_)
      obtain ⟨i, hi, hwi⟩ := (mem_unionUpto_iff F n w).mp hw
      exact hdisj i n (by omega) (Nat.lt_succ_self n) (by omega) w hwi
    · obtain ⟨a, ha⟩ := hpN
      obtain ⟨b, hb⟩ := hpm
      exact ⟨a + b, by rw [ha, hb, Nat.mul_add]⟩

/-- A finite set is the range of a `Nat`-indexed family, injectively.
`unionUpto` folds a Lean function over an initial segment, while finiteness is a
bijection with a numeral; this is the one step between them.

The second clause is not decoration. `dvd_card_unionUpto` consumes *disjointness
of the blocks*, and blocks indexed by a family that repeats itself are not
disjoint however disjoint the underlying sets are -- so an enumeration without
it cannot reach the count it exists to serve. -/
theorem exists_enum_of_equinumerous {S : ZFSet.{u}} {N : Nat}
    (h : Equinumerous S (ofNat.{u} N)) :
    ∃ F : Nat → ZFSet.{u},
      (∀ w, w ∈ S ↔ ∃ i, i < N ∧ w = F i) ∧
      (∀ i j, i < N → j < N → i ≠ j → F i ≠ F j) := by
  obtain ⟨f, hinj, hsurj⟩ := equinumerous_symm h
  refine ⟨fun i => app f (ofNat.{u} i), fun w => ⟨fun hw => ?_, fun hw => ?_⟩, ?_⟩
  · obtain ⟨a, ha, hfa⟩ := isSurjection_onto hsurj hw
    obtain ⟨i, hi, rfl⟩ := (mem_ofNat_iff a N).mp ha
    exact ⟨i, hi, hfa.symm⟩
  · obtain ⟨i, hi, rfl⟩ := hw
    exact app_mem_of_isSurjection hsurj ((mem_ofNat_iff _ N).mpr ⟨i, hi, rfl⟩)
  · intro i j hi hj hne he
    refine hne (ofNat_injective ?_)
    exact isInjection_inj hinj ((mem_ofNat_iff _ N).mpr ⟨i, hi, rfl⟩)
      ((mem_ofNat_iff _ N).mpr ⟨j, hj, rfl⟩) he

#print axioms dvd_card_unionUpto
#print axioms exists_enum_of_equinumerous
end Combinatorics

namespace ZFSet
export Combinatorics (dvd_card_unionUpto exists_enum_of_equinumerous)
end ZFSet
