/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The least element of a detachable set of naturals

`Scott.lean` pins the least element of an arbitrary set of ordinals at `em`:
`em_of_leastRank_spec` builds a set with one element or two, undecidably, and
asking for its least member decides which. That is the general case, and it is
classical.

This file is the other case. When membership is detachable -- when `k in S or
k not-in S` is a theorem rather than a hypothesis -- the least element is
definable outright, with no principle at all. The term is the same
union-of-a-singleton trick `leastRank` uses: the minimal members of `S` form a
singleton, and `sUnion` reads it.

Separate from `Search.lean` so material below the reals can reach it.
Nothing here mentions a rational: the whole file rests on `omega`, `sep`,
`sUnion` and `ofNat`. `Search.lean` keeps the rational and interval-shrinking
half and imports this, so the polynomial tower can name `least` without
importing the real numbers.

`condP` is here for the same reason and by the same measurement. Branching on
an undecided proposition needs a set rather than a `Bool`, and the term is
again a union of a singleton -- so it rests on nothing above `Algebra.lean`,
and a file wanting a two-way branch need not import the tower to get one.
-/

import FromAxioms.Core.NatSearch
import FromAxioms.NumberTheory.Natural

universe u

open Algebra Core NumberTheory
namespace SetTheory

/-- Membership decided, one element at a time. Stated over `ω` because that is
where the search runs. -/
def Detachable (S : ZFSet.{u}) : Prop :=
  ∀ k, k ∈ omega.{u} → k ∈ S ∨ k ∉ S

/-- A witness below a bound yields a least witness. The recursion is on the
bound, and the step descends to the smaller witness `exists_lt_or_not` produced. -/
private theorem nat_least_le {P : Nat → Prop} (hdec : ∀ n, P n ∨ ¬ P n) :
    ∀ N M, M ≤ N → P M → ∃ m, P m ∧ ∀ k, P k → m ≤ k
  | 0, M, hle, h =>
    ⟨M, h, fun k _ => by
      have : M = 0 := Nat.le_zero.mp hle
      exact this ▸ Nat.zero_le k⟩
  | N + 1, M, hle, h => by
    rcases exists_lt_or_not hdec M with ⟨k, hk, hPk⟩ | hall
    · exact nat_least_le hdec N k (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hk hle)) hPk
    · refine ⟨M, h, fun k hPk => ?_⟩
      rcases Nat.lt_or_ge k M with hlt | hge
      · exact absurd hPk (hall k hlt)
      · exact hge

theorem nat_least {P : Nat → Prop} (hdec : ∀ n, P n ∨ ¬ P n) {N : Nat} (h : P N) :
    ∃ m, P m ∧ ∀ k, P k → m ≤ k :=
  nat_least_le hdec N N (Nat.le_refl N) h

/-- The least member of a set of naturals: the union of its minimal members.

Defining it costs nothing and says nothing -- for a set with no least member the
separation is empty and this is `∅`. `least_mem` is where the content is. -/
def least (S : ZFSet.{u}) : ZFSet.{u} :=
  sUnion (sep (fun k => ∀ j, j ∈ S → k ⊆ j) S)

/-- The search terminates in a term. Detachable and inhabited is enough:
`least S` is a member, and it is below every member.

Compare `em_of_leastRank_spec`. Nothing here is weaker than that reversal -- the
hypothesis is. -/
theorem least_mem {S : ZFSet.{u}} (hS : S ⊆ omega.{u}) (hdet : Detachable S)
    (hne : ∃ n, n ∈ S) : least S ∈ S ∧ ∀ j, j ∈ S → least S ⊆ j := by
  obtain ⟨n, hn⟩ := hne
  obtain ⟨N, rfl⟩ := (mem_omega_iff n).mp (hS n hn)
  have hdec : ∀ k : Nat, ofNat.{u} k ∈ S ∨ ¬ ofNat.{u} k ∈ S :=
    fun k => hdet _ (ofNat_mem_omega k)
  obtain ⟨m, hm, hmin⟩ := nat_least hdec hn
  have hbelow : ∀ j, j ∈ S → ofNat.{u} m ⊆ j := by
    intro j hj
    obtain ⟨k, rfl⟩ := (mem_omega_iff j).mp (hS j hj)
    exact (ofNat_subset_iff m k).mpr (hmin k hj)
  have hsing : sep (fun k => ∀ j, j ∈ S → k ⊆ j) S = singleton (ofNat.{u} m) := by
    refine ext _ _ fun z => ⟨fun hz => ?_, fun hz => ?_⟩
    · obtain ⟨hzS, hzmin⟩ := (mem_sep_iff _ _ _).mp hz
      refine (mem_singleton_iff _ _).mpr (ext _ _ fun w =>
        ⟨fun hw => hzmin _ hm w hw, fun hw => hbelow z hzS w hw⟩)
    · rw [(mem_singleton_iff _ _).mp hz]
      exact (mem_sep_iff _ _ _).mpr ⟨hm, hbelow⟩
  rw [least, hsing, sUnion_singleton]
  exact ⟨hm, hbelow⟩

#print axioms nat_least
#print axioms least_mem
/-! ## Definition by cases, as a term

A construction that must branch on a proposition needs more than the
proposition: it needs a set. `condP` is that set, and it is definable for any
`P` whatever, decided or not -- the two separations are taken over `P` and over
`¬ P`, so exactly one of them is inhabited when `P` is decided and the union
reads whichever it is.

Nothing is chosen: what a `Decidable` instance would supply, and what this
development cannot get, is a `Bool` in Lean. Inside the set theory the branch
is a term.
-/

/-- `A` if `P`, `B` if not. -/
def condP (P : Prop) (A B : ZFSet.{u}) : ZFSet.{u} :=
  sUnion (union (sep (fun _ => P) (singleton A)) (sep (fun _ => ¬ P) (singleton B)))

end SetTheory

namespace ZFSet
export SetTheory (Detachable condP least least_mem nat_least nat_least_le)
end ZFSet
