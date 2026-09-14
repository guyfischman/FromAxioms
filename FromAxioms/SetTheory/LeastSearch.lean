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

This file is the other case. When membership is detachable -- when
`k in S or k not-in S` is a theorem rather than a hypothesis -- the least
element is definable outright, with no principle at all. The term is the same
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

/-- Membership decided, one element at a time, over `ω`, where the search
runs. -/
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

Defining it costs nothing and says nothing -- for a set with no least member
the separation is empty and this is `∅`. The content is in `least_mem`. -/
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

theorem condP_pos {P : Prop} (h : P) (A B : ZFSet.{u}) : condP P A B = A := by
  have hset : union (sep (fun _ => P) (singleton A)) (sep (fun _ => ¬ P) (singleton B))
      = singleton A := by
    refine ext _ _ fun w => ⟨fun hw => ?_, fun hw => ?_⟩
    · rcases (mem_union_iff w _ _).mp hw with hin | hin
      · exact ((mem_sep_iff _ _ _).mp hin).left
      · exact absurd h ((mem_sep_iff _ _ _).mp hin).right
    · exact (mem_union_iff w _ _).mpr (Or.inl ((mem_sep_iff _ _ _).mpr ⟨hw, h⟩))
  rw [condP, hset, sUnion_singleton]

theorem condP_neg {P : Prop} (h : ¬ P) (A B : ZFSet.{u}) : condP P A B = B := by
  have hset : union (sep (fun _ => P) (singleton A)) (sep (fun _ => ¬ P) (singleton B))
      = singleton B := by
    refine ext _ _ fun w => ⟨fun hw => ?_, fun hw => ?_⟩
    · rcases (mem_union_iff w _ _).mp hw with hin | hin
      · exact absurd ((mem_sep_iff _ _ _).mp hin).right h
      · exact ((mem_sep_iff _ _ _).mp hin).left
    · exact (mem_union_iff w _ _).mpr (Or.inr ((mem_sep_iff _ _ _).mpr ⟨hw, h⟩))
  rw [condP, hset, sUnion_singleton]

/-! ## The first firing of a boolean sequence

`nat_least` above answers does a least satisfier exist; `firstFire` answers
which index, as data, bounded by the argument. The existential needs a
witness and decidability; the bounded fold needs neither, so the
harmonic-jump family can consume it without paying for a search. -/

/-- Has `α` fired by stage `n`? A bounded search over a decidable
predicate, so this is a `Bool` and not a decision. -/
def firedBy (α : Nat → Bool) : Nat → Bool
  | 0 => α 0
  | n + 1 => firedBy α n || α (n + 1)
theorem firedBy_true_iff {α : Nat → Bool} :
    ∀ n, firedBy α n = true ↔ ∃ k, k ≤ n ∧ α k = true
  | 0 => by
    constructor
    · intro h; exact ⟨0, Nat.le_refl 0, h⟩
    · rintro ⟨k, hk, hα⟩
      have : k = 0 := by omega
      subst this
      exact hα
  | n + 1 => by
    constructor
    · intro h
      rcases Bool.or_eq_true_iff.mp h with h' | h'
      · obtain ⟨k, hk, hα⟩ := (firedBy_true_iff n).mp h'
        exact ⟨k, by omega, hα⟩
      · exact ⟨n + 1, Nat.le_refl _, h'⟩
    · rintro ⟨k, hk, hα⟩
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · exact Bool.or_eq_true_iff.mpr
          (Or.inl ((firedBy_true_iff n).mpr ⟨k, by omega, hα⟩))
      · have : k = n + 1 := by omega
        subst this
        exact Bool.or_eq_true_iff.mpr (Or.inr hα)
/-- `firedBy` is monotone: what has fired stays fired. -/
theorem firedBy_mono {α : Nat → Bool} {m n : Nat} (h : m ≤ n)
    (hm : firedBy α m = true) : firedBy α n = true := by
  obtain ⟨k, hk, hα⟩ := (firedBy_true_iff m).mp hm
  exact (firedBy_true_iff n).mpr ⟨k, by omega, hα⟩
/-- Silence up to `n` is silence at every index below it. -/
theorem not_firedBy_iff {α : Nat → Bool} {n : Nat} :
    firedBy α n = false ↔ ∀ k, k ≤ n → α k = false := by
  constructor
  · intro h k hk
    cases hα : α k with
    | false => rfl
    | true =>
      rw [(firedBy_true_iff n).mpr ⟨k, hk, hα⟩] at h
      exact absurd h (by simp)
  · intro h
    cases hf : firedBy α n with
    | false => rfl
    | true =>
      obtain ⟨k, hk, hα⟩ := (firedBy_true_iff n).mp hf
      rw [h k hk] at hα
      exact absurd hα (by simp)
/-- The first index at which `α` fires, read off once `firedBy` says it has.
Meaningless before that, so every lemma below guards on `firedBy`. -/
def firstFire (α : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if firedBy α n then firstFire α n else n + 1
theorem firstFire_le {α : Nat → Bool} : ∀ n, firstFire α n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    show (if firedBy α n then firstFire α n else n + 1) ≤ n + 1
    split
    · exact Nat.le_succ_of_le (firstFire_le n)
    · exact Nat.le_refl _
theorem firedBy_at_firstFire {α : Nat → Bool} :
    ∀ n, firedBy α n = true → α (firstFire α n) = true
  | 0 => fun h => h
  | n + 1 => by
    intro h
    show α (if firedBy α n then firstFire α n else n + 1) = true
    cases hf : firedBy α n with
    | true => simpa [hf] using firedBy_at_firstFire n hf
    | false =>
      show α (if False then firstFire α n else n + 1) = true
      rw [if_neg (fun h => h)]
      rcases Bool.or_eq_true_iff.mp h with h' | h'
      · exact absurd (hf ▸ h') (by simp)
      · exact h'
/-- The index stabilises once it exists, so the value is a single real
rather than a sequence of guesses. -/
theorem firstFire_stable {α : Nat → Bool} {n : Nat} (hn : firedBy α n = true) :
    ∀ m, n ≤ m → firstFire α m = firstFire α n := by
  intro m
  induction m with
  | zero => intro h; have : n = 0 := by omega
            rw [this]
  | succ k ih =>
    intro h
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · have hk : firedBy α k = true := firedBy_mono (by omega) hn
      show (if firedBy α k then firstFire α k else k + 1) = firstFire α n
      rw [if_pos hk]
      exact ih (by omega)
    · have : n = k + 1 := by omega
      rw [this]
/-- Silence pushes the first firing strictly later. -/
theorem firstFire_gt_of_silent {α : Nat → Bool} {m n : Nat}
    (hm : firedBy α m = false) (hn : firedBy α n = true) :
    m + 1 ≤ firstFire α n := by
  rcases Nat.lt_or_ge m (firstFire α n) with h | h
  · omega
  · have := not_firedBy_iff.mp hm _ h
    rw [firedBy_at_firstFire n hn] at this
    exact absurd this (by simp)


/-- The stage to sample at: the first fire if there has been one, else
`n` itself.

Booij's construction samples a converging sequence at the first index where a
predicate fires, and at the running index while it has not. Naming the index
separately lets its monotonicity be proved before any sequence is built on it.
-/
def fireStage (α : Nat → Bool) (n : Nat) : Nat :=
  if firedBy α n then firstFire α n else n

/-- Silent at `N` puts every later sampling stage at or beyond `N`.

One half of the case split a Cauchy estimate on the sampled sequence needs.
If `α` has not fired by `N`, then at a later `j` either it still has not ---
and the stage is `j` itself --- or it has, and the first firing was pushed
strictly past `N`. -/
theorem fireStage_ge_of_silent {α : Nat → Bool} {N j : Nat}
    (hN : firedBy α N = false) (h : N ≤ j) : N ≤ fireStage α j := by
  rw [fireStage]
  by_cases hj : firedBy α j = true
  · rw [if_pos hj]
    have := firstFire_gt_of_silent hN hj
    omega
  · rw [if_neg hj]
    exact h

/-- Fired by `N` fixes every later sampling stage at the same index.

The other half. Once the predicate has fired, `firstFire` has stabilised, so
the sampled sequence is CONSTANT from `N` on --- so the Cauchy
estimate is trivial in this case rather than needing a width bound. -/
theorem fireStage_eq_of_fired {α : Nat → Bool} {N j : Nat}
    (hN : firedBy α N = true) (h : N ≤ j) :
    fireStage α j = firstFire α N := by
  have hj : firedBy α j = true := firedBy_mono h hN
  rw [fireStage, if_pos hj, firstFire_stable hN j h]

#print axioms SetTheory.firedBy
#print axioms SetTheory.firedBy_true_iff
#print axioms SetTheory.firedBy_mono
#print axioms SetTheory.not_firedBy_iff
#print axioms SetTheory.firstFire
#print axioms SetTheory.firstFire_le
#print axioms SetTheory.firedBy_at_firstFire
#print axioms SetTheory.firstFire_stable
#print axioms SetTheory.firstFire_gt_of_silent
#print axioms SetTheory.fireStage
#print axioms SetTheory.fireStage_ge_of_silent
#print axioms SetTheory.fireStage_eq_of_fired

#print axioms SetTheory.condP_pos
#print axioms nat_least_le

#print axioms condP_neg
end SetTheory

namespace ZFSet
export SetTheory (Detachable condP condP_neg condP_pos fireStage fireStage_eq_of_fired fireStage_ge_of_silent firedBy firedBy_at_firstFire firedBy_mono firedBy_true_iff firstFire firstFire_gt_of_silent firstFire_le firstFire_stable least least_mem nat_least not_firedBy_iff)
end ZFSet
