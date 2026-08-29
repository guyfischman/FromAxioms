/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Decidable search over `Nat`, bounded and unbounded.

Pure arithmetic: no `ZFSet` and nothing imported. A predicate on `Nat` whose
truth is decided by a HYPOTHESIS rather than by a principle can be searched,
and the two halves terminate for different reasons -- the bounded search
because the bound counts down, the unbounded one because accessibility of the
step relation is supplied as an argument.

The bounded half is the pigeonhole and the search it is built from. The
Prop-to-Bool crossing is `BoolReadout1` and `BoolReadoutOn`, stripped of every
subject; it is the one thing here carrying a universe, since the crossing at
an arbitrary type is what makes the `Nat` carry no content either.

The unbounded half is `seekFrom` and `natFind`. What it costs is an
accessibility argument supplied by the caller.
-/

namespace Core

/-- Bounded search over `Nat`, with the decision as a hypothesis. Pure
arithmetic -- no sets, so no universe travels with it. -/
theorem exists_lt_or_not {Q : Nat → Prop} (hdec : ∀ j, Q j ∨ ¬ Q j) :
    ∀ n : Nat, (∃ j, j < n ∧ Q j) ∨ ∀ j, j < n → ¬ Q j
  | 0 => Or.inr fun j hj => absurd hj (Nat.not_lt_zero j)
  | n + 1 => by
    rcases exists_lt_or_not hdec n with ⟨j, hj, hQ⟩ | hno
    · exact Or.inl ⟨j, Nat.lt_succ_of_lt hj, hQ⟩
    · rcases hdec n with h | h
      · exact Or.inl ⟨n, Nat.lt_succ_self n, h⟩
      · refine Or.inr fun j hj => ?_
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | he
        · exact hno j hlt
        · exact he ▸ h

/-- Either two distinct indices below `n` are related, or the relation is
injective there. -/
theorem exists_pair_or_inj {P : Nat → Nat → Prop} (hdec : ∀ j k, P j k ∨ ¬ P j k) :
    ∀ n : Nat, (∃ j k, j < n ∧ k < n ∧ j ≠ k ∧ P j k) ∨
      ∀ j k, j < n → k < n → P j k → j = k
  | 0 => Or.inr (fun j k hj => absurd hj (by omega))
  | n + 1 => by
    rcases exists_pair_or_inj hdec n with ⟨j, k, hj, hk, hne, hP⟩ | hinj
    · exact Or.inl ⟨j, k, by omega, by omega, hne, hP⟩
    · -- does the new index collide with an old one, in either order?
      rcases exists_lt_or_not (Q := fun j => P j n ∨ P n j)
        (fun j => by
          rcases hdec j n with h | h
          · exact Or.inl (Or.inl h)
          · rcases hdec n j with h' | h'
            · exact Or.inl (Or.inr h')
            · exact Or.inr (fun hc => hc.elim h h')) n with ⟨j, hj, hQ⟩ | hno
      · rcases hQ with h | h
        · exact Or.inl ⟨j, n, by omega, by omega, by omega, h⟩
        · exact Or.inl ⟨n, j, by omega, by omega, by omega, h⟩
      · refine Or.inr (fun j k hj hk hP => ?_)
        rcases Nat.lt_or_ge j n with hjn | hjn <;> rcases Nat.lt_or_ge k n with hkn | hkn
        · exact hinj j k hjn hkn hP
        · rw [show k = n by omega] at hP
          exact absurd (Or.inl hP) (hno j hjn)
        · rw [show j = n by omega] at hP
          exact absurd (Or.inr hP) (hno k hkn)
        · omega

/-- A decidable predicate with a witness has a least one. Strong induction, and
the decision is a hypothesis. -/
theorem exists_least {Q : Nat → Prop} (hdec : ∀ n, Q n ∨ ¬ Q n) :
    ∀ n : Nat, Q n → ∃ m, Q m ∧ ∀ k, k < m → ¬ Q k := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hQ
    rcases exists_lt_or_not hdec n with ⟨j, hj, hQj⟩ | hno
    · exact ih j hj hQj
    · exact ⟨n, hQ, hno⟩

/-! ## Unbounded search over a decidable sequence

`Nat.find` is not in core against this toolchain, and BD-N's diagonal needs the
witness as data: from `∃ n, α n = true` alone, compute the least such `n`.
The recursion is on accessibility of the walk upward from `0`, and the
existential steers it through `Acc` -- the one place a `Prop` may drive a
computation without choice. The interface takes `α : Nat → Bool`, not a
`Prop`-valued disjunction, because a `Prop`-level `Or` cannot eliminate into
data. -/

/-- The naturals below `n`, descending: `below 3 = [2, 1, 0]`.

Empty at zero, consing `n` onto `below n` at the successor -- so the head always
exceeds everything in the tail, which is what makes it repeat-free by
construction and what `mem_below` and `length_below` are about.

-/
def below : Nat → List Nat
  | 0 => []
  | n + 1 => n :: below n
theorem mem_below : ∀ {n e : Nat}, e ∈ below n ↔ e < n
  | 0, e => ⟨fun h => absurd h (by simp [below]), fun h => absurd h (by omega)⟩
  | n + 1, e => by
    constructor
    · intro h
      cases h with
      | head => omega
      | tail _ ht => have := mem_below.mp ht; omega
    · intro h
      rcases Nat.lt_or_ge e n with hlt | hge
      · exact List.Mem.tail _ (mem_below.mpr hlt)
      · have : e = n := by omega
        exact this ▸ List.Mem.head _
theorem length_below : ∀ n : Nat, (below n).length = n
  | 0 => rfl
  | n + 1 => by rw [below, List.length_cons, length_below n]

#print axioms Core.mem_below
#print axioms Core.length_below

/-! ## Bounded search: the decision, the witness, and the largest failure

A bounded conjunction of decidable propositions is decidable, and the same
induction hands back the failing index -- which a negated universal cannot.
`exists_top_fail` is the shape a degree argument wants: the largest index at
which a predicate fails, given that it holds above a bound. -/

/-- Extending a bounded universal by one index. The step every bounded
search shares: below `n` the old hypothesis serves, and at `n` itself there is
one new fact. -/
theorem forall_lt_succ {P : Nat → Prop} {n : Nat}
    (hall : ∀ i, i < n → P i) (hn : P n) : ∀ i, i < n + 1 → P i := by
  intro i hi
  rcases Nat.lt_or_ge i n with h | h
  · exact hall i h
  · have hin : i = n := by omega
    exact hin ▸ hn

/-- A bounded conjunction of decidable propositions is decidable. No
principle: the induction decides `n + 1` from `n` and the single new index. This
is what makes `exists_least` applicable to every slice above `m` vanishes,
whose decision at each index is supplied by a `DecidableVanishing` the caller
already holds. -/
theorem bounded_forall_dec {P : Nat → Prop} :
    ∀ n : Nat, (∀ j, j < n → P j ∨ ¬ P j) →
      (∀ i, i < n → P i) ∨ ¬ (∀ i, i < n → P i)
  | 0, _ => Or.inl (fun i hi => absurd hi (by omega))
  | n + 1, hdec => by
      rcases bounded_forall_dec n (fun j hj => hdec j (by omega)) with hall | hno
      · rcases hdec n (by omega) with hn | hn
        · exact Or.inl (forall_lt_succ hall hn)
        · exact Or.inr (fun hc => hn (hc n (by omega)))
      · exact Or.inr (fun hc => hno (fun i hi => hc i (by omega)))

/-- The bounded search over TWO POSITIVE alternatives.

`bounded_forall_or_witness` below takes `P j ∨ ¬ P j`. Cotransitivity of the
real order hands back `A j ∨ B j` where neither side is the negation of the
other, so that hypothesis cannot express it and the two predicates have to be
separate.

Returns `∀ j < i, A j` alongside the witness: a caller locating a point against
a grid needs the alternatives on BOTH sides of `i`, and the bare existential
loses exactly that.

Structurally recursive on the numeral, so nothing is selected and no principle
is spent. NOT to be confused with `BinaryDC`, whose hypothesis has this shape
and whose CONCLUSION is a sequence: the dependence of each stage on the numeral
built from the earlier ones is what costs choice there, and here the bound is
fixed and the answer is one index. -/
theorem bounded_forall_or_witness_of_or {A B : Nat → Prop} :
    ∀ n : Nat, (∀ j, j < n → A j ∨ B j) →
      (∀ i, i < n → A i) ∨ ∃ i, i < n ∧ B i ∧ ∀ j, j < i → A j
  | 0, _ => Or.inl (fun i hi => absurd hi (by omega))
  | n + 1, hdec => by
      rcases bounded_forall_or_witness_of_or n (fun j hj => hdec j (by omega))
        with hall | ⟨i, hi, hB, hlt⟩
      · rcases hdec n (by omega) with hA | hB
        · exact Or.inl (forall_lt_succ hall hA)
        · exact Or.inr ⟨n, by omega, hB, hall⟩
      · exact Or.inr ⟨i, by omega, hB, hlt⟩

/-- The bounded decision that HANDS BACK A WITNESS.

`bounded_forall_dec` returns `not (forall ...)`, and a negated universal yields
no witness constructively -- so it cannot drive a search for the largest failing
index. This returns the failing index itself, which is what a bounded search can
always do and an unbounded one cannot.

The `B := ¬ P` instance of `bounded_forall_or_witness_of_or`, which is what
makes the widening a widening: the compiler checks the subsumption, and no
second theorem carries this elaborated type. -/
theorem bounded_forall_or_witness {P : Nat → Prop} (n : Nat)
    (hdec : ∀ j, j < n → P j ∨ ¬ P j) :
    (∀ i, i < n → P i) ∨ ∃ i, i < n ∧ ¬ P i :=
  (bounded_forall_or_witness_of_or n hdec).imp id
    (fun ⟨i, hi, hnp, _⟩ => ⟨i, hi, hnp⟩)

/-- The product of the first `n` degrees. -/
def prodUpto (d : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => prodUpto d n * d n

end Core

#print axioms Core.exists_lt_or_not
#print axioms Core.exists_pair_or_inj
#print axioms Core.exists_least
#print axioms Core.bounded_forall_dec
#print axioms Core.bounded_forall_or_witness_of_or
#print axioms Core.bounded_forall_or_witness
#print axioms Core.prodUpto

namespace ZFSet
export Core (below bounded_forall_dec bounded_forall_or_witness bounded_forall_or_witness_of_or exists_least exists_lt_or_not exists_pair_or_inj forall_lt_succ length_below mem_below prodUpto)
end ZFSet
