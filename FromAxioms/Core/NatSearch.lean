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

end Core

#print axioms Core.exists_lt_or_not
namespace ZFSet
export Core (below exists_lt_or_not length_below mem_below)
end ZFSet
