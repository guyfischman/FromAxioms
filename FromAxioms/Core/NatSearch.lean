/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Decidable search over `Nat`, bounded and unbounded.

Pure arithmetic: no `ZFSet` and nothing imported. A predicate on
`Nat` whose truth is decided by a HYPOTHESIS rather than by a principle can be
searched, and the two halves terminate for different reasons -- the bounded
search because the bound counts down, the unbounded one because accessibility
of the step relation is supplied as an argument.

The bounded half is the pigeonhole and the search it is built from. Nothing
about either is group-theoretic, though finite order is what wants them, so
they sit here where a file that does not import group theory can reach them.

The Prop-to-Bool crossing is here for the same reason and arrived last: it is
`BoolReadout1` and `BoolReadoutOn`, stripped of every subject -- not relations,
not pairs, not sets, not Ramsey, and not ideals. Three towers instantiate it
(Ramsey, ideals of `Z`, formal power series) and two of them cannot see
`RamseySet.lean`, which is the subject-bound home for it. It is the one thing here carrying a
UNIVERSE, since the crossing at an arbitrary type is what makes the `Nat` carry
no content either; nothing else in the file needs one.

The unbounded half is `seekFrom` and `natFind`, and it is here for the same
reason one level up: a search that decides a `Bool` needs neither the reals nor
`ZFSet`, so requiring them would put a modulus out of reach of any file below
the analysis tower -- which is exactly what `RamseyNatRel.lean` needs. What it
costs is an accessibility argument supplied by the caller, and `Search.lean`
re-exports this file so consumers reaching `seekFrom` through the rationals are
unaffected.
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

/-- The largest member, or zero for an empty list. -/
def listMax : List Nat → Nat
  | [] => 0
  | e :: es => max e (listMax es)

/-- The smallest member, or zero for an empty list. -/
def listMin : List Nat → Nat
  | [] => 0
  | e :: es => min e (listMin es)

theorem le_listMax : ∀ (l : List Nat) (e : Nat), e ∈ l → e ≤ listMax l
  | [], e, he => absurd he (by simp)
  | a :: t, e, he => by
    have hstep : listMax (a :: t) = max a (listMax t) := rfl
    cases he with
    | head => rw [hstep]; omega
    | tail _ ht =>
      have := le_listMax t e ht
      rw [hstep]
      omega

theorem listMin_le : ∀ (l : List Nat) (e : Nat), e ∈ l → listMin l ≤ e
  | [], e, he => absurd he (by simp)
  | a :: t, e, he => by
    have hstep : listMin (a :: t) = min a (listMin t) := rfl
    cases he with
    | head => rw [hstep]; omega
    | tail _ ht =>
      have := listMin_le t e ht
      rw [hstep]
      omega

theorem listMax_mem : ∀ (l : List Nat), l ≠ [] → listMax l ∈ l
  | [], h => absurd rfl h
  | a :: t, _ => by
    show max a (listMax t) ∈ a :: t
    rcases Nat.le_total (listMax t) a with hle | hle
    · have hm : max a (listMax t) = a := by omega
      rw [hm]
      exact List.Mem.head _
    · cases t with
      | nil =>
        have h0 : listMax ([] : List Nat) = 0 := rfl
        have hm : max a (listMax ([] : List Nat)) = a := by omega
        rw [hm]
        exact List.Mem.head _
      | cons b r =>
        have hm : max a (listMax (b :: r)) = listMax (b :: r) := by omega
        rw [hm]
        exact List.Mem.tail _
          (listMax_mem (b :: r) (fun h => List.noConfusion h))

/-! ## Unbounded search over a decidable sequence

`Nat.find` is not in core against this toolchain, and BD-N's diagonal needs the
witness as data: from `∃ n, α n = true` alone, compute the least such `n`.
The recursion is on accessibility of the walk upward from `0`, and the
existential steers it through `Acc` -- the one place a `Prop` may drive a
computation without choice. The interface takes `α : Nat → Bool`, not a
`Prop`-valued disjunction, because a `Prop`-level `Or` cannot eliminate into
data. -/

/-- One step up the walk, allowed only over a miss. -/
def seekStep (α : Nat → Bool) (a b : Nat) : Prop :=
  And (a = b + 1) (α b = false)

/-- A point with a hit above it is accessible: the walk cannot step past the
hit. The induction is on the distance to the witness. -/
theorem seekStep_acc (α : Nat → Bool) :
    ∀ (m n : Nat), α (n + m) = true → Acc (seekStep α) n
  | 0, n, h =>
    Acc.intro n (fun _ hs => Bool.noConfusion (h.symm.trans hs.right))
  | m + 1, n, h =>
    Acc.intro n (fun a hs => by
      rw [hs.left]
      exact seekStep_acc α m (n + 1) (by
        rw [show n + 1 + m = n + (m + 1) from by omega]
        exact h))

/-- The walk itself: stop at a hit, step over a miss. Structural on the
accessibility proof, so it computes. -/
noncomputable def seekFrom (α : Nat → Bool) :
    (n : Nat) → Acc (seekStep α) n → Nat :=
  fun _ a =>
    Acc.rec (motive := fun _ _ => Nat)
      (fun n _ ih =>
        match h : α n with
        | true => n
        | false => ih (n + 1) ⟨rfl, h⟩)
      a

/-- The search: the existential steers, the walk computes -- at the
kernel; the code generator does not support `Acc.rec`, which is a fact about
the compiler backend and not about choice. -/
noncomputable def natFind (α : Nat → Bool) (h : ∃ n, α n = true) : Nat :=
  seekFrom α 0 (h.elim (fun m hm => seekStep_acc α m 0 (by
    rw [show 0 + m = m from by omega]
    exact hm)))

/-- The walk finds a hit. -/
theorem seekFrom_hit (α : Nat → Bool) :
    ∀ (n : Nat) (a : Acc (seekStep α) n), α (seekFrom α n a) = true := by
  intro n a
  induction a with
  | intro n hchild ih =>
    show α (match h : α n with
      | true => n
      | false => seekFrom α (n + 1) (hchild (n + 1) ⟨rfl, h⟩)) = true
    split
    case h_1 heq => exact heq
    case h_2 heq => exact ih (n + 1) ⟨rfl, heq⟩

/-- Everything the walk stepped over was a miss. -/
theorem seekFrom_least (α : Nat → Bool) :
    ∀ (n : Nat) (a : Acc (seekStep α) n) (k : Nat), n ≤ k →
      k < seekFrom α n a → α k = false := by
  intro n a
  induction a with
  | intro n hchild ih =>
    intro k hnk hk
    rw [show seekFrom α n (Acc.intro n hchild)
        = (match h : α n with
          | true => n
          | false => seekFrom α (n + 1) (hchild (n + 1) ⟨rfl, h⟩))
      from rfl] at hk
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · have hkn : k = n := by omega
      revert hk
      split
      case h_1 => intro hk; exact absurd hk (by omega)
      case h_2 heq => intro _; rw [hkn]; exact heq
    · revert hk
      split
      case h_1 => intro hk; exact absurd hk (by omega)
      case h_2 heq =>
        intro hk
        exact ih (n + 1) ⟨rfl, heq⟩ k hge hk

/-- `natFind` hits. -/
theorem natFind_spec (α : Nat → Bool) (h : ∃ n, α n = true) :
    α (natFind α h) = true :=
  seekFrom_hit α 0 _

/-- `natFind` is least. -/
theorem natFind_least (α : Nat → Bool) (h : ∃ n, α n = true) :
    ∀ k, k < natFind α h → α k = false :=
  fun k hk => seekFrom_least α 0 _ k (Nat.zero_le k) hk

/-- The naturals below `n`, descending: `below 3 = [2, 1, 0]`.

Empty at zero, consing `n` onto `below n` at the successor -- so the head
always exceeds everything in the tail, so it is repeat-free by construction and
what `mem_below` and `length_below` are about.

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

/-- The smallest of `a` and the members of `l`. Seeded with a member rather
than with zero, the bound says something: a zero seed sits below
every position and the window degenerates to `[0, listMax + 1)`. -/
def minOf (a : Nat) : List Nat → Nat
  | [] => a
  | b :: r => min b (minOf a r)

theorem minOf_le_seed (a : Nat) : ∀ l : List Nat, minOf a l ≤ a
  | [] => Nat.le_refl a
  | b :: r => by
    have := minOf_le_seed a r
    show min b (minOf a r) ≤ a
    omega

theorem minOf_le (a : Nat) : ∀ (l : List Nat) (e : Nat), e ∈ l → minOf a l ≤ e
  | [], e, he => absurd he (by simp)
  | b :: r, e, he => by
    show min b (minOf a r) ≤ e
    cases he with
    | head => omega
    | tail _ ht =>
      have := minOf_le a r e ht
      omega

/-- The seeded minimum is a member, or the seed. The rational step needs
it: the window's lower end must BE a selected position, or the strict
inequality it has to supply has nothing to come from. -/
theorem minOf_mem (a : Nat) : ∀ l : List Nat, minOf a l = a ∨ minOf a l ∈ l
  | [] => Or.inl rfl
  | b :: r => by
    show min b (minOf a r) = a ∨ min b (minOf a r) ∈ b :: r
    rcases Nat.le_total b (minOf a r) with hle | hle
    · have hb : min b (minOf a r) = b := by omega
      exact Or.inr (by rw [hb]; exact List.Mem.head _)
    · have hb : min b (minOf a r) = minOf a r := by omega
      rcases minOf_mem a r with h | h
      · exact Or.inl (by rw [hb, h])
      · exact Or.inr (by rw [hb]; exact List.Mem.tail _ h)

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
principle: the induction decides `n + 1` from `n` and the single new index, so
`exists_least` applies to every slice above `m` vanishes, whose decision at
each index is supplied by a `DecidableVanishing` the caller already holds. -/
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

The `B := ¬ P` instance of `bounded_forall_or_witness_of_or`, which widens it:
the compiler checks the subsumption, and no second theorem carries this
elaborated type. -/
theorem bounded_forall_or_witness {P : Nat → Prop} (n : Nat)
    (hdec : ∀ j, j < n → P j ∨ ¬ P j) :
    (∀ i, i < n → P i) ∨ ∃ i, i < n ∧ ¬ P i :=
  (bounded_forall_or_witness_of_or n hdec).imp id
    (fun ⟨i, hi, hnp, _⟩ => ⟨i, hi, hnp⟩)

/-- The product of the first `n` degrees. -/
def prodUpto (d : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => prodUpto d n * d n

theorem mod_ne_zero_of_between {p m : Nat}
    (hlo : 2 ≤ m) (hhi : m < 2 * p) (hne : m ≠ p) : m % p ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
  match k with
  | 0 => omega
  | 1 => omega
  | (k + 2) =>
    have : 2 * p ≤ p * (k + 2) := by
      calc 2 * p = p * 2 := Nat.mul_comm 2 p
        _ ≤ p * (k + 2) := Nat.mul_le_mul_left p (by omega)
    omega

#print axioms mod_ne_zero_of_between

/-! ## The reduction, finished -/
/-- The unary crossing: a decided predicate on `Nat` has a `Bool` function.

This is the schema CF_d, stated as a Prop rather than as a schema.
Vafeiadou, A comparison of minimal systems for constructive analysis
(arXiv:1808.00383), §3.1.1, verbatim:

    CF_d   ∀x (B(x) ∨ ¬B(x)) → ∃β ∀x [ β(x) ≤ 1 & (β(x) = 0 ↔ B(x)) ]

with `β` not free in `B(x)`. Her `β(x) ≤ 1` is `Bool`, and `β(x) = 0 ↔ B(x)`
is `K i = true ↔ P i` with the polarity written the other way round.

This is STATED AS a Prop rather than being the schema, because CF_d ranges over
FORMULAS `B` of a two-sorted arithmetic, where this quantifies over
`P : Nat → Prop`, an object of the theory. A statement is at least as strong as
its schema, so this bounds CF_d from above and the converse is a question about
the language rather than about the principle.

Its place there: CF_d is what separates Troelstra's `EL` from Kleene's `M`.
`AC₀₀!` entails it (Proposition 3.1), `QF-AC₀₀ + CF_d` entails `AC₀₀!`
(Theorem 3.2), and `EL` does not prove it (Theorem 3.4). -/
def BoolReadout1 : Prop :=
  ∀ P : Nat → Prop, (∀ i, P i ∨ ¬ P i) →
    ∃ K : Nat → Bool, ∀ i, (K i = true ↔ P i)
#print axioms seekStep_acc
#print axioms forall_lt_succ
end Core

#print axioms Core.exists_lt_or_not
#print axioms Core.exists_pair_or_inj
#print axioms Core.exists_least
#print axioms Core.seekFrom_hit
#print axioms Core.seekFrom_least
#print axioms Core.natFind_spec
#print axioms Core.natFind_least

#print axioms Core.le_listMax
#print axioms Core.listMin_le
#print axioms Core.listMax_mem
#print axioms Core.minOf
#print axioms Core.minOf_le_seed
#print axioms Core.minOf_le
#print axioms Core.minOf_mem
#print axioms Core.bounded_forall_dec
#print axioms Core.bounded_forall_or_witness_of_or
#print axioms Core.bounded_forall_or_witness
#print axioms Core.prodUpto

namespace ZFSet
export Core (BoolReadout1 below bounded_forall_dec bounded_forall_or_witness bounded_forall_or_witness_of_or exists_least exists_lt_or_not exists_pair_or_inj forall_lt_succ le_listMax length_below listMax listMax_mem listMin listMin_le mem_below minOf minOf_le minOf_le_seed minOf_mem mod_ne_zero_of_between natFind natFind_least natFind_spec prodUpto seekFrom seekFrom_hit seekFrom_least seekStep seekStep_acc)
end ZFSet
