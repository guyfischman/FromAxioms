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


/-- `A ∩ (Y \ X) = (A \ X) ∩ Y`, free: both sides are `w ∈ A ∧ w ∈ Y ∧ w ∉ X`. -/
theorem inter_sdiff_comm {A X Y : ZFSet.{u}} :
    inter A (sdiff Y X) = inter (sdiff A X) Y :=
  ext _ _ fun w => ⟨fun hw =>
      have h1 := (mem_inter_iff w A (sdiff Y X)).mp hw
      have h2 := (mem_sdiff_iff w Y X).mp h1.right
      (mem_inter_iff w (sdiff A X) Y).mpr
        ⟨(mem_sdiff_iff w A X).mpr ⟨h1.left, h2.right⟩, h2.left⟩,
    fun hw =>
      have h1 := (mem_inter_iff w (sdiff A X) Y).mp hw
      have h2 := (mem_sdiff_iff w A X).mp h1.left
      (mem_inter_iff w A (sdiff Y X)).mpr
        ⟨h2.left, (mem_sdiff_iff w Y X).mpr ⟨h1.right, h2.right⟩⟩⟩

/-- Union commutes. With the laws around it -- associativity, distribution,
and the difference laws below -- this is Boole's algebra of logic. -/
theorem union_comm (x y : ZFSet.{u}) : x ∪ y = y ∪ x :=
  ext _ _ fun z => by simp [Or.comm]

@[simp] theorem union_self (x : ZFSet.{u}) : x ∪ x = x :=
  ext _ _ fun z => by simp

@[simp] theorem union_empty (x : ZFSet.{u}) : x ∪ empty.{u} = x :=
  ext _ _ fun z => by simp

@[simp] theorem empty_union (x : ZFSet.{u}) : empty.{u} ∪ x = x :=
  ext _ _ fun z => by simp

theorem inter_comm (x y : ZFSet.{u}) : x ∩ y = y ∩ x :=
  ext _ _ fun z => by simp [And.comm]

theorem inter_assoc (x y z : ZFSet.{u}) : x ∩ y ∩ z = x ∩ (y ∩ z) :=
  ext _ _ fun w => by simp [and_assoc]

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
theorem sdiff_union (x y z : ZFSet.{u}) : x \ (y ∪ z) = (x \ y) ∩ (x \ z) :=
  ext _ _ fun w => by
    simp only [mem_sdiff_iff, mem_union_iff, mem_inter_iff, not_or]
    exact ⟨fun ⟨hx, hy, hz⟩ => ⟨⟨hx, hy⟩, hx, hz⟩,
           fun ⟨⟨hx, hy⟩, _, hz⟩ => ⟨hx, hy, hz⟩⟩

/-! ### The double difference

Detachability decides `y` and double negation does not, and the refined forms
below differ in that. -/

/-- The cancellation at a DETACHABILITY hypothesis.

The version a caller who can already decide `y` pays nothing for.

Deciding `y` is the whole of what the forward direction needs; backwards is free. -/
theorem sdiff_sdiff_cancel_of_detachable {x y : ZFSet.{u}}
    (hdet : ∀ w : ZFSet.{u}, w ∈ y ∨ w ∉ y) : x \ (x \ y) = x ∩ y :=
  ext _ _ fun w => ⟨fun hw =>
      have h := (mem_sdiff_iff w x (x \ y)).mp hw
      (hdet w).elim
        (fun hy => (mem_inter_iff w x y).mpr ⟨h.left, hy⟩)
        (fun hy => absurd ((mem_sdiff_iff w x y).mpr ⟨h.left, hy⟩) h.right),
    fun hw =>
      have h := (mem_inter_iff w x y).mp hw
      (mem_sdiff_iff w x (x \ y)).mpr
        ⟨h.left, fun hs => ((mem_sdiff_iff w x y).mp hs).right h.right⟩⟩

#print axioms sdiff_sdiff_cancel_of_detachable

/-- Meeting a subset with a carrier-complement is just removing.

The `sdiff_sdiff_cancel` forms above both take the OUTER set and the inner base
to be the same `x`. A caller working inside a carrier has neither: it holds
`a ⊆ x` and asks about `a ∩ (x \ y)`. This is that shape.

NO DECISION ANYWHERE. `hsub` is spent in the BACKWARD direction only, supplying
the ambient membership the right side does not carry; forwards, `w ∈ x` is
discarded and `y` is never asked about. That asymmetry is the whole difference
between this and `sdiff_sdiff_of_subset_of_detachable` below, which must decide.

It follows from `inter_sdiff_comm`, which is unconditional, and
`inter_eq_self_iff_subset`, which absorbs the carrier. -/
theorem inter_sdiff_of_subset {a x y : ZFSet.{u}}
    (hsub : ∀ w : ZFSet.{u}, w ∈ a → w ∈ x) : a ∩ (x \ y) = a \ y :=
  ext _ _ fun w => ⟨fun hw =>
      have h := (mem_inter_iff w a (x \ y)).mp hw
      (mem_sdiff_iff w a y).mpr ⟨h.left, ((mem_sdiff_iff w x y).mp h.right).right⟩,
    fun hw =>
      have h := (mem_sdiff_iff w a y).mp hw
      (mem_inter_iff w a (x \ y)).mpr
        ⟨h.left, (mem_sdiff_iff w x y).mpr ⟨hsub w h.left, h.right⟩⟩⟩

#print axioms inter_sdiff_of_subset

/-- `sdiff_sdiff_cancel_of_detachable`, relativised to a carrier.

`sdiff_sdiff_cancel_of_detachable` is this at `a = x`, where `hsub` is
`fun _ h => h` --- so generalising costs its callers nothing, and
`sdiff_sdiff_cancel_of_subset_is_cancel` below is that equation rather than a
claim about it.

WHERE THE DECISION GOES, and it is the same single step the unrelativised form
charges for: turning `¬ (w ∈ x ∧ w ∉ y)` into `w ∈ y`. `hsub` supplies the
`w ∈ x` that step consumes and is used nowhere else; backwards is free in both
hypotheses. So relativising costs nothing more. -/
theorem sdiff_sdiff_of_subset_of_detachable {a x y : ZFSet.{u}}
    (hdet : ∀ w : ZFSet.{u}, w ∈ y ∨ w ∉ y)
    (hsub : ∀ w : ZFSet.{u}, w ∈ a → w ∈ x) : a \ (x \ y) = a ∩ y :=
  ext _ _ fun w => ⟨fun hw =>
      have h := (mem_sdiff_iff w a (x \ y)).mp hw
      (mem_inter_iff w a y).mpr
        ⟨h.left, (hdet w).elim id (fun hy =>
          absurd ((mem_sdiff_iff w x y).mpr ⟨hsub w h.left, hy⟩) h.right)⟩,
    fun hw =>
      have h := (mem_inter_iff w a y).mp hw
      (mem_sdiff_iff w a (x \ y)).mpr
        ⟨h.left, fun hs => ((mem_sdiff_iff w x y).mp hs).right h.right⟩⟩

#print axioms sdiff_sdiff_of_subset_of_detachable

/-- Removing `x` from anything already inside `x` leaves nothing. -/
@[simp] theorem sdiff_sdiff_left_self (x y : ZFSet.{u}) : (x \ y) \ x = empty.{u} :=
  ext _ _ fun w => by
    simp only [mem_sdiff_iff, not_mem_empty, iff_false]
    rintro ⟨⟨h, _⟩, h'⟩
    exact h' h

/-! ### Subset characterizations -/

@[simp] theorem empty_subset (x : ZFSet.{u}) : empty.{u} ⊆ x :=
  fun w hw => absurd hw (not_mem_empty w)

theorem inter_subset_left (x y : ZFSet.{u}) : x ∩ y ⊆ x :=
  fun _ h => ((mem_inter_iff _ x y).mp h).left

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

theorem inter_eq_self_iff_subset (x y : ZFSet.{u}) : x ∩ y = x ↔ x ⊆ y := by
  constructor
  · intro h w hw
    rw [← h] at hw
    exact ((mem_inter_iff w x y).mp hw).right
  · intro h
    refine ext _ _ fun w => ?_
    simp only [mem_inter_iff]
    exact ⟨And.left, fun hw => ⟨hw, h w hw⟩⟩

/-! ## Audit -/

#print axioms mem_union_iff
#print axioms union_comm
#print axioms inter_comm
#print axioms inter_assoc
#print axioms empty_subset
#print axioms union_sdiff_self
#print axioms sdiff_union
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

/-- A partial union is disjoint from the next member, given pairwise
disjointness: a point in both lies in some `F i` with `i < k` and in `F k`, and those
indices differ. Free -- nothing is decided, because the index comes out of
`mem_unionUpto_iff` rather than being searched for. -/
theorem unionUpto_inter_eq_empty {F : Nat → ZFSet.{u}}
    (hdisj : ∀ i j : Nat, i ≠ j → inter (F i) (F j) = empty.{u}) (k : Nat) :
    inter (unionUpto F k) (F k) = empty.{u} := by
  refine ext _ _ fun w => ⟨fun hw => ?_, fun hw => absurd hw (not_mem_empty w)⟩
  obtain ⟨hwl, hwr⟩ := (mem_inter_iff w _ _).mp hw
  obtain ⟨i, hik, hwi⟩ := (mem_unionUpto_iff F k w).mp hwl
  have hboth : w ∈ inter (F i) (F k) := (mem_inter_iff w _ _).mpr ⟨hwi, hwr⟩
  rw [hdisj i k (by omega)] at hboth
  exact absurd hboth (not_mem_empty w)

/-- The same disjointness, POINTWISE -- which is the form a consumer wants.

`unionUpto_inter_eq_empty` states it as an equation because that is the algebra's own
idiom, and every consumer of disjointness in the measure development asks instead for
`∀ w, w ∈ B → w ∉ A`: `lebesgueOuter_add_of_measurableGe` takes exactly that. The two
are interderivable through `mem_inter_iff` and neither is redundant, since a proof
supplying disjointness naturally produces the equation and a proof consuming it
naturally wants the implication. -/
theorem not_mem_unionUpto_of_mem {F : Nat → ZFSet.{u}}
    (hdisj : ∀ i j : Nat, i ≠ j → inter (F i) (F j) = empty.{u}) (k : Nat)
    (w : ZFSet.{u}) (hw : w ∈ F k) : w ∉ unionUpto F k := by
  intro hu
  have hboth : w ∈ inter (unionUpto F k) (F k) := (mem_inter_iff w _ _).mpr ⟨hu, hw⟩
  rw [unionUpto_inter_eq_empty hdisj k] at hboth
  exact absurd hboth (not_mem_empty w)

/-- The disjointness is bounded by the cutoff, and the unbounded form is what
a caller cannot supply.

`unionUpto F k` mentions only indices below `k` and the argument cites
`hdisj i k` only for `i < k`, so demanding disjointness at every pair asks for
what is never used. An `IntegralOn` bundle's `disjoint` field is stated only
BELOW its count, because a piece at an index past the count is unconstrained
and says nothing --- so the families these lemmas exist to serve satisfy the
bounded hypothesis and NOT the unbounded one. -/
theorem unionUpto_inter_eq_empty_below {F : Nat → ZFSet.{u}} {k : Nat}
    (hdisj : ∀ i j : Nat, i < k + 1 → j < k + 1 → i ≠ j →
      inter (F i) (F j) = empty.{u}) :
    inter (unionUpto F k) (F k) = empty.{u} := by
  refine ext _ _ fun w => ⟨fun hw => ?_, fun hw => absurd hw (not_mem_empty w)⟩
  obtain ⟨hwl, hwr⟩ := (mem_inter_iff w _ _).mp hw
  obtain ⟨i, hik, hwi⟩ := (mem_unionUpto_iff F k w).mp hwl
  have hboth : w ∈ inter (F i) (F k) := (mem_inter_iff w _ _).mpr ⟨hwi, hwr⟩
  rw [hdisj i k (by omega) (by omega) (by omega)] at hboth
  exact absurd hboth (not_mem_empty w)

/-- Pointwise disjointness gives the equation -- the other direction, and the one a
SUPPLIER of disjointness needs.

Every proof that two sets are disjoint naturally produces the implication (it
takes a point of one and derives a contradiction), while the algebra's lemmas
consume the equation. So both conversions are wanted. -/
theorem inter_eq_empty_of_disjoint {X Y : ZFSet.{u}}
    (h : ∀ w : ZFSet.{u}, w ∈ X → w ∉ Y) : inter X Y = empty.{u} :=
  ext _ _ (fun w => ⟨fun hw =>
      absurd ((mem_inter_iff w X Y).mp hw).right
        (h w ((mem_inter_iff w X Y).mp hw).left),
    fun hw => absurd hw (not_mem_empty w)⟩)


/-- The equation gives pointwise disjointness -- the converse of
`inter_eq_empty_of_disjoint`.

Oriented to match its sibling; a caller wanting the other order composes with
`inter_comm`. -/
theorem disjoint_of_inter_eq_empty {X Y : ZFSet.{u}} (h : inter X Y = empty.{u}) :
    ∀ w : ZFSet.{u}, w ∈ X → w ∉ Y := by
  intro w hwX hwY
  exact not_mem_empty w (h ▸ (mem_inter_iff w X Y).mpr ⟨hwX, hwY⟩)
/-- A union met with its left part is that part. -/
theorem inter_union_left {X Y : ZFSet.{u}} : inter (X ∪ Y) X = X :=
  ext _ _ (fun z => ⟨fun hz => ((mem_inter_iff z (X ∪ Y) X).mp hz).right,
    fun hz => (mem_inter_iff z (X ∪ Y) X).mpr
      ⟨(mem_union_iff z X Y).mpr (Or.inl hz), hz⟩⟩)

/-- A union less its left part is the right part, GIVEN disjointness.

Stated pointwise rather than as `inter X Y = empty`, because the measure
development's splitting lemmas consume disjointness in this form. With
`inter_union_left` it identifies the two Caratheodory pieces of a union with
its two parts. -/
theorem sdiff_union_left {X Y : ZFSet.{u}} (hdisj : ∀ w : ZFSet.{u}, w ∈ Y → w ∉ X) :
    sdiff (X ∪ Y) X = Y :=
  ext _ _ (fun z => ⟨fun hz => by
      obtain ⟨hzU, hzX⟩ := (mem_sdiff_iff z (X ∪ Y) X).mp hz
      exact ((mem_union_iff z X Y).mp hzU).elim (fun h => absurd h hzX) id,
    fun hz => (mem_sdiff_iff z (X ∪ Y) X).mpr
      ⟨(mem_union_iff z X Y).mpr (Or.inr hz), hdisj z hz⟩⟩)


/-- A partial union stays inside anything its members are inside.

Stated for an arbitrary family because the proof uses nothing about the members; the measure
development's instance is at the dyadic pieces, whose own `⊆` lemma is the per-member input. -/
theorem unionUpto_subset {amb : ZFSet.{u}} {F : Nat → ZFSet.{u}}
    (hF : ∀ i : Nat, F i ⊆ amb) : ∀ n : Nat, unionUpto F n ⊆ amb
  | 0 => fun z hz => absurd hz (not_mem_empty z)
  | k + 1 => by
    have h : unionUpto F (k + 1) = unionUpto F k ∪ F k := rfl
    rw [h]
    exact fun z hz => ((mem_union_iff z _ _).mp hz).elim
      (fun hl => unionUpto_subset hF k z hl) (fun hr => hF k z hr)

#print axioms unionUpto
#print axioms unionUpto_subset
#print axioms mem_unionUpto_iff
#print axioms unionUpto_inter_eq_empty

/-- The union of a whole `Nat`-indexed family, bounded by a set holding
every member.

`unionUpto` gives the FINITE partial unions, and every subadditivity statement
in this tower is phrased over those. The countable union is available too: a
`sep` collects the family and `sUnion` unions it, exactly the two steps
`natFun` uses to turn a Lean-indexed family into a ZFSet function. No
replacement and no choice.

The bound `B` is the same hypothesis `natFun` and `equinumerous_natImage` take
when they collect a family they are handed. -/
def unionAll (B : ZFSet.{u}) (F : Nat → ZFSet.{u}) : ZFSet.{u} :=
  sUnion (sep (fun w => ∃ i : Nat, w = F i) B)

/-- Membership in the countable union is membership in some member. -/
theorem mem_unionAll_iff {B : ZFSet.{u}} {F : Nat → ZFSet.{u}}
    (hB : ∀ i, F i ∈ B) (z : ZFSet.{u}) :
    z ∈ unionAll B F ↔ ∃ i : Nat, z ∈ F i := by
  refine Iff.trans (mem_sUnion_iff _ _) ⟨?_, ?_⟩
  · rintro ⟨y, hy, hzy⟩
    obtain ⟨-, i, rfl⟩ := (mem_sep_iff _ _ _).mp hy
    exact ⟨i, hzy⟩
  · rintro ⟨i, hzi⟩
    exact ⟨F i, (mem_sep_iff _ _ _).mpr ⟨hB i, ⟨i, rfl⟩⟩, hzi⟩

#print axioms unionAll
#print axioms mem_unionAll_iff
#print axioms not_mem_unionUpto_of_mem
#print axioms unionUpto_inter_eq_empty_below
#print axioms inter_eq_empty_of_disjoint
#print axioms inter_union_left
#print axioms sdiff_union_left

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

theorem theOnly_mem {P : ZFSet.{u} → Prop} {S a : ZFSet.{u}}
    (ha : a ∈ S) (hPa : P a) (huniq : ∀ b, b ∈ S → P b → b = a) :
    theOnly P S ∈ S := by
  rw [theOnly_eq ha hPa huniq]; exact ha

theorem theOnly_spec {P : ZFSet.{u} → Prop} {S a : ZFSet.{u}}
    (ha : a ∈ S) (hPa : P a) (huniq : ∀ b, b ∈ S → P b → b = a) :
    P (theOnly P S) := by
  rw [theOnly_eq ha hPa huniq]; exact hPa

#print axioms sep_eq_singleton
#print axioms theOnly
#print axioms theOnly_eq
#print axioms theOnly_mem
#print axioms theOnly_spec

/-- The predicate carrier for the algebra of logic.

The lattice laws of `α → Prop` fall out of `and_assoc` and `or_comm` almost
definitionally. This tree's laws are about `ZFSet` and are
proved by extensionality, which is a different theorem about a different object
even though the two coincide.

Writing the predicate carrier down lets the ZFSet laws be DERIVED from the
propositional ones rather than restated beside them. Nothing here costs
anything: `And` and `Or` are associative and commutative constructively. -/
def PSet (α : Type u) : Type u := α → Prop

#print axioms Algebra.PSet
/-! ## Family intersection

An intersection needs no bound, because any one member bounds it.

The `Nat` index supplies that member as `F 0`. An arbitrary index type does not
--- it may be empty, and then the intersection would have to be the universal
set, which `ZFSet` cannot form. So the arbitrary-index law is stated at the
predicate carrier, where `piInter` over an empty index is `fun _ => True`. -/

def interAll (F : Nat → ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => ∀ i : Nat, z ∈ F i) (F 0)

#print axioms interAll
#print axioms Algebra.interAll
#print axioms mem_singleton_iff
#print axioms mem_singleton_self
#print axioms singleton_injective
#print axioms mem_inter_iff
#print axioms mem_sdiff_iff
#print axioms sdiff_self
#print axioms sdiff_empty
#print axioms sdiff_subset
#print axioms sUnion_singleton
#print axioms sUnion_empty
#print axioms inter_eq_self_iff_subset
end Algebra
#print axioms Algebra.inter_sdiff_comm
#print axioms Algebra.empty_inter
#print axioms Algebra.empty_sdiff
#print axioms Algebra.inter_subset_left
#print axioms Algebra.inter_union_cancel
#print axioms Algebra.powerset_empty
#print axioms Algebra.sep_empty
#print axioms Algebra.union_inter_cancel
#print axioms Algebra.empty_union
#print axioms Algebra.inter_empty
#print axioms Algebra.inter_self
#print axioms Algebra.union_empty
#print axioms Algebra.union_self
#print axioms Algebra.disjoint_of_inter_eq_empty

namespace ZFSet
export Algebra (unionUpto_inter_eq_empty_below disjoint_of_inter_eq_empty empty_inter empty_sdiff empty_subset empty_union inter interAll inter_assoc inter_comm inter_empty inter_eq_empty_of_disjoint inter_eq_self_iff_subset inter_sdiff_comm inter_sdiff_of_subset inter_self inter_subset_left inter_union_cancel inter_union_left mem_inter_iff mem_sdiff_iff mem_singleton_iff mem_singleton_self mem_unionAll_iff mem_unionUpto_iff mem_union_iff not_mem_unionUpto_of_mem powerset_empty sUnion_empty sUnion_singleton sdiff sdiff_empty sdiff_sdiff_cancel_of_detachable sdiff_sdiff_of_subset_of_detachable sdiff_sdiff_left_self sdiff_self sdiff_subset sdiff_union sdiff_union_left sep_empty sep_eq_singleton singleton singleton_injective theOnly theOnly_eq theOnly_mem theOnly_spec union unionAll unionUpto unionUpto_inter_eq_empty unionUpto_subset union_comm union_empty union_inter_cancel union_sdiff_self union_self)
end ZFSet
