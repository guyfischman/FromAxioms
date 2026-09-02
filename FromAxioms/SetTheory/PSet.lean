/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Pre-sets: a model of ZFC, built rather than assumed.

The obvious way to get set theory into a proof assistant is to declare the ZFC
axioms as `axiom`s. This file does the opposite: every ZFC axiom below is a
theorem, and the axiom count stays at zero.

The idea is that a set is nothing more than a well-founded tree. A set has
some members; each member is itself a set with its own members; and the nesting
bottoms out. Written as an inductive type that is:

  a set = an index type `α`, together with an `α`-indexed family of sets

which is `PSet` below. Because it is an ordinary inductive definition, the
recursor gives ∈-induction for free, and the ZFC axioms become facts about a
structure we constructed rather than assumptions about one we postulated.

## The catch: equality

Trees carry more information than sets do. The tree indexed by `Bool` sending
both branches to the empty set, and the tree indexed by `Unit` doing the same,
are different trees but both denote the singleton `{∅}`. So `PSet` is not yet
set theory -- it is set theory up to a coarser equality, `Equiv` below, which
identifies trees with the same members. Quotienting by it yields `ZFSet`, and is
the next file.

Everything here is therefore stated in terms of `Equiv` rather than `=`, so
many results carry an explicit congruence hypothesis.

## What this does and does not show

It does not derive ZFC from nothing. It builds a model of ZFC inside
Lean's type theory, which shows Lean's type theory is at least as strong -- a
relative consistency result, and Gödel guarantees nothing better is available.

Note also the universe: `PSet.{u} : Type (u+1)`, since it quantifies over
`Type u`. So this is a model of ZFC at one universe level, not a theory of
"all sets whatsoever".
-/

universe u

/-- A pre-set: an index type together with a family of pre-sets indexed by
it. This is a definition, not an axiom, and every result below flows from it. -/
inductive PSet : Type (u + 1) where
  | mk (α : Type u) (A : α → PSet) : PSet

namespace PSet

/-- The index type of a pre-set. -/
def Idx : PSet.{u} → Type u
  | ⟨α, _⟩ => α

/-- The family of members of a pre-set. -/
def Fam : (x : PSet.{u}) → Idx x → PSet.{u}
  | ⟨_, A⟩ => A

@[simp] theorem idx_mk (α : Type u) (A : α → PSet.{u}) : Idx ⟨α, A⟩ = α := rfl
@[simp] theorem fam_mk (α : Type u) (A : α → PSet.{u}) (a : α) :
    Fam ⟨α, A⟩ a = A a := rfl

/-! ## Extensional equivalence

Two pre-sets are equivalent when each member of one is equivalent to some member
of the other. The definition is recursive, and well-founded because the members
are structurally smaller.
-/

/-- Mutual inclusion, recursively. -/
def Equiv : PSet.{u} → PSet.{u} → Prop
  | ⟨_, A⟩, ⟨_, B⟩ =>
    (∀ a, ∃ b, Equiv (A a) (B b)) ∧ (∀ b, ∃ a, Equiv (A a) (B b))

theorem equiv_iff : ∀ x y : PSet.{u},
    Equiv x y ↔
      (∀ a : Idx x, ∃ b : Idx y, Equiv (Fam x a) (Fam y b)) ∧
      (∀ b : Idx y, ∃ a : Idx x, Equiv (Fam x a) (Fam y b))
  | ⟨_, _⟩, ⟨_, _⟩ => Iff.rfl

protected theorem Equiv.refl : ∀ x : PSet.{u}, Equiv x x
  | ⟨_, A⟩ => ⟨fun a => ⟨a, Equiv.refl (A a)⟩, fun b => ⟨b, Equiv.refl (A b)⟩⟩

/-- The Euclidean property: things equivalent to the same thing are
equivalent. Proved directly, by simultaneous recursion on all three pre-sets,
because it is easier than symmetry and transitivity separately -- both of which
then fall out of it in one line each. -/
protected theorem Equiv.euc :
    ∀ {x y z : PSet.{u}}, Equiv x y → Equiv z y → Equiv x z
  | ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, ⟨αβ, βα⟩, ⟨γβ, βγ⟩ =>
    ⟨fun a =>
       let ⟨b, ab⟩ := αβ a
       let ⟨c, cb⟩ := βγ b
       ⟨c, Equiv.euc ab cb⟩,
     fun c =>
       let ⟨b, cb⟩ := γβ c
       let ⟨a, ab⟩ := βα b
       ⟨a, Equiv.euc ab cb⟩⟩

protected theorem Equiv.symm {x y : PSet.{u}} (h : Equiv x y) : Equiv y x :=
  Equiv.euc (Equiv.refl y) h

protected theorem Equiv.trans {x y z : PSet.{u}}
    (h₁ : Equiv x y) (h₂ : Equiv y z) : Equiv x z :=
  Equiv.euc h₁ (Equiv.symm h₂)

/-- `Equiv` is an equivalence relation, packaged for the quotient to come. -/
instance setoid : Setoid PSet.{u} :=
  ⟨Equiv, ⟨Equiv.refl, Equiv.symm, Equiv.trans⟩⟩

/-! ## Membership -/

/-- `w` is a member of `x` when it is equivalent to one of `x`'s branches. -/
protected def Mem (w x : PSet.{u}) : Prop := ∃ a : Idx x, Equiv w (Fam x a)

instance : Membership PSet.{u} PSet.{u} := ⟨fun x w => PSet.Mem w x⟩

instance : HasSubset PSet.{u} := ⟨fun x y => ∀ w : PSet.{u}, w ∈ x → w ∈ y⟩

/-! ## EXTENSIONALITY

The first ZFC axiom, and here a theorem: equivalent pre-sets are exactly those
with the same members. This is the bridge between the recursive `Equiv` and the
membership-based statement a set theorist would write, and nearly every proof
below routes through it.
-/

theorem equiv_iff_ext : ∀ x y : PSet.{u}, Equiv x y ↔ ∀ w : PSet.{u}, w ∈ x ↔ w ∈ y
  | ⟨_, A⟩, ⟨_, B⟩ =>
    ⟨fun ⟨αβ, βα⟩ _ =>
       ⟨fun ⟨a, ha⟩ => let ⟨b, hb⟩ := αβ a; ⟨b, ha.trans hb⟩,
        fun ⟨b, hb⟩ => let ⟨a, ha⟩ := βα b; ⟨a, hb.trans ha.symm⟩⟩,
     fun h =>
       ⟨fun a => (h (A a)).mp ⟨a, Equiv.refl (A a)⟩,
        fun b => let ⟨a, ha⟩ := (h (B b)).mpr ⟨b, Equiv.refl (B b)⟩; ⟨a, ha.symm⟩⟩⟩

/-- Membership respects equivalence on the right. -/
theorem mem_congr_right {x y : PSet.{u}} (h : Equiv x y) (w : PSet.{u}) :
    w ∈ x ↔ w ∈ y :=
  (equiv_iff_ext x y).mp h w

/-- Membership respects equivalence on the left. -/
theorem mem_congr_left {w v : PSet.{u}} (h : Equiv w v) (x : PSet.{u}) :
    w ∈ x ↔ v ∈ x :=
  ⟨fun ⟨a, ha⟩ => ⟨a, h.symm.trans ha⟩, fun ⟨a, ha⟩ => ⟨a, h.trans ha⟩⟩

/-! ## EMPTY SET

Indexed by the empty type, so there is nothing to be a member. -/

def empty : PSet.{u} := ⟨PEmpty, fun e => e.elim⟩

theorem not_mem_empty (w : PSet.{u}) : w ∉ empty.{u} := fun ⟨e, _⟩ => e.elim

@[simp] theorem mem_empty_iff (w : PSet.{u}) : w ∈ empty.{u} ↔ False :=
  ⟨not_mem_empty w, False.elim⟩

/-! ## PAIRING

Adjoining one element is indexed by `Option`: one extra index for the new
member, and the old indices for the old ones. Unordered pairs follow. -/

def insert (y x : PSet.{u}) : PSet.{u} :=
  ⟨Option (Idx x), fun o => match o with | none => y | some a => Fam x a⟩

theorem mem_insert_iff (w y x : PSet.{u}) :
    w ∈ insert y x ↔ Equiv w y ∨ w ∈ x := by
  constructor
  · rintro ⟨o, ho⟩
    cases o with
    | none => exact Or.inl ho
    | some a => exact Or.inr ⟨a, ho⟩
  · rintro (h | ⟨a, ha⟩)
    · exact ⟨none, h⟩
    · exact ⟨some a, ha⟩

/-- Adjoining respects equivalence in both arguments.

Composed with `Iff.trans` rather than closed by `rw`. Rewriting under `↔` goes
through `propext`, and while that axiom is available, routing around it keeps
this whole file at zero -- so the audit at the bottom says something stronger. -/
theorem insert_congr {y y' x x' : PSet.{u}} (hy : Equiv y y') (hx : Equiv x x') :
    Equiv (insert y x) (insert y' x') := by
  refine (equiv_iff_ext _ _).mpr (fun w => ?_)
  refine Iff.trans (mem_insert_iff w y x)
    (Iff.trans ?_ (mem_insert_iff w y' x').symm)
  constructor
  · rintro (h | h)
    · exact Or.inl (h.trans hy)
    · exact Or.inr ((mem_congr_right hx w).mp h)
  · rintro (h | h)
    · exact Or.inl (h.trans hy.symm)
    · exact Or.inr ((mem_congr_right hx w).mpr h)

/-! ## UNION

The members of the members. Indexed by a dependent pair: pick a branch of `x`,
then a branch of that. -/

def sUnion (x : PSet.{u}) : PSet.{u} :=
  ⟨(a : Idx x) × Idx (Fam x a), fun p => Fam (Fam x p.1) p.2⟩

/-- ZFC's union. -/
theorem mem_sUnion_iff (w x : PSet.{u}) :
    w ∈ sUnion x ↔ ∃ z : PSet.{u}, z ∈ x ∧ w ∈ z := by
  constructor
  · rintro ⟨⟨a, i⟩, h⟩
    exact ⟨Fam x a, ⟨a, Equiv.refl _⟩, ⟨i, h⟩⟩
  · rintro ⟨z, ⟨a, hza⟩, hwz⟩
    obtain ⟨i, hi⟩ := (mem_congr_right hza w).mp hwz
    exact ⟨⟨a, i⟩, hi⟩

/-! ## POWER SET

Indexed by predicates on the index type. This is the step that makes the
model's strength visible: `Idx x → Prop` is an impredicative function type, and
it is doing exactly the work Cantor's theorem says it must. -/

def powerset (x : PSet.{u}) : PSet.{u} :=
  ⟨Idx x → Prop, fun p => ⟨{a : Idx x // p a}, fun s => Fam x s.1⟩⟩

/-- ZFC's power set. -/
theorem mem_powerset_iff (w x : PSet.{u}) : w ∈ powerset x ↔ w ⊆ x := by
  constructor
  · rintro ⟨p, hp⟩ z hz
    obtain ⟨s, hs⟩ := (mem_congr_right hp z).mp hz
    exact ⟨s.1, hs⟩
  · intro h
    refine ⟨fun a => Fam x a ∈ w, (equiv_iff_ext _ _).mpr (fun v => ?_)⟩
    constructor
    · intro hv
      obtain ⟨a, ha⟩ := h v hv
      exact ⟨⟨a, (mem_congr_left ha w).mp hv⟩, ha⟩
    · rintro ⟨s, hs⟩
      exact (mem_congr_left hs w).mpr s.2

/-! ## SEPARATION

Carving out a sub-pre-set by a predicate. The predicate must respect `Equiv` --
otherwise it could distinguish two trees denoting the same set, and the result
would not be well defined on the quotient. That hypothesis is the price of
working with pre-sets instead of sets, and it disappears in the next file. -/

def sep (p : PSet.{u} → Prop) (x : PSet.{u}) : PSet.{u} :=
  ⟨{a : Idx x // p (Fam x a)}, fun s => Fam x s.1⟩

/-- ZFC's separation (restricted comprehension). -/
theorem mem_sep_iff {p : PSet.{u} → Prop}
    (hp : ∀ {a b : PSet.{u}}, Equiv a b → p a → p b) (w x : PSet.{u}) :
    w ∈ sep p x ↔ w ∈ x ∧ p w := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨⟨s.1, hs⟩, hp hs.symm s.2⟩
  · rintro ⟨⟨a, ha⟩, hpw⟩
    exact ⟨⟨a, hp ha hpw⟩, ha⟩

/-! ## INFINITY

The von Neumann naturals: `0 = ∅` and `n+1 = n ∪ {n}`. Note that the recursion
is ordinary structural recursion on Lean's `Nat` -- the infinite set exists here
because `Nat` already does, which is precisely the sense in which type theory
supplies infinity rather than assuming it. -/

def succ (x : PSet.{u}) : PSet.{u} := insert x x

def ofNat : Nat → PSet.{u}
  | 0     => empty
  | n + 1 => succ (ofNat n)

def omega : PSet.{u} := ⟨ULift Nat, fun n => ofNat n.down⟩

theorem empty_mem_omega : empty.{u} ∈ omega.{u} :=
  ⟨ULift.up 0, Equiv.refl _⟩

/-- ZFC's infinity: a set containing `∅` and closed under successor. -/
theorem succ_mem_omega {x : PSet.{u}} (h : x ∈ omega.{u}) : succ x ∈ omega.{u} := by
  obtain ⟨n, hn⟩ := h
  exact ⟨ULift.up (n.down + 1), insert_congr hn hn⟩

/-! ## Congruence

Every construction above respects `Equiv`. `insert_congr` was proved where it
was needed; the rest are collected here.

These are exactly the obligations that must be discharged to push each
construction through the quotient in `ZFSet.lean` -- `Quotient.lift` will not
accept a function unless it is known to be constant on equivalence classes, and
these lemmas are that proof. They are all the same shape: apply
`equiv_iff_ext`, rewrite both sides with the relevant membership lemma, and the
result falls out.
-/

theorem sUnion_congr {x y : PSet.{u}} (h : Equiv x y) :
    Equiv (sUnion x) (sUnion y) := by
  refine (equiv_iff_ext _ _).mpr (fun w => ?_)
  refine Iff.trans (mem_sUnion_iff w x) (Iff.trans ?_ (mem_sUnion_iff w y).symm)
  constructor
  · rintro ⟨z, hzx, hwz⟩
    exact ⟨z, (mem_congr_right h z).mp hzx, hwz⟩
  · rintro ⟨z, hzy, hwz⟩
    exact ⟨z, (mem_congr_right h z).mpr hzy, hwz⟩

theorem powerset_congr {x y : PSet.{u}} (h : Equiv x y) :
    Equiv (powerset x) (powerset y) := by
  refine (equiv_iff_ext _ _).mpr (fun w => ?_)
  refine Iff.trans (mem_powerset_iff w x) (Iff.trans ?_ (mem_powerset_iff w y).symm)
  constructor
  · intro hw z hz
    exact (mem_congr_right h z).mp (hw z hz)
  · intro hw z hz
    exact (mem_congr_right h z).mpr (hw z hz)

theorem sep_congr {p : PSet.{u} → Prop}
    (hp : ∀ {a b : PSet.{u}}, Equiv a b → p a → p b) {x y : PSet.{u}}
    (h : Equiv x y) : Equiv (sep p x) (sep p y) := by
  refine (equiv_iff_ext _ _).mpr (fun w => ?_)
  refine Iff.trans (mem_sep_iff hp w x) (Iff.trans ?_ (mem_sep_iff hp w y).symm)
  constructor
  · rintro ⟨hwx, hpw⟩
    exact ⟨(mem_congr_right h w).mp hwx, hpw⟩
  · rintro ⟨hwy, hpw⟩
    exact ⟨(mem_congr_right h w).mpr hwy, hpw⟩

#print axioms equiv_iff_ext      -- EXTENSIONALITY
#print axioms mem_empty_iff      -- EMPTY SET
#print axioms mem_sUnion_iff     -- UNION
#print axioms mem_powerset_iff   -- POWER SET
#print axioms mem_sep_iff        -- SEPARATION
#print axioms succ_mem_omega     -- INFINITY

end PSet
