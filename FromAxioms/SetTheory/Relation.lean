/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Relations and functions.

A relation is a set of ordered pairs; a function is a relation that is
single-valued. Both are predicates on sets rather than new constructions, which
is what encoding pairs buys.

Domain and range are carved out of `⋃⋃r` by separation: if `⟨a, b⟩ ∈ r` then
`{a}` and `{a, b}` are members of a member of `r`, so both `a` and `b` are
members of a member of a member.

Application avoids choice. `f ⬝ a` is defined as `⋃ {b ∈ range f | ⟨a,b⟩ ∈ f}`;
single-valuedness makes that separation a singleton, and the union of a
singleton is its element. No representative has to be selected.
-/

import FromAxioms.NumberTheory.Natural
import FromAxioms.SetTheory.Pair

universe u

open Algebra NumberTheory
namespace SetTheory

/-! ## Relations -/

def IsRelation (r : ZFSet.{u}) : Prop :=
  ∀ p, p ∈ r → ∃ a b, p = opair a b

/-- Both coordinates of a pair in `r` live in `⋃⋃r`. -/
theorem mem_sUnion_sUnion_of_opair_mem {a b r : ZFSet.{u}} (h : opair a b ∈ r) :
    a ∈ sUnion (sUnion r) ∧ b ∈ sUnion (sUnion r) := by
  have hsa : singleton a ∈ sUnion r :=
    (mem_sUnion_iff _ r).mpr ⟨opair a b, h, (mem_opair_iff _ a b).mpr (Or.inl rfl)⟩
  have hpa : pair a b ∈ sUnion r :=
    (mem_sUnion_iff _ r).mpr ⟨opair a b, h, (mem_opair_iff _ a b).mpr (Or.inr rfl)⟩
  exact ⟨(mem_sUnion_iff _ _).mpr ⟨singleton a, hsa, mem_singleton_self a⟩,
         (mem_sUnion_iff _ _).mpr
           ⟨pair a b, hpa, (mem_pair_iff b a b).mpr (Or.inr rfl)⟩⟩

def domain (r : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun a => ∃ b, opair a b ∈ r) (sUnion (sUnion r))

def range (r : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun b => ∃ a, opair a b ∈ r) (sUnion (sUnion r))

@[simp] theorem mem_domain_iff (a r : ZFSet.{u}) :
    a ∈ domain r ↔ ∃ b, opair a b ∈ r := by
  refine Iff.trans (mem_sep_iff _ a _) ⟨And.right, ?_⟩
  rintro ⟨b, hb⟩
  exact ⟨(mem_sUnion_sUnion_of_opair_mem hb).left, b, hb⟩

@[simp] theorem mem_range_iff (b r : ZFSet.{u}) :
    b ∈ range r ↔ ∃ a, opair a b ∈ r := by
  refine Iff.trans (mem_sep_iff _ b _) ⟨And.right, ?_⟩
  rintro ⟨a, ha⟩
  exact ⟨(mem_sUnion_sUnion_of_opair_mem ha).right, a, ha⟩

/-! ### The empty relation

The relation laws at `empty`. -/

@[simp] theorem domain_empty : domain empty.{u} = empty.{u} :=
  ext _ _ fun a => ⟨fun ha =>
    let ⟨b, hb⟩ := (mem_domain_iff a _).mp ha
    absurd hb (not_mem_empty _), fun ha => absurd ha (not_mem_empty a)⟩

@[simp] theorem range_empty : range empty.{u} = empty.{u} :=
  ext _ _ fun b => ⟨fun hb =>
    let ⟨a, ha⟩ := (mem_range_iff b _).mp hb
    absurd ha (not_mem_empty _), fun hb => absurd hb (not_mem_empty b)⟩

/-! ## Functions -/

def IsFunction (f : ZFSet.{u}) : Prop :=
  IsRelation f ∧ ∀ a b c, opair a b ∈ f → opair a c ∈ f → b = c

/-- The empty set is a function: vacuously single-valued, and its domain is
empty, so it is the function on no arguments. -/
theorem isFunction_empty : IsFunction empty.{u} :=
  ⟨fun p hp => absurd hp (not_mem_empty p),
    fun _ _ _ hb => absurd hb (not_mem_empty _)⟩

/-- A Lean-level family, carved into a graph, is a function.

This is how a `ZFSet → ZFSet` becomes an object the theory can quantify over,
and it is the same three lines everywhere it is done: single-valuedness is
`opair_injective` twice and then the two second components agree because the
first ones did. Extracted from three copies
-- `Cardinal.lean`, `FiniteSubsets.lean` and `Halving.lean` -- each building a
graph for a different family.

The codomain `C` is a parameter and not `image f D`: a caller may know only that
the values land somewhere, which is enough, and demanding the exact image would
force each caller to prove surjectivity it does not need. -/
theorem isFunction_graphOn {D C : ZFSet.{u}} (f : ZFSet.{u} → ZFSet.{u}) :
    IsFunction (sep (fun z => ∃ a, a ∈ D ∧ z = opair a (f a)) (prod D C)) := by
  constructor
  · intro z hz
    obtain ⟨-, a, -, he⟩ := (mem_sep_iff _ z _).mp hz
    exact ⟨_, _, he⟩
  · intro a b b' hb hb'
    obtain ⟨-, c, -, he⟩ := (mem_sep_iff _ _ _).mp hb
    obtain ⟨-, c', -, he'⟩ := (mem_sep_iff _ _ _).mp hb'
    obtain ⟨rfl, rfl⟩ := opair_injective he
    obtain ⟨hc, rfl⟩ := opair_injective he'
    rw [hc]

/-- Application, without choice: the separation below is a singleton. -/
def app (f a : ZFSet.{u}) : ZFSet.{u} :=
  sUnion (sep (fun b => opair a b ∈ f) (range f))

theorem sep_range_eq_singleton {f a b : ZFSet.{u}} (hf : IsFunction f)
    (h : opair a b ∈ f) :
    sep (fun v => opair a v ∈ f) (range f) = singleton b :=
  ext _ _ fun v => by
    refine Iff.trans (mem_sep_iff _ v _) ?_
    refine Iff.trans ?_ (mem_singleton_iff v b).symm
    exact ⟨fun ⟨_, hv⟩ => hf.right a v b hv h,
           fun hvb => ⟨(mem_range_iff v f).mpr ⟨a, hvb ▸ h⟩, hvb ▸ h⟩⟩

theorem app_eq {f a b : ZFSet.{u}} (hf : IsFunction f) (h : opair a b ∈ f) :
    app f a = b := by
  rw [app, sep_range_eq_singleton hf h, sUnion_singleton]

theorem opair_app_mem {f a : ZFSet.{u}} (hf : IsFunction f)
    (ha : a ∈ domain f) : opair a (app f a) ∈ f := by
  obtain ⟨b, hb⟩ := (mem_domain_iff a f).mp ha
  rw [app_eq hf hb]
  exact hb

theorem app_mem_range {f a : ZFSet.{u}} (hf : IsFunction f) (ha : a ∈ domain f) :
    app f a ∈ range f :=
  (mem_range_iff _ f).mpr ⟨a, opair_app_mem hf ha⟩

#print axioms IsFunction

/-- Two functions with the same domain that agree pointwise are equal. -/
theorem funext_zf {f g : ZFSet.{u}} (hf : IsFunction f) (hg : IsFunction g)
    (hdom : domain f = domain g)
    (hval : ∀ a, a ∈ domain f → app f a = app g a) : f = g := by
  refine ext _ _ fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨a, b, rfl⟩ := hf.left p hp
    have ha : a ∈ domain f := (mem_domain_iff a f).mpr ⟨b, hp⟩
    have : app g a = b := by rw [← hval a ha, app_eq hf hp]
    exact this ▸ opair_app_mem hg (hdom ▸ ha)
  · obtain ⟨a, b, rfl⟩ := hg.left p hp
    have hag : a ∈ domain g := (mem_domain_iff a g).mpr ⟨b, hp⟩
    have haf : a ∈ domain f := hdom ▸ hag
    have : app f a = b := by rw [hval a haf, app_eq hg hp]
    exact this ▸ opair_app_mem hf haf

/-! ### Extending a function by one pair

The step of every recursion on `ω`, and stated with `k ∉ domain g` as a
hypothesis rather than derived: the caller knows why its new key is fresh, and
for the naturals that reason is `not_mem_self`, which lives further down the
tower than this file. -/

/-- `g`, with `k` sent to `v`. -/
def extendAt (g k v : ZFSet.{u}) : ZFSet.{u} := g ∪ singleton (opair k v)

theorem mem_extendAt_iff (g k v p : ZFSet.{u}) :
    p ∈ extendAt g k v ↔ Or (p ∈ g) (p = opair k v) :=
  Iff.trans (mem_union_iff p _ _)
    (or_congr Iff.rfl (mem_singleton_iff p _))

theorem opair_mem_extendAt (g k v : ZFSet.{u}) : opair k v ∈ extendAt g k v :=
  (mem_extendAt_iff g k v _).mpr (Or.inr rfl)

theorem subset_extendAt (g k v : ZFSet.{u}) : g ⊆ extendAt g k v :=
  fun _ hp => (mem_extendAt_iff g k v _).mpr (Or.inl hp)

/-- A fresh key keeps it a function. Both mixed cases are where the
hypothesis is spent: a pair of `g` at the new key would put that key in
`domain g`. -/
theorem isFunction_extendAt {g k v : ZFSet.{u}} (hg : IsFunction g)
    (hk : k ∉ domain g) : IsFunction (extendAt g k v) := by
  refine ⟨fun p hp => ?_, fun a b c hb hc => ?_⟩
  · rcases (mem_extendAt_iff g k v p).mp hp with h | h
    · exact hg.left p h
    · exact ⟨k, v, h⟩
  · rcases (mem_extendAt_iff g k v _).mp hb with hb' | hb' <;>
      rcases (mem_extendAt_iff g k v _).mp hc with hc' | hc'
    · exact hg.right a b c hb' hc'
    · obtain ⟨hak, -⟩ := opair_injective hc'
      exact absurd (hak ▸ (mem_domain_iff a g).mpr ⟨b, hb'⟩) hk
    · obtain ⟨hak, -⟩ := opair_injective hb'
      exact absurd (hak ▸ (mem_domain_iff a g).mpr ⟨c, hc'⟩) hk
    · obtain ⟨-, hbv⟩ := opair_injective hb'
      obtain ⟨-, hcv⟩ := opair_injective hc'
      rw [hbv, hcv]

/-- The domain grows by exactly the new key. -/
theorem domain_extendAt_succ {g k v : ZFSet.{u}} (hd : domain g = k) :
    domain (extendAt g k v) = succ k := by
  refine ext _ _ fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · obtain ⟨b, hb⟩ := (mem_domain_iff a _).mp ha
    rcases (mem_extendAt_iff g k v _).mp hb with h | h
    · exact (mem_succ_iff a k).mpr (Or.inr (hd ▸ (mem_domain_iff a g).mpr ⟨b, h⟩))
    · exact (mem_succ_iff a k).mpr (Or.inl (opair_injective h).left)
  · rcases (mem_succ_iff a k).mp ha with rfl | h
    · exact (mem_domain_iff a _).mpr ⟨v, opair_mem_extendAt g a v⟩
    · obtain ⟨b, hb⟩ := (mem_domain_iff a g).mp (hd ▸ h)
      exact (mem_domain_iff a _).mpr ⟨b, subset_extendAt g k v _ hb⟩

theorem app_extendAt_self {g k v : ZFSet.{u}} (hg : IsFunction g)
    (hk : k ∉ domain g) : app (extendAt g k v) k = v :=
  app_eq (isFunction_extendAt hg hk) (opair_mem_extendAt g k v)

/-- Below the new key nothing moves, so an approximation extends without
disturbing what it already said. -/
theorem app_extendAt_of_mem {g k v a : ZFSet.{u}} (hg : IsFunction g)
    (hk : k ∉ domain g) (ha : a ∈ domain g) :
    app (extendAt g k v) a = app g a :=
  app_eq (isFunction_extendAt hg hk) (subset_extendAt g k v _ (opair_app_mem hg ha))

/-! ### The recursion theorem: finite approximations

`natSeq` below internalises a recursion Lean has already performed, so it says
what Lean's `Nat` can do and nothing about what `ω` can. This
is the other thing: the approximations are built as SETS, from `a` and `f`
alone.

They are indexed from ONE. The step needs the previous value to apply `f` to,
and at stage zero there is none -- so a zero-indexed statement forces a case
split on empty-or-successor inside the step, while indexing from one makes the
base `{(∅, a)}` and leaves the previous stage always in hand. -/

/-- A finite approximation: a function on `n` obeying both recursion clauses
wherever they apply inside `n`. -/
structure IsRecApprox (A a f n g : ZFSet.{u}) : Prop where
  isFun : IsFunction g
  dom : domain g = n
  bounded : g ⊆ prod n A
  zero : empty.{u} ∈ n → app g empty.{u} = a
  step : ∀ k, succ k ∈ n → app g (succ k) = app f (app g k)

/-- An approximation exists at every stage. The recursion is on the `Nat`
that indexes the stage, but every step BUILDS a set and the statement is about
sets throughout -- so unlike `natSeq` nothing is transported in from outside. -/
theorem exists_recApprox {A a f : ZFSet.{u}} (ha : a ∈ A)
    (hval : ∀ v, v ∈ A → app f v ∈ A) (n : Nat) :
    ∃ g, IsRecApprox.{u} A a f (ofNat.{u} (n + 1)) g := by
  induction n with
  | zero =>
    have hfresh : empty.{u} ∉ domain empty.{u} := by
      rw [domain_empty]; exact not_mem_empty _
    refine ⟨extendAt empty.{u} empty.{u} a, isFunction_extendAt isFunction_empty hfresh,
      domain_extendAt_succ domain_empty, ?_, ?_, ?_⟩
    · intro p hp
      rcases (mem_extendAt_iff _ _ _ p).mp hp with h | h
      · exact absurd h (not_mem_empty p)
      · exact h ▸ (mem_prod_iff _ _ _).mpr
          ⟨empty.{u}, (mem_succ_iff _ _).mpr (Or.inl rfl), a, ha, rfl⟩
    · exact fun _ => app_extendAt_self isFunction_empty hfresh
    · intro k hk
      rcases (mem_succ_iff (succ k) empty.{u}).mp hk with h | h
      · exact absurd h (succ_ne_empty k)
      · exact absurd h (not_mem_empty _)
  | succ n ih =>
    obtain ⟨g, hfun, hdom, hsub, hzero, hstep⟩ := ih
    have hfresh : ofNat.{u} (n + 1) ∉ domain g := by
      rw [hdom]; exact not_mem_self _
    have hprev : ofNat.{u} n ∈ domain g := by
      rw [hdom]; exact (mem_succ_iff _ _).mpr (Or.inl rfl)
    have hprevA : app g (ofNat.{u} n) ∈ A := by
      have := hsub _ (opair_app_mem hfun hprev)
      obtain ⟨x, _, y, hy, he⟩ := (mem_prod_iff _ _ _).mp this
      rw [(opair_injective he).right]; exact hy
    refine ⟨extendAt g (ofNat.{u} (n + 1)) (app f (app g (ofNat.{u} n))),
      isFunction_extendAt hfun hfresh, domain_extendAt_succ hdom, ?_, ?_, ?_⟩
    · intro p hp
      rcases (mem_extendAt_iff _ _ _ p).mp hp with h | h
      · obtain ⟨x, hx, y, hy, rfl⟩ := (mem_prod_iff _ _ _).mp (hsub p h)
        exact (mem_prod_iff _ _ _).mpr
          ⟨x, (mem_succ_iff _ _).mpr (Or.inr hx), y, hy, rfl⟩
      · exact h ▸ (mem_prod_iff _ _ _).mpr
          ⟨ofNat.{u} (n + 1), (mem_succ_iff _ _).mpr (Or.inl rfl),
            app f (app g (ofNat.{u} n)), hval _ hprevA, rfl⟩
    · intro _
      have hz : empty.{u} ∈ domain g := by rw [hdom]; exact empty_mem_ofNat_succ n
      rw [app_extendAt_of_mem hfun hfresh hz]
      exact hzero (hdom ▸ hz)
    · intro k hk
      rcases (mem_succ_iff (succ k) (ofNat.{u} (n + 1))).mp hk with h | h
      · have hkn : k = ofNat.{u} n := succ_injective h
        rw [h, app_extendAt_self hfun hfresh, hkn,
          app_extendAt_of_mem hfun hfresh hprev]
      · have hkdom : succ k ∈ domain g := by rw [hdom]; exact h
        have hkd : k ∈ domain g := by
          rw [hdom]
          exact ofNat_transitive (n + 1) h (mem_succ_self k)
        rw [app_extendAt_of_mem hfun hfresh hkdom,
          app_extendAt_of_mem hfun hfresh hkd]
        exact hstep k (hdom ▸ hkdom)

/-- Any two approximations agree wherever both are defined. The induction is
on the stage, and both clauses are used exactly once: the base says both send
`∅` to `a`, and the step says both send `k⁺` to `f` of their own value at `k`,
which the inductive hypothesis has already equated.

Stated over NUMERAL domains rather than arbitrary ones, because the step needs
`k⁺ ∈ n → k ∈ n` and that is `ofNat_transitive` -- true of a natural and not of
a set in general. `exists_recApprox` only ever produces numeral domains, so
nothing is lost. -/
theorem recApprox_agree {A a f : ZFSet.{u}} {p q : Nat} {g g' : ZFSet.{u}}
    (hg : IsRecApprox.{u} A a f (ofNat.{u} (p + 1)) g)
    (hg' : IsRecApprox.{u} A a f (ofNat.{u} (q + 1)) g') :
    ∀ j : Nat, ofNat.{u} j ∈ ofNat.{u} (p + 1) → ofNat.{u} j ∈ ofNat.{u} (q + 1) →
      app g (ofNat.{u} j) = app g' (ofNat.{u} j) := by
  obtain ⟨-, -, -, hz, hs⟩ := hg
  obtain ⟨-, -, -, hz', hs'⟩ := hg'
  intro j
  induction j with
  | zero => intro h1 h2; rw [ofNat_zero, hz (ofNat_zero ▸ h1), hz' (ofNat_zero ▸ h2)]
  | succ j ih =>
    intro h1 h2
    have t1 : ofNat.{u} j ∈ ofNat.{u} (p + 1) :=
      ofNat_transitive (p + 1) h1 (mem_succ_self _)
    have t2 : ofNat.{u} j ∈ ofNat.{u} (q + 1) :=
      ofNat_transitive (q + 1) h2 (mem_succ_self _)
    rw [ofNat_succ, hs (ofNat.{u} j) (ofNat_succ j ▸ h1),
      hs' (ofNat.{u} j) (ofNat_succ j ▸ h2), ih t1 t2]

/-! ### The recursion theorem: the union

All the approximations at once, as a set -- a separation over
`powerset (prod ω A)`, so the bound is the axiom of power set and nothing
stronger. `recApprox_agree` is exactly what makes the union single-valued:
without it two approximations could disagree and the union would be a relation
rather than a function. -/

/-- Every finite approximation, collected. -/
def recSet (A a f : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun g => ∃ p : Nat, IsRecApprox.{u} A a f (ofNat.{u} (p + 1)) g)
    (powerset (prod omega.{u} A))

theorem mem_recSet_iff (A a f g : ZFSet.{u}) :
    g ∈ recSet A a f ↔ And (g ∈ powerset (prod omega.{u} A))
      (∃ p : Nat, IsRecApprox.{u} A a f (ofNat.{u} (p + 1)) g) :=
  mem_sep_iff _ _ _

/-- An approximation qualifies: its pairs are bounded by `ω × A`, because its
domain is a numeral and every member of a numeral is in `ω`. -/
theorem recApprox_mem_recSet {A a f g : ZFSet.{u}} {p : Nat}
    (hg : IsRecApprox.{u} A a f (ofNat.{u} (p + 1)) g) : g ∈ recSet A a f := by
  refine (mem_recSet_iff A a f g).mpr ⟨(mem_powerset_iff _ _).mpr ?_, p, hg⟩
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ :=
    (mem_prod_iff _ _ _).mp (hg.bounded z hz)
  exact (mem_prod_iff _ _ _).mpr ⟨x, mem_of_mem_ofNat (p + 1) hx, y, hy, rfl⟩

/-- The recursion's function: every approximation, unioned. -/
def recFun (A a f : ZFSet.{u}) : ZFSet.{u} := sUnion (recSet A a f)

theorem mem_recFun_iff (A a f z : ZFSet.{u}) :
    z ∈ recFun A a f ↔ ∃ g, And (g ∈ recSet A a f) (z ∈ g) :=
  mem_sUnion_iff _ _

/-- The union is a function. Two pairs at one key come from two
approximations; the key is a numeral because it lies in a numeral domain, and
`recApprox_agree` then equates the two values. -/
theorem isFunction_recFun (A a f : ZFSet.{u}) : IsFunction (recFun A a f) := by
  refine ⟨fun z hz => ?_, fun k b c hb hc => ?_⟩
  · obtain ⟨g, hgS, hzg⟩ := (mem_recFun_iff A a f z).mp hz
    obtain ⟨-, p, hg⟩ := (mem_recSet_iff A a f g).mp hgS
    exact hg.isFun.left z hzg
  · obtain ⟨g, hgS, hbg⟩ := (mem_recFun_iff A a f _).mp hb
    obtain ⟨g', hgS', hcg⟩ := (mem_recFun_iff A a f _).mp hc
    obtain ⟨-, p, hg⟩ := (mem_recSet_iff A a f g).mp hgS
    obtain ⟨-, q, hg'⟩ := (mem_recSet_iff A a f g').mp hgS'
    have hk : k ∈ ofNat.{u} (p + 1) :=
      hg.dom ▸ (mem_domain_iff k g).mpr ⟨b, hbg⟩
    have hk' : k ∈ ofNat.{u} (q + 1) :=
      hg'.dom ▸ (mem_domain_iff k g').mpr ⟨c, hcg⟩
    obtain ⟨j, rfl⟩ := (mem_omega_iff k).mp (mem_of_mem_ofNat (p + 1) hk)
    rw [← app_eq hg.isFun hbg, ← app_eq hg'.isFun hcg]
    exact recApprox_agree hg hg' j hk hk'

/-- The union's value is any approximation's value. Every later fact about
`recFun` goes through this: pick a stage whose domain reaches far enough, and
the union answers exactly as that stage does. -/
theorem app_recFun_eq {A a f g : ZFSet.{u}} {p j : Nat}
    (hg : IsRecApprox.{u} A a f (ofNat.{u} (p + 1)) g)
    (hj : ofNat.{u} j ∈ ofNat.{u} (p + 1)) :
    app (recFun A a f) (ofNat.{u} j) = app g (ofNat.{u} j) :=
  app_eq (isFunction_recFun A a f)
    ((mem_recFun_iff A a f _).mpr
      ⟨g, recApprox_mem_recSet hg, opair_app_mem hg.isFun (hg.dom ▸ hj)⟩)

/-- The union is defined on all of `ω` -- no further, because every
approximation is bounded by `ω × A`, and no less, because a stage reaching any
given numeral exists. -/
theorem domain_recFun {A a f : ZFSet.{u}} (ha : a ∈ A)
    (hval : ∀ v, v ∈ A → app f v ∈ A) : domain (recFun A a f) = omega.{u} := by
  refine ext _ _ fun k => ⟨fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨b, hb⟩ := (mem_domain_iff k _).mp hk
    obtain ⟨g, hgS, hbg⟩ := (mem_recFun_iff A a f _).mp hb
    have hbound := (mem_powerset_iff _ _).mp ((mem_recSet_iff A a f g).mp hgS).left
    exact mem_prod_left (hbound _ hbg)
  · obtain ⟨j, rfl⟩ := (mem_omega_iff k).mp hk
    obtain ⟨g, hg⟩ := exists_recApprox ha hval j
    have hj : ofNat.{u} j ∈ ofNat.{u} (j + 1) := (mem_succ_iff _ _).mpr (Or.inl rfl)
    exact (mem_domain_iff _ _).mpr ⟨app g (ofNat.{u} j),
      (mem_recFun_iff A a f _).mpr
        ⟨g, recApprox_mem_recSet hg, opair_app_mem hg.isFun (hg.dom ▸ hj)⟩⟩

/-- The base clause, read off the stage-zero approximation. -/
theorem app_recFun_empty {A a f : ZFSet.{u}} (ha : a ∈ A)
    (hval : ∀ v, v ∈ A → app f v ∈ A) :
    app (recFun A a f) empty.{u} = a := by
  obtain ⟨g, hg⟩ := exists_recApprox ha hval 0
  have h0 : empty.{u} ∈ ofNat.{u} (0 + 1) := empty_mem_ofNat_succ 0
  rw [← ofNat_zero, app_recFun_eq hg (ofNat_zero ▸ h0), ofNat_zero]
  exact hg.zero h0

/-- The step clause. The stage is chosen one past the successor, so both the
successor and its predecessor are inside that approximation's domain and the
union agrees with it at each. -/
theorem app_recFun_succ {A a f : ZFSet.{u}} (ha : a ∈ A)
    (hval : ∀ v, v ∈ A → app f v ∈ A) :
    ∀ n, n ∈ omega.{u} →
      app (recFun A a f) (succ n) = app f (app (recFun A a f) n) := by
  intro n hn
  obtain ⟨j, rfl⟩ := (mem_omega_iff n).mp hn
  obtain ⟨g, hg⟩ := exists_recApprox ha hval (j + 1)
  have hsj : ofNat.{u} (j + 1) ∈ ofNat.{u} (j + 1 + 1) :=
    (mem_succ_iff _ _).mpr (Or.inl rfl)
  have hj : ofNat.{u} j ∈ ofNat.{u} (j + 1 + 1) :=
    ofNat_transitive (j + 1 + 1) hsj (mem_succ_self _)
  rw [show succ (ofNat.{u} j) = ofNat.{u} (j + 1) from rfl,
    app_recFun_eq hg hsj, app_recFun_eq hg hj,
    show ofNat.{u} (j + 1) = succ (ofNat.{u} j) from rfl]
  exact hg.step (ofNat.{u} j) hsj

/-- The recursion's values stay in `A`, which the bound on every approximation
already forces. -/
theorem app_recFun_mem {A a f : ZFSet.{u}} (ha : a ∈ A)
    (hval : ∀ v, v ∈ A → app f v ∈ A) :
    ∀ n, n ∈ omega.{u} → app (recFun A a f) n ∈ A := by
  intro n hn
  have hpair := opair_app_mem (isFunction_recFun A a f) (domain_recFun ha hval ▸ hn)
  obtain ⟨g, hgS, hg⟩ := (mem_recFun_iff A a f _).mp hpair
  have hbound := (mem_powerset_iff _ _).mp ((mem_recSet_iff A a f g).mp hgS).left
  exact mem_prod_right (hbound _ hg)

/-! ### Second-order Peano models, and categoricity

A model is a set with a zero and a successor OPERATION -- the successor is a
set function, not a Lean one, so the whole statement lives inside the theory.
The induction clause quantifies over every subset of the carrier, which is what
second-order means here and what categoricity rests on; the first-order schema
of `Peano.lean` has non-standard models (`Nonstandard.lean` builds one). -/

structure IsPeano (N z s : ZFSet.{u}) : Prop where
  zero_mem : z ∈ N
  succ_fun : IsFunction s
  succ_dom : domain s = N
  succ_mem : ∀ x, x ∈ N → app s x ∈ N
  succ_ne_zero : ∀ x, x ∈ N → app s x ≠ z
  succ_inj : ∀ x, x ∈ N → ∀ y, y ∈ N → app s x = app s y → x = y
  induct : ∀ S, S ⊆ N → z ∈ S → (∀ x, x ∈ S → app s x ∈ S) → S = N

/-- The map `ω → N` the recursion theorem supplies. -/
def peanoMap (N z s : ZFSet.{u}) : ZFSet.{u} := recFun N z s

theorem peanoMap_zero {N z s : ZFSet.{u}} (h : IsPeano.{u} N z s) :
    app (peanoMap N z s) empty.{u} = z :=
  app_recFun_empty h.zero_mem h.succ_mem

theorem peanoMap_succ {N z s : ZFSet.{u}} (h : IsPeano.{u} N z s) :
    ∀ n, n ∈ omega.{u} →
      app (peanoMap N z s) (succ n) = app s (app (peanoMap N z s) n) :=
  app_recFun_succ h.zero_mem h.succ_mem

theorem peanoMap_mem {N z s : ZFSet.{u}} (h : IsPeano.{u} N z s) :
    ∀ n, n ∈ omega.{u} → app (peanoMap N z s) n ∈ N :=
  app_recFun_mem h.zero_mem h.succ_mem

/-- The map is onto. Its image is a subset of `N` containing `z` and closed
under the successor, so the model's own induction clause forces it to be all of
`N` -- which is the whole use made of second-order induction. -/
theorem peanoMap_surjective {N z s : ZFSet.{u}} (h : IsPeano.{u} N z s) :
    ∀ y, y ∈ N → ∃ n, And (n ∈ omega.{u}) (app (peanoMap N z s) n = y) := by
  have himg : sep (fun y => ∃ n, And (n ∈ omega.{u})
      (app (peanoMap N z s) n = y)) N = N := by
    refine h.induct _ (fun w hw => ((mem_sep_iff _ w _).mp hw).left) ?_ ?_
    · exact (mem_sep_iff _ _ _).mpr
        ⟨h.zero_mem, empty.{u}, empty_mem_omega, peanoMap_zero h⟩
    · intro x hx
      obtain ⟨hxN, n, hn, hval⟩ := (mem_sep_iff _ x _).mp hx
      refine (mem_sep_iff _ _ _).mpr ⟨h.succ_mem x hxN, succ n, succ_mem_omega n hn, ?_⟩
      rw [peanoMap_succ h n hn, hval]
  intro y hy
  exact ((mem_sep_iff _ y _).mp (himg ▸ hy)).right

/-- The map is injective. A double induction on the stage: at zero the
model's `succ_ne_zero` separates the images, and at a successor the model's
`succ_inj` peels one step off each side. Both Peano clauses of `N` are used, and
`ω`'s own `succ_injective` is not needed at all -- the recursion carries the
index. -/
theorem peanoMap_injective {N z s : ZFSet.{u}} (h : IsPeano.{u} N z s) :
    ∀ (m n : Nat), app (peanoMap N z s) (ofNat.{u} m)
      = app (peanoMap N z s) (ofNat.{u} n) → m = n := by
  intro m
  induction m with
  | zero =>
    intro n hmn
    cases n with
    | zero => rfl
    | succ n =>
      rw [ofNat_zero, peanoMap_zero h, ofNat_succ,
        peanoMap_succ h (ofNat.{u} n) (ofNat_mem_omega n)] at hmn
      exact absurd hmn.symm
        (h.succ_ne_zero _ (peanoMap_mem h _ (ofNat_mem_omega n)))
  | succ m ih =>
    intro n hmn
    cases n with
    | zero =>
      rw [ofNat_zero, peanoMap_zero h, ofNat_succ,
        peanoMap_succ h (ofNat.{u} m) (ofNat_mem_omega m)] at hmn
      exact absurd hmn (h.succ_ne_zero _ (peanoMap_mem h _ (ofNat_mem_omega m)))
    | succ n =>
      rw [ofNat_succ, ofNat_succ, peanoMap_succ h (ofNat.{u} m) (ofNat_mem_omega m),
        peanoMap_succ h (ofNat.{u} n) (ofNat_mem_omega n)] at hmn
      exact congrArg (· + 1) (ih n (h.succ_inj _ (peanoMap_mem h _ (ofNat_mem_omega m))
        _ (peanoMap_mem h _ (ofNat_mem_omega n)) hmn))

/-! ## Graphs

A Lean-level function on sets becomes a set function by taking its graph over a
domain, provided the values stay inside some set. Nothing here needs
replacement: the graph is carved out of `x × y` by separation, which is the same
bounding move as everywhere else. -/

def graphOn (x y : ZFSet.{u}) (F : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => ∃ n, n ∈ x ∧ z = opair n (F n)) (prod x y)

theorem mem_graphOn_iff (x y : ZFSet.{u}) (F : ZFSet.{u} → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∈ graphOn x y F ↔ z ∈ prod x y ∧ ∃ n, n ∈ x ∧ z = opair n (F n) :=
  mem_sep_iff _ _ _

theorem graphOn_subset (x y : ZFSet.{u}) (F : ZFSet.{u} → ZFSet.{u}) :
    graphOn x y F ⊆ prod x y := fun _ hz => ((mem_graphOn_iff x y F _).mp hz).left

theorem graphOn_isFunction (x y : ZFSet.{u}) (F : ZFSet.{u} → ZFSet.{u}) :
    IsFunction (graphOn x y F) := by
  constructor
  · intro p hp
    obtain ⟨-, n, -, rfl⟩ := (mem_graphOn_iff x y F p).mp hp
    exact ⟨n, F n, rfl⟩
  · intro a b c hb hc
    obtain ⟨-, n, -, he⟩ := (mem_graphOn_iff x y F _).mp hb
    obtain ⟨-, m, -, he'⟩ := (mem_graphOn_iff x y F _).mp hc
    obtain ⟨rfl, rfl⟩ := opair_injective he
    obtain ⟨rfl, rfl⟩ := opair_injective he'
    rfl

theorem graphOn_domain {x y : ZFSet.{u}} {F : ZFSet.{u} → ZFSet.{u}}
    (hF : ∀ n, n ∈ x → F n ∈ y) : domain (graphOn x y F) = x := by
  refine ext _ _ fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · obtain ⟨b, hb⟩ := (mem_domain_iff a _).mp ha
    obtain ⟨-, n, hn, he⟩ := (mem_graphOn_iff x y F _).mp hb
    obtain ⟨rfl, -⟩ := opair_injective he
    exact hn
  · exact (mem_domain_iff a _).mpr ⟨F a, (mem_graphOn_iff x y F _).mpr
      ⟨opair_mem_prod ha (hF a ha), a, ha, rfl⟩⟩

theorem app_graphOn {x y n : ZFSet.{u}} {F : ZFSet.{u} → ZFSet.{u}}
    (hF : ∀ m, m ∈ x → F m ∈ y) (hn : n ∈ x) : app (graphOn x y F) n = F n :=
  app_eq (graphOn_isFunction x y F) ((mem_graphOn_iff x y F _).mpr
    ⟨opair_mem_prod hn (hF n hn), n, hn, rfl⟩)

#print axioms graphOn_isFunction

/-- The operation applied to a pair, written the way the axioms read. -/
def opAt (op a b : ZFSet.{u}) : ZFSet.{u} := app op (opair a b)

/-- The identity function on a set, as a set of pairs. -/
def idOn (x : ZFSet.{u}) : ZFSet.{u} := graphOn x x (fun w => w)

theorem app_idOn {x w : ZFSet.{u}} (hw : w ∈ x) : app (idOn x) w = w :=
  app_graphOn (fun _ hm => hm) hw

/-- The identity map on a set, as a set of ordered pairs. -/
def idMap (x : ZFSet.{u}) : ZFSet.{u} := graphOn x x (fun z => z)

theorem app_idMap {x a : ZFSet.{u}} (ha : a ∈ x) : app (idMap x) a = a :=
  app_graphOn (fun _ hm => hm) ha

/-- Two functions with disjoint domains are a function. What lets a map
defined by cases be assembled from pieces, each of which is the graph of a
total Lean function on its own part of the domain. Nothing is decided: the
cases are separated by where they are defined, not by a test. -/
theorem isFunction_union {f g : ZFSet.{u}} (hf : IsFunction f)
    (hg : IsFunction g)
    (hd : ∀ a b c, opair a b ∈ f → opair a c ∈ g → False) :
    IsFunction (f ∪ g) :=
  ⟨fun p hp => ((mem_union_iff p f g).mp hp).elim (hf.left p) (hg.left p),
   fun a b c hb hc =>
     ((mem_union_iff _ f g).mp hb).elim
       (fun hbf => ((mem_union_iff _ f g).mp hc).elim
         (fun hcf => hf.right a b c hbf hcf)
         (fun hcg => absurd hcg (fun h => hd a b c hbf h)))
       (fun hbg => ((mem_union_iff _ f g).mp hc).elim
         (fun hcf => absurd hbg (fun h => hd a c b hcf h))
         (fun hcg => hg.right a b c hbg hcg))⟩

#print axioms isFunction_union

/-! ## Images

The image of a subset under a set function, bounded by a codomain that is known
in advance -- separation standing in for replacement, as in `natSeq`.
-/

/-- The image of `S` under a set function, inside a known codomain. -/
def imageIn (f S y : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun v => ∃ w, w ∈ S ∧ v = app f w) y

theorem mem_imageIn_iff (f S y v : ZFSet.{u}) :
    v ∈ imageIn f S y ↔ v ∈ y ∧ ∃ w, w ∈ S ∧ v = app f w :=
  mem_sep_iff _ _ _

theorem imageIn_subset (f S y : ZFSet.{u}) : imageIn f S y ⊆ y :=
  fun _ hv => ((mem_imageIn_iff f S y _).mp hv).left

/-! ## Sequences from Lean-level families

A Lean function `Nat → ZFSet` is not a set, and turning it into one meets the
same obstacle replacement does. A bounding set settles it: if
every term lies in `B`, separation over `B` recovers the term from its index and
`graphOn` assembles the graph. -/

def natFun (B : ZFSet.{u}) (K : Nat → ZFSet.{u}) (x : ZFSet.{u}) : ZFSet.{u} :=
  sUnion (sep (fun z => ∃ m : Nat, x = ofNat.{u} m ∧ z = K m) B)

theorem natFun_ofNat {B : ZFSet.{u}} {K : Nat → ZFSet.{u}} (hK : ∀ m, K m ∈ B) (n : Nat) :
    natFun B K (ofNat.{u} n) = K n := by
  have hsing : sep (fun z => ∃ m : Nat, ofNat.{u} n = ofNat.{u} m ∧ z = K m) B
      = singleton (K n) := by
    refine ext _ _ fun z => ⟨fun hz => ?_, fun hz => ?_⟩
    · obtain ⟨-, m, hm, rfl⟩ := (mem_sep_iff _ _ _).mp hz
      rw [ofNat_injective hm]
      exact (mem_singleton_iff _ _).mpr rfl
    · rw [(mem_singleton_iff z (K n)).mp hz]
      exact (mem_sep_iff _ _ _).mpr ⟨hK n, n, rfl, rfl⟩
  rw [natFun, hsing, sUnion_singleton]

theorem natFun_mem {B : ZFSet.{u}} {K : Nat → ZFSet.{u}} (hK : ∀ m, K m ∈ B) :
    ∀ n, n ∈ omega.{u} → natFun B K n ∈ B := by
  intro n hn
  obtain ⟨m, rfl⟩ := (mem_omega_iff n).mp hn
  rw [natFun_ofNat hK m]
  exact hK m

/-- The sequence as a set function `ω → B`. -/
def natSeq (B : ZFSet.{u}) (K : Nat → ZFSet.{u}) : ZFSet.{u} :=
  graphOn omega.{u} B (natFun B K)

theorem app_natSeq {B : ZFSet.{u}} {K : Nat → ZFSet.{u}} (hK : ∀ m, K m ∈ B) (n : Nat) :
    app (natSeq B K) (ofNat.{u} n) = K n := by
  rw [natSeq, app_graphOn (natFun_mem hK) (ofNat_mem_omega n), natFun_ofNat hK]

/-! ## Injections and surjections

Stated for set functions, so that "there is an injection `x → y`" is a
statement about sets rather than about Lean's function space. The distinction
matters: a Lean-level function is available for refuting things about it, but
only a set function can be quantified over inside the theory. -/

def IsInjection (f x y : ZFSet.{u}) : Prop :=
  IsFunction f ∧ domain f = x ∧ range f ⊆ y ∧
    ∀ a, a ∈ x → ∀ b, b ∈ x → app f a = app f b → a = b

/-- The clause a proof reaches for: injectivity itself. -/
theorem isInjection_inj {f x y a b : ZFSet.{u}} (h : IsInjection f x y)
    (ha : a ∈ x) (hb : b ∈ x) (he : app f a = app f b) : a = b :=
  h.right.right.right a ha b hb he

def IsSurjection (f x y : ZFSet.{u}) : Prop :=
  IsFunction f ∧ domain f = x ∧ range f ⊆ y ∧ ∀ b, b ∈ y → ∃ a, a ∈ x ∧ app f a = b

/-- The clause a proof reaches for: every point of `y` is hit. -/
theorem isSurjection_onto {f x y b : ZFSet.{u}} (h : IsSurjection f x y) (hb : b ∈ y) :
    ∃ a, a ∈ x ∧ app f a = b := h.right.right.right b hb

theorem app_mem_of_isSurjection {f x y : ZFSet.{u}} (h : IsSurjection f x y)
    {a : ZFSet.{u}} (ha : a ∈ x) : app f a ∈ y := by
  obtain ⟨hfun, hdom, hran, -⟩ := h
  exact hran _ (app_mem_range hfun (hdom ▸ ha))

#print axioms mem_domain_iff
#print axioms app_eq
#print axioms funext_zf
#print axioms extendAt
#print axioms isFunction_extendAt
#print axioms domain_extendAt_succ
#print axioms app_extendAt_self
#print axioms app_extendAt_of_mem
#print axioms IsRecApprox
#print axioms exists_recApprox
#print axioms recApprox_agree
#print axioms recSet
#print axioms recApprox_mem_recSet
#print axioms recFun
#print axioms isFunction_recFun
#print axioms app_recFun_eq
#print axioms domain_recFun
#print axioms app_recFun_empty
#print axioms app_recFun_succ
#print axioms app_recFun_mem
#print axioms IsPeano
#print axioms peanoMap
#print axioms peanoMap_zero
#print axioms peanoMap_succ
#print axioms peanoMap_mem
#print axioms peanoMap_surjective
#print axioms peanoMap_injective
#print axioms graphOn_domain
#print axioms app_graphOn
#print axioms app_idMap
#print axioms app_mem_of_isSurjection

end SetTheory

namespace ZFSet
export SetTheory (IsFunction IsInjection IsPeano IsRecApprox IsRelation IsSurjection app app_eq app_extendAt_of_mem app_extendAt_self app_graphOn app_idMap app_idOn app_mem_of_isSurjection app_mem_range app_natSeq app_recFun_empty app_recFun_eq app_recFun_mem app_recFun_succ domain domain_empty domain_extendAt_succ domain_recFun exists_recApprox extendAt funext_zf graphOn graphOn_domain graphOn_isFunction graphOn_subset idMap idOn imageIn imageIn_subset isFunction_empty isFunction_extendAt isFunction_graphOn isFunction_recFun isFunction_union isInjection_inj isSurjection_onto mem_domain_iff mem_extendAt_iff mem_graphOn_iff mem_imageIn_iff mem_range_iff mem_recFun_iff mem_recSet_iff mem_sUnion_sUnion_of_opair_mem natFun natFun_mem natFun_ofNat natSeq opAt opair_app_mem opair_mem_extendAt peanoMap peanoMap_injective peanoMap_mem peanoMap_succ peanoMap_surjective peanoMap_zero range range_empty recApprox_agree recApprox_mem_recSet recFun recSet sep_range_eq_singleton subset_extendAt)
end ZFSet
