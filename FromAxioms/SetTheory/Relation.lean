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
#print axioms graphOn_domain
#print axioms app_graphOn
#print axioms app_idMap
#print axioms app_mem_of_isSurjection

end SetTheory

namespace ZFSet
export SetTheory (IsFunction IsInjection IsRelation IsSurjection app app_eq app_graphOn app_idMap app_idOn app_mem_of_isSurjection app_mem_range app_natSeq domain domain_empty funext_zf graphOn graphOn_domain graphOn_isFunction graphOn_subset idMap idOn imageIn imageIn_subset isFunction_union isInjection_inj isSurjection_onto mem_domain_iff mem_graphOn_iff mem_imageIn_iff mem_range_iff mem_sUnion_sUnion_of_opair_mem natFun natFun_mem natFun_ofNat natSeq opAt opair_app_mem range range_empty sep_range_eq_singleton)
end ZFSet
