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

/-! ## Graphs

A Lean-level function on sets becomes a set function by taking its graph over a
domain, provided the values stay inside some set. Nothing here needs
replacement: the graph is carved out of `x × y` by separation, which is the same
bounding move as everywhere else. -/

/-- The operation applied to a pair, written the way the axioms read. -/
def opAt (op a b : ZFSet.{u}) : ZFSet.{u} := app op (opair a b)

#print axioms mem_domain_iff
#print axioms app_eq
end SetTheory

namespace ZFSet
export SetTheory (IsFunction IsRelation app app_eq app_mem_range domain domain_empty mem_domain_iff mem_range_iff mem_sUnion_sUnion_of_opair_mem opAt opair_app_mem range range_empty sep_range_eq_singleton)
end ZFSet
