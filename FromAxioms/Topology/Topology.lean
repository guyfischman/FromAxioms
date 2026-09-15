/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Topological spaces.

A topology on a set `X` is a family of subsets containing `∅` and `X`, closed
under pairwise intersection and under arbitrary union. Everything here is
constructive: an arbitrary union is `sUnion` of a subfamily, which the axioms
already provide, and no separation axiom is assumed unless it is named.
-/

import FromAxioms.Core.CoreShim
import FromAxioms.SetTheory.Cantor
import FromAxioms.SetTheory.Cardinal

universe u

open Algebra Analysis Constructive NumberTheory SetTheory
namespace Topology

/-! ## The structure -/

structure IsTopology (T X : ZFSet.{u}) : Prop where
  opens_sub : ∀ U, U ∈ T → U ⊆ X
  mem_empty : empty.{u} ∈ T
  mem_univ : X ∈ T
  inter_closed : ∀ U, U ∈ T → ∀ V, V ∈ T → inter U V ∈ T
  union_closed : ∀ F, F ⊆ T → sUnion F ∈ T

/-- The subspace topology: the traces of the opens on a subset.

Defined by SEPARATION over `powerset A` rather than by replacing each open with
its trace. The two describe the same set, and the sep form is the one that needs
nothing: replacement would hand back a family indexed by the opens, and reading
a trace back to an open it came from is a choice this does not have to make.

`union_closed` is where that matters. Given a family of traces, the union is the
trace of the union of the opens they came from --- but "the opens they came
from" is exactly the choice being avoided. The repair is to take ALL opens whose
trace lies in the family, `sep (fun U => inter U A ∈ F) T`, which is a set by
separation and contains a witness for every member. -/
def subspaceOpens (T A : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun W => ∃ U, U ∈ T ∧ W = inter U A) (powerset A)

theorem mem_subspaceOpens_iff (T A W : ZFSet.{u}) :
    W ∈ subspaceOpens T A ↔ W ⊆ A ∧ ∃ U, U ∈ T ∧ W = inter U A :=
  Iff.trans (mem_sep_iff _ _ _)
    ⟨fun h => ⟨(mem_powerset_iff _ _).mp h.left, h.right⟩,
     fun h => ⟨(mem_powerset_iff _ _).mpr h.left, h.right⟩⟩

/-- A subspace of a space is a space. -/
theorem isTopology_subspaceOpens {T X A : ZFSet.{u}} (hT : IsTopology T X)
    (hA : A ⊆ X) : IsTopology (subspaceOpens T A) A where
  opens_sub W hW := ((mem_subspaceOpens_iff T A W).mp hW).left
  mem_empty := (mem_subspaceOpens_iff T A _).mpr
    ⟨empty_subset A, empty.{u}, hT.mem_empty, (empty_inter A).symm⟩
  mem_univ := (mem_subspaceOpens_iff T A _).mpr
    -- `A = X ∩ A` by membership. NOT by `rw [inter_comm ...]`: the goal carries
    -- `X.inter A` and the rewrite pattern is `X ∩ A`, which does not match
    -- syntactically even though `mem_inter_iff` applies to both.
    ⟨fun w hw => hw, X, hT.mem_univ, ext _ _ (fun w =>
      ⟨fun hw => (mem_inter_iff w X A).mpr ⟨hA w hw, hw⟩,
       fun hw => ((mem_inter_iff w X A).mp hw).right⟩)⟩
  inter_closed W₁ h₁ W₂ h₂ := by
    obtain ⟨hs₁, U₁, hU₁, rfl⟩ := (mem_subspaceOpens_iff T A W₁).mp h₁
    obtain ⟨hs₂, U₂, hU₂, rfl⟩ := (mem_subspaceOpens_iff T A W₂).mp h₂
    refine (mem_subspaceOpens_iff T A _).mpr
      ⟨fun w hw => hs₁ w ((mem_inter_iff w _ _).mp hw).left,
       U₁ ∩ U₂, hT.inter_closed U₁ hU₁ U₂ hU₂, ?_⟩
    -- `(U₁ ∩ A) ∩ (U₂ ∩ A) = (U₁ ∩ U₂) ∩ A`, by membership on both sides,
    -- written out rather than by `simp only` -- which made no progress here.
    refine ext _ _ (fun w => ⟨fun h => ?_, fun h => ?_⟩)
    · obtain ⟨h₁, h₂⟩ := (mem_inter_iff w _ _).mp h
      obtain ⟨hu₁, ha⟩ := (mem_inter_iff w U₁ A).mp h₁
      obtain ⟨hu₂, _⟩ := (mem_inter_iff w U₂ A).mp h₂
      exact (mem_inter_iff w _ A).mpr ⟨(mem_inter_iff w U₁ U₂).mpr ⟨hu₁, hu₂⟩, ha⟩
    · obtain ⟨hu, ha⟩ := (mem_inter_iff w _ A).mp h
      obtain ⟨hu₁, hu₂⟩ := (mem_inter_iff w U₁ U₂).mp hu
      exact (mem_inter_iff w _ _).mpr
        ⟨(mem_inter_iff w U₁ A).mpr ⟨hu₁, ha⟩, (mem_inter_iff w U₂ A).mpr ⟨hu₂, ha⟩⟩
  union_closed F hF := by
    -- ALL opens whose trace is in the family: a set by separation, and it
    -- contains a witness for every member, so no choice is made.
    refine (mem_subspaceOpens_iff T A _).mpr ⟨fun w hw => ?_, sUnion (sep (fun U => U ∩ A ∈ F) T),
      hT.union_closed _ (fun U hU => (mem_sep_iff _ _ _).mp hU |>.left), ?_⟩
    · obtain ⟨W, hWF, hwW⟩ := (mem_sUnion_iff w F).mp hw
      exact ((mem_subspaceOpens_iff T A W).mp (hF W hWF)).left w hwW
    · -- Written out rather than by `simp only`: the tactic shape is the part an
      -- audit cannot check, so keep every step a named membership lemma.
      refine ext _ _ (fun w => ⟨fun h => ?_, fun h => ?_⟩)
      · obtain ⟨W, hWF, hwW⟩ := (mem_sUnion_iff w F).mp h
        obtain ⟨_, U, hU, rfl⟩ := (mem_subspaceOpens_iff T A W).mp (hF W hWF)
        obtain ⟨hwU, hwA⟩ := (mem_inter_iff w U A).mp hwW
        exact (mem_inter_iff w _ A).mpr
          ⟨(mem_sUnion_iff w _).mpr ⟨U, (mem_sep_iff _ _ _).mpr ⟨hU, hWF⟩, hwU⟩, hwA⟩
      · obtain ⟨hwS, hwA⟩ := (mem_inter_iff w _ A).mp h
        obtain ⟨U, hU, hwU⟩ := (mem_sUnion_iff w _).mp hwS
        exact (mem_sUnion_iff w F).mpr
          ⟨U ∩ A, ((mem_sep_iff _ _ _).mp hU).right,
           (mem_inter_iff w U A).mpr ⟨hwU, hwA⟩⟩

/-! ## The specialisation order

The up-set topology remembers the relation it came from: `a` is in every open
containing... rather, every open containing `a` contains `b` exactly when `a`
relates to `b`. So `upSets` and `spec` are inverse on preorders, which is the
Alexandrov correspondence in the one direction this file can state without a
category.

Only reflexivity and transitivity are used, and each is used once:
transitivity to make the principal up-set open, reflexivity to put `a` in it.
-/

/-- `a` specialises to `b` when every open containing `a` contains `b`. -/
def spec (T X : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => ∀ U, U ∈ T → fst z ∈ U → snd z ∈ U) (prod X X)

/-! ## Closed sets, interior and closure -/

def IsClosed (T X C : ZFSet.{u}) : Prop := C ⊆ X ∧ sdiff X C ∈ T

/-- Closed sets are closed under binary union, and that direction is the
constructive one: `X \ (C₁ ∪ C₂) = (X \ C₁) ∩ (X \ C₂)` is `sdiff_union`,
while the dual law `sdiff_inter` -- which is what closure under intersection
would need -- is classical (it is in `tools/classical.json`). So a constructive
topology has closed sets closed under finite unions and not, without further
hypotheses, under finite intersections. -/
theorem isClosed_union {T X C D : ZFSet.{u}} (h : IsTopology T X)
    (hC : IsClosed T X C) (hD : IsClosed T X D) : IsClosed T X (C ∪ D) := by
  refine ⟨fun w hw => ?_, ?_⟩
  · rcases (mem_union_iff w C D).mp hw with h' | h'
    · exact hC.left w h'
    · exact hD.left w h'
  · show X \ (C ∪ D) ∈ T
    rw [sdiff_union]
    exact h.inter_closed _ hC.right _ hD.right

/-- And under intersection exactly when one of them is detachable. The
missing step is `sdiff_inter`, de Morgan's third law, which this project has
reversed to weak excluded middle -- so the asymmetry above is not
an artefact of how `isClosed_union` was proved. Detachability of `C` on `X` is
what supplies the case split the law needs, and it is a hypothesis about one set
rather than a principle. -/
theorem isClosed_inter_of_detachable {T X C D : ZFSet.{u}} (h : IsTopology T X)
    (hC : IsClosed T X C) (hD : IsClosed T X D)
    (hdec : ∀ w, w ∈ X → w ∈ C ∨ w ∉ C) : IsClosed T X (C ∩ D) := by
  refine ⟨fun w hw => hC.left w ((mem_inter_iff w C D).mp hw).left, ?_⟩
  have hde : X \ (C ∩ D) = (X \ C) ∪ (X \ D) := by
    refine ext _ _ fun w => ⟨fun hw => ?_, fun hw => ?_⟩
    · obtain ⟨hwX, hwCD⟩ := (mem_sdiff_iff w _ _).mp hw
      rcases hdec w hwX with hwC | hwC
      · exact (mem_union_iff w _ _).mpr (Or.inr ((mem_sdiff_iff w X D).mpr
          ⟨hwX, fun hwD => hwCD ((mem_inter_iff w C D).mpr ⟨hwC, hwD⟩)⟩))
      · exact (mem_union_iff w _ _).mpr (Or.inl ((mem_sdiff_iff w X C).mpr ⟨hwX, hwC⟩))
    · rcases (mem_union_iff w _ _).mp hw with hin | hin
      · obtain ⟨hwX, hwC⟩ := (mem_sdiff_iff w X C).mp hin
        exact (mem_sdiff_iff w _ _).mpr
          ⟨hwX, fun hc => hwC ((mem_inter_iff w C D).mp hc).left⟩
      · obtain ⟨hwX, hwD⟩ := (mem_sdiff_iff w X D).mp hin
        exact (mem_sdiff_iff w _ _).mpr
          ⟨hwX, fun hc => hwD ((mem_inter_iff w C D).mp hc).right⟩
  show X \ (C ∩ D) ∈ T
  rw [hde]
  show sUnion (pair (X \ C) (X \ D)) ∈ T
  refine h.union_closed _ fun w hw => ?_
  rcases (mem_pair_iff w _ _).mp hw with rfl | rfl
  · exact hC.right
  · exact hD.right

#print axioms Topology.IsTopology

/-! ## Continuity -/

def preimageIn (f X V : ZFSet.{u}) : ZFSet.{u} := sep (fun x => app f x ∈ V) X

theorem mem_preimageIn_iff (f X V w : ZFSet.{u}) :
    w ∈ preimageIn f X V ↔ w ∈ X ∧ app f w ∈ V := mem_sep_iff _ _ _

/-- Compactness, by open covers given as INDEXED FAMILIES.

A cover is a set function `u` from an index set `J` to opens, and a finite
subcover is a bound `n` with an enumeration of INDICES. Not a set of opens with
a finite subset, and the difference is not presentation: with indices the image
theorem is choice-free.

MEASURED, by writing the set version first and watching it fail. With a cover
as a SET `C`, pulling it back through `f` produces the set of preimages, and a
finite subcover of the source comes back as opens `V i` each satisfying
`∃ U ∈ C, V i = preimageIn f X U`. Pushing that forward needs the `U` for each
`i` --- an existential per index, extracted, which is a choice. With indices the
correspondence is definitional: the same `idx i` names a member of `J` on both
sides, and nothing is chosen.

That is this tree's standing rule (`UniformOn`'s modulus, `TotallyBoundedOn`'s
net) applied to compactness: carry the DATA, not an existential over it.

Stated as a `Prop` because it is a HYPOTHESIS here rather than a construction:
`[0,1]` is not open-cover compact without the fan theorem, so this predicate has
no located-real instance and must not be read as having one. -/
def IsCompact (T X K : ZFSet.{u}) : Prop :=
  K ⊆ X ∧ ∀ J u, IsFunction u → domain u = J → (∀ j, j ∈ J → app u j ∈ T) →
    (∀ x, x ∈ K → ∃ j, j ∈ J ∧ x ∈ app u j) →
      ∃ (n : Nat) (idx : Nat → ZFSet.{u}),
        (∀ i, i < n → idx i ∈ J) ∧
        ∀ x, x ∈ K → ∃ i, i < n ∧ x ∈ app u (idx i)

def IsContinuous (f X Y S T : ZFSet.{u}) : Prop :=
  IsFunction f ∧ domain f = X ∧ range f ⊆ Y ∧ ∀ V, V ∈ T → preimageIn f X V ∈ S

/-- A cover that carries what a finite subcover has to be COMPUTED from.

`Topology.IsCompact`'s conclusion demands `idx : Nat -> ZFSet` --- an index per
member of the subcover, as DATA. Its hypothesis offers only
`forall x in K, exists j, x in u j`, a `Prop`. Nothing constructs the one from
the other: extracting a function from a bounded `forall`-`exists` is finite
choice, and membership in a located open is not decidable, so it cannot be
searched for either.

That is why open-cover compactness of `[0, 1]` is the FANΔ THEOREM here and not
a consequence of `Analysis.totallyBoundedOn_realLIcc`. The obstruction is not the
interval and not the reals; it is the same one rung 9 met for compactness and
rung 16 met for connectedness --- a decision handed over as a proposition.

A `CoverData` hands over both missing pieces:

  * `sel`, saying WHICH open a point is in, so the subcover's indices can be
    computed rather than chosen; and
  * `mesh`, a Lebesgue scale, so finitely many net points suffice --- without
    it the net is fine enough for the metric and still says nothing about the
    cover.

Neither is derivable from the other, and neither is derivable from the `Prop`
cover. With both, a totally bounded carrier yields a finite subcover by
computation. -/
structure CoverData (d K J u : ZFSet.{u}) : Type (u + 1) where
  sel : ZFSet.{u} → ZFSet.{u}
  sel_mem : ∀ x, x ∈ K → sel x ∈ J
  sel_covers : ∀ x, x ∈ K → x ∈ app u (sel x)
  mesh : Nat
  lebesgue : ∀ x, x ∈ K → ∀ y, y ∈ K →
    realLLt (app d (opair x y)) (realLOf (invWidth (ofNat.{u} mesh))) →
    y ∈ app u (sel x)

/-! ## The order topology on ℝ

A set of reals is open when every point of it has an interval around it inside
it. The two closure conditions need the order to be a lattice, and for cuts that
is free: the larger of two cuts is their union, the smaller their intersection.
-/

def realMax (x y : ZFSet.{u}) : ZFSet.{u} := x ∪ y

def realMin (x y : ZFSet.{u}) : ZFSet.{u} := inter x y

theorem realMax_mem_Real {x y : ZFSet.{u}} (hx : x ∈ Real.{u}) (hy : y ∈ Real.{u}) :
    realMax x y ∈ Real.{u} := by
  obtain hx' := (mem_Real_iff x).mp hx
  obtain hy' := (mem_Real_iff y).mp hy
  refine (mem_Real_iff _).mpr ⟨fun q hq => ?_, ?_, ?_, ?_, ?_⟩
  · rcases (mem_union_iff q x y).mp hq with h | h
    · exact hx'.subset _ h
    · exact hy'.subset _ h
  · obtain ⟨q, hq⟩ := hx'.nonempty
    exact ⟨q, (mem_union_iff q x y).mpr (Or.inl hq)⟩
  · -- a rational above both bounds is outside the union
    obtain ⟨q, hqR, hqx⟩ := hx'.proper
    obtain ⟨r, hrR, hry⟩ := hy'.proper
    rcases ratLt_trichotomy hqR hrR with hlt | heq | hgt
    · refine ⟨r, hrR, fun hmem => ?_⟩
      rcases (mem_union_iff r x y).mp hmem with h | h
      · exact hqx (hx'.down _ h _ hqR hlt)
      · exact hry h
    · refine ⟨r, hrR, fun hmem => ?_⟩
      rcases (mem_union_iff r x y).mp hmem with h | h
      · exact hqx (heq ▸ h)
      · exact hry h
    · refine ⟨q, hqR, fun hmem => ?_⟩
      rcases (mem_union_iff q x y).mp hmem with h | h
      · exact hqx h
      · exact hry (hy'.down _ h _ hrR hgt)
  · intro q hq p hp hlt
    rcases (mem_union_iff q x y).mp hq with h | h
    · exact (mem_union_iff p x y).mpr (Or.inl (hx'.down _ h _ hp hlt))
    · exact (mem_union_iff p x y).mpr (Or.inr (hy'.down _ h _ hp hlt))
  · intro q hq
    rcases (mem_union_iff q x y).mp hq with h | h
    · obtain ⟨p, hp, hlt⟩ := hx'.no_greatest q h
      exact ⟨p, (mem_union_iff p x y).mpr (Or.inl hp), hlt⟩
    · obtain ⟨p, hp, hlt⟩ := hy'.no_greatest q h
      exact ⟨p, (mem_union_iff p x y).mpr (Or.inr hp), hlt⟩

theorem realMin_mem_Real {x y : ZFSet.{u}} (hx : x ∈ Real.{u}) (hy : y ∈ Real.{u}) :
    realMin x y ∈ Real.{u} := by
  obtain hx' := (mem_Real_iff x).mp hx
  obtain hy' := (mem_Real_iff y).mp hy
  refine (mem_Real_iff _).mpr ⟨fun q hq => hx'.subset _ ((mem_inter_iff q x y).mp hq).left,
    ?_, ?_, ?_, ?_⟩
  · -- a rational below both is in the intersection
    obtain ⟨q, hq⟩ := hx'.nonempty
    obtain ⟨r, hr⟩ := hy'.nonempty
    rcases ratLt_trichotomy (hx'.subset _ hq) (hy'.subset _ hr) with hlt | heq | hgt
    · exact ⟨q, (mem_inter_iff q x y).mpr ⟨hq, hy'.down _ hr _ (hx'.subset _ hq) hlt⟩⟩
    · exact ⟨q, (mem_inter_iff q x y).mpr ⟨hq, heq ▸ hr⟩⟩
    · exact ⟨r, (mem_inter_iff r x y).mpr ⟨hx'.down _ hq _ (hy'.subset _ hr) hgt, hr⟩⟩
  · obtain ⟨q, hqR, hqx⟩ := hx'.proper
    exact ⟨q, hqR, fun hmem => hqx ((mem_inter_iff q x y).mp hmem).left⟩
  · intro q hq p hp hlt
    obtain ⟨hqx, hqy⟩ := (mem_inter_iff q x y).mp hq
    exact (mem_inter_iff p x y).mpr ⟨hx'.down _ hqx _ hp hlt, hy'.down _ hqy _ hp hlt⟩
  · intro q hq
    obtain ⟨hqx, hqy⟩ := (mem_inter_iff q x y).mp hq
    obtain ⟨p, hp, hlt⟩ := hx'.no_greatest q hqx
    obtain ⟨p', hp', hlt'⟩ := hy'.no_greatest q hqy
    rcases ratLt_trichotomy (hx'.subset _ hp) (hy'.subset _ hp') with hlt2 | heq | hgt
    · exact ⟨p, (mem_inter_iff p x y).mpr ⟨hp, hy'.down _ hp' _ (hx'.subset _ hp) hlt2⟩, hlt⟩
    · exact ⟨p, (mem_inter_iff p x y).mpr ⟨hp, heq ▸ hp'⟩, hlt⟩
    · exact ⟨p', (mem_inter_iff p' x y).mpr ⟨hx'.down _ hp _ (hy'.subset _ hp') hgt, hp'⟩, hlt'⟩

/-- The strict order, with a witness: some rational is in `y` and not in `x`.
`x ⊆ y ∧ x ≠ y` would not do -- from `x ≠ y` one cannot produce the rational
that separates them without excluded middle. -/
def realLt (x y : ZFSet.{u}) : Prop := ∃ q, q ∈ y ∧ q ∉ x

/-- Every real has a rational cut strictly below and one strictly above. -/
theorem exists_realLt_around {x : ZFSet.{u}} (hx : x ∈ Real.{u}) :
    (∃ p, p ∈ Real.{u} ∧ realLt p x) ∧ ∃ q, q ∈ Real.{u} ∧ realLt x q := by
  have hxc := (mem_Real_iff x).mp hx
  constructor
  · obtain ⟨q, hq⟩ := hxc.nonempty
    have hqR := hxc.subset _ hq
    exact ⟨ratCut q, ratCut_mem_Real hqR, q, hq,
      fun hmem => ratLt_irrefl ((mem_ratCut_iff q q).mp hmem).right⟩
  · obtain ⟨r, hrR, hrx⟩ := hxc.proper
    obtain ⟨t, htR, hrt⟩ := rat_no_greatest hrR
    exact ⟨ratCut t, ratCut_mem_Real htR, r, (mem_ratCut_iff t r).mpr ⟨hrR, hrt⟩, hrx⟩

/-- The larger of two cuts below `x` is below `x`. -/
theorem realLt_realMax {p p2 x : ZFSet.{u}} (hp : p ∈ Real.{u}) (hp2 : p2 ∈ Real.{u})
    (hx : x ∈ Real.{u}) (h : realLt p x) (h2 : realLt p2 x) : realLt (realMax p p2) x := by
  have hxc := (mem_Real_iff x).mp hx
  have hpc := (mem_Real_iff p).mp hp
  have hp2c := (mem_Real_iff p2).mp hp2
  obtain ⟨a, haX, hap⟩ := h
  obtain ⟨b, hbX, hbp⟩ := h2
  rcases ratLt_trichotomy (hxc.subset _ haX) (hxc.subset _ hbX) with hlt | heq | hgt
  · refine ⟨b, hbX, fun hmem => ?_⟩
    rcases (mem_union_iff b p p2).mp hmem with hb | hb
    · exact hap (hpc.down _ hb _ (hxc.subset _ haX) hlt)
    · exact hbp hb
  · refine ⟨b, hbX, fun hmem => ?_⟩
    rcases (mem_union_iff b p p2).mp hmem with hb | hb
    · exact hap (heq ▸ hb)
    · exact hbp hb
  · refine ⟨a, haX, fun hmem => ?_⟩
    rcases (mem_union_iff a p p2).mp hmem with ha | ha
    · exact hap ha
    · exact hbp (hp2c.down _ ha _ (hxc.subset _ hbX) hgt)

/-- The smaller of two cuts above `x` is above `x`. -/
theorem realLt_realMin {x q q2 : ZFSet.{u}} (hq : q ∈ Real.{u})
    (hq2 : q2 ∈ Real.{u}) (h : realLt x q) (h2 : realLt x q2) : realLt x (realMin q q2) := by
  have hqc := (mem_Real_iff q).mp hq
  have hq2c := (mem_Real_iff q2).mp hq2
  obtain ⟨a, haQ, haX⟩ := h
  obtain ⟨b, hbQ, hbX⟩ := h2
  rcases ratLt_trichotomy (hqc.subset _ haQ) (hq2c.subset _ hbQ) with hlt | heq | hgt
  · exact ⟨a, (mem_inter_iff a q q2).mpr ⟨haQ, hq2c.down _ hbQ _ (hqc.subset _ haQ) hlt⟩, haX⟩
  · exact ⟨a, (mem_inter_iff a q q2).mpr ⟨haQ, heq ▸ hbQ⟩, haX⟩
  · exact ⟨b, (mem_inter_iff b q q2).mpr ⟨hqc.down _ haQ _ (hq2c.subset _ hbQ) hgt, hbQ⟩, hbX⟩

def realInterval (p q : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun x => realLt p x ∧ realLt x q) Real.{u}

theorem mem_realInterval_iff (p q x : ZFSet.{u}) :
    x ∈ realInterval p q ↔ x ∈ Real.{u} ∧ realLt p x ∧ realLt x q := mem_sep_iff _ _ _

/-- The order topology: open means every point has an interval around it. -/
def realOpens : ZFSet.{u} :=
  sep (fun U => ∀ x, x ∈ U → ∃ p, p ∈ Real.{u} ∧ ∃ q, q ∈ Real.{u} ∧
    realLt p x ∧ realLt x q ∧ realInterval p q ⊆ U) (powerset Real.{u})

theorem mem_realOpens_iff (U : ZFSet.{u}) :
    U ∈ realOpens.{u} ↔ U ⊆ Real.{u} ∧ ∀ x, x ∈ U → ∃ p, p ∈ Real.{u} ∧ ∃ q, q ∈ Real.{u} ∧
      realLt p x ∧ realLt x q ∧ realInterval p q ⊆ U :=
  Iff.trans (mem_sep_iff _ _ _) ⟨fun h => ⟨(mem_powerset_iff _ _).mp h.left, h.right⟩,
    fun h => ⟨(mem_powerset_iff _ _).mpr h.left, h.right⟩⟩

/-- The order topology on ℝ is a topology, constructively. -/
theorem isTopology_realOpens : IsTopology realOpens.{u} Real.{u} where
  opens_sub U hU := (mem_realOpens_iff U).mp hU |>.left
  mem_empty := (mem_realOpens_iff _).mpr ⟨empty_subset _, fun x hx => absurd hx (not_mem_empty x)⟩
  mem_univ := (mem_realOpens_iff _).mpr ⟨fun w hw => hw, fun x hx => by
    obtain ⟨⟨p, hp, hpx⟩, q, hq, hxq⟩ := exists_realLt_around hx
    exact ⟨p, hp, q, hq, hpx, hxq, fun w hw => (mem_realInterval_iff p q w).mp hw |>.left⟩⟩
  inter_closed U hU V hV := by
    obtain ⟨hUsub, hUopen⟩ := (mem_realOpens_iff U).mp hU
    obtain ⟨hVsub, hVopen⟩ := (mem_realOpens_iff V).mp hV
    refine (mem_realOpens_iff _).mpr ⟨fun w hw => hUsub _ ((mem_inter_iff w U V).mp hw).left,
      fun x hx => ?_⟩
    obtain ⟨hxU, hxV⟩ := (mem_inter_iff x U V).mp hx
    obtain ⟨p1, hp1, q1, hq1, hp1x, hxq1, hsub1⟩ := hUopen x hxU
    obtain ⟨p2, hp2, q2, hq2, hp2x, hxq2, hsub2⟩ := hVopen x hxV
    have hxR : x ∈ Real.{u} := hUsub _ hxU
    refine ⟨realMax p1 p2, realMax_mem_Real hp1 hp2, realMin q1 q2,
      realMin_mem_Real hq1 hq2, realLt_realMax hp1 hp2 hxR hp1x hp2x,
      realLt_realMin hq1 hq2 hxq1 hxq2, fun w hw => ?_⟩
    obtain ⟨hwR, hlo, hhi⟩ := (mem_realInterval_iff _ _ w).mp hw
    obtain ⟨a, haw, hamax⟩ := hlo
    obtain ⟨b, hbmin, hbw⟩ := hhi
    refine (mem_inter_iff w U V).mpr ⟨hsub1 _ ((mem_realInterval_iff _ _ w).mpr ⟨hwR,
      ⟨a, haw, fun hmem => hamax ((mem_union_iff a p1 p2).mpr (Or.inl hmem))⟩,
      ⟨b, ((mem_inter_iff b q1 q2).mp hbmin).left, hbw⟩⟩),
      hsub2 _ ((mem_realInterval_iff _ _ w).mpr ⟨hwR,
      ⟨a, haw, fun hmem => hamax ((mem_union_iff a p1 p2).mpr (Or.inr hmem))⟩,
      ⟨b, ((mem_inter_iff b q1 q2).mp hbmin).right, hbw⟩⟩)⟩
  union_closed F hF := by
    refine (mem_realOpens_iff _).mpr ⟨fun w hw => ?_, fun x hx => ?_⟩
    · obtain ⟨U, hU, hwU⟩ := (mem_sUnion_iff w F).mp hw
      exact ((mem_realOpens_iff U).mp (hF U hU)).left _ hwU
    · obtain ⟨U, hU, hxU⟩ := (mem_sUnion_iff x F).mp hx
      obtain ⟨p, hp, q, hq, hpx, hxq, hsub⟩ := ((mem_realOpens_iff U).mp (hF U hU)).right x hxU
      exact ⟨p, hp, q, hq, hpx, hxq, fun w hw =>
        (mem_sUnion_iff w F).mpr ⟨U, hU, hsub _ hw⟩⟩

/-! ## Audit -/

#print axioms isTopology_realOpens
/-- The order topology: generated by the rays, with endpoints in the SPACE.

Mathlib's `OrderTopology`, and NOT what `Topology.realLOpens` is --- measured: that
one's basic opens have RATIONAL endpoints, so it is the order topology
presented through a dense subset, with second countability baked in. The two
agreeing on `RealL` is a THEOREM about density (`exists_rat_bracket`), not an
unfolding, and rung 11 owes it.

A `Prop` about a topology `T` rather than a construction of one: building the
generated topology needs an arbitrary intersection of topologies, and this
tree's `IsTopology` is closed under FINITE intersection only --- the same wall
`isClosed_inter_of_detachable` names one level down. Characterising is enough
for every use above, and it costs no decision. -/
def IsOrderTopology (T X lt : ZFSet.{u}) : Prop :=
  IsTopology T X ∧
    (∀ a, a ∈ X → sep (fun x => opair a x ∈ lt) X ∈ T) ∧
    (∀ b, b ∈ X → sep (fun x => opair x b ∈ lt) X ∈ T) ∧
    ∀ U, U ∈ T → ∀ x, x ∈ U →
      ∃ a, ∃ b, (a ∈ X ∧ opair a x ∈ lt ∨ a = x) ∧
                (b ∈ X ∧ opair x b ∈ lt ∨ b = x) ∧
        sep (fun w => (opair a w ∈ lt ∨ a = w) ∧ (opair w b ∈ lt ∨ w = b)) X ⊆ U

/-- Conditional completeness: every inhabited, bounded-above subset has a
least upper bound IN the carrier.

Mathlib's `ConditionallyCompleteLinearOrder`, and the hypothesis its EVT and
IVT both carry. Stated with the supremum EXISTENTIAL rather than as a function,
a `sSup` operator would have to return something for the empty and unbounded
cases, and every such choice is a decision about a set the order cannot see
into.

`RealL` will not satisfy this in the naive form. A located real has no
decidable order, so `∃ s, IsLUB s` for an arbitrary subset is exactly the shape
that fails --- the tree's `Analysis.rangeSup` is a supremum of a LOCATED FAMILY,
built from the family's own approximants, and that is the instance to expect.
Rung 12 must take the located form as its hypothesis or it will have a
definition nothing here satisfies. -/
def IsConditionallyComplete (X lt : ZFSet.{u}) : Prop :=
  ∀ S, S ⊆ X → (∃ a, a ∈ S) →
    (∃ b, b ∈ X ∧ ∀ x, x ∈ S → opair b x ∉ lt) →
      ∃ s, s ∈ X ∧ (∀ x, x ∈ S → opair s x ∉ lt) ∧
        ∀ u, u ∈ X → (∀ x, x ∈ S → opair u x ∉ lt) → opair u s ∉ lt

/-- Below a supremum there is a member of the set, under `EM`.

THE LEAST-UPPER-BOUND CLAUSE IS STATED NEGATIVELY --- *no `u` bounding `S` has
`u < s`* --- so instantiating it at a `u < s` yields `¬ (∀ x ∈ S, ¬ (u < x))`, a
double negation. Turning that into a WITNESS is the step constructive
mathematics refuses, and it is the whole content of this lemma.

STATED OVER ANY `X` AND `lt`, because nothing here is about reals: it is the
third clause read contrapositively. `hleast` is that clause verbatim, so a
caller holding a supremum from `IsConditionallyComplete` can pass its third
component unchanged.
-/
theorem exists_mem_of_lt_sup (hem : Constructive.EM) {X lt S s u : ZFSet.{u}}
    (hu : u ∈ X)
    (hleast : ∀ v, v ∈ X → (∀ x, x ∈ S → opair v x ∉ lt) → opair v s ∉ lt)
    (hu_lt : opair u s ∈ lt) :
    ∃ x, x ∈ S ∧ opair u x ∈ lt := by
  rcases hem (∃ x, x ∈ S ∧ opair u x ∈ lt) with h | h
  · exact h
  · exact absurd hu_lt (hleast u hu (fun x hx hlt => h ⟨x, hx, hlt⟩))

/-- A subset LOCATED in the order: between any two points of the carrier,
either the subset reaches above the lower one, or it stays below the upper one.

The repair `Topology.IsConditionallyComplete` needs, and the point of stating
it here is that it needs NOTHING but the order. Locatedness is usually phrased
with rational approximants, which `Analysis.rangeSup` is built from, and a
general carrier has no approximants to phrase it with. Read as a straddling
condition on a PAIR of carrier points it becomes order-theoretic, and the
metric statement is the instance where the pair is a pair of rationals.

The disjunction is genuine information: a located real supplies it and an
arbitrary subset of the reals does not.
`Metamath.wlpo_of_conditionally_complete` builds the subset `{0}` together with
`1` if a Boolean sequence fires, and locatedness at the pair `(0, 1)` for THAT
subset is precisely the decision the sequence withholds --- so the
counterexample to the naive predicate is refuted by this hypothesis rather than
dodged by it.

Not itself conditional completeness: this is the hypothesis on the subset,
carried alongside inhabitedness and boundedness. -/
def IsLocatedSubset (X lt S : ZFSet.{u}) : Prop :=
  ∀ u v, u ∈ X → v ∈ X → opair u v ∈ lt →
    (∃ x, x ∈ S ∧ opair u x ∈ lt) ∨ (∀ x, x ∈ S → opair v x ∉ lt)

/-- Conditional completeness for LOCATED subsets, which is the form a
carrier without a decidable order can satisfy.

`Topology.IsConditionallyComplete` asks every inhabited bounded-above subset for a
least upper bound, and `Metamath.wlpo_of_conditionally_complete` shows that costs
`WLPO`. The only change here is `Topology.IsLocatedSubset` on the subset, which is
exactly what that counterexample lacks.

Weaker as a HYPOTHESIS on the carrier, so a descent proved from it measures
more, and every subset a located real actually presents --- the range of a
uniformly continuous function on a closed interval, which is what
`Analysis.rangeSup` sums up --- meets it. -/
def IsConditionallyCompleteLocated (X lt : ZFSet.{u}) : Prop :=
  ∀ S, S ⊆ X → (∃ a, a ∈ S) → IsLocatedSubset X lt S →
    (∃ b, b ∈ X ∧ ∀ x, x ∈ S → opair b x ∉ lt) →
      ∃ s, s ∈ X ∧ (∀ x, x ∈ S → opair s x ∉ lt) ∧
        ∀ u, u ∈ X → (∀ x, x ∈ S → opair u x ∉ lt) → opair u s ∉ lt

/-- The naive form implies the located one, by dropping the extra
hypothesis. Both are stated because the ordering matters: a descent from
`Topology.IsConditionallyCompleteLocated` is a stronger result than the same
descent from `Topology.IsConditionallyComplete`. -/
theorem isConditionallyCompleteLocated_of_isConditionallyComplete
    {X lt : ZFSet.{u}} (h : IsConditionallyComplete X lt) :
    IsConditionallyCompleteLocated X lt :=
  fun S hsub hne _ hbdd => h S hsub hne hbdd

/-- A strict order, as a set of pairs.

`Topology.IsOrderTopology` and `Topology.IsConditionallyComplete` take `lt` as an
ARBITRARY relation, and that turned out to be a defect rather than a
generalisation: mathlib's extreme value theorem is over a
`ConditionallyCompleteLinearOrder`, and dropping the order axioms makes the
theorem FALSE.

The refutation is one point. Take `Y = K = {a}` and `lt = {(a,a)}`, with the
indiscrete topology and the identity map. Both rays are `Y`, so the order
topology clauses hold; NOTHING is bounded above, because the only candidate
bound `a` satisfies `(a,a) ∈ lt`, so conditional completeness holds VACUOUSLY;
a singleton is compact. Every hypothesis is met and the conclusion asks for
`(a,a) ∉ lt`, which is false.

Irreflexivity is what that example violates and transitivity is what the finite
subcover argument needs, so those are the two clauses. Linearity is NOT
required here: the proof compares only elements the cover already relates. -/
def IsStrictOrderOn (X lt : ZFSet.{u}) : Prop :=
  (∀ x, x ∈ X → opair x x ∉ lt) ∧
    ∀ x, x ∈ X → ∀ y, y ∈ X → ∀ z, z ∈ X →
      opair x y ∈ lt → opair y z ∈ lt → opair x z ∈ lt

/-- Excluded middle locates every subset of a strict order.

`Topology.IsLocatedSubset` is a DISJUNCTION of two `Prop`s, so `EM` decides it
outright --- but only the left branch comes for free. The right one, *`S` stays
below `v`*, does NOT follow from the negation on its own: `¬ ∃ x ∈ S, u < x`
says nothing about `v` until transitivity carries `u < v < x` back to `u < x`.
That is the only use of `hso`, and it is why this is not `hem` applied to the
definition.
-/
theorem isLocatedSubset_of_em (hem : Constructive.EM) {X lt S : ZFSet.{u}}
    (hS : S ⊆ X) (hso : IsStrictOrderOn X lt) :
    IsLocatedSubset X lt S := by
  intro u v hu hv huv
  rcases hem (∃ x, x ∈ S ∧ opair u x ∈ lt) with h | h
  · exact Or.inl h
  · exact Or.inr (fun x hx hvx =>
      h ⟨x, hx, hso.right u hu v hv x (hS x hx) huv hvx⟩)

/-- Under `EM` the located completeness gives the naive one, which is
`Topology.isConditionallyCompleteLocated_of_isConditionallyComplete` run
backwards at the price of excluded middle.

The extra hypothesis the located form carries is DISCHARGED rather than
assumed, so the two predicates coincide classically and the whole distance
between them is that one disjunction.
-/
theorem isConditionallyComplete_of_located_of_em (hem : Constructive.EM)
    {X lt : ZFSet.{u}} (hso : IsStrictOrderOn X lt)
    (h : IsConditionallyCompleteLocated X lt) :
    IsConditionallyComplete X lt :=
  fun S hsub hne hbdd => h S hsub hne (isLocatedSubset_of_em hem hsub hso) hbdd

#print axioms mem_subspaceOpens_iff
#print axioms isTopology_subspaceOpens
#print axioms mem_preimageIn_iff
#print axioms realMax_mem_Real
#print axioms realMin_mem_Real
#print axioms exists_realLt_around
#print axioms realLt_realMax
#print axioms realLt_realMin
#print axioms mem_realInterval_iff
#print axioms mem_realOpens_iff
end Topology
#print axioms Topology.isClosed_union
#print axioms Topology.isClosed_inter_of_detachable
#print axioms Topology.IsCompact
#print axioms Topology.CoverData
#print axioms Topology.IsStrictOrderOn
#print axioms Topology.IsOrderTopology
#print axioms Topology.IsConditionallyComplete
#print axioms Topology.IsLocatedSubset
#print axioms Topology.IsConditionallyCompleteLocated
#print axioms Topology.isConditionallyCompleteLocated_of_isConditionallyComplete
#print axioms Topology.exists_mem_of_lt_sup
#print axioms Topology.isLocatedSubset_of_em
#print axioms Topology.isConditionallyComplete_of_located_of_em
namespace ZFSet
export Topology (CoverData IsClosed IsCompact IsConditionallyComplete IsConditionallyCompleteLocated IsContinuous IsLocatedSubset IsOrderTopology IsStrictOrderOn IsTopology exists_mem_of_lt_sup exists_realLt_around isClosed_inter_of_detachable isClosed_union isConditionallyCompleteLocated_of_isConditionallyComplete isConditionallyComplete_of_located_of_em isLocatedSubset_of_em isTopology_realOpens isTopology_subspaceOpens mem_preimageIn_iff mem_realInterval_iff mem_realOpens_iff mem_subspaceOpens_iff preimageIn realInterval realLt realLt_realMax realLt_realMin realMax realMax_mem_Real realMin realMin_mem_Real realOpens spec subspaceOpens)
end ZFSet
