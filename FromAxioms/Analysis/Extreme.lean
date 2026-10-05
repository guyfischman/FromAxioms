/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The extreme value theorem, in halves

The approximate maximum is free (Bishop): sample the function on a
rational grid, read each sample to a rational bracket, and carry the
best bracket through a decidable comparison -- uniform continuity
spreads the grid's reach to the whole interval. The exact maximum is
not free: `llpo_of_max_attainment` is the lower bound, and the converse
climb from the principles is this file's other half.
-/

import FromAxioms.Algebra.Ring
import FromAxioms.Core.NatPair
import FromAxioms.Metamath.Calibrate

set_option autoImplicit false

universe u

open Algebra Constructive Metamath NumberTheory SetTheory Topology
namespace Analysis


/-! ## The exact maximum, from the principles

The converse climb. The payload the halving machine carries is "the
global supremum is still the supremum here"; the sign disjunction
compares the two halves' suprema and keeps the larger, and it also
sends every point of the parent interval into one half, so the parent's
supremum never exceeds the larger half's. At the limit, uniform
continuity pins `F` to the supremum. With `llpo_of_max_attainment` this
closes the third sandwich:

    LLPO  ≤  MaxAttainment01  ≤  LLPO + BinaryDC + DC -/


/-- The order-theoretic locatedness of `Topology.IsLocatedSubset` is
`Analysis.FamilyLocated`, which is the cut-level condition the supremum
construction actually consumes.

The two differ in one place. `FamilyLocated` asks, for rationals `p < q`, that
some member's lower cut hold `p` or that every member's upper cut hold `q` ---
both strict. `IsLocatedSubset` gives the right-hand side only as `¬ (v < x)`, a
`≤`, because that is the only spelling available when the carrier is a bare
order with no cuts to speak of. A rational strictly between supplies the
missing gap: locate at `(p, m)` with `p < m < q`, and `x ≤ m < q` is `x < q`.
Density of the rationals is doing the work, through `Analysis.realLLt_cotrans`
rather than through any decision. -/
theorem familyLocated_of_isLocatedSubset {S : ZFSet.{u}}
    (hS : S ⊆ RealL.{u}) (hloc : IsLocatedSubset RealL.{u} realLLtRel.{u} S) :
    FamilyLocated S := by
  intro p hp q hq hpq
  obtain ⟨m, hmQ, hpm, hmq⟩ :=
    exists_rat_between (realLOf_mem hp) (realLOf_mem hq)
      ((realLOf_lt_realLOf hp hq).mpr hpq)
  rcases hloc (realLOf p) (realLOf m) (realLOf_mem hp) (realLOf_mem hmQ)
      ((opair_mem_realLLtRel_iff (realLOf_mem hp) (realLOf_mem hmQ)).mpr hpm)
    with ⟨x, hxS, hxlt⟩ | hright
  · obtain ⟨L, U, heq, -⟩ := (mem_RealL_iff x).mp (hS x hxS)
    refine Or.inl ⟨x, hxS, L, U, heq, ?_⟩
    have hL := (realLOf_lt_iff_mem_lower (hS x hxS) hp).mp
      ((opair_mem_realLLtRel_iff (realLOf_mem hp) (hS x hxS)).mp hxlt)
    rw [heq, fst_opair] at hL
    exact hL
  · refine Or.inr (fun z hz L U heq => ?_)
    have hzR := hS z hz
    have hzq : realLLt z (realLOf q) := by
      rcases realLLt_cotrans (realLOf_mem hmQ) (realLOf_mem hq) hzR hmq with h | h
      · exact absurd ((opair_mem_realLLtRel_iff (realLOf_mem hmQ) hzR).mpr h)
          (hright z hz)
      · exact h
    have hU := (lt_realLOf_iff_mem_upper hzR hq).mp hzq
    rw [heq, snd_opair] at hU
    exact hU

/-- The located reals are strictly ordered, which is what the max-attainment
predicates ask of their order.

Irreflexivity and transitivity of `realLLt`, read through
`opair_mem_realLLtRel_iff` because `IsStrictOrderOn` quantifies over the
reified relation rather than the proposition. `Topology.MaxAttainmentTop` and
`Topology.MaxAttainmentTopLocated` both take `IsStrictOrderOn Y lt`, which this
supplies. Open-cover `IsCompact` for `[0, 1]` is the fan-theorem step their
docstrings name, and `IsConditionallyCompleteLocated` is below.
-/
theorem isStrictOrderOn_realLLtRel : IsStrictOrderOn RealL.{u} realLLtRel.{u} := by
  refine ⟨fun x hx hmem => ?_, fun x hx y hy z hz hxy hyz => ?_⟩
  · exact realLLt_irrefl hx ((opair_mem_realLLtRel_iff hx hx).mp hmem)
  · exact (opair_mem_realLLtRel_iff hx hz).mpr
      (realLLt_trans hx hy hz ((opair_mem_realLLtRel_iff hx hy).mp hxy)
        ((opair_mem_realLLtRel_iff hy hz).mp hyz))

/-- `RealL` satisfies conditional completeness for located subsets.

The naive form, `Topology.IsConditionallyComplete RealL realLLtRel`, is priced
at `WLPO` by `Metamath.wlpo_of_conditionally_complete`, because a located real
admits no decidable order. Restricted to located subsets the principle is a
theorem here, at `[propext, Quot.sound]` and no principle at all.

`Analysis.supLower` and `Analysis.supUpper` are defined over an arbitrary set
of located reals, `Analysis.isLocated_sup_of_familyLocated` produces the
supremum from `FamilyLocated`, and `Analysis.le_sup_realLLe` and
`Analysis.sup_realLLe_of_forall_le` give the two bound directions; the
order-level locatedness a general carrier can state is exactly the cut-level
locatedness those consume.

The bound is converted once, from a real upper bound to a rational one, because
`FamilyLocated`'s consumers work at the cuts: `Analysis.exists_rat_bracket` puts a
rational above the bound and cotransitivity carries every member under it. -/
theorem isConditionallyCompleteLocated_realL :
    IsConditionallyCompleteLocated RealL.{u} realLLtRel.{u} := by
  intro S hS hne hloc hbdd
  obtain ⟨b, hbR, hbub⟩ := hbdd
  obtain ⟨p₀, r, hp₀Q, hrQ, hp₀b, hbr, -⟩ :=
    exists_rat_bracket hbR ratOne_mem_Rat ratZero_lt_one
  have hbdR : ∃ r, r ∈ NumberTheory.Rat.{u} ∧ ∀ z, z ∈ S → ∀ L U, z = opair L U → r ∈ U := by
    refine ⟨r, hrQ, fun z hz L U heq => ?_⟩
    have hzR := hS z hz
    have hzr : realLLt z (realLOf r) := by
      rcases realLLt_cotrans hbR (realLOf_mem hrQ) hzR hbr with h | h
      · exact absurd ((opair_mem_realLLtRel_iff hbR hzR).mpr h) (hbub z hz)
      · exact h
    have hU := (lt_realLOf_iff_mem_upper hzR hrQ).mp hzr
    rw [heq, snd_opair] at hU
    exact hU
  have hsupR : opair (supLower S) (supUpper S) ∈ RealL.{u} :=
    (mem_RealL_iff _).mpr ⟨_, _, rfl,
      isLocated_sup_of_familyLocated hS hne hbdR
        (familyLocated_of_isLocatedSubset hS hloc)⟩
  refine ⟨opair (supLower S) (supUpper S), hsupR, fun x hx hlt => ?_,
    fun u huR hubu hlt => ?_⟩
  · obtain ⟨L, U, heq, hlocx⟩ := (mem_RealL_iff x).mp (hS x hx)
    exact le_sup_realLLe hx heq hlocx
      ((opair_mem_realLLtRel_iff hsupR (hS x hx)).mp hlt)
  · exact sup_realLLe_of_forall_le
      (fun z hz hcon =>
        hubu z hz ((opair_mem_realLLtRel_iff huR (hS z hz)).mpr hcon))
      ((opair_mem_realLLtRel_iff huR hsupR).mp hlt)

/-- The naive supremum property for the located reals, priced at `EM`.

`Topology.IsConditionallyComplete RealL realLLtRel` is carried as a hypothesis
across this tree --- `Metamath.maxAttainment01_of_top` and
`Metamath.llpo_of_max_attainment_top` both take it as `hsup`. A located real
admits no decidable order, so the located form beside this one exists.
`Metamath.llpo_of_conditionally_complete` derives `LLPO` from it; this closes
the bracket from above, `LLPO <= IsConditionallyComplete RealL <= EM`, by
composing `Analysis.isStrictOrderOn_realLLtRel`,
`Analysis.isConditionallyCompleteLocated_realL` and
`Topology.isConditionallyComplete_of_located_of_em`.
-/
theorem isConditionallyComplete_realL_of_em (hem : Constructive.EM) :
    IsConditionallyComplete RealL.{u} realLLtRel.{u} :=
  Topology.isConditionallyComplete_of_located_of_em hem
    isStrictOrderOn_realLLtRel isConditionallyCompleteLocated_realL

/-- Every inhabited subset of `[p,q]` has a supremum, under `EM`.

The bound is `realLOf q` and it needs nothing but membership in the interval:
`mem_realLIcc_iff` gives `x <= realLOf q` as `¬ realLOf q < x` directly, which
is the shape `IsConditionallyComplete` asks for.

`p ∈ Rat` is not taken: the left endpoint never enters, so this applies to a
set sitting in an interval whose left endpoint is any set at all.
-/
theorem exists_sup_of_subset_realLIcc_of_em (hem : Constructive.EM)
    {p q S : ZFSet.{u}} (hq : q ∈ NumberTheory.Rat.{u})
    (hS : S ⊆ realLIcc p q) (hne : ∃ a, a ∈ S) :
    ∃ s, s ∈ RealL.{u} ∧
      (∀ x, x ∈ S → opair s x ∉ realLLtRel.{u}) ∧
      ∀ u, u ∈ RealL.{u} → (∀ x, x ∈ S → opair u x ∉ realLLtRel.{u}) →
        opair u s ∉ realLLtRel.{u} := by
  have hmem : ∀ x, x ∈ S → x ∈ RealL.{u} := fun x hx =>
    ((mem_realLIcc_iff p q x).mp (hS x hx)).left
  refine isConditionallyComplete_realL_of_em hem S hmem hne
    ⟨realLOf q, realLOf_mem hq, fun x hx hlt => ?_⟩
  exact ((mem_realLIcc_iff p q x).mp (hS x hx)).right.right
    ((opair_mem_realLLtRel_iff (realLOf_mem hq) (hmem x hx)).mp hlt)

/-- Below a supremum there is a member, over the located reals.

`Topology.exists_mem_of_lt_sup` at `RealL`, with `realLLt` in and `realLLt`
out. The two `opair_mem_realLLtRel_iff` rewrites are absorbed here.
-/
theorem exists_mem_realLLt_of_lt_sup (hem : Constructive.EM) {S s u : ZFSet.{u}}
    (hu : u ∈ RealL.{u}) (hs : s ∈ RealL.{u})
    (hSmem : ∀ x, x ∈ S → x ∈ RealL.{u})
    (hleast : ∀ v, v ∈ RealL.{u} → (∀ x, x ∈ S → opair v x ∉ realLLtRel.{u}) →
      opair v s ∉ realLLtRel.{u})
    (hu_lt : realLLt u s) :
    ∃ x, x ∈ S ∧ realLLt u x := by
  obtain ⟨x, hx, hlt⟩ := Topology.exists_mem_of_lt_sup hem hu hleast
    ((opair_mem_realLLtRel_iff hu hs).mpr hu_lt)
  exact ⟨x, hx, (opair_mem_realLLtRel_iff hu (hSmem x hx)).mp hlt⟩

/-- A rational strictly between `s` and two reals above it.

`exists_rat_between` gives one for each bound separately; the `EM` here picks
whichever is smaller, because rational order is not decidable in this tree, so
that choice is a decision and not a computation.
-/
theorem exists_rat_between_two (hem : Constructive.EM) {s a b : ZFSet.{u}}
    (hs : s ∈ RealL.{u}) (ha : a ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (hsa : realLLt s a) (hsb : realLLt s b) :
    ∃ r, r ∈ NumberTheory.Rat.{u} ∧ realLLt s (realLOf r) ∧
      realLLt (realLOf r) a ∧ realLLt (realLOf r) b := by
  obtain ⟨r₁, hr₁, hsr₁, hr₁a⟩ := exists_rat_between hs ha hsa
  obtain ⟨r₂, hr₂, hsr₂, hr₂b⟩ := exists_rat_between hs hb hsb
  rcases hem (realLLt (realLOf r₁) (realLOf r₂)) with h | h
  · exact ⟨r₁, hr₁, hsr₁, hr₁a, realLLt_trans (realLOf_mem hr₁)
      (realLOf_mem hr₂) hb h hr₂b⟩
  · refine ⟨r₂, hr₂, hsr₂, ?_, hr₂b⟩
    rcases realLLt_cotrans (realLOf_mem hr₁) ha (realLOf_mem hr₂) hr₁a with h' | h'
    · exact absurd h' h
    · exact h'

/-!
### The classical intermediate value theorem, priced at `EM`

The constructive routes to `ExactIVT01` bisect, and a bisection needs its
sequence, so each carries a choice principle ---
`SignDisjunction + BinaryDCOn`, `SignDisjunction + DC`,
`LLPO + BinaryDC + BinaryDCOn`, `LLPO + BinaryDC + DC`. The classical route
takes the supremum of `{x in [0,1] : G x <= 0}` instead, which
`Analysis.isConditionallyComplete_realL_of_em` prices.

Where the `EM` goes --- four uses, not interchangeable: the supremum's
existence; turning the least-upper-bound clause, stated negatively, into a
witness (`Topology.exists_mem_of_lt_sup`); `s < realLOf 1`, before a point
above `s` can be found inside `[0,1]`; and choosing the smaller of two rational
candidates, since rational order is not decidable here.

What is not spent on it is the step that looks most classical: `x <= s` with
`s < realLOf q` gives `x < realLOf q` by cotransitivity.
-/

/-- A real lies in the positive ray of the order topology if and only if it is
positive. -/
theorem mem_posRay_iff {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    x ∈ sep (fun z => opair realLZero.{u} z ∈ realLLtRel.{u}) RealL.{u}
      ↔ realLLt realLZero.{u} x := by
  refine Iff.trans (mem_sep_iff _ _ _) ⟨fun h => ?_, fun h => ⟨hx, ?_⟩⟩
  · exact (opair_mem_realLLtRel_iff realLZero_mem hx).mp h.right
  · exact (opair_mem_realLLtRel_iff realLZero_mem hx).mpr h


/-- The value of `G` at the supremum of `S` is not strictly positive. -/
theorem not_realLZero_lt_G_sup (hem : EM) {G : ZFSet.{u} → ZFSet.{u}}
    {S s : ZFSet.{u}}
    (hGmaps : ∀ x, x ∈ realLIcc ratZero.{u} ratOne.{u} → G x ∈ RealL.{u})
    (hcont : IsContinuous
      (graphOn (realLIcc ratZero.{u} ratOne.{u}) RealL.{u} G)
      (realLIcc ratZero.{u} ratOne.{u}) RealL.{u}
      (subspaceOpens realLOpens.{u} (realLIcc ratZero.{u} ratOne.{u}))
      realLOpens.{u})
    (hSsub : ∀ x, x ∈ S → x ∈ realLIcc ratZero.{u} ratOne.{u})
    (hSle : ∀ x, x ∈ S → ¬ realLLt realLZero.{u} (G x))
    (hs_mem : s ∈ realLIcc ratZero.{u} ratOne.{u})
    (hub : ∀ x, x ∈ S → ¬ realLLt s x)
    (hleast : ∀ v, v ∈ RealL.{u} → (∀ x, x ∈ S → opair v x ∉ realLLtRel.{u}) →
      opair v s ∉ realLLtRel.{u}) :
    ¬ realLLt realLZero.{u} (G s) := by
  intro hpos
  have hsR : s ∈ RealL.{u} :=
    ((mem_realLIcc_iff _ _ s).mp hs_mem).left
  have hSmem : ∀ x, x ∈ S → x ∈ RealL.{u} := fun x hx =>
    ((mem_realLIcc_iff _ _ x).mp (hSsub x hx)).left
  -- the positive ray is open, so its preimage is open in the subspace
  have hray : sep (fun z => opair realLZero.{u} z ∈ realLLtRel.{u}) RealL.{u}
      ∈ realLOpens.{u} :=
    isOrderTopology_realLOpens.right.left realLZero.{u} realLZero_mem
  have hP := hcont.right.right.right _ hray
  obtain ⟨-, U, hU, hPU⟩ := (mem_subspaceOpens_iff _ _ _).mp hP
  -- `s` lies in it, because `G s` is positive
  have hsP : s ∈ preimageIn
      (graphOn (realLIcc ratZero.{u} ratOne.{u}) RealL.{u} G)
      (realLIcc ratZero.{u} ratOne.{u})
      (sep (fun z => opair realLZero.{u} z ∈ realLLtRel.{u}) RealL.{u}) := by
    refine (mem_preimageIn_iff _ _ _ _).mpr ⟨hs_mem, ?_⟩
    rw [app_graphOn hGmaps hs_mem]
    exact (mem_posRay_iff (hGmaps s hs_mem)).mpr hpos
  have hsU : s ∈ U := by
    have := hPU ▸ hsP
    exact ((mem_inter_iff s U (realLIcc ratZero.{u} ratOne.{u})).mp this).left
  -- the concrete bracket: rationals strictly either side
  obtain ⟨p, hp, q, hq, hps, hsq, hIoo⟩ :=
    ((mem_realLOpens_iff U).mp hU).right s hsU
  -- a member of `S` above `realLOf p`
  obtain ⟨x, hxS, hpx⟩ := exists_mem_realLLt_of_lt_sup hem
    (realLOf_mem hp) hsR hSmem hleast hps
  have hxR : x ∈ RealL.{u} := hSmem x hxS
  -- `x <= s < realLOf q` gives `x < realLOf q` by cotransitivity
  have hxq : realLLt x (realLOf q) := by
    rcases realLLt_cotrans hsR (realLOf_mem hq) hxR hsq with h | h
    · exact absurd h (hub x hxS)
    · exact h
  -- so `x` is in the bracket, hence in `U`, hence in the preimage
  have hxU : x ∈ U := hIoo x ((mem_realLIoo_iff p q x).mpr ⟨hxR, hpx, hxq⟩)
  have hxP : x ∈ preimageIn
      (graphOn (realLIcc ratZero.{u} ratOne.{u}) RealL.{u} G)
      (realLIcc ratZero.{u} ratOne.{u})
      (sep (fun z => opair realLZero.{u} z ∈ realLLtRel.{u}) RealL.{u}) := by
    rw [hPU]
    exact (mem_inter_iff x U (realLIcc ratZero.{u} ratOne.{u})).mpr ⟨hxU, hSsub x hxS⟩
  -- and there `G` is positive, which `S` forbids
  have hGx := ((mem_preimageIn_iff _ _ _ _).mp hxP).right
  rw [app_graphOn hGmaps (hSsub x hxS)] at hGx
  exact hSle x hxS ((mem_posRay_iff (hGmaps x (hSsub x hxS))).mp hGx)


/-- A real lies in the negative ray of the order topology if and only if it is
negative. -/
theorem mem_negRay_iff {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    x ∈ sep (fun z => opair z realLZero.{u} ∈ realLLtRel.{u}) RealL.{u}
      ↔ realLLt x realLZero.{u} := by
  refine Iff.trans (mem_sep_iff _ _ _) ⟨fun h => ?_, fun h => ⟨hx, ?_⟩⟩
  · exact (opair_mem_realLLtRel_iff hx realLZero_mem).mp h.right
  · exact (opair_mem_realLLtRel_iff hx realLZero_mem).mpr h


theorem not_G_sup_lt_realLZero (hem : EM) {G : ZFSet.{u} → ZFSet.{u}}
    {S s : ZFSet.{u}}
    (hGmaps : ∀ x, x ∈ realLIcc ratZero.{u} ratOne.{u} → G x ∈ RealL.{u})
    (hcont : IsContinuous
      (graphOn (realLIcc ratZero.{u} ratOne.{u}) RealL.{u} G)
      (realLIcc ratZero.{u} ratOne.{u}) RealL.{u}
      (subspaceOpens realLOpens.{u} (realLIcc ratZero.{u} ratOne.{u}))
      realLOpens.{u})
    (hhi : realLLt realLZero.{u} (G (realLOf ratOne.{u})))
    (hSdef : ∀ x, x ∈ realLIcc ratZero.{u} ratOne.{u} →
      realLLt (G x) realLZero.{u} → x ∈ S)
    (hs_mem : s ∈ realLIcc ratZero.{u} ratOne.{u})
    (hub : ∀ x, x ∈ S → ¬ realLLt s x) :
    ¬ realLLt (G s) realLZero.{u} := by
  intro hneg
  have hsR : s ∈ RealL.{u} := ((mem_realLIcc_iff _ _ s).mp hs_mem).left
  have hs1 : realLLe s (realLOf ratOne.{u}) :=
    ((mem_realLIcc_iff _ _ s).mp hs_mem).right.right
  -- `s` is strictly below `1`, because at `1` the value is positive
  have hslt1 : realLLt s (realLOf ratOne.{u}) := by
    rcases hem (realLLt s (realLOf ratOne.{u})) with h | h
    · exact h
    · exfalso
      have : s = realLOf ratOne.{u} :=
        realLLe_antisymm hsR (realLOf_mem ratOne_mem_Rat) hs1 h
      rw [this] at hneg
      exact realLLt_irrefl (hGmaps _ (right_mem_realLIcc ratZero_mem_Rat
        ratOne_mem_Rat (ratLe_of_lt ratZero_mem_Rat ratOne_mem_Rat
          ratZero_lt_one)))
        (realLLt_trans (hGmaps _ (right_mem_realLIcc ratZero_mem_Rat
          ratOne_mem_Rat (ratLe_of_lt ratZero_mem_Rat ratOne_mem_Rat
            ratZero_lt_one))) realLZero_mem
          (hGmaps _ (right_mem_realLIcc ratZero_mem_Rat ratOne_mem_Rat
            (ratLe_of_lt ratZero_mem_Rat ratOne_mem_Rat ratZero_lt_one)))
          hneg hhi)
  -- the negative ray is open; pull it back
  have hray : sep (fun z => opair z realLZero.{u} ∈ realLLtRel.{u}) RealL.{u}
      ∈ realLOpens.{u} :=
    isOrderTopology_realLOpens.right.right.left realLZero.{u} realLZero_mem
  have hP := hcont.right.right.right _ hray
  obtain ⟨-, U, hU, hPU⟩ := (mem_subspaceOpens_iff _ _ _).mp hP
  have hsP : s ∈ preimageIn
      (graphOn (realLIcc ratZero.{u} ratOne.{u}) RealL.{u} G)
      (realLIcc ratZero.{u} ratOne.{u})
      (sep (fun z => opair z realLZero.{u} ∈ realLLtRel.{u}) RealL.{u}) := by
    refine (mem_preimageIn_iff _ _ _ _).mpr ⟨hs_mem, ?_⟩
    rw [app_graphOn hGmaps hs_mem]
    exact (mem_negRay_iff (hGmaps s hs_mem)).mpr hneg
  have hsU : s ∈ U := by
    have := hPU ▸ hsP
    exact ((mem_inter_iff s U (realLIcc ratZero.{u} ratOne.{u})).mp this).left
  obtain ⟨p, hp, q, hq, hps, hsq, hIoo⟩ :=
    ((mem_realLOpens_iff U).mp hU).right s hsU
  -- a rational above `s`, below `realLOf q`, and below `1`
  obtain ⟨r, hr, hsr, hrq, hr1⟩ := exists_rat_between_two hem hsR
    (realLOf_mem hq) (realLOf_mem ratOne_mem_Rat) hsq hslt1
  have hrR : realLOf r ∈ RealL.{u} := realLOf_mem hr
  -- it lies in `[0,1]`
  have hr_icc : realLOf r ∈ realLIcc ratZero.{u} ratOne.{u} := by
    refine (mem_realLIcc_iff _ _ _).mpr ⟨hrR, fun h => ?_, fun h => ?_⟩
    · exact ((mem_realLIcc_iff _ _ s).mp hs_mem).right.left
        (realLLt_trans hsR hrR (realLOf_mem ratZero_mem_Rat) hsr h)
    · exact realLLt_irrefl hrR (realLLt_trans hrR (realLOf_mem ratOne_mem_Rat)
        hrR hr1 h)
  -- and in `U`, so `G` is negative there, so it belongs to `S`
  have hrU : realLOf r ∈ U := hIoo _ ((mem_realLIoo_iff p q _).mpr
    ⟨hrR, realLLt_trans (realLOf_mem hp) hsR hrR hps hsr, hrq⟩)
  have hrP : realLOf r ∈ preimageIn
      (graphOn (realLIcc ratZero.{u} ratOne.{u}) RealL.{u} G)
      (realLIcc ratZero.{u} ratOne.{u})
      (sep (fun z => opair z realLZero.{u} ∈ realLLtRel.{u}) RealL.{u}) := by
    rw [hPU]
    exact (mem_inter_iff _ U (realLIcc ratZero.{u} ratOne.{u})).mpr
      ⟨hrU, hr_icc⟩
  have hGr := ((mem_preimageIn_iff _ _ _ _).mp hrP).right
  rw [app_graphOn hGmaps hr_icc] at hGr
  exact hub _ (hSdef _ hr_icc ((mem_negRay_iff (hGmaps _ hr_icc)).mp hGr)) hsr


/-- The classical intermediate value theorem, priced at `EM`.

The set is `{x in [0,1] : not (0 < G x)}`, its supremum exists by
`exists_sup_of_subset_realLIcc_of_em`, and the two refutations close both
sides. `realLLe_antisymm` turns neither above nor below into equality ---
which is the step a constructive proof cannot take and is exactly what the
price buys. -/
theorem exactIVT01Top_of_em (hem : EM) : ExactIVT01Top.{u} := by
  intro G hGmaps hcont hlo hhi
  let S : ZFSet.{u} :=
    sep (fun x => ¬ realLLt realLZero.{u} (G x))
      (realLIcc ratZero.{u} ratOne.{u})
  have hSsub : ∀ x, x ∈ S → x ∈ realLIcc ratZero.{u} ratOne.{u} :=
    fun x hx => ((mem_sep_iff _ _ _).mp hx).left
  have hSle : ∀ x, x ∈ S → ¬ realLLt realLZero.{u} (G x) :=
    fun x hx => ((mem_sep_iff _ _ _).mp hx).right
  have hzero_icc : realLOf ratZero.{u} ∈ realLIcc ratZero.{u} ratOne.{u} :=
    left_mem_realLIcc ratZero_mem_Rat ratOne_mem_Rat
      (ratLe_of_lt ratZero_mem_Rat ratOne_mem_Rat ratZero_lt_one)
  have hone_icc : realLOf ratOne.{u} ∈ realLIcc ratZero.{u} ratOne.{u} :=
    right_mem_realLIcc ratZero_mem_Rat ratOne_mem_Rat
      (ratLe_of_lt ratZero_mem_Rat ratOne_mem_Rat ratZero_lt_one)
  -- `G 0 < 0` puts `0` in the set
  have hne : ∃ a, a ∈ S := by
    refine ⟨realLOf ratZero.{u}, (mem_sep_iff _ _ _).mpr ⟨hzero_icc, fun h => ?_⟩⟩
    exact realLLt_irrefl (hGmaps _ hzero_icc)
      (realLLt_trans (hGmaps _ hzero_icc) realLZero_mem (hGmaps _ hzero_icc) hlo h)
  -- the supremum
  obtain ⟨s, hsR, hub_pair, hleast⟩ :=
    exists_sup_of_subset_realLIcc_of_em hem ratOne_mem_Rat hSsub hne
  have hSmem : ∀ x, x ∈ S → x ∈ RealL.{u} := fun x hx =>
    ((mem_realLIcc_iff _ _ x).mp (hSsub x hx)).left
  have hub : ∀ x, x ∈ S → ¬ realLLt s x := fun x hx hlt =>
    hub_pair x hx ((opair_mem_realLLtRel_iff hsR (hSmem x hx)).mpr hlt)
  -- `s` lies in `[0,1]`: above `0` because `0` is in the set, below `1`
  -- because `1` bounds the set and `s` is least among such bounds
  have hs_mem : s ∈ realLIcc ratZero.{u} ratOne.{u} := by
    refine (mem_realLIcc_iff _ _ s).mpr ⟨hsR, fun h => ?_, fun h => ?_⟩
    · -- `0` is in the set, so the upper bound refutes `s < 0` outright --- no
      -- cotransitivity is needed on this side, unlike the `realLOf q` step.
      exact hub _ ((mem_sep_iff _ _ _).mpr ⟨hzero_icc, fun hpos =>
        realLLt_irrefl (hGmaps _ hzero_icc) (realLLt_trans (hGmaps _ hzero_icc)
          realLZero_mem (hGmaps _ hzero_icc) hlo hpos)⟩) h
    · -- `1` bounds the set, and `s` is least among such bounds
      refine hleast (realLOf ratOne.{u}) (realLOf_mem ratOne_mem_Rat)
        (fun x hx hlt => ((mem_realLIcc_iff _ _ x).mp (hSsub x hx)).right.right
          ((opair_mem_realLLtRel_iff (realLOf_mem ratOne_mem_Rat)
            (hSmem x hx)).mp hlt))
        ((opair_mem_realLLtRel_iff (realLOf_mem ratOne_mem_Rat) hsR).mpr h)
  -- both refutations, then antisymmetry
  refine ⟨s, hs_mem, realLLe_antisymm (hGmaps s hs_mem) realLZero_mem ?_ ?_⟩
  · exact not_realLZero_lt_G_sup hem hGmaps hcont hSsub hSle hs_mem hub hleast
  · refine not_G_sup_lt_realLZero hem hGmaps hcont hhi ?_ hs_mem hub
    intro x hx hneg
    exact (mem_sep_iff _ _ _).mpr ⟨hx, fun hpos => realLLt_irrefl (hGmaps x hx)
      (realLLt_trans (hGmaps x hx) realLZero_mem (hGmaps x hx) hneg hpos)⟩


end Analysis

namespace Analysis

end Analysis

#print axioms Analysis.familyLocated_of_isLocatedSubset
#print axioms Analysis.isStrictOrderOn_realLLtRel
#print axioms Analysis.isConditionallyCompleteLocated_realL

#print axioms Analysis.isConditionallyComplete_realL_of_em
#print axioms Analysis.mem_posRay_iff
#print axioms Analysis.mem_negRay_iff
#print axioms Analysis.not_realLZero_lt_G_sup
#print axioms Analysis.not_G_sup_lt_realLZero
#print axioms Analysis.exactIVT01Top_of_em
#print axioms Analysis.exists_sup_of_subset_realLIcc_of_em
#print axioms Analysis.exists_mem_realLLt_of_lt_sup
#print axioms Analysis.exists_rat_between_two
namespace ZFSet
export Analysis (exists_mem_realLLt_of_lt_sup exists_rat_between_two exists_sup_of_subset_realLIcc_of_em familyLocated_of_isLocatedSubset isConditionallyCompleteLocated_realL isConditionallyComplete_realL_of_em isStrictOrderOn_realLLtRel)
end ZFSet
