/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The complex numbers.

Pairs of located reals, with the twisted multiplication.

The reals are `Located.lean`'s, not `Real.lean`'s. Multiplication of cuts costs
`Classical.choice` -- it is defined by the four sign cases, and picking one is a
decision -- so ℂ over cuts would pay choice in every product.
Located reals carry the witness pair that makes the decision unnecessary, so
everything here is at `[propext, Quot.sound]`.

The carrier is `opair`, not a two-element function. `LinAlg.lean` argues for
indexed families, but that argument is about arbitrary `n`; at a fixed 2,
`Pair.lean` already supplies `fst`, `snd`, `prod` and injectivity, and a
function would add an index type to carry for nothing.
-/

import FromAxioms.Algebra.Ring

universe u

open Algebra NumberTheory SetTheory
namespace Analysis

/-- A complex number is a pair of located reals. -/
def Complex : ZFSet.{u} := prod RealL.{u} RealL.{u}

/-! ## The located reals are a ring

Stated here rather than in `Located.lean` because `Ring.lean` sits above it in
the import order -- `IsRing` is not in scope there. `Complex.lean` is the first
file that imports both. -/

def realLAddOp : ZFSet.{u} :=
  graphOn (prod RealL.{u} RealL.{u}) RealL.{u} (fun z => realLAdd (fst z) (snd z))

def realLMulOp : ZFSet.{u} :=
  graphOn (prod RealL.{u} RealL.{u}) RealL.{u} (fun z => realLMul (fst z) (snd z))

private theorem realLAdd_maps {z : ZFSet.{u}} (hz : z ∈ prod RealL.{u} RealL.{u}) :
    realLAdd (fst z) (snd z) ∈ RealL.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff z _ _).mp hz
  rw [fst_opair, snd_opair]
  exact realLAdd_mem ha hb

private theorem realLMul_maps {z : ZFSet.{u}} (hz : z ∈ prod RealL.{u} RealL.{u}) :
    realLMul (fst z) (snd z) ∈ RealL.{u} := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff z _ _).mp hz
  rw [fst_opair, snd_opair]
  exact realLMul_mem ha hb

theorem opAt_realLAddOp {z w : ZFSet.{u}} (hz : z ∈ RealL.{u}) (hw : w ∈ RealL.{u}) :
    opAt realLAddOp.{u} z w = realLAdd z w := by
  rw [opAt, realLAddOp, app_graphOn (fun _ hm => realLAdd_maps hm) (opair_mem_prod hz hw),
    fst_opair, snd_opair]

theorem opAt_realLMulOp {z w : ZFSet.{u}} (hz : z ∈ RealL.{u}) (hw : w ∈ RealL.{u}) :
    opAt realLMulOp.{u} z w = realLMul z w := by
  rw [opAt, realLMulOp, app_graphOn (fun _ hm => realLMul_maps hm) (opair_mem_prod hz hw),
    fst_opair, snd_opair]

private theorem range_graphOn_realL {F : ZFSet.{u} → ZFSet.{u}}
    (hF : ∀ z, z ∈ prod RealL.{u} RealL.{u} → F z ∈ RealL.{u}) :
    range (graphOn (prod RealL.{u} RealL.{u}) RealL.{u} F) ⊆ RealL.{u} := by
  intro w hw
  obtain ⟨c, hc⟩ := (mem_range_iff w _).mp hw
  obtain ⟨-, m, hm, he⟩ := (mem_graphOn_iff _ _ _ _).mp hc
  obtain ⟨-, rfl⟩ := opair_injective he
  exact hF m hm

/-- The located reals form a ring, constructively. -/
theorem isRing_realL :
    IsRing RealL.{u} realLAddOp.{u} realLMulOp.{u} realLZero.{u} realLOne.{u} where
  addGroup :=
    { isFun := graphOn_isFunction _ _ _
      dom := graphOn_domain (fun _ hm => realLAdd_maps hm)
      ran := range_graphOn_realL (fun _ hm => realLAdd_maps hm)
      mem_e := realLZero_mem
      assoc a ha b hb c hc := by
        rw [opAt_realLAddOp ha hb, opAt_realLAddOp (realLAdd_mem ha hb) hc,
          opAt_realLAddOp hb hc, opAt_realLAddOp ha (realLAdd_mem hb hc),
          realLAdd_assoc ha hb hc]
      left_id a ha := by
        rw [opAt_realLAddOp realLZero_mem ha, realLAdd_comm realLZero_mem ha,
          realLAdd_zero ha]
      right_id a ha := by rw [opAt_realLAddOp ha realLZero_mem, realLAdd_zero ha]
      inverses a ha := ⟨realLNeg a, realLNeg_mem ha,
        by rw [opAt_realLAddOp ha (realLNeg_mem ha), realLAdd_neg ha],
        by rw [opAt_realLAddOp (realLNeg_mem ha) ha,
          realLAdd_comm (realLNeg_mem ha) ha, realLAdd_neg ha]⟩ }
  addComm a ha b hb := by
    rw [opAt_realLAddOp ha hb, opAt_realLAddOp hb ha, realLAdd_comm ha hb]
  mulFun := graphOn_isFunction _ _ _
  mulDom := graphOn_domain (fun _ hm => realLMul_maps hm)
  mulRan := range_graphOn_realL (fun _ hm => realLMul_maps hm)
  mulAssoc a ha b hb c hc := by
    rw [opAt_realLMulOp ha hb, opAt_realLMulOp (realLMul_mem ha hb) hc,
      opAt_realLMulOp hb hc, opAt_realLMulOp ha (realLMul_mem hb hc),
      realLMul_assoc ha hb hc]
  mulComm a ha b hb := by
    rw [opAt_realLMulOp ha hb, opAt_realLMulOp hb ha, realLMul_comm ha hb]
  mem_one := realLOne_mem
  mul_one a ha := by rw [opAt_realLMulOp ha realLOne_mem, realLMul_one ha]
  distrib a ha b hb c hc := by
    rw [opAt_realLAddOp hb hc, opAt_realLMulOp ha (realLAdd_mem hb hc),
      opAt_realLMulOp ha hb, opAt_realLMulOp ha hc,
      opAt_realLAddOp (realLMul_mem ha hb) (realLMul_mem ha hc),
      realLMul_distrib ha hb hc]

/-! ## `RealL` as a constructive field

The raw material -- negation against multiplication, inverses, positive
squares -- lives in `Located.lean`; here it is packaged against the ring
operations. -/

theorem ringNeg_realL {a : ZFSet.{u}} (ha : a ∈ RealL.{u}) :
    ringNeg RealL.{u} realLAddOp.{u} realLZero.{u} a = realLNeg a :=
  ringNeg_eq_of_add_zero isRing_realL ha (realLNeg_mem ha)
    (by rw [opAt_realLAddOp ha (realLNeg_mem ha), realLAdd_neg ha])

#print axioms Complex
#print axioms isRing_realL
end Analysis

namespace ZFSet
export Analysis (Complex isRing_realL opAt_realLAddOp opAt_realLMulOp realLAddOp realLMulOp ringNeg_realL)
end ZFSet
