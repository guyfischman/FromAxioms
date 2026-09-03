/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The polynomial ring as an object.

`Poly.lean` evaluates a Lean-level list of coefficients; that is enough to bound
roots but it is not a ring inside the theory. Here a polynomial is a set: a
function from `ω` to `R` that is eventually `zero`. The carrier `PolyRing R zero`
is then a set, and the operations are set functions on it, so `IsRing` can be
stated about them the same way it is stated about `ℤ` or `ℤ/nℤ`.

Addition is pointwise, so it needs no index arithmetic: the coefficient at `w` is
`f w + g w`, and the support bound is the larger of the two. Multiplication is
the convolution and does need arithmetic on indices; it is built separately.
-/

import FromAxioms.Algebra.Ring

universe u

open NumberTheory SetTheory
namespace Algebra

/-! ## The carrier -/

/-- A polynomial: a function on `ω` into `R` whose coefficients are eventually
`zero`. -/
def IsPolyOver (R zero f : ZFSet.{u}) : Prop :=
  IsFunction f ∧ domain f = omega.{u} ∧ range f ⊆ R ∧
    ∃ N : Nat, ∀ i : Nat, N ≤ i → app f (ofNat.{u} i) = zero

def PolyRing (R zero : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun f => IsPolyOver R zero f) (powerset (prod omega.{u} R))

theorem mem_polyRing_iff (R zero f : ZFSet.{u}) :
    f ∈ PolyRing R zero ↔ IsPolyOver R zero f := by
  refine Iff.trans (mem_sep_iff _ _ _) ⟨And.right, fun h => ⟨?_, h⟩⟩
  refine (mem_powerset_iff _ _).mpr (fun z hz => ?_)
  obtain ⟨a, b, rfl⟩ := h.left.left z hz
  refine opair_mem_prod ?_ (h.right.right.left _ ((mem_range_iff b f).mpr ⟨a, hz⟩))
  rw [← h.right.left]
  exact (mem_domain_iff a f).mpr ⟨b, hz⟩

/-- A polynomial over a subset is a polynomial over the ambient set. Only
the range clause moves; the support bound and functionhood do not mention the
ring at all. -/
theorem isPolyOver_mono {S R zero f : ZFSet.{u}} (hSR : S ⊆ R)
    (hf : IsPolyOver S zero f) : IsPolyOver R zero f :=
  ⟨hf.left, hf.right.left,
    fun y hy => hSR y (hf.right.right.left y hy), hf.right.right.right⟩

#print axioms isPolyOver_mono

/-! ## The operations -/

def polyAdd (R add f g : ZFSet.{u}) : ZFSet.{u} :=
  graphOn omega.{u} R (fun w => opAt add (app f w) (app g w))

def polyZero (R zero : ZFSet.{u}) : ZFSet.{u} := graphOn omega.{u} R (fun _ => zero)

def polyNeg (R add zero f : ZFSet.{u}) : ZFSet.{u} :=
  graphOn omega.{u} R (fun w => ringNeg R add zero (app f w))

/-! ## Coefficients -/

theorem coeff_mem {R zero f : ZFSet.{u}} (h : IsPolyOver R zero f) {w : ZFSet.{u}}
    (hw : w ∈ omega.{u}) : app f w ∈ R :=
  h.right.right.left _ (app_mem_range h.left (by rw [h.right.left]; exact hw))

theorem app_polyAdd {R add mul zero one f g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) {w : ZFSet.{u}}
    (hw : w ∈ omega.{u}) :
    app (polyAdd R add f g) w = opAt add (app f w) (app g w) :=
  app_graphOn (fun m hm => addAt_mem hR (coeff_mem hf hm) (coeff_mem hg hm)) hw

theorem app_polyZero {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one)
    {w : ZFSet.{u}} (hw : w ∈ omega.{u}) : app (polyZero R zero) w = zero :=
  app_graphOn (fun _ _ => hR.addGroup.mem_e) hw

theorem app_polyNeg {R add mul zero one f : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) {w : ZFSet.{u}} (hw : w ∈ omega.{u}) :
    app (polyNeg R add zero f) w = ringNeg R add zero (app f w) :=
  app_graphOn (fun m hm => ringNeg_mem hR (coeff_mem hf hm)) hw

/-! ## Closure -/

theorem isPolyOver_polyAdd {R add mul zero one f g : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) :
    IsPolyOver R zero (polyAdd R add f g) := by
  have hmaps : ∀ m, m ∈ omega.{u} → opAt add (app f m) (app g m) ∈ R :=
    fun m hm => addAt_mem hR (coeff_mem hf hm) (coeff_mem hg hm)
  obtain ⟨Nf, hNf⟩ := hf.right.right.right
  obtain ⟨Ng, hNg⟩ := hg.right.right.right
  refine ⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range,
    Nf + Ng, fun i hi => ?_⟩
  rw [app_polyAdd hR hf hg (ofNat_mem_omega i), hNf i (by omega), hNg i (by omega),
    ringAdd_zero hR hR.addGroup.mem_e]

theorem isPolyOver_polyZero {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    IsPolyOver R zero (polyZero R zero) :=
  ⟨graphOn_isFunction _ _ _, graphOn_domain (fun _ _ => hR.addGroup.mem_e), graphOn_range,
    0, fun i _ => app_polyZero hR (ofNat_mem_omega i)⟩

theorem isPolyOver_polyNeg {R add mul zero one f : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) : IsPolyOver R zero (polyNeg R add zero f) := by
  have hmaps : ∀ m, m ∈ omega.{u} → ringNeg R add zero (app f m) ∈ R :=
    fun m hm => ringNeg_mem hR (coeff_mem hf hm)
  obtain ⟨N, hN⟩ := hf.right.right.right
  refine ⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range, N, fun i hi => ?_⟩
  rw [app_polyNeg hR hf (ofNat_mem_omega i), hN i hi]
  -- `-0 = 0`, because `0` is its own inverse
  exact inv_unique hR.addGroup hR.addGroup.mem_e (ringNeg_mem hR hR.addGroup.mem_e)
    hR.addGroup.mem_e (ringAdd_neg hR hR.addGroup.mem_e)
    (ringAdd_zero hR hR.addGroup.mem_e)

/-! ## Polynomials are equal when their coefficients are -/

theorem poly_ext {R zero f g : ZFSet.{u}} (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g)
    (h : ∀ w, w ∈ omega.{u} → app f w = app g w) : f = g :=
  funext_zf hf.left hg.left (by rw [hf.right.left, hg.right.left])
    (fun a ha => h a (by rw [← hf.right.left]; exact ha))

/-! ## The additive group -/

def polyAddOp (R add zero : ZFSet.{u}) : ZFSet.{u} :=
  graphOn (prod (PolyRing R zero) (PolyRing R zero)) (PolyRing R zero)
    (fun p => polyAdd R add (fst p) (snd p))

theorem opAt_polyAddOp {R add mul zero one f g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : f ∈ PolyRing R zero) (hg : g ∈ PolyRing R zero) :
    opAt (polyAddOp R add zero) f g = polyAdd R add f g := by
  have hmaps : ∀ p, p ∈ prod (PolyRing R zero) (PolyRing R zero) →
      polyAdd R add (fst p) (snd p) ∈ PolyRing R zero := by
    intro p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff p _ _).mp hp
    rw [fst_opair, snd_opair]
    exact (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyAdd hR
      ((mem_polyRing_iff _ _ _).mp ha) ((mem_polyRing_iff _ _ _).mp hb))
  show app (polyAddOp R add zero) (opair f g) = _
  rw [polyAddOp, app_graphOn hmaps (opair_mem_prod hf hg), fst_opair, snd_opair]

theorem isGroup_polyAdd {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    IsGroup (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero) := by
  have hmaps : ∀ p, p ∈ prod (PolyRing R zero) (PolyRing R zero) →
      polyAdd R add (fst p) (snd p) ∈ PolyRing R zero := by
    intro p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff p _ _).mp hp
    rw [fst_opair, snd_opair]
    exact (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyAdd hR
      ((mem_polyRing_iff _ _ _).mp ha) ((mem_polyRing_iff _ _ _).mp hb))
  have hzero : polyZero R zero ∈ PolyRing R zero :=
    (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyZero hR)
  refine ⟨⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range, hzero,
    ?_, ?_, ?_⟩, ?_⟩
  · intro a ha b hb c hc
    have hpa := (mem_polyRing_iff _ _ _).mp ha
    have hpb := (mem_polyRing_iff _ _ _).mp hb
    have hpc := (mem_polyRing_iff _ _ _).mp hc
    have hab := isPolyOver_polyAdd hR hpa hpb
    have hbc := isPolyOver_polyAdd hR hpb hpc
    rw [opAt_polyAddOp hR ha hb, opAt_polyAddOp hR hb hc,
      opAt_polyAddOp hR ((mem_polyRing_iff _ _ _).mpr hab) hc,
      opAt_polyAddOp hR ha ((mem_polyRing_iff _ _ _).mpr hbc)]
    refine poly_ext (isPolyOver_polyAdd hR hab hpc) (isPolyOver_polyAdd hR hpa hbc)
      (fun w hw => ?_)
    rw [app_polyAdd hR hab hpc hw, app_polyAdd hR hpa hbc hw,
      app_polyAdd hR hpa hpb hw, app_polyAdd hR hpb hpc hw,
      ringAdd_assoc hR (coeff_mem hpa hw) (coeff_mem hpb hw) (coeff_mem hpc hw)]
  · intro a ha
    have hpa := (mem_polyRing_iff _ _ _).mp ha
    rw [opAt_polyAddOp hR hzero ha]
    refine poly_ext (isPolyOver_polyAdd hR (isPolyOver_polyZero hR) hpa) hpa (fun w hw => ?_)
    rw [app_polyAdd hR (isPolyOver_polyZero hR) hpa hw, app_polyZero hR hw,
      ringZero_add hR (coeff_mem hpa hw)]
  · intro a ha
    have hpa := (mem_polyRing_iff _ _ _).mp ha
    rw [opAt_polyAddOp hR ha hzero]
    refine poly_ext (isPolyOver_polyAdd hR hpa (isPolyOver_polyZero hR)) hpa (fun w hw => ?_)
    rw [app_polyAdd hR hpa (isPolyOver_polyZero hR) hw, app_polyZero hR hw,
      ringAdd_zero hR (coeff_mem hpa hw)]
  · intro a ha
    have hpa := (mem_polyRing_iff _ _ _).mp ha
    have hneg := isPolyOver_polyNeg hR hpa
    refine ⟨polyNeg R add zero a, (mem_polyRing_iff _ _ _).mpr hneg, ?_, ?_⟩
    · rw [opAt_polyAddOp hR ha ((mem_polyRing_iff _ _ _).mpr hneg)]
      refine poly_ext (isPolyOver_polyAdd hR hpa hneg) (isPolyOver_polyZero hR) (fun w hw => ?_)
      rw [app_polyAdd hR hpa hneg hw, app_polyNeg hR hpa hw, app_polyZero hR hw,
        ringAdd_neg hR (coeff_mem hpa hw)]
    · rw [opAt_polyAddOp hR ((mem_polyRing_iff _ _ _).mpr hneg) ha]
      refine poly_ext (isPolyOver_polyAdd hR hneg hpa) (isPolyOver_polyZero hR) (fun w hw => ?_)
      rw [app_polyAdd hR hneg hpa hw, app_polyNeg hR hpa hw, app_polyZero hR hw,
        ringNeg_add hR (coeff_mem hpa hw)]

#print axioms mem_polyRing_iff
#print axioms isGroup_polyAdd
end Algebra

namespace ZFSet
export Algebra (IsPolyOver PolyRing app_polyAdd app_polyNeg app_polyZero coeff_mem isGroup_polyAdd isPolyOver_mono isPolyOver_polyAdd isPolyOver_polyNeg isPolyOver_polyZero mem_polyRing_iff opAt_polyAddOp polyAdd polyAddOp polyNeg polyZero poly_ext)
end ZFSet
