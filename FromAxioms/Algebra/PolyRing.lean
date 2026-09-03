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

import FromAxioms.Algebra.Field
import FromAxioms.Algebra.Poly

universe u

open Core NumberTheory SetTheory
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

theorem isAbelian_polyAdd {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    IsAbelian (PolyRing R zero) (polyAddOp R add zero) := by
  intro a ha b hb
  have hpa := (mem_polyRing_iff _ _ _).mp ha
  have hpb := (mem_polyRing_iff _ _ _).mp hb
  rw [opAt_polyAddOp hR ha hb, opAt_polyAddOp hR hb ha]
  refine poly_ext (isPolyOver_polyAdd hR hpa hpb) (isPolyOver_polyAdd hR hpb hpa)
    (fun w hw => ?_)
  rw [app_polyAdd hR hpa hpb hw, app_polyAdd hR hpb hpa hw,
    ringAdd_comm hR (coeff_mem hpa hw) (coeff_mem hpb hw)]

/-! ## A sequence of coefficients as a polynomial

Three constructions -- the product, the unit, and a list of coefficients -- all
build a polynomial from a `Nat`-indexed sequence. This is that construction. -/

def polyOfSeq (R : ZFSet.{u}) (C : Nat → ZFSet.{u}) : ZFSet.{u} :=
  sep (fun z => ∃ k : Nat, z = opair (ofNat.{u} k) (C k)) (prod omega.{u} R)

theorem mem_polyOfSeq_iff {R : ZFSet.{u}} {C : Nat → ZFSet.{u}} {z : ZFSet.{u}} :
    z ∈ polyOfSeq R C ↔ z ∈ prod omega.{u} R ∧ ∃ k : Nat, z = opair (ofNat.{u} k) (C k) :=
  mem_sep_iff _ _ _

theorem isFunction_polyOfSeq {R : ZFSet.{u}} {C : Nat → ZFSet.{u}} :
    IsFunction (polyOfSeq R C) := by
  constructor
  · intro z hz
    obtain ⟨-, k, rfl⟩ := mem_polyOfSeq_iff.mp hz
    exact ⟨_, _, rfl⟩
  · intro a b b' hb hb'
    obtain ⟨-, k, he⟩ := mem_polyOfSeq_iff.mp hb
    obtain ⟨-, k', he'⟩ := mem_polyOfSeq_iff.mp hb'
    obtain ⟨hka, rfl⟩ := opair_injective he
    obtain ⟨hka', rfl⟩ := opair_injective he'
    rw [ofNat_injective (hka.symm.trans hka')]

theorem app_polyOfSeq {R : ZFSet.{u}} {C : Nat → ZFSet.{u}} (hC : ∀ k, C k ∈ R) (k : Nat) :
    app (polyOfSeq R C) (ofNat.{u} k) = C k :=
  app_eq isFunction_polyOfSeq (mem_polyOfSeq_iff.mpr
    ⟨opair_mem_prod (ofNat_mem_omega k) (hC k), k, rfl⟩)

theorem isPolyOver_polyOfSeq {R zero : ZFSet.{u}} {C : Nat → ZFSet.{u}} (hC : ∀ k, C k ∈ R)
    {N : Nat} (hN : ∀ i : Nat, N ≤ i → C i = zero) : IsPolyOver R zero (polyOfSeq R C) := by
  refine ⟨isFunction_polyOfSeq, ?_, ?_, N, fun i hi => ?_⟩
  · refine ext _ _ fun a => ⟨fun ha => ?_, fun ha => ?_⟩
    · obtain ⟨b, hb⟩ := (mem_domain_iff a _).mp ha
      obtain ⟨-, k, he⟩ := mem_polyOfSeq_iff.mp hb
      rw [(opair_injective he).left]
      exact ofNat_mem_omega k
    · obtain ⟨k, rfl⟩ := (mem_omega_iff a).mp ha
      exact (mem_domain_iff _ _).mpr ⟨_, mem_polyOfSeq_iff.mpr
        ⟨opair_mem_prod (ofNat_mem_omega k) (hC k), k, rfl⟩⟩
  · intro b hb
    obtain ⟨a, hab⟩ := (mem_range_iff b _).mp hb
    obtain ⟨-, k, he⟩ := mem_polyOfSeq_iff.mp hab
    rw [(opair_injective he).right]
    exact hC k
  · rw [app_polyOfSeq hC i]
    exact hN i hi

/-! ## Multiplication

The convolution `(fg)_k = ∑_{i≤k} f_i·g_{k-i}` is a `foldF` over `Nat` indices,
so the coefficient is computed before any set is built. The set is then the
pairs `⟨ofNat k, (fg)_k⟩` -- built by separation rather than `graphOn`, so the
`Nat` index stays available. -/

def convCoeff (R add mul zero f g : ZFSet.{u}) (k : Nat) : ZFSet.{u} :=
  foldF add zero (fun i => opAt mul (app f (ofNat.{u} i)) (app g (ofNat.{u} (k - i)))) (k + 1)

def polyMul (R add mul zero f g : ZFSet.{u}) : ZFSet.{u} :=
  polyOfSeq R (fun k => convCoeff R add mul zero f g k)

theorem isCommMonoid_ringAdd {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    IsCommMonoid R add zero :=
  isCommMonoid_of_isGroup hR.addGroup hR.addComm

theorem convCoeff_mem {R add mul zero one f g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) (k : Nat) :
    convCoeff R add mul zero f g k ∈ R :=
  foldF_mem (isCommMonoid_ringAdd hR) (k + 1)
    (fun i _ => mulAt_mem hR (coeff_mem hf (ofNat_mem_omega i))
      (coeff_mem hg (ofNat_mem_omega (k - i))))

theorem app_polyMul {R add mul zero one f g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) (k : Nat) :
    app (polyMul R add mul zero f g) (ofNat.{u} k) = convCoeff R add mul zero f g k :=
  app_polyOfSeq (fun j => convCoeff_mem hR hf hg j) k

/-- Beyond the two support bounds every term of the convolution has a zero
factor. -/
theorem convCoeff_eq_zero {R add mul zero one f g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) {Nf Ng : Nat}
    (hNf : ∀ i : Nat, Nf ≤ i → app f (ofNat.{u} i) = zero)
    (hNg : ∀ i : Nat, Ng ≤ i → app g (ofNat.{u} i) = zero)
    {k : Nat} (hk : Nf + Ng ≤ k) : convCoeff R add mul zero f g k = zero := by
  have hzeros : ∀ i : Nat, i < k + 1 →
      opAt mul (app f (ofNat.{u} i)) (app g (ofNat.{u} (k - i))) = zero := by
    intro i hi
    rcases Nat.lt_or_ge i Nf with hlt | hge
    · rw [hNg (k - i) (by omega), mul_zero_of_isRing hR (coeff_mem hf (ofNat_mem_omega i))]
    · rw [hNf i hge, ringZero_mul hR (coeff_mem hg (ofNat_mem_omega (k - i)))]
  -- a fold of zeros is zero
  have hall : ∀ n : Nat, n < k + 2 →
      foldF add zero (fun i => opAt mul (app f (ofNat.{u} i)) (app g (ofNat.{u} (k - i)))) n
        = zero := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      show opAt add (foldF add zero
        (fun i => opAt mul (app f (ofNat.{u} i)) (app g (ofNat.{u} (k - i)))) j)
          (opAt mul (app f (ofNat.{u} j)) (app g (ofNat.{u} (k - j)))) = zero
      rw [ih (by omega), hzeros j (by omega), ringAdd_zero hR hR.addGroup.mem_e]
  exact hall (k + 1) (by omega)

theorem isPolyOver_polyMul {R add mul zero one f g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) :
    IsPolyOver R zero (polyMul R add mul zero f g) := by
  obtain ⟨Nf, hNf⟩ := hf.right.right.right
  obtain ⟨Ng, hNg⟩ := hg.right.right.right
  exact isPolyOver_polyOfSeq (fun k => convCoeff_mem hR hf hg k)
    (N := Nf + Ng) (fun i hi => convCoeff_eq_zero hR hf hg hNf hNg hi)

/-! ## Commutativity of the convolution -/

theorem convCoeff_comm {R add mul zero one f g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) (k : Nat) :
    convCoeff R add mul zero f g k = convCoeff R add mul zero g f k := by
  have hM := isCommMonoid_ringAdd hR
  have hmem : ∀ i : Nat, i < k + 1 →
      opAt mul (app f (ofNat.{u} i)) (app g (ofNat.{u} (k - i))) ∈ R :=
    fun i _ => mulAt_mem hR (coeff_mem hf (ofNat_mem_omega i))
      (coeff_mem hg (ofNat_mem_omega (k - i)))
  rw [convCoeff, foldF_reverse hM (k + 1) hmem]
  refine foldF_congr (k + 1) (fun i hi => ?_)
  show opAt mul (app f (ofNat.{u} (k + 1 - 1 - i))) (app g (ofNat.{u} (k - (k + 1 - 1 - i))))
    = opAt mul (app g (ofNat.{u} i)) (app f (ofNat.{u} (k - i)))
  rw [show k + 1 - 1 - i = k - i from rfl, show k - (k - i) = i by omega,
    hR.mulComm _ (coeff_mem hf (ofNat_mem_omega (k - i))) _ (coeff_mem hg (ofNat_mem_omega i))]

/-! ## Distributivity of the convolution -/

theorem convCoeff_distrib {R add mul zero one f g h : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g)
    (hh : IsPolyOver R zero h) (k : Nat) :
    convCoeff R add mul zero f (polyAdd R add g h) k
      = opAt add (convCoeff R add mul zero f g k) (convCoeff R add mul zero f h k) := by
  have hM := isCommMonoid_ringAdd hR
  rw [convCoeff, foldF_congr (F := fun i => opAt mul (app f (ofNat.{u} i))
      (app (polyAdd R add g h) (ofNat.{u} (k - i))))
    (G := fun i => opAt add (opAt mul (app f (ofNat.{u} i)) (app g (ofNat.{u} (k - i))))
      (opAt mul (app f (ofNat.{u} i)) (app h (ofNat.{u} (k - i))))) (k + 1) (fun i _ => by
      show opAt mul (app f (ofNat.{u} i)) (app (polyAdd R add g h) (ofNat.{u} (k - i))) = _
      rw [app_polyAdd hR hg hh (ofNat_mem_omega (k - i)),
        hR.distrib _ (coeff_mem hf (ofNat_mem_omega i))
          _ (coeff_mem hg (ofNat_mem_omega (k - i)))
          _ (coeff_mem hh (ofNat_mem_omega (k - i)))]),
    foldF_add hM (k + 1)
      (fun i _ => mulAt_mem hR (coeff_mem hf (ofNat_mem_omega i))
        (coeff_mem hg (ofNat_mem_omega (k - i))))
      (fun i _ => mulAt_mem hR (coeff_mem hf (ofNat_mem_omega i))
        (coeff_mem hh (ofNat_mem_omega (k - i))))]
  rfl

/-- Coefficients of a sum, over a semiring: closure of the additive
monoid is all `polyAdd`'s graph needs. -/
theorem app_polyAdd_semi {R add mul zero one f g : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) {w : ZFSet.{u}}
    (hw : w ∈ omega.{u}) :
    app (polyAdd R add f g) w = opAt add (app f w) (app g w) :=
  app_graphOn (fun m hm => addAt_mem_semi hR (coeff_mem hf hm) (coeff_mem hg hm)) hw

/-- Coefficients of the zero polynomial, over a semiring -- every one is
the additive monoid's identity. -/
theorem app_polyZero_semi {R add mul zero one : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    {w : ZFSet.{u}} (hw : w ∈ omega.{u}) : app (polyZero R zero) w = zero :=
  app_graphOn (fun _ _ => hR.addMonoid.mem_e) hw

/-- A sum of polynomials is a polynomial, over a semiring. The tail
vanishes past both degrees, and `zero + zero = zero` closes it by the LEFT
unit law, which is the only one `IsCommMonoid` states. -/
theorem isPolyOver_polyAdd_semi {R add mul zero one f g : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (hf : IsPolyOver R zero f)
    (hg : IsPolyOver R zero g) :
    IsPolyOver R zero (polyAdd R add f g) := by
  have hmaps : ∀ m, m ∈ omega.{u} → opAt add (app f m) (app g m) ∈ R :=
    fun m hm => addAt_mem_semi hR (coeff_mem hf hm) (coeff_mem hg hm)
  obtain ⟨Nf, hNf⟩ := hf.right.right.right
  obtain ⟨Ng, hNg⟩ := hg.right.right.right
  refine ⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range,
    Nf + Ng, fun i hi => ?_⟩
  rw [app_polyAdd_semi hR hf hg (ofNat_mem_omega i), hNf i (by omega), hNg i (by omega),
    hR.addMonoid.left_id _ hR.addMonoid.mem_e]

/-- The zero polynomial is a polynomial, over a semiring. -/
theorem isPolyOver_polyZero_semi {R add mul zero one : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) :
    IsPolyOver R zero (polyZero R zero) :=
  ⟨graphOn_isFunction _ _ _, graphOn_domain (fun _ _ => hR.addMonoid.mem_e), graphOn_range,
    0, fun i _ => app_polyZero_semi hR (ofNat_mem_omega i)⟩

/-- The convolution distributes over addition, over a semiring: left
distributivity termwise, then `foldF_add` over the additive monoid. -/
theorem convCoeff_distrib_semi {R add mul zero one f g h : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g)
    (hh : IsPolyOver R zero h) (k : Nat) :
    convCoeff R add mul zero f (polyAdd R add g h) k
      = opAt add (convCoeff R add mul zero f g k) (convCoeff R add mul zero f h k) := by
  have hM := hR.addMonoid
  rw [convCoeff, foldF_congr (F := fun i => opAt mul (app f (ofNat.{u} i))
      (app (polyAdd R add g h) (ofNat.{u} (k - i))))
    (G := fun i => opAt add (opAt mul (app f (ofNat.{u} i)) (app g (ofNat.{u} (k - i))))
      (opAt mul (app f (ofNat.{u} i)) (app h (ofNat.{u} (k - i))))) (k + 1) (fun i _ => by
      show opAt mul (app f (ofNat.{u} i)) (app (polyAdd R add g h) (ofNat.{u} (k - i))) = _
      rw [app_polyAdd_semi hR hg hh (ofNat_mem_omega (k - i)),
        hR.distrib _ (coeff_mem hf (ofNat_mem_omega i))
          _ (coeff_mem hg (ofNat_mem_omega (k - i)))
          _ (coeff_mem hh (ofNat_mem_omega (k - i)))]),
    foldF_add hM (k + 1)
      (fun i _ => mulAt_mem_semi hR (coeff_mem hf (ofNat_mem_omega i))
        (coeff_mem hg (ofNat_mem_omega (k - i))))
      (fun i _ => mulAt_mem_semi hR (coeff_mem hf (ofNat_mem_omega i))
        (coeff_mem hh (ofNat_mem_omega (k - i))))]
  rfl

#print axioms Algebra.app_polyAdd_semi
#print axioms Algebra.app_polyZero_semi
#print axioms Algebra.isPolyOver_polyAdd_semi
#print axioms Algebra.isPolyOver_polyZero_semi
#print axioms Algebra.convCoeff_distrib_semi

/-! ## Associativity of the convolution

Both `(fg)h` and `f(gh)` are the sum of `f_a·g_b·h_c` over `a+b+c = k`; the two
groupings are the two sides of `foldF_triangle`. -/


/-- A constant multiplies into a finite sum on the LEFT, over a semiring:
`c · (Σ T i) = Σ (c · T i)`.

Left distributivity and the base case `c · 0 = 0`, which a semiring ASSUMES as
`mulZero` where a ring proves it by cancelling. Nothing else is used, so this
holds without additive inverses and without commutativity. -/
theorem foldF_mul_left_semi {R add mul zero one c : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (hc : c ∈ R) {T : Nat → ZFSet.{u}}
    (hT : ∀ i, T i ∈ R) :
    ∀ n : Nat, opAt mul c (foldF add zero T n)
      = foldF add zero (fun i => opAt mul c (T i)) n
  | 0 => hR.mulZero _ hc
  | n + 1 => by
    show opAt mul c (opAt add (foldF add zero T n) (T n))
      = opAt add (foldF add zero (fun i => opAt mul c (T i)) n) (opAt mul c (T n))
    rw [hR.distrib _ hc _ (foldF_mem hR.addMonoid n (fun i _ => hT i)) _ (hT n),
      foldF_mul_left_semi hR hc hT n]

/-- A constant multiplies into a finite sum on the RIGHT, over a semiring:
`(Σ T i) · c = Σ (T i · c)`.

`foldF_mul_right` reaches this by COMMUTING to the left form, so the polynomial
ring inherited commutativity it never needed: the statement is right
distributivity over a finite sum, and `distribRight` proves it directly by the
same induction the left form uses. That detour was one of only two `mulComm`
sites among the forty-one lemmas the ring structure rests on. -/
theorem foldF_mul_right_semi {R add mul zero one c : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (hc : c ∈ R) {T : Nat → ZFSet.{u}}
    (hT : ∀ i, T i ∈ R) :
    ∀ n : Nat, opAt mul (foldF add zero T n) c
      = foldF add zero (fun i => opAt mul (T i) c) n
  | 0 => hR.zeroMul _ hc
  | n + 1 => by
    show opAt mul (opAt add (foldF add zero T n) (T n)) c
      = opAt add (foldF add zero (fun i => opAt mul (T i) c) n) (opAt mul (T n) c)
    rw [hR.distribRight _ (foldF_mem hR.addMonoid n (fun i _ => hT i)) _ (hT n) _ hc,
      foldF_mul_right_semi hR hc hT n]

#print axioms Algebra.foldF_mul_left_semi
#print axioms Algebra.foldF_mul_right_semi

theorem foldF_mul_left {R add mul zero one c : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hc : c ∈ R) {T : Nat → ZFSet.{u}} (hT : ∀ i, T i ∈ R) :
    ∀ n : Nat, opAt mul c (foldF add zero T n)
      = foldF add zero (fun i => opAt mul c (T i)) n
  | 0 => mul_zero_of_isRing hR hc
  | n + 1 => by
    show opAt mul c (opAt add (foldF add zero T n) (T n))
      = opAt add (foldF add zero (fun i => opAt mul c (T i)) n) (opAt mul c (T n))
    rw [hR.distrib _ hc _ (foldF_mem (isCommMonoid_ringAdd hR) n (fun i _ => hT i)) _ (hT n),
      foldF_mul_left hR hc hT n]

theorem foldF_mul_left_lt {R add mul zero one c : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hc : c ∈ R) {T : Nat → ZFSet.{u}} :
    ∀ n : Nat, (∀ i, i < n → T i ∈ R) → opAt mul c (foldF add zero T n)
      = foldF add zero (fun i => opAt mul c (T i)) n
  | 0, _ => mul_zero_of_isRing hR hc
  | n + 1, hT => by
    show opAt mul c (opAt add (foldF add zero T n) (T n))
      = opAt add (foldF add zero (fun i => opAt mul c (T i)) n) (opAt mul c (T n))
    rw [hR.distrib _ hc _ (foldF_mem (isCommMonoid_ringAdd hR) n
        (fun i hi => hT i (by omega))) _ (hT n (by omega)),
      foldF_mul_left_lt hR hc n (fun i hi => hT i (by omega))]


theorem foldF_mul_right_lt {R add mul zero one c : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hc : c ∈ R) {T : Nat → ZFSet.{u}} (n : Nat) (hT : ∀ i, i < n → T i ∈ R) :
    opAt mul (foldF add zero T n) c = foldF add zero (fun i => opAt mul (T i) c) n := by
  rw [hR.mulComm _ (foldF_mem (isCommMonoid_ringAdd hR) n (fun i hi => hT i hi)) _ hc,
    foldF_mul_left_lt hR hc n hT]
  exact foldF_congr n (fun i hi => hR.mulComm _ hc _ (hT i hi))

theorem foldF_mul_right {R add mul zero one c : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hc : c ∈ R) {T : Nat → ZFSet.{u}} (hT : ∀ i, T i ∈ R) :
    ∀ n : Nat, opAt mul (foldF add zero T n) c
      = foldF add zero (fun i => opAt mul (T i) c) n := by
  intro n
  rw [hR.mulComm _ (foldF_mem (isCommMonoid_ringAdd hR) n (fun i _ => hT i)) _ hc,
    foldF_mul_left hR hc hT n]
  exact foldF_congr n (fun i _ => hR.mulComm _ hc _ (hT i))

/-- A telescoping sum collapses to its ends.

`sum_{k<m} (T k - T (k+1)) = T 0 - T m`. The tower telescopes in several places
over the reals; this is the ring-level statement, and the whole content is
`ringSub_trans` applied once per step. -/
theorem foldF_telescope {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) {T : Nat → ZFSet.{u}} (hT : ∀ k, T k ∈ R) :
    ∀ m : Nat,
      foldF add zero (fun k => ringSub R add zero (T k) (T (k + 1))) m
        = ringSub R add zero (T 0) (T m)
  | 0 => (ringSub_self hR (hT 0)).symm
  | m + 1 => by
    show opAt add (foldF add zero (fun k => ringSub R add zero (T k) (T (k + 1))) m)
        (ringSub R add zero (T m) (T (m + 1))) = _
    rw [foldF_telescope hR hT m]
    exact ringSub_trans hR (hT 0) (hT m) (hT (m + 1))

#print axioms foldF_telescope
/-- The triple product term. -/
def convTerm (R add mul zero f g h : ZFSet.{u}) (k a b : Nat) : ZFSet.{u} :=
  opAt mul (opAt mul (app f (ofNat.{u} a)) (app g (ofNat.{u} b)))
    (app h (ofNat.{u} (k - a - b)))

/-- A convolution term lies in the ring, over a semiring: the term is a
product of three coefficients, so closure of multiplication is the whole
proof. `IsPolyOver` already says the coefficients are in `R`. -/
theorem convTerm_mem_semi {R add mul zero one f g h : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) (hh : IsPolyOver R zero h)
    (k a b : Nat) : convTerm R add mul zero f g h k a b ∈ R :=
  mulAt_mem_semi hR (mulAt_mem_semi hR (coeff_mem hf (ofNat_mem_omega a))
    (coeff_mem hg (ofNat_mem_omega b))) (coeff_mem hh (ofNat_mem_omega (k - a - b)))

/-- A convolution coefficient lies in the ring, over a semiring. A fold of
products over the additive monoid -- `isCommMonoid_ringAdd` built that monoid
from the additive GROUP, and a semiring simply carries it as `addMonoid`. -/
theorem convCoeff_mem_semi {R add mul zero one f g : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) (k : Nat) :
    convCoeff R add mul zero f g k ∈ R :=
  foldF_mem hR.addMonoid (k + 1)
    (fun i _ => mulAt_mem_semi hR (coeff_mem hf (ofNat_mem_omega i))
      (coeff_mem hg (ofNat_mem_omega (k - i))))

#print axioms Algebra.convTerm_mem_semi
#print axioms Algebra.convCoeff_mem_semi

/-! ## The unit, and the ring

`polyOne` is `1, 0, 0, …`. Multiplying by it leaves every coefficient alone,
because in `∑_{i≤k} f_i·1_{k-i}` only the last term survives. -/

def unitCoeff (zero one : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => one
  | _ + 1 => zero

def polyOne (R zero one : ZFSet.{u}) : ZFSet.{u} := polyOfSeq R (unitCoeff zero one)

theorem unitCoeff_mem {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    ∀ k : Nat, unitCoeff zero one k ∈ R
  | 0 => hR.mem_one
  | _ + 1 => hR.addGroup.mem_e

theorem app_polyOne {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) (k : Nat) :
    app (polyOne R zero one) (ofNat.{u} k) = unitCoeff zero one k :=
  app_polyOfSeq (unitCoeff_mem hR) k

theorem isPolyOver_polyOne {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    IsPolyOver R zero (polyOne R zero one) :=
  isPolyOver_polyOfSeq (unitCoeff_mem hR) (N := 1) (fun i hi => by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rfl)

/-- `polyOne` lies in the polynomial ring. The membership form of
`isPolyOver_polyOne`, which five proofs re-derived inline. -/
theorem polyOne_mem {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    polyOne R zero one ∈ PolyRing R zero :=
  (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyOne hR)

/-- And the membership form of `isPolyOver_polyNeg`. -/
theorem polyNeg_mem {R add mul zero one f : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) :
    polyNeg R add zero f ∈ PolyRing R zero :=
  (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyNeg hR hf)

/-- A fold whose every term is a multiple of `d` is a multiple of `d`.

The one fact Eisenstein's criterion needs that `FinProd.lean` does not already
carry. `foldF_drop_last` splits the convolution at its top index and isolates
`g_k·h_0`; this says the rest of the fold keeps the common factor, turning *`p`
divides every earlier coefficient of `g`* into `p` divides the partial sum.

Same induction as `foldF_zeros` one step weaker: there the terms are `zero`,
here they are `d` times something, and the step is left distributivity instead
of `ringAdd_zero`. -/
theorem foldF_multiple {R add mul zero one d : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hd : d ∈ R) {T : Nat → ZFSet.{u}} :
    ∀ n : Nat, (∀ i, i < n → ∃ c, c ∈ R ∧ T i = opAt mul d c) →
      ∃ c, c ∈ R ∧ foldF add zero T n = opAt mul d c
  | 0, _ => ⟨zero, hR.addGroup.mem_e, (mul_zero_of_isRing hR hd).symm⟩
  | n + 1, hmul => by
    obtain ⟨c₁, hc₁, he₁⟩ := foldF_multiple hR hd n (fun i hi => hmul i (by omega))
    obtain ⟨c₂, hc₂, he₂⟩ := hmul n (by omega)
    refine ⟨opAt add c₁ c₂, addAt_mem hR hc₁ hc₂, ?_⟩
    show opAt add (foldF add zero T n) (T n) = _
    rw [he₁, he₂, hR.distrib d hd c₁ hc₁ c₂ hc₂]

/-- A divisor of a sum and of one summand divides the other.

Stated with the divisibility written out as an existential rather than through a
predicate: the tree has `Divides` for `Nat`, `DividesSet` for `ω`, `Dvd` for the
Eisenstein integers and `polyDvd` for polynomials, but nothing general over a
ring, and one lemma is not enough to justify a fifth notion.

Paired with `convCoeff_split`, this turns *`p` divides the product's `k`-th
coefficient* into `p` divides `f_k·g_0` -- the step the least-index argument
closes on. -/
theorem dvd_of_addAt_dvd {R add mul zero one d a b : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hd : d ∈ R) (ha : a ∈ R) (hb : b ∈ R)
    (h1 : ∃ c, c ∈ R ∧ a = opAt mul d c)
    (h2 : ∃ c, c ∈ R ∧ opAt add a b = opAt mul d c) :
    ∃ c, c ∈ R ∧ b = opAt mul d c := by
  obtain ⟨c₁, hc₁, he₁⟩ := h1
  obtain ⟨c₂, hc₂, he₂⟩ := h2
  refine ⟨ringSub R add zero c₂ c₁, ringSub_mem hR hc₂ hc₁, ?_⟩
  rw [ringMul_sub hR hd hc₂ hc₁, ← he₁, ← he₂]
  have hcomm : opAt add a b = opAt add b a := ringAdd_comm hR ha hb
  rw [hcomm, ringAdd_sub_cancel hR hb ha]

/-- THE CONVOLUTION SPLIT EISENSTEIN'S CRITERION TURNS ON.

If `d` divides every coefficient of `f` below index `k`, then the `k`-th
coefficient of `f·g` is `d·c` plus the single term `f_k·g_0`:

    convCoeff f g k = d·c + f_k·g_0

Every other term of the convolution pairs a coefficient of `f` below `k` --
divisible by
`d` -- against something, so `foldF_multiple` carries the factor out of the
whole partial sum, and `foldF`'s own step equation isolates the last term.

The criterion costs nothing beyond arithmetic. The textbook proof reduces
mod `p`, gets `x^n` in `(ℤ/p)[x]`, and appeals to unique factorisation. Read
off the convolution instead, the statement is about divisibility in the ring
itself: no quotient, no homomorphism, no factorisation theory. -/
theorem convCoeff_split {R add mul zero one d f g : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hd : d ∈ R)
    (hg : IsPolyOver R zero g) (k : Nat)
    (hlow : ∀ i, i < k -> ∃ c, c ∈ R ∧ app f (ofNat.{u} i) = opAt mul d c) :
    ∃ c, c ∈ R ∧ convCoeff R add mul zero f g k
      = opAt add (opAt mul d c)
          (opAt mul (app f (ofNat.{u} k)) (app g (ofNat.{u} 0))) := by
  have hterms : ∀ i, i < k -> ∃ c, c ∈ R ∧
      opAt mul (app f (ofNat.{u} i)) (app g (ofNat.{u} (k - i))) = opAt mul d c := by
    intro i hi
    obtain ⟨c, hc, he⟩ := hlow i hi
    have hgi : app g (ofNat.{u} (k - i)) ∈ R := coeff_mem hg (ofNat_mem_omega _)
    refine ⟨opAt mul c (app g (ofNat.{u} (k - i))), mulAt_mem hR hc hgi, ?_⟩
    rw [he, hR.mulAssoc d hd c hc _ hgi]
  obtain ⟨c, hc, he⟩ := foldF_multiple hR hd k hterms
  refine ⟨c, hc, ?_⟩
  show opAt add (foldF add zero
      (fun i => opAt mul (app f (ofNat.{u} i)) (app g (ofNat.{u} (k - i)))) k)
      (opAt mul (app f (ofNat.{u} k)) (app g (ofNat.{u} (k - k)))) = _
  rw [he, Nat.sub_self]

/-- The least coefficient index that `d` does not divide.

Eisenstein's argument needs the SMALLEST `k` at which `d` fails to divide the
coefficient, so that everything below it is divisible and `convCoeff_split`
applies. The downward search of NatSearch supplies it from any witness, given
the predicate is decidable.

Decidability is a hypothesis rather than a fact: divisibility in an arbitrary
ring is not decidable, and over `ℤ` -- the only ring the criterion is stated for
-- it is. Taking it as a premise keeps the lemma at the level its proof works
at, and lets the caller discharge it where the carrier is concrete. -/
theorem exists_least_not_dvd {R mul d f : ZFSet.{u}}
    (hdec : ∀ i : Nat, (∃ c, c ∈ R ∧ app f (ofNat.{u} i) = opAt mul d c)
      ∨ ¬ (∃ c, c ∈ R ∧ app f (ofNat.{u} i) = opAt mul d c))
    {N : Nat} (hN : ¬ ∃ c, c ∈ R ∧ app f (ofNat.{u} N) = opAt mul d c) :
    ∃ k : Nat, (¬ ∃ c, c ∈ R ∧ app f (ofNat.{u} k) = opAt mul d c)
      ∧ ∀ i, i < k -> ∃ c, c ∈ R ∧ app f (ofNat.{u} i) = opAt mul d c := by
  have hQ : ∀ n : Nat,
      (¬ ∃ c, c ∈ R ∧ app f (ofNat.{u} n) = opAt mul d c)
        ∨ ¬ ¬ (∃ c, c ∈ R ∧ app f (ofNat.{u} n) = opAt mul d c) := by
    intro n
    rcases hdec n with h | h
    · exact Or.inr (fun hn => hn h)
    · exact Or.inl h
  obtain ⟨k, hk, hbelow⟩ := exists_least hQ N hN
  refine ⟨k, hk, ?_⟩
  intro i hi
  rcases hdec i with h | h
  · exact h
  · exact absurd h (fun hn => hbelow i hi hn)

/-- THE LEAST-INDEX STEP OF EISENSTEIN'S CRITERION.

If `d` is prime, divides every coefficient of `f` below `k`, and divides neither
`f`'s `k`-th coefficient nor `g`'s constant term, then it does not divide the
`k`-th coefficient of `f·g`.

`convCoeff_split` writes that coefficient as `d·c` plus the product of those
two; if `d` divided it, `dvd_of_addAt_dvd` would give `d` dividing the product,
and primality then forces `d` to divide one of the two factors.

Primality is a HYPOTHESIS in the divisibility form the statement uses, not an
appeal to a primality predicate: the tree has one per carrier and none over a
general ring, and the argument needs only this clause about being prime. -/
theorem not_dvd_convCoeff {R add mul zero one d f g : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hd : d ∈ R)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) (k : Nat)
    (hlow : ∀ i, i < k -> ∃ c, c ∈ R ∧ app f (ofNat.{u} i) = opAt mul d c)
    (hprime : ∀ a b, a ∈ R -> b ∈ R ->
        (∃ c, c ∈ R ∧ opAt mul a b = opAt mul d c) ->
        (∃ c, c ∈ R ∧ a = opAt mul d c) ∨ (∃ c, c ∈ R ∧ b = opAt mul d c))
    (hfk : ¬ ∃ c, c ∈ R ∧ app f (ofNat.{u} k) = opAt mul d c)
    (hg0 : ¬ ∃ c, c ∈ R ∧ app g (ofNat.{u} 0) = opAt mul d c) :
    ¬ ∃ c, c ∈ R ∧ convCoeff R add mul zero f g k = opAt mul d c := by
  intro hcon
  obtain ⟨c, hc, hsplit⟩ := convCoeff_split hR hd hg k hlow
  have hfkm : app f (ofNat.{u} k) ∈ R := coeff_mem hf (ofNat_mem_omega _)
  have hg0m : app g (ofNat.{u} 0) ∈ R := coeff_mem hg (ofNat_mem_omega _)
  have hsum : ∃ e, e ∈ R ∧
      opAt add (opAt mul d c) (opAt mul (app f (ofNat.{u} k)) (app g (ofNat.{u} 0)))
        = opAt mul d e := by
    rw [← hsplit]; exact hcon
  have hprod := dvd_of_addAt_dvd hR hd (mulAt_mem hR hd hc)
    (mulAt_mem hR hfkm hg0m) ⟨c, hc, rfl⟩ hsum
  rcases hprime _ _ hfkm hg0m hprod with h | h
  · exact hfk h
  · exact hg0 h

/-- The Eisenstein data for a candidate factorisation `g·h`.

Both factors are polynomials over `R`; divisibility of `g`'s coefficients by `d`
is decidable index by index; `d` is prime in the divisibility form the argument
uses; and `d` does not divide `h`'s constant term.

Bundled because every step of the criterion consumes exactly these four and
differs only in what it concludes. Decidability and primality are clauses rather
than appeals to a predicate for the reason `not_dvd_convCoeff` gives: divisibility
in an arbitrary ring is neither decidable nor equipped with a primality notion
this tree defines over a general carrier. -/
structure IsEisenstein (R mul zero d g h : ZFSet.{u}) : Prop where
  polyG : IsPolyOver R zero g
  polyH : IsPolyOver R zero h
  dec : ∀ i : Nat, (∃ c, c ∈ R ∧ app g (ofNat.{u} i) = opAt mul d c)
    ∨ ¬ (∃ c, c ∈ R ∧ app g (ofNat.{u} i) = opAt mul d c)
  prime : ∀ a b, a ∈ R -> b ∈ R ->
      (∃ c, c ∈ R ∧ opAt mul a b = opAt mul d c) ->
      (∃ c, c ∈ R ∧ a = opAt mul d c) ∨ (∃ c, c ∈ R ∧ b = opAt mul d c)
  const : ¬ ∃ c, c ∈ R ∧ app h (ofNat.{u} 0) = opAt mul d c

/-- EISENSTEIN'S CRITERION, its substantive half.

If `d` is prime, divides the first `n` coefficients of the product `g·h`, and
does not divide `h`'s constant term, then the least index at which `d` fails to
divide `g` is at least `n`.

That is the whole content of the criterion. The usual conclusion -- that a
polynomial satisfying the Eisenstein conditions is irreducible -- follows by
degree counting: `n` is the degree, so `g` has at least `n` coefficients before
its first `d`-free one, hence degree at least `n`, hence `h` is constant.

No reduction mod `d`, no quotient ring, no unique factorisation. The textbook
route passes to `(R/d)[x]`, observes the product is `x^n`, and appeals to
factorisation there. Read off the convolution instead and the argument is
divisibility in `R` throughout, so nothing here costs a principle. -/
theorem eisenstein_least_index {R add mul zero one d g h : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hd : d ∈ R)
    (he : IsEisenstein R mul zero d g h)
    (n : Nat)
    (hlow : ∀ i, i < n -> ∃ c, c ∈ R ∧
      convCoeff R add mul zero g h i = opAt mul d c)
    {N : Nat} (hN : ¬ ∃ c, c ∈ R ∧ app g (ofNat.{u} N) = opAt mul d c) :
    ∃ k : Nat, n <= k ∧ (¬ ∃ c, c ∈ R ∧ app g (ofNat.{u} k) = opAt mul d c)
      ∧ ∀ i, i < k -> ∃ c, c ∈ R ∧ app g (ofNat.{u} i) = opAt mul d c := by
  obtain ⟨k, hk, hbelow⟩ := exists_least_not_dvd he.dec hN
  refine ⟨k, ?_, hk, hbelow⟩
  rcases Nat.lt_or_ge k n with hlt | hge
  · exact absurd (hlow k hlt)
      (not_dvd_convCoeff hR hd he.polyG he.polyH k hbelow he.prime hk he.const)
  · exact hge

/-- Eisenstein forces a non-zero coefficient at or above the top index.

`eisenstein_least_index` returns a `k ≥ n` at which `d` does not divide `g`.
Nothing divides zero except by dividing it -- `d·0 = 0` -- so that coefficient
is non-zero.

This is the form the degree argument consumes: a non-vanishing coefficient at
index at least `n` puts `g`'s degree at least `n`, and with the degrees adding
to `n` the other factor is constant. Stated separately because degree
additivity for a product is not in this file and this step does not need it. -/
theorem eisenstein_nonzero_high {R add mul zero one d g h : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hd : d ∈ R)
    (he : IsEisenstein R mul zero d g h)
    (n : Nat)
    (hlow : ∀ i, i < n -> ∃ c, c ∈ R ∧
      convCoeff R add mul zero g h i = opAt mul d c)
    {N : Nat} (hN : ¬ ∃ c, c ∈ R ∧ app g (ofNat.{u} N) = opAt mul d c) :
    ∃ k : Nat, n <= k ∧ app g (ofNat.{u} k) ≠ zero := by
  obtain ⟨k, hk, hnd, -⟩ := eisenstein_least_index hR hd he n hlow hN
  refine ⟨k, hk, ?_⟩
  intro hzero
  exact hnd ⟨zero, hR.addGroup.mem_e, by rw [hzero, mul_zero_of_isRing hR hd]⟩

/-- A fold whose terms all vanish is `zero`. -/
theorem foldF_zeros {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one)
    {T : Nat → ZFSet.{u}} : ∀ n : Nat, (∀ i, i < n → T i = zero) →
      foldF add zero T n = zero
  | 0, _ => rfl
  | n + 1, hz => by
    show opAt add (foldF add zero T n) (T n) = zero
    rw [foldF_zeros hR n (fun i hi => hz i (by omega)), hz n (by omega),
      ringAdd_zero hR hR.addGroup.mem_e]

/-- A fold in which only the last term survives. -/
theorem foldF_extend {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) {F : Nat → ZFSet.{u}}
    (hF : ∀ i, F i ∈ R) (m d : Nat) (hz : ∀ i, i < d → F (m + i) = zero) :
    foldF add zero F (m + d) = foldF add zero F m := by
  rw [foldF_split (isCommMonoid_ringAdd hR) m d (fun i _ => hF i),
    foldF_zeros hR d hz,
    ringAdd_zero hR (foldF_mem (isCommMonoid_ringAdd hR) m (fun i _ => hF i))]

#print axioms foldF_extend

theorem foldF_last {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one)
    {T : Nat → ZFSet.{u}} {k : Nat} (hT : T k ∈ R) (hz : ∀ i, i < k → T i = zero) :
    foldF add zero T (k + 1) = T k := by
  show opAt add (foldF add zero T k) (T k) = T k
  rw [foldF_zeros hR k hz, ringZero_add hR hT]

theorem convCoeff_one {R add mul zero one f : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) (k : Nat) :
    convCoeff R add mul zero f (polyOne R zero one) k = app f (ofNat.{u} k) := by
  have hlast : ∀ i : Nat, i < k →
      opAt mul (app f (ofNat.{u} i)) (app (polyOne R zero one) (ofNat.{u} (k - i))) = zero := by
    intro i hi
    rw [app_polyOne hR (k - i), show k - i = (k - i - 1) + 1 by omega]
    exact mul_zero_of_isRing hR (coeff_mem hf (ofNat_mem_omega i))
  rw [convCoeff, foldF_last hR (T := fun i => opAt mul (app f (ofNat.{u} i))
      (app (polyOne R zero one) (ofNat.{u} (k - i))))
    (mulAt_mem hR (coeff_mem hf (ofNat_mem_omega k))
      (coeff_mem (isPolyOver_polyOne hR) (ofNat_mem_omega (k - k)))) hlast]
  show opAt mul (app f (ofNat.{u} k)) (app (polyOne R zero one) (ofNat.{u} (k - k))) = _
  rw [show k - k = 0 by omega, app_polyOne hR 0]
  exact hR.mul_one _ (coeff_mem hf (ofNat_mem_omega k))

/-- A fold of zeros is zero, over a semiring. `foldF_zeros` closes the
step with `ringAdd_zero`, the RIGHT unit law; `IsCommMonoid` states only the
left one, and here the left suffices because the accumulated fold has already
been rewritten to `zero`. -/
theorem foldF_zeros_semi {R add mul zero one : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) {T : Nat → ZFSet.{u}} :
    ∀ n : Nat, (∀ i, i < n → T i = zero) → foldF add zero T n = zero
  | 0, _ => rfl
  | n + 1, hz => by
    show opAt add (foldF add zero T n) (T n) = zero
    rw [foldF_zeros_semi hR n (fun i hi => hz i (by omega)), hz n (by omega),
      hR.addMonoid.left_id _ hR.addMonoid.mem_e]

/-- A fold in which only the last term survives, over a semiring. -/
theorem foldF_last_semi {R add mul zero one : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) {T : Nat → ZFSet.{u}} {k : Nat}
    (hT : T k ∈ R) (hz : ∀ i, i < k → T i = zero) :
    foldF add zero T (k + 1) = T k := by
  show opAt add (foldF add zero T k) (T k) = T k
  rw [foldF_zeros_semi hR k hz, hR.addMonoid.left_id _ hT]

/-- The unit sequence lands in the ring, over a semiring: `one` at index
zero and `zero` after. `unitCoeff_mem` reads the zero off the additive GROUP,
but only as its identity element -- `addMonoid.mem_e` is the same element and
needs no inverse. -/
theorem unitCoeff_mem_semi {R add mul zero one : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) :
    ∀ k : Nat, unitCoeff zero one k ∈ R
  | 0 => hR.mem_one
  | _ + 1 => hR.addMonoid.mem_e

/-- `polyOne`'s coefficients, over a semiring. -/
theorem app_polyOne_semi {R add mul zero one : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (k : Nat) :
    app (polyOne R zero one) (ofNat.{u} k) = unitCoeff zero one k :=
  app_polyOfSeq (unitCoeff_mem_semi hR) k

/-- `polyOne` is a polynomial over the semiring. -/
theorem isPolyOver_polyOne_semi {R add mul zero one : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) :
    IsPolyOver R zero (polyOne R zero one) :=
  isPolyOver_polyOfSeq (unitCoeff_mem_semi hR) (N := 1) (fun i hi => by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rfl)

/-- `polyOne` is a right unit for the convolution, over a semiring.

Every summand past the last is `f_i · 0`, which a semiring ASSUMES is zero as
`mulZero` where a ring proves it by cancelling -- so this is the first place
in the polynomial construction where the dropped inverse is visibly paid for
by an axiom rather than a theorem. -/
theorem convCoeff_one_semi {R add mul zero one f : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    (hf : IsPolyOver R zero f) (k : Nat) :
    convCoeff R add mul zero f (polyOne R zero one) k = app f (ofNat.{u} k) := by
  have hlast : ∀ i : Nat, i < k →
      opAt mul (app f (ofNat.{u} i)) (app (polyOne R zero one) (ofNat.{u} (k - i))) = zero := by
    intro i hi
    rw [app_polyOne_semi hR (k - i), show k - i = (k - i - 1) + 1 by omega]
    exact hR.mulZero _ (coeff_mem hf (ofNat_mem_omega i))
  rw [convCoeff, foldF_last_semi hR (T := fun i => opAt mul (app f (ofNat.{u} i))
      (app (polyOne R zero one) (ofNat.{u} (k - i))))
    (mulAt_mem_semi hR (coeff_mem hf (ofNat_mem_omega k))
      (coeff_mem (isPolyOver_polyOne_semi hR) (ofNat_mem_omega (k - k)))) hlast]
  show opAt mul (app f (ofNat.{u} k)) (app (polyOne R zero one) (ofNat.{u} (k - k))) = _
  rw [show k - k = 0 by omega, app_polyOne_semi hR 0]
  exact hR.mul_one _ (coeff_mem hf (ofNat_mem_omega k))

#print axioms Algebra.foldF_zeros_semi

#print axioms Algebra.foldF_last_semi
#print axioms Algebra.unitCoeff_mem_semi
#print axioms Algebra.app_polyOne_semi
#print axioms Algebra.isPolyOver_polyOne_semi
#print axioms Algebra.convCoeff_one_semi

/-! ## The ring -/

def polyMulOp (R add mul zero : ZFSet.{u}) : ZFSet.{u} :=
  graphOn (prod (PolyRing R zero) (PolyRing R zero)) (PolyRing R zero)
    (fun p => polyMul R add mul zero (fst p) (snd p))

theorem polyMul_mem {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    ∀ p, p ∈ prod (PolyRing R zero) (PolyRing R zero) →
      polyMul R add mul zero (fst p) (snd p) ∈ PolyRing R zero := by
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff p _ _).mp hp
  rw [fst_opair, snd_opair]
  exact (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyMul hR
    ((mem_polyRing_iff _ _ _).mp ha) ((mem_polyRing_iff _ _ _).mp hb))

theorem opAt_polyMulOp {R add mul zero one f g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : f ∈ PolyRing R zero) (hg : g ∈ PolyRing R zero) :
    opAt (polyMulOp R add mul zero) f g = polyMul R add mul zero f g := by
  show app (polyMulOp R add mul zero) (opair f g) = _
  rw [polyMulOp, app_graphOn (polyMul_mem hR) (opair_mem_prod hf hg), fst_opair, snd_opair]

/-- The addition operation applied, over a semiring -- `graphOn`'s value
at a pair, once both arguments are known to be polynomials. -/
theorem opAt_polyAddOp_semi {R add mul zero one f g : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    (hf : f ∈ PolyRing R zero) (hg : g ∈ PolyRing R zero) :
    opAt (polyAddOp R add zero) f g = polyAdd R add f g := by
  have hmaps : ∀ p, p ∈ prod (PolyRing R zero) (PolyRing R zero) →
      polyAdd R add (fst p) (snd p) ∈ PolyRing R zero := by
    intro p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff p _ _).mp hp
    rw [fst_opair, snd_opair]
    exact (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyAdd_semi hR
      ((mem_polyRing_iff _ _ _).mp ha) ((mem_polyRing_iff _ _ _).mp hb))
  show app (polyAddOp R add zero) (opair f g) = _
  rw [polyAddOp, app_graphOn hmaps (opair_mem_prod hf hg), fst_opair, snd_opair]

/-- Polynomial addition is commutative, over a semiring -- coefficientwise
from the additive monoid's own commutativity. -/
theorem isAbelian_polyAdd_semi {R add mul zero one : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) :
    IsAbelian (PolyRing R zero) (polyAddOp R add zero) := by
  intro a ha b hb
  have hpa := (mem_polyRing_iff _ _ _).mp ha
  have hpb := (mem_polyRing_iff _ _ _).mp hb
  rw [opAt_polyAddOp_semi hR ha hb, opAt_polyAddOp_semi hR hb ha]
  refine poly_ext (isPolyOver_polyAdd_semi hR hpa hpb) (isPolyOver_polyAdd_semi hR hpb hpa)
    (fun w hw => ?_)
  rw [app_polyAdd_semi hR hpa hpb hw, app_polyAdd_semi hR hpb hpa hw,
    hR.addMonoid.comm _ (coeff_mem hpa hw) _ (coeff_mem hpb hw)]

/-- Polynomial addition is a commutative MONOID, over a semiring.

This REPLACES `isGroup_polyAdd` rather than widening it: the group's inverse
clause is `polyNeg`, and a semiring has no negation to build it from. The
monoid clauses are the same proofs -- closure, the zero polynomial,
associativity and the left unit, all coefficientwise -- and commutativity comes
from `isAbelian_polyAdd_semi` in place of the inverse. This is the second of
the module row's two axes, at the polynomial level: a polynomial semiring's
additive structure is exactly this. -/
theorem isCommMonoid_polyAdd_semi {R add mul zero one : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) :
    IsCommMonoid (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero) := by
  have hmaps : ∀ p, p ∈ prod (PolyRing R zero) (PolyRing R zero) →
      polyAdd R add (fst p) (snd p) ∈ PolyRing R zero := by
    intro p hp
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff p _ _).mp hp
    rw [fst_opair, snd_opair]
    exact (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyAdd_semi hR
      ((mem_polyRing_iff _ _ _).mp ha) ((mem_polyRing_iff _ _ _).mp hb))
  have hzero : polyZero R zero ∈ PolyRing R zero :=
    (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyZero_semi hR)
  refine ⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range, hzero,
    ?_, ?_, ?_⟩
  · intro a ha b hb c hc
    have hpa := (mem_polyRing_iff _ _ _).mp ha
    have hpb := (mem_polyRing_iff _ _ _).mp hb
    have hpc := (mem_polyRing_iff _ _ _).mp hc
    have hab := isPolyOver_polyAdd_semi hR hpa hpb
    have hbc := isPolyOver_polyAdd_semi hR hpb hpc
    rw [opAt_polyAddOp_semi hR ha hb, opAt_polyAddOp_semi hR hb hc,
      opAt_polyAddOp_semi hR ((mem_polyRing_iff _ _ _).mpr hab) hc,
      opAt_polyAddOp_semi hR ha ((mem_polyRing_iff _ _ _).mpr hbc)]
    refine poly_ext (isPolyOver_polyAdd_semi hR hab hpc) (isPolyOver_polyAdd_semi hR hpa hbc)
      (fun w hw => ?_)
    rw [app_polyAdd_semi hR hab hpc hw, app_polyAdd_semi hR hpa hbc hw,
      app_polyAdd_semi hR hpa hpb hw, app_polyAdd_semi hR hpb hpc hw,
      hR.addMonoid.assoc _ (coeff_mem hpa hw) _ (coeff_mem hpb hw) _ (coeff_mem hpc hw)]
  · intro a ha
    have hpa := (mem_polyRing_iff _ _ _).mp ha
    rw [opAt_polyAddOp_semi hR hzero ha]
    refine poly_ext (isPolyOver_polyAdd_semi hR (isPolyOver_polyZero_semi hR) hpa)
      hpa (fun w hw => ?_)
    rw [app_polyAdd_semi hR (isPolyOver_polyZero_semi hR) hpa hw, app_polyZero_semi hR hw,
      hR.addMonoid.left_id _ (coeff_mem hpa hw)]
  · intro a ha b hb
    exact isAbelian_polyAdd_semi hR a ha b hb

/-- The zero polynomial annihilates on the LEFT, over a semiring:
`convCoeff polyZero g k = zero`.

Every summand is `0 . g_(k-i)`, which is `zero` by the semiring's `zeroMul`
AXIOM -- a ring proves the same step by cancelling, so `isRing_polyRing` never
had to state this clause at all. -/
theorem convCoeff_zero_left_semi {R add mul zero one g : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (hg : IsPolyOver R zero g) (k : Nat) :
    convCoeff R add mul zero (polyZero R zero) g k = zero := by
  rw [convCoeff]
  refine foldF_zeros_semi hR (k + 1) (fun i _ => ?_)
  show opAt mul (app (polyZero R zero) (ofNat.{u} i)) (app g (ofNat.{u} (k - i))) = zero
  rw [app_polyZero_semi hR (ofNat_mem_omega i)]
  exact hR.zeroMul _ (coeff_mem hg (ofNat_mem_omega (k - i)))

/-- The zero polynomial annihilates on the RIGHT, over a semiring. The
mirror of the left form, on `mulZero`. -/
theorem convCoeff_zero_right_semi {R add mul zero one f : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (hf : IsPolyOver R zero f) (k : Nat) :
    convCoeff R add mul zero f (polyZero R zero) k = zero := by
  rw [convCoeff]
  refine foldF_zeros_semi hR (k + 1) (fun i _ => ?_)
  show opAt mul (app f (ofNat.{u} i)) (app (polyZero R zero) (ofNat.{u} (k - i))) = zero
  rw [app_polyZero_semi hR (ofNat_mem_omega (k - i))]
  exact hR.mulZero _ (coeff_mem hf (ofNat_mem_omega i))

/-- `polyOne` is a LEFT unit for the convolution, over a semiring.

`convCoeff_one` does the right-hand case with `foldF_last`, because there the
surviving index is the last one. Here it is the FIRST, so the fold is peeled
by `foldF_cons` instead and the tail -- every term carrying `unitCoeff (i+1)`,
which is `zero` -- collapses by `zeroMul`. The two unit laws are genuinely
different proofs, and a commutative ring needs only one of them. -/
theorem convCoeff_one_left_semi {R add mul zero one g : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (hg : IsPolyOver R zero g) (k : Nat) :
    convCoeff R add mul zero (polyOne R zero one) g k = app g (ofNat.{u} k) := by
  have hone := isPolyOver_polyOne_semi hR
  rw [convCoeff, foldF_cons hR.addMonoid k (fun i _ =>
    mulAt_mem_semi hR (coeff_mem hone (ofNat_mem_omega i))
      (coeff_mem hg (ofNat_mem_omega (k - i))))]
  have htail : foldF add zero
      (fun i => opAt mul (app (polyOne R zero one) (ofNat.{u} (i + 1)))
        (app g (ofNat.{u} (k - (i + 1))))) k = zero := by
    refine foldF_zeros_semi hR k (fun i _ => ?_)
    rw [app_polyOne_semi hR (i + 1)]
    exact hR.zeroMul _ (coeff_mem hg (ofNat_mem_omega (k - (i + 1))))
  rw [htail, right_id_monoid hR.addMonoid
    (mulAt_mem_semi hR (coeff_mem hone (ofNat_mem_omega 0))
      (coeff_mem hg (ofNat_mem_omega (k - 0))))]
  show opAt mul (app (polyOne R zero one) (ofNat.{u} 0)) (app g (ofNat.{u} (k - 0))) = _
  rw [app_polyOne_semi hR 0, show k - 0 = k by omega]
  exact hR.one_mul _ (coeff_mem hg (ofNat_mem_omega k))

/-- The convolution distributes over addition on the RIGHT, over a
semiring: `(f+g) * h = f*h + g*h` coefficientwise.

`convCoeff_distrib` is the LEFT form and uses `distrib`; this uses
`distribRight`, which `IsRing` derives from `mulComm` and so never states.
`foldF_add` splits the sum the same way in both. -/
theorem convCoeff_distrib_right_semi {R add mul zero one f g h : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (hf : IsPolyOver R zero f)
    (hg : IsPolyOver R zero g) (hh : IsPolyOver R zero h) (k : Nat) :
    convCoeff R add mul zero (polyAdd R add f g) h k
      = opAt add (convCoeff R add mul zero f h k) (convCoeff R add mul zero g h k) := by
  rw [convCoeff, foldF_congr (F := fun i => opAt mul (app (polyAdd R add f g) (ofNat.{u} i))
      (app h (ofNat.{u} (k - i))))
    (G := fun i => opAt add (opAt mul (app f (ofNat.{u} i)) (app h (ofNat.{u} (k - i))))
      (opAt mul (app g (ofNat.{u} i)) (app h (ofNat.{u} (k - i))))) (k + 1) (fun i _ => by
      show opAt mul (app (polyAdd R add f g) (ofNat.{u} i)) (app h (ofNat.{u} (k - i))) = _
      rw [app_polyAdd_semi hR hf hg (ofNat_mem_omega i),
        hR.distribRight _ (coeff_mem hf (ofNat_mem_omega i))
          _ (coeff_mem hg (ofNat_mem_omega i))
          _ (coeff_mem hh (ofNat_mem_omega (k - i)))]),
    foldF_add hR.addMonoid (k + 1)
      (fun i _ => mulAt_mem_semi hR (coeff_mem hf (ofNat_mem_omega i))
        (coeff_mem hh (ofNat_mem_omega (k - i))))
      (fun i _ => mulAt_mem_semi hR (coeff_mem hg (ofNat_mem_omega i))
        (coeff_mem hh (ofNat_mem_omega (k - i))))]
  rfl

#print axioms Algebra.convCoeff_zero_left_semi
#print axioms Algebra.convCoeff_zero_right_semi
#print axioms Algebra.convCoeff_one_left_semi
#print axioms Algebra.convCoeff_distrib_right_semi

#print axioms Algebra.isCommMonoid_polyAdd_semi

/-- The convolution vanishes past the sum of the degrees, over a
semiring. Each summand has a factor beyond one polynomial's degree, so it is
`zero` by `zeroMul` or `mulZero` -- ASSUMED here, proved by cancelling in a
ring. -/
theorem convCoeff_eq_zero_semi {R add mul zero one f g : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) {Nf Ng : Nat}
    (hNf : ∀ i : Nat, Nf ≤ i → app f (ofNat.{u} i) = zero)
    (hNg : ∀ i : Nat, Ng ≤ i → app g (ofNat.{u} i) = zero)
    {k : Nat} (hk : Nf + Ng ≤ k) : convCoeff R add mul zero f g k = zero := by
  have hzeros : ∀ i : Nat, i < k + 1 →
      opAt mul (app f (ofNat.{u} i)) (app g (ofNat.{u} (k - i))) = zero := by
    intro i hi
    rcases Nat.lt_or_ge i Nf with hlt | hge
    · rw [hNg (k - i) (by omega), hR.mulZero _ (coeff_mem hf (ofNat_mem_omega i))]
    · rw [hNf i hge, hR.zeroMul _ (coeff_mem hg (ofNat_mem_omega (k - i)))]
  -- a fold of zeros is zero
  have hall : ∀ n : Nat, n < k + 2 →
      foldF add zero (fun i => opAt mul (app f (ofNat.{u} i)) (app g (ofNat.{u} (k - i)))) n
        = zero := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      show opAt add (foldF add zero
        (fun i => opAt mul (app f (ofNat.{u} i)) (app g (ofNat.{u} (k - i)))) j)
          (opAt mul (app f (ofNat.{u} j)) (app g (ofNat.{u} (k - j)))) = zero
      rw [ih (by omega), hzeros j (by omega), hR.addMonoid.left_id _ hR.addMonoid.mem_e]
  exact hall (k + 1) (by omega)

/-- `polyMul` is a polynomial over the semiring -- the `IsPolyOver` form
of `polyMul_mem_semi`. -/
theorem isPolyOver_polyMul_semi {R add mul zero one f g : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) :
    IsPolyOver R zero (polyMul R add mul zero f g) := by
  obtain ⟨Nf, hNf⟩ := hf.right.right.right
  obtain ⟨Ng, hNg⟩ := hg.right.right.right
  exact isPolyOver_polyOfSeq (fun k => convCoeff_mem_semi hR hf hg k)
    (N := Nf + Ng) (fun i hi => convCoeff_eq_zero_semi hR hf hg hNf hNg hi)

/-- Coefficients of a product, over a semiring: the `k`-th is the
convolution, placed in `R` by `convCoeff_mem_semi`. -/
theorem app_polyMul_semi {R add mul zero one f g : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) (k : Nat) :
    app (polyMul R add mul zero f g) (ofNat.{u} k) = convCoeff R add mul zero f g k :=
  app_polyOfSeq (fun j => convCoeff_mem_semi hR hf hg j) k

#print axioms Algebra.app_polyMul_semi

/-- Regrouping a convolution on the left, over a semiring. -/
theorem convCoeff_mul_left_semi {R add mul zero one f g h : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (hf : IsPolyOver R zero f)
    (hg : IsPolyOver R zero g)
    (hh : IsPolyOver R zero h) (k : Nat) :
    convCoeff R add mul zero (polyMul R add mul zero f g) h k
      = foldF add zero (fun i => foldF add zero
          (fun a => convTerm R add mul zero f g h k a (i - a)) (i + 1)) (k + 1) := by
  refine foldF_congr (k + 1) (fun i hi => ?_)
  show opAt mul (app (polyMul R add mul zero f g) (ofNat.{u} i)) (app h (ofNat.{u} (k - i)))
    = foldF add zero (fun a => convTerm R add mul zero f g h k a (i - a)) (i + 1)
  rw [app_polyMul_semi hR hf hg i, convCoeff,
    foldF_mul_right_semi hR (coeff_mem hh (ofNat_mem_omega (k - i)))
      (fun a => mulAt_mem_semi hR (coeff_mem hf (ofNat_mem_omega a))
        (coeff_mem hg (ofNat_mem_omega (i - a)))) (i + 1)]
  refine foldF_congr (i + 1) (fun a ha => ?_)
  show opAt mul (opAt mul (app f (ofNat.{u} a)) (app g (ofNat.{u} (i - a))))
      (app h (ofNat.{u} (k - i)))
    = convTerm R add mul zero f g h k a (i - a)
  rw [convTerm, show k - a - (i - a) = k - i by omega]

/-- Regrouping a convolution on the right, over a semiring. This is where
`mulAssoc` does the work that commutativity used to hide. -/
theorem convCoeff_mul_right_semi {R add mul zero one f g h : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (hf : IsPolyOver R zero f)
    (hg : IsPolyOver R zero g)
    (hh : IsPolyOver R zero h) (k : Nat) :
    convCoeff R add mul zero f (polyMul R add mul zero g h) k
      = foldF add zero (fun a => foldF add zero
          (fun b => convTerm R add mul zero f g h k a b) (k - a + 1)) (k + 1) := by
  refine foldF_congr (k + 1) (fun a ha => ?_)
  show opAt mul (app f (ofNat.{u} a)) (app (polyMul R add mul zero g h) (ofNat.{u} (k - a)))
    = foldF add zero (fun b => convTerm R add mul zero f g h k a b) (k - a + 1)
  rw [app_polyMul_semi hR hg hh (k - a), convCoeff,
    foldF_mul_left_semi hR (coeff_mem hf (ofNat_mem_omega a))
      (fun b => mulAt_mem_semi hR (coeff_mem hg (ofNat_mem_omega b))
        (coeff_mem hh (ofNat_mem_omega (k - a - b)))) (k - a + 1)]
  refine foldF_congr (k - a + 1) (fun b hb => ?_)
  show opAt mul (app f (ofNat.{u} a))
      (opAt mul (app g (ofNat.{u} b)) (app h (ofNat.{u} (k - a - b))))
    = convTerm R add mul zero f g h k a b
  rw [convTerm, hR.mulAssoc _ (coeff_mem hf (ofNat_mem_omega a))
    _ (coeff_mem hg (ofNat_mem_omega b)) _ (coeff_mem hh (ofNat_mem_omega (k - a - b)))]

/-- The convolution is associative, over a semiring. Both groupings are
the same triangular sum of `f_a . g_b . h_c`, and only `mulAssoc` is spent. -/
theorem convCoeff_assoc_semi {R add mul zero one f g h : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (hf : IsPolyOver R zero f)
    (hg : IsPolyOver R zero g)
    (hh : IsPolyOver R zero h) (k : Nat) :
    convCoeff R add mul zero (polyMul R add mul zero f g) h k
      = convCoeff R add mul zero f (polyMul R add mul zero g h) k := by
  rw [convCoeff_mul_left_semi hR hf hg hh k, convCoeff_mul_right_semi hR hf hg hh k]
  exact foldF_triangle (hR.addMonoid)
    (fun a b => convTerm_mem_semi hR hf hg hh k a b) k

/-- `polyOne` lies in the polynomial ring, over a semiring. -/
theorem polyOne_mem_semi {R add mul zero one : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) :
    polyOne R zero one ∈ PolyRing R zero :=
  (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyOne_semi hR)

/-- A product of polynomials is a polynomial, over a semiring: each
coefficient is a convolution, and `convCoeff_mem_semi` places it in `R`. -/
theorem polyMul_mem_semi {R add mul zero one : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) :
    ∀ p, p ∈ prod (PolyRing R zero) (PolyRing R zero) →
      polyMul R add mul zero (fst p) (snd p) ∈ PolyRing R zero := by
  intro p hp
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff p _ _).mp hp
  rw [fst_opair, snd_opair]
  exact (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyMul_semi hR
    ((mem_polyRing_iff _ _ _).mp ha) ((mem_polyRing_iff _ _ _).mp hb))

/-- The multiplication operation applied, over a semiring. -/
theorem opAt_polyMulOp_semi {R add mul zero one f g : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    (hf : f ∈ PolyRing R zero) (hg : g ∈ PolyRing R zero) :
    opAt (polyMulOp R add mul zero) f g = polyMul R add mul zero f g := by
  show app (polyMulOp R add mul zero) (opair f g) = _
  rw [polyMulOp, app_graphOn (polyMul_mem_semi hR) (opair_mem_prod hf hg), fst_opair, snd_opair]

#print axioms Algebra.opAt_polyAddOp_semi
#print axioms Algebra.isAbelian_polyAdd_semi
#print axioms Algebra.convCoeff_eq_zero_semi
#print axioms Algebra.isPolyOver_polyMul_semi
#print axioms Algebra.convCoeff_mul_left_semi
#print axioms Algebra.convCoeff_mul_right_semi
#print axioms Algebra.convCoeff_assoc_semi
#print axioms Algebra.polyOne_mem_semi
#print axioms Algebra.polyMul_mem_semi
#print axioms Algebra.opAt_polyMulOp_semi


/-- Two polynomials are equal when their convolutions agree at every numeral. -/
theorem poly_ext_coeff {R zero f g : ZFSet.{u}} (hf : IsPolyOver R zero f)
    (hg : IsPolyOver R zero g) (h : ∀ k : Nat, app f (ofNat.{u} k) = app g (ofNat.{u} k)) :
    f = g := by
  refine poly_ext hf hg (fun w hw => ?_)
  obtain ⟨k, rfl⟩ := (mem_omega_iff w).mp hw
  exact h k

/-- `R[x]` is a SEMIRING when `R` is, over a `Semiring` rather than a
commutative ring.

TWELVE FIELDS AGAINST `isRing_polyRing`'s TEN, and the extra two pairs are the
whole content of the widening. `IsRing` states `mul_one` and `distrib` and
derives their transposes from `mulComm`; `IsSemiring` must state `one_mul` and
`distribRight` as well, and it must state both annihilation laws because
without additive inverses there is no cancelling to prove them by. So four
clauses here have no counterpart in the commutative construction to be renamed
from -- `convCoeff_one_left_semi`, `convCoeff_zero_left_semi`,
`convCoeff_zero_right_semi` and `convCoeff_distrib_right_semi` were written
for them.

The additive structure is `isCommMonoid_polyAdd_semi`, which REPLACES
`isGroup_polyAdd`: `polyNeg` needs a negation the scalars do not have. -/
theorem isSemiring_polyRing {R add mul zero one : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) :
    IsSemiring (PolyRing R zero) (polyAddOp R add zero) (polyMulOp R add mul zero)
      (polyZero R zero) (polyOne R zero one) := by
  have hone : polyOne R zero one ∈ PolyRing R zero := polyOne_mem_semi hR
  have hpz := isPolyOver_polyZero_semi hR
  have hzero : polyZero R zero ∈ PolyRing R zero := (mem_polyRing_iff _ _ _).mpr hpz
  refine ⟨isCommMonoid_polyAdd_semi hR, graphOn_isFunction _ _ _,
    graphOn_domain (polyMul_mem_semi hR), graphOn_range, ?_, hone, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb c hc
    have hpa := (mem_polyRing_iff _ _ _).mp ha
    have hpb := (mem_polyRing_iff _ _ _).mp hb
    have hpc := (mem_polyRing_iff _ _ _).mp hc
    have hab := isPolyOver_polyMul_semi hR hpa hpb
    have hbc := isPolyOver_polyMul_semi hR hpb hpc
    rw [opAt_polyMulOp_semi hR ha hb, opAt_polyMulOp_semi hR hb hc,
      opAt_polyMulOp_semi hR ((mem_polyRing_iff _ _ _).mpr hab) hc,
      opAt_polyMulOp_semi hR ha ((mem_polyRing_iff _ _ _).mpr hbc)]
    refine poly_ext_coeff (isPolyOver_polyMul_semi hR hab hpc)
      (isPolyOver_polyMul_semi hR hpa hbc) (fun k => ?_)
    rw [app_polyMul_semi hR hab hpc k, app_polyMul_semi hR hpa hbc k]
    exact convCoeff_assoc_semi hR hpa hpb hpc k
  · intro a ha
    have hpa := (mem_polyRing_iff _ _ _).mp ha
    rw [opAt_polyMulOp_semi hR ha hone]
    refine poly_ext_coeff
      (isPolyOver_polyMul_semi hR hpa (isPolyOver_polyOne_semi hR)) hpa (fun k => ?_)
    rw [app_polyMul_semi hR hpa (isPolyOver_polyOne_semi hR) k]
    exact convCoeff_one_semi hR hpa k
  · intro a ha
    have hpa := (mem_polyRing_iff _ _ _).mp ha
    rw [opAt_polyMulOp_semi hR hone ha]
    refine poly_ext_coeff
      (isPolyOver_polyMul_semi hR (isPolyOver_polyOne_semi hR) hpa) hpa (fun k => ?_)
    rw [app_polyMul_semi hR (isPolyOver_polyOne_semi hR) hpa k]
    exact convCoeff_one_left_semi hR hpa k
  · intro a ha
    have hpa := (mem_polyRing_iff _ _ _).mp ha
    rw [opAt_polyMulOp_semi hR hzero ha]
    refine poly_ext_coeff (isPolyOver_polyMul_semi hR hpz hpa) hpz (fun k => ?_)
    rw [app_polyMul_semi hR hpz hpa k, app_polyZero_semi hR (ofNat_mem_omega k)]
    exact convCoeff_zero_left_semi hR hpa k
  · intro a ha
    have hpa := (mem_polyRing_iff _ _ _).mp ha
    rw [opAt_polyMulOp_semi hR ha hzero]
    refine poly_ext_coeff (isPolyOver_polyMul_semi hR hpa hpz) hpz (fun k => ?_)
    rw [app_polyMul_semi hR hpa hpz k, app_polyZero_semi hR (ofNat_mem_omega k)]
    exact convCoeff_zero_right_semi hR hpa k
  · intro a ha b hb c hc
    have hpa := (mem_polyRing_iff _ _ _).mp ha
    have hpb := (mem_polyRing_iff _ _ _).mp hb
    have hpc := (mem_polyRing_iff _ _ _).mp hc
    have hbc := isPolyOver_polyAdd_semi hR hpb hpc
    rw [opAt_polyAddOp_semi hR hb hc,
      opAt_polyMulOp_semi hR ha ((mem_polyRing_iff _ _ _).mpr hbc),
      opAt_polyMulOp_semi hR ha hb, opAt_polyMulOp_semi hR ha hc,
      opAt_polyAddOp_semi hR
        ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyMul_semi hR hpa hpb))
        ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyMul_semi hR hpa hpc))]
    refine poly_ext_coeff (isPolyOver_polyMul_semi hR hpa hbc)
      (isPolyOver_polyAdd_semi hR (isPolyOver_polyMul_semi hR hpa hpb)
        (isPolyOver_polyMul_semi hR hpa hpc)) (fun k => ?_)
    rw [app_polyMul_semi hR hpa hbc k,
      app_polyAdd_semi hR (isPolyOver_polyMul_semi hR hpa hpb)
        (isPolyOver_polyMul_semi hR hpa hpc) (ofNat_mem_omega k),
      app_polyMul_semi hR hpa hpb k, app_polyMul_semi hR hpa hpc k]
    exact convCoeff_distrib_semi hR hpa hpb hpc k
  · intro a ha b hb c hc
    have hpa := (mem_polyRing_iff _ _ _).mp ha
    have hpb := (mem_polyRing_iff _ _ _).mp hb
    have hpc := (mem_polyRing_iff _ _ _).mp hc
    have hab := isPolyOver_polyAdd_semi hR hpa hpb
    rw [opAt_polyAddOp_semi hR ha hb,
      opAt_polyMulOp_semi hR ((mem_polyRing_iff _ _ _).mpr hab) hc,
      opAt_polyMulOp_semi hR ha hc, opAt_polyMulOp_semi hR hb hc,
      opAt_polyAddOp_semi hR
        ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyMul_semi hR hpa hpc))
        ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyMul_semi hR hpb hpc))]
    refine poly_ext_coeff (isPolyOver_polyMul_semi hR hab hpc)
      (isPolyOver_polyAdd_semi hR (isPolyOver_polyMul_semi hR hpa hpc)
        (isPolyOver_polyMul_semi hR hpb hpc)) (fun k => ?_)
    rw [app_polyMul_semi hR hab hpc k,
      app_polyAdd_semi hR (isPolyOver_polyMul_semi hR hpa hpc)
        (isPolyOver_polyMul_semi hR hpb hpc) (ofNat_mem_omega k),
      app_polyMul_semi hR hpa hpc k, app_polyMul_semi hR hpb hpc k]
    exact convCoeff_distrib_right_semi hR hpa hpb hpc k

#print axioms Algebra.isSemiring_polyRing

/-- `R[x]` is a ring. -/
theorem isRing_polyRing {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    IsRing (PolyRing R zero) (polyAddOp R add zero) (polyMulOp R add mul zero)
      (polyZero R zero) (polyOne R zero one) := by
  have hS := isSemiring_polyRing hR.toNC.toSemiring
  refine ⟨isGroup_polyAdd hR, isAbelian_polyAdd hR, hS.mulFun, hS.mulDom,
    hS.mulRan, hS.mulAssoc, ?_, hS.mem_one, hS.mul_one, hS.distrib⟩
  intro a ha b hb
  have hpa := (mem_polyRing_iff _ _ _).mp ha
  have hpb := (mem_polyRing_iff _ _ _).mp hb
  rw [opAt_polyMulOp hR ha hb, opAt_polyMulOp hR hb ha]
  refine poly_ext_coeff (isPolyOver_polyMul hR hpa hpb)
    (isPolyOver_polyMul hR hpb hpa) (fun k => ?_)
  rw [app_polyMul hR hpa hpb k, app_polyMul hR hpb hpa k]
  exact convCoeff_comm hR hpa hpb k


/-- Reading a coefficient commutes with a SUM of polynomials.

`app_polyAdd` is the two-term case; a matrix product over `R[X]` is a fold, so
comparing coefficients on both sides of the adjugate identity needs the fold
case. The induction is `app_polyAdd` once per step with `app_polyZero` at the
base. -/
theorem app_foldF_polyAdd {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) {F : Nat → ZFSet.{u}}
    (hF : ∀ i, F i ∈ PolyRing R zero) {w : ZFSet.{u}} (hw : w ∈ omega.{u}) :
    ∀ m : Nat,
      app (foldF (polyAddOp R add zero) (polyZero R zero) F m) w
        = foldF add zero (fun i => app (F i) w) m
  | 0 => app_polyZero hR hw
  | m + 1 => by
    have hP := isRing_polyRing (one := one) hR
    have hpart : foldF (polyAddOp R add zero) (polyZero R zero) F m ∈ PolyRing R zero :=
      foldF_mem (isCommMonoid_ringAdd hP) m (fun i _ => hF i)
    show app (opAt (polyAddOp R add zero)
        (foldF (polyAddOp R add zero) (polyZero R zero) F m) (F m)) w = _
    rw [opAt_polyAddOp hR hpart (hF m),
      app_polyAdd hR ((mem_polyRing_iff _ _ _).mp hpart)
        ((mem_polyRing_iff _ _ _).mp (hF m)) hw,
      app_foldF_polyAdd hR hF hw m]
    rfl

#print axioms app_foldF_polyAdd

/-! ## Monomials

`monomial a k` is `a·x^k`. Multiplying by one is a shift, which is what division
with remainder needs. -/

/-- One surviving term, with the vanishing required only *below the fold's
own bound*. A power series has no vanishing above, so the unbounded form
below cannot reach it -- the fold never looks past `n` and this says so. -/

theorem foldF_single_below {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one)
    {T : Nat → ZFSet.{u}} {k : Nat} (hTk : T k ∈ R) :
    ∀ n : Nat, k < n → (∀ i, i < n → i ≠ k → T i = zero) →
      foldF add zero T n = T k
  | 0, hk, _ => absurd hk (by omega)
  | n + 1, hk, hz => by
    show opAt add (foldF add zero T n) (T n) = T k
    rcases Nat.eq_or_lt_of_le (show k + 1 ≤ n + 1 from hk) with heq | hlt
    · obtain rfl : k = n := by omega
      rw [foldF_zeros hR _ (fun i hi => hz i (by omega) (by omega)),
        ringZero_add hR hTk]
    · rw [foldF_single_below hR hTk n (by omega)
        (fun i hi hne => hz i (by omega) hne), hz n (by omega) (by omega),
        ringAdd_zero hR hTk]

theorem foldF_single {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one)
    {T : Nat → ZFSet.{u}} {k : Nat} (hTk : T k ∈ R)
    (hz : ∀ i, i ≠ k → T i = zero) :
    ∀ n : Nat, k < n → foldF add zero T n = T k :=
  fun n hk => foldF_single_below hR hTk n hk (fun i _ hne => hz i hne)

def monomialCoeff (zero a : ZFSet.{u}) (k i : Nat) : ZFSet.{u} := if i = k then a else zero

def monomial (R zero a : ZFSet.{u}) (k : Nat) : ZFSet.{u} :=
  polyOfSeq R (monomialCoeff zero a k)

/-- The unit polynomial has two spellings and they agree.

`polyOne` is `polyOfSeq (unitCoeff …)`, a pattern match; `monomial … one 0` is
`polyOfSeq (monomialCoeff …)`, an `if`. Pointwise equal and not definitionally
so, so a caller holding one form cannot rewrite with the other. -/
theorem monomial_zero_eq_polyOne {R zero one : ZFSet.{u}} :
    monomial R zero one 0 = polyOne R zero one := by
  unfold monomial polyOne
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ n => rfl

#print axioms monomial_zero_eq_polyOne


theorem monomialCoeff_mem {R add mul zero one a : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (k : Nat) : ∀ i : Nat, monomialCoeff zero a k i ∈ R := by
  intro i
  rcases Nat.decEq i k with hne | heq
  · rw [monomialCoeff, if_neg hne]
    exact hR.addGroup.mem_e
  · rw [monomialCoeff, if_pos heq]
    exact ha

theorem app_monomial {R add mul zero one a : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (k i : Nat) :
    app (monomial R zero a k) (ofNat.{u} i) = monomialCoeff zero a k i :=
  app_polyOfSeq (monomialCoeff_mem hR ha k) i

theorem isPolyOver_monomial {R add mul zero one a : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (k : Nat) : IsPolyOver R zero (monomial R zero a k) :=
  isPolyOver_polyOfSeq (monomialCoeff_mem hR ha k) (N := k + 1) (fun i hi => by
    rw [monomialCoeff, if_neg (by omega)])

/-- Multiplying by `a·x^k` shifts the coefficients up by `k`. -/
theorem convCoeff_monomial {R add mul zero one a g : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (ha : a ∈ R) (hg : IsPolyOver R zero g) (k i : Nat) :
    convCoeff R add mul zero (monomial R zero a k) g i
      = if k ≤ i then opAt mul a (app g (ofNat.{u} (i - k))) else zero := by
  have hterm : ∀ j : Nat, opAt mul (app (monomial R zero a k) (ofNat.{u} j))
      (app g (ofNat.{u} (i - j))) ∈ R := fun j =>
    mulAt_mem hR (coeff_mem (isPolyOver_monomial hR ha k) (ofNat_mem_omega j))
      (coeff_mem hg (ofNat_mem_omega (i - j)))
  have hzero : ∀ j : Nat, j ≠ k → opAt mul (app (monomial R zero a k) (ofNat.{u} j))
      (app g (ofNat.{u} (i - j))) = zero := by
    intro j hj
    rw [app_monomial hR ha k j, monomialCoeff, if_neg hj,
      ringZero_mul hR (coeff_mem hg (ofNat_mem_omega (i - j)))]
  rcases Nat.lt_or_ge i k with hlt | hge
  · rw [if_neg (by omega), convCoeff]
    exact foldF_zeros hR (i + 1) (fun j hj => hzero j (by omega))
  · rw [if_pos hge, convCoeff,
      foldF_single hR (hterm k) hzero (i + 1) (by omega), app_monomial hR ha k k,
      monomialCoeff, if_pos rfl]

/-! ## The binomial theorem

`(a+b)^n = ∑_{k ≤ n} C(n,k)·a^k·b^(n-k)`, with `C(n,k)` acting by repeated
addition. The sum is a `foldF`, so the induction step is `foldF_add` and
`foldF_cons` -- Pascal's rule appears as the recombination of the two shifted
sums. -/

def binomTerm (R add mul zero one a b : ZFSet.{u}) (n k : Nat) : ZFSet.{u} :=
  gpow add zero (opAt mul (gpow mul one a k) (gpow mul one b (n - k))) (choose n k)

/-- `x^j · x^k = x^(j+k)`, with coefficients multiplied. -/
theorem monomial_mul_monomial {R add mul zero one a b : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (j k : Nat) :
    polyMul R add mul zero (monomial R zero a j) (monomial R zero b k)
      = monomial R zero (opAt mul a b) (j + k) := by
  refine poly_ext_coeff (isPolyOver_polyMul hR (isPolyOver_monomial hR ha j)
    (isPolyOver_monomial hR hb k)) (isPolyOver_monomial hR (mulAt_mem hR ha hb) (j + k))
    (fun i => ?_)
  rw [app_polyMul hR (isPolyOver_monomial hR ha j) (isPolyOver_monomial hR hb k) i,
    convCoeff_monomial hR ha (isPolyOver_monomial hR hb k) j i,
    app_monomial hR (mulAt_mem hR ha hb) (j + k) i, monomialCoeff]
  rcases Nat.decLt i j with hle | hlt
  · rw [if_pos (by omega), app_monomial hR hb k (i - j), monomialCoeff]
    rcases Nat.decEq (i - j) k with hne | heq
    · rw [if_neg hne, if_neg (by omega), mul_zero_of_isRing hR ha]
    · rw [if_pos heq, if_pos (by omega)]
  · rw [if_neg (by omega), if_neg (by omega)]

theorem binomTerm_mem {R add mul zero one a b : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (n k : Nat) : binomTerm R add mul zero one a b n k ∈ R :=
  ringNsmul_mem hR (mulAt_mem hR (ringPow_mem hR ha k) (ringPow_mem hR hb (n - k))) _

/-- `binomTerm_mem` over a semiring. Every ingredient is the `_semi` form:
the additive iterate, the product, and the two powers. -/
theorem binomTerm_mem_semi {R add mul zero one a b : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (n k : Nat) :
    binomTerm R add mul zero one a b n k ∈ R :=
  ringNsmul_mem_semi hR
    (mulAt_mem_semi hR (ringPow_mem_semi hR ha k) (ringPow_mem_semi hR hb (n - k))) _

#print axioms binomTerm_mem_semi

/-- The binomial sum, `∑_{k < n+1} C(n,k)·a^k·b^(n-k)`. -/

def binomSum (R add mul zero one a b : ZFSet.{u}) (n : Nat) : ZFSet.{u} :=
  foldF add zero (fun k => binomTerm R add mul zero one a b n k) (n + 1)

/-- A binomial term above the degree is the ring's zero. `binomTerm` carries
`choose n k` as `gpow add zero _ (choose n k)`, and `gpow` at exponent zero is
the unit -- so `choose_gt` is the whole proof and no ring law is used. -/
theorem binomTerm_eq_zero_of_gt {R add mul zero one a b : ZFSet.{u}}
    {n k : Nat} (h : n < k) :
    binomTerm R add mul zero one a b n k = zero := by
  rw [binomTerm, choose_gt n k h]
  rfl

#print axioms binomTerm_eq_zero_of_gt

theorem binomSum_mem {R add mul zero one a b : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (n : Nat) : binomSum R add mul zero one a b n ∈ R :=
  foldF_mem (isCommMonoid_ringAdd hR) (n + 1) (fun k _ => binomTerm_mem hR ha hb n k)

/-- `binomSum_mem` over a semiring: `IsSemiring.addMonoid` IS the commutative
monoid `foldF_mem` asks for, so the ring detour disappears. -/
theorem binomSum_mem_semi {R add mul zero one a b : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (n : Nat) :
    binomSum R add mul zero one a b n ∈ R :=
  foldF_mem hR.addMonoid (n + 1) (fun k _ => binomTerm_mem_semi hR ha hb n k)

#print axioms binomSum_mem_semi

/-- Multiplying the binomial sum out, term by term. -/
theorem binomSum_mul {R add mul zero one a b : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (c : ZFSet.{u}) (hc : c ∈ R) (n : Nat) :
    opAt mul (binomSum R add mul zero one a b n) c
      = foldF add zero (fun k => opAt mul (binomTerm R add mul zero one a b n k) c) (n + 1) :=
  foldF_mul_right hR hc (fun k => binomTerm_mem hR ha hb n k) (n + 1)

/-- `binomSum_mul` over a semiring, on `foldF_mul_right_semi` --- which the
polynomial migration had already landed. -/
theorem binomSum_mul_semi {R add mul zero one a b : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (c : ZFSet.{u}) (hc : c ∈ R) (n : Nat) :
    opAt mul (binomSum R add mul zero one a b n) c
      = foldF add zero (fun k => opAt mul (binomTerm R add mul zero one a b n k) c) (n + 1) :=
  foldF_mul_right_semi hR hc (fun k => binomTerm_mem_semi hR ha hb n k) (n + 1)

#print axioms binomSum_mul_semi

theorem binomTerm_mul_left {R add mul zero one a b : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (n k : Nat) :
    opAt mul (binomTerm R add mul zero one a b n k) a
      = gpow add zero (opAt mul (gpow mul one a (k + 1)) (gpow mul one b (n - k)))
        (choose n k) := by
  have hak := ringPow_mem hR ha k
  have hbk := ringPow_mem hR hb (n - k)
  rw [binomTerm, ← ringNsmul_mul hR (mulAt_mem hR hak hbk) ha]
  refine congrArg (fun t => gpow add zero t (choose n k)) ?_
  rw [hR.mulComm _ hak _ hbk, hR.mulAssoc _ hbk _ hak _ ha,
    hR.mulComm _ hbk _ (mulAt_mem hR hak ha), ringPow_succ mul one a k]

/-- `binomTerm_mul_left` over a COMMUTATIVE semiring. The binomial theorem
spends commutativity here, twice: once to walk
`a^k` past `b^(n-k)` and once to walk it back after the associativity step.
Its twin `binomTerm_mul_right_semi` needs none, because multiplying on the
right leaves the factors in order. -/
theorem binomTerm_mul_left_semi {R add mul zero one a b : ZFSet.{u}}
    (hR : IsCommSemiring R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (n k : Nat) :
    opAt mul (binomTerm R add mul zero one a b n k) a
      = gpow add zero (opAt mul (gpow mul one a (k + 1)) (gpow mul one b (n - k)))
        (choose n k) := by
  have hak := ringPow_mem_semi hR.semiring ha k
  have hbk := ringPow_mem_semi hR.semiring hb (n - k)
  rw [binomTerm, ← ringNsmul_mul_semi hR.semiring
    (mulAt_mem_semi hR.semiring hak hbk) ha]
  refine congrArg (fun t => gpow add zero t (choose n k)) ?_
  rw [hR.mulComm _ hak _ hbk, hR.semiring.mulAssoc _ hbk _ hak _ ha,
    hR.mulComm _ hbk _ (mulAt_mem_semi hR.semiring hak ha), ringPow_succ mul one a k]

#print axioms binomTerm_mul_left_semi

theorem binomTerm_mul_right {R add mul zero one a b : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (n k : Nat) (hk : k ≤ n) :
    opAt mul (binomTerm R add mul zero one a b n k) b
      = gpow add zero (opAt mul (gpow mul one a k) (gpow mul one b (n + 1 - k)))
        (choose n k) := by
  have hak := ringPow_mem hR ha k
  have hbk := ringPow_mem hR hb (n - k)
  rw [binomTerm, ← ringNsmul_mul hR (mulAt_mem hR hak hbk) hb]
  refine congrArg (fun t => gpow add zero t (choose n k)) ?_
  rw [hR.mulAssoc _ hak _ hbk _ hb, show n + 1 - k = (n - k) + 1 by omega,
    ringPow_succ mul one b (n - k)]

/-- `binomTerm_mul_right` over a semiring, and it needs NO commutativity ---
multiplying on the right leaves the factors in order. Its twin
`binomTerm_mul_left_semi` spends `mulComm` for the binomial theorem. -/
theorem binomTerm_mul_right_semi {R add mul zero one a b : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (n k : Nat)
    (hk : k ≤ n) :
    opAt mul (binomTerm R add mul zero one a b n k) b
      = gpow add zero (opAt mul (gpow mul one a k) (gpow mul one b (n + 1 - k)))
        (choose n k) := by
  have hak := ringPow_mem_semi hR ha k
  have hbk := ringPow_mem_semi hR hb (n - k)
  rw [binomTerm, ← ringNsmul_mul_semi hR (mulAt_mem_semi hR hak hbk) hb]
  refine congrArg (fun t => gpow add zero t (choose n k)) ?_
  rw [hR.mulAssoc _ hak _ hbk _ hb, show n + 1 - k = (n - k) + 1 by omega,
    ringPow_succ mul one b (n - k)]

#print axioms binomTerm_mul_right_semi

/-- The shifted summand of the binomial sum. -/
def binomShift (add mul zero one a b : ZFSet.{u}) (n j c : Nat) : ZFSet.{u} :=
  gpow add zero (opAt mul (gpow mul one a (j + 1)) (gpow mul one b (n - j))) c

theorem binomShift_mem {R add mul zero one a b : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (n j c : Nat) : binomShift add mul zero one a b n j c ∈ R :=
  ringNsmul_mem hR (mulAt_mem hR (ringPow_mem hR ha (j + 1)) (ringPow_mem hR hb (n - j))) c

/-- `binomShift_mem` over a semiring. -/
theorem binomShift_mem_semi {R add mul zero one a b : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (n j c : Nat) :
    binomShift add mul zero one a b n j c ∈ R :=
  ringNsmul_mem_semi hR (mulAt_mem_semi hR (ringPow_mem_semi hR ha (j + 1))
    (ringPow_mem_semi hR hb (n - j))) c

#print axioms binomShift_mem_semi

/-- Pascal's rule, on the terms of the binomial sum. -/
theorem binomTerm_succ {R add mul zero one a b : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (n j : Nat) :
    binomTerm R add mul zero one a b (n + 1) (j + 1)
      = opAt add (binomShift add mul zero one a b n j (choose n j))
        (binomShift add mul zero one a b n j (choose n (j + 1))) := by
  rw [binomTerm, choose_succ_succ, show n + 1 - (j + 1) = n - j by omega, binomShift,
    binomShift]
  exact ringNsmul_sum hR (mulAt_mem hR (ringPow_mem hR ha (j + 1))
    (ringPow_mem hR hb (n - j))) _ _

/-- `binomTerm_succ` over a semiring: Pascal's rule, on `ringNsmul_sum_semi`. -/
theorem binomTerm_succ_semi {R add mul zero one a b : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (n j : Nat) :
    binomTerm R add mul zero one a b (n + 1) (j + 1)
      = opAt add (binomShift add mul zero one a b n j (choose n j))
        (binomShift add mul zero one a b n j (choose n (j + 1))) := by
  rw [binomTerm, choose_succ_succ, show n + 1 - (j + 1) = n - j by omega, binomShift,
    binomShift]
  exact ringNsmul_sum_semi hR (mulAt_mem_semi hR (ringPow_mem_semi hR ha (j + 1))
    (ringPow_mem_semi hR hb (n - j))) _ _

#print axioms binomTerm_succ_semi

/-- The other shifted summand: `C(n,k)·a^k·b^(n+1-k)`. -/
def binomUp (add mul zero one a b : ZFSet.{u}) (n k : Nat) : ZFSet.{u} :=
  gpow add zero (opAt mul (gpow mul one a k) (gpow mul one b (n + 1 - k))) (choose n k)

theorem binomUp_mem {R add mul zero one a b : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (n k : Nat) : binomUp add mul zero one a b n k ∈ R :=
  ringNsmul_mem hR (mulAt_mem hR (ringPow_mem hR ha k) (ringPow_mem hR hb (n + 1 - k))) _

/-- `binomUp_mem` over a semiring. -/
theorem binomUp_mem_semi {R add mul zero one a b : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (n k : Nat) :
    binomUp add mul zero one a b n k ∈ R :=
  ringNsmul_mem_semi hR (mulAt_mem_semi hR (ringPow_mem_semi hR ha k)
    (ringPow_mem_semi hR hb (n + 1 - k))) _

#print axioms binomUp_mem_semi

/-- The term of the next binomial sum splits into one from each shifted sum. -/
theorem binomTerm_split {R add mul zero one a b : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (n j : Nat) :
    opAt add (binomShift add mul zero one a b n j (choose n j))
        (binomUp add mul zero one a b n (j + 1))
      = binomTerm R add mul zero one a b (n + 1) (j + 1) := by
  rw [binomTerm_succ hR ha hb n j, binomUp, binomShift, binomShift,
    show n + 1 - (j + 1) = n - j by omega]

/-- `binomTerm_split` over a semiring. -/
theorem binomTerm_split_semi {R add mul zero one a b : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (n j : Nat) :
    opAt add (binomShift add mul zero one a b n j (choose n j))
        (binomUp add mul zero one a b n (j + 1))
      = binomTerm R add mul zero one a b (n + 1) (j + 1) := by
  rw [binomTerm_succ_semi hR ha hb n j, binomUp, binomShift, binomShift,
    show n + 1 - (j + 1) = n - j by omega]

#print axioms binomTerm_split_semi

theorem binomSum_succ {R add mul zero one a b : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (n : Nat) :
    binomSum R add mul zero one a b (n + 1)
      = opAt add (binomTerm R add mul zero one a b (n + 1) 0)
        (foldF add zero (fun j => binomTerm R add mul zero one a b (n + 1) (j + 1)) (n + 1)) :=
  foldF_cons (isCommMonoid_ringAdd hR) (n + 1)
    (fun k _ => binomTerm_mem hR ha hb (n + 1) k)

/-- `binomSum_succ` over a semiring. `foldF_cons` already takes an
`IsCommMonoid`. -/
theorem binomSum_succ_semi {R add mul zero one a b : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (n : Nat) :
    binomSum R add mul zero one a b (n + 1)
      = opAt add (binomTerm R add mul zero one a b (n + 1) 0)
        (foldF add zero (fun j => binomTerm R add mul zero one a b (n + 1) (j + 1)) (n + 1)) :=
  foldF_cons hR.addMonoid (n + 1)
    (fun k _ => binomTerm_mem_semi hR ha hb (n + 1) k)

#print axioms binomSum_succ_semi

theorem binomUp_succ {R add mul zero one a b : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) (n : Nat) :
    foldF add zero (fun k => binomUp add mul zero one a b n k) (n + 1)
      = opAt add (binomUp add mul zero one a b n 0)
        (foldF add zero (fun j => binomUp add mul zero one a b n (j + 1)) n) :=
  foldF_cons (isCommMonoid_ringAdd hR) n (fun k _ => binomUp_mem hR ha hb n k)

/-- `binomUp_succ` over a semiring. -/
theorem binomUp_succ_semi {R add mul zero one a b : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (n : Nat) :
    foldF add zero (fun k => binomUp add mul zero one a b n k) (n + 1)
      = opAt add (binomUp add mul zero one a b n 0)
        (foldF add zero (fun j => binomUp add mul zero one a b n (j + 1)) n) :=
  foldF_cons hR.addMonoid n (fun k _ => binomUp_mem_semi hR ha hb n k)

#print axioms binomUp_succ_semi

/-- The recombination step. -/
theorem binomSum_recombine {R add mul zero one a b : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (n : Nat) :
    opAt add
        (foldF add zero (fun k => binomShift add mul zero one a b n k (choose n k)) (n + 1))
        (foldF add zero (fun k => binomUp add mul zero one a b n k) (n + 1))
      = binomSum R add mul zero one a b (n + 1) := by
  have hM := isCommMonoid_ringAdd hR
  have hS₁ := foldF_mem hM (n + 1)
    (fun k (_ : k < n + 1) => binomShift_mem hR ha hb n k (choose n k))
  have hS₂ : foldF add zero (fun j => binomUp add mul zero one a b n (j + 1)) n ∈ R :=
    foldF_mem hM n (fun j _ => binomUp_mem hR ha hb n (j + 1))
  -- peel the leading term off the second sum, and expand the target the same way
  rw [binomUp_succ hR ha hb n, binomSum_succ hR ha hb n,
    ← foldF_pointwise_add hM (n + 1)
      (fun j _ => binomShift_mem hR ha hb n j (choose n j))
      (fun j _ => binomUp_mem hR ha hb n (j + 1))
      (fun j _ => binomTerm_split hR ha hb n j)]
  have hdrop := foldF_drop_last (M := R) (F := fun j => binomUp add mul zero one a b n (j + 1))
    hM (fun j _ => binomUp_mem hR ha hb n (j + 1))
    (by
      show binomUp add mul zero one a b n (n + 1) = zero
      rw [binomUp, choose_gt n (n + 1) (by omega)]
      rfl)
  rw [hdrop]
  have hzero : binomUp add mul zero one a b n 0
      = binomTerm R add mul zero one a b (n + 1) 0 := by
    rw [binomUp, binomTerm, choose_zero, choose_zero]
  rw [hzero]
  exact ringAdd_left_comm hR hS₁ (binomTerm_mem hR ha hb (n + 1) 0) hS₂

/-- `binomSum_recombine` over a semiring. Every fold lemma it uses already
takes an `IsCommMonoid`, which `IsSemiring.addMonoid` IS; the one gap was
`ringAdd_left_comm`, now `left_comm_monoid` on that same monoid. -/
theorem binomSum_recombine_semi {R add mul zero one a b : ZFSet.{u}}
    (hR : IsSemiring R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (n : Nat) :
    opAt add
        (foldF add zero (fun k => binomShift add mul zero one a b n k (choose n k)) (n + 1))
        (foldF add zero (fun k => binomUp add mul zero one a b n k) (n + 1))
      = binomSum R add mul zero one a b (n + 1) := by
  have hM := hR.addMonoid
  have hS₁ := foldF_mem hM (n + 1)
    (fun k (_ : k < n + 1) => binomShift_mem_semi hR ha hb n k (choose n k))
  have hS₂ : foldF add zero (fun j => binomUp add mul zero one a b n (j + 1)) n ∈ R :=
    foldF_mem hM n (fun j _ => binomUp_mem_semi hR ha hb n (j + 1))
  rw [binomUp_succ_semi hR ha hb n, binomSum_succ_semi hR ha hb n,
    ← foldF_pointwise_add hM (n + 1)
      (fun j _ => binomShift_mem_semi hR ha hb n j (choose n j))
      (fun j _ => binomUp_mem_semi hR ha hb n (j + 1))
      (fun j _ => binomTerm_split_semi hR ha hb n j)]
  have hdrop := foldF_drop_last (M := R) (F := fun j => binomUp add mul zero one a b n (j + 1))
    hM (fun j _ => binomUp_mem_semi hR ha hb n (j + 1))
    (by
      show binomUp add mul zero one a b n (n + 1) = zero
      rw [binomUp, choose_gt n (n + 1) (by omega)]
      rfl)
  rw [hdrop]
  have hzero : binomUp add mul zero one a b n 0
      = binomTerm R add mul zero one a b (n + 1) 0 := by
    rw [binomUp, binomTerm, choose_zero, choose_zero]
  rw [hzero]
  exact left_comm_monoid hM hS₁ (binomTerm_mem_semi hR ha hb (n + 1) 0) hS₂

#print axioms binomSum_recombine_semi

/-- The binomial theorem. -/
theorem binomial_semi {R add mul zero one a b : ZFSet.{u}}
    (hR : IsCommSemiring R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) :
    ∀ n : Nat, gpow mul one (opAt add a b) n = binomSum R add mul zero one a b n
  | 0 => by
    show one = opAt add zero (binomTerm R add mul zero one a b 0 0)
    rw [binomTerm, choose_zero]
    show one = opAt add zero (opAt add zero (opAt mul one one))
    rw [hR.semiring.mul_one one hR.semiring.mem_one,
      hR.semiring.addMonoid.left_id _ hR.semiring.mem_one,
      hR.semiring.addMonoid.left_id _ hR.semiring.mem_one]
  | n + 1 => by
    have hstep : gpow mul one (opAt add a b) (n + 1)
        = opAt add (opAt mul (binomSum R add mul zero one a b n) a)
          (opAt mul (binomSum R add mul zero one a b n) b) := by
      show opAt mul (gpow mul one (opAt add a b) n) (opAt add a b) = _
      rw [binomial_semi hR ha hb n,
        hR.semiring.distrib _ (binomSum_mem_semi hR.semiring ha hb n) _ ha _ hb]
    rw [hstep, binomSum_mul_semi hR.semiring ha hb a ha n,
      binomSum_mul_semi hR.semiring ha hb b hb n,
      foldF_congr (n + 1) (fun k _ => binomTerm_mul_left_semi hR ha hb n k),
      foldF_congr (n + 1) (fun k hk => binomTerm_mul_right_semi hR.semiring ha hb n k
        (by omega))]
    exact binomSum_recombine_semi hR.semiring ha hb n

#print axioms binomial_semi

/-- The binomial theorem over a commutative ring, now a corollary of the
semiring form. The 108 call sites across 14 files are untouched: the statement
is unchanged and only its proof moved. -/
theorem binomial {R add mul zero one a b : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) :
    ∀ n : Nat, gpow mul one (opAt add a b) n = binomSum R add mul zero one a b n :=
  binomial_semi (isCommSemiring_of_isRing hR) ha hb


/-- Scaling a fold scales its terms. -/
theorem ringNsmul_foldF {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one)
    {F : Nat → ZFSet.{u}} (hF : ∀ i, F i ∈ R) (m : Nat) :
    ∀ n : Nat, gpow add zero (foldF add zero F n) m
      = foldF add zero (fun i => gpow add zero (F i) m) n
  | 0 => gpow_id hR.addGroup m
  | n + 1 => by
    show gpow add zero (opAt add (foldF add zero F n) (F n)) m
      = opAt add (foldF add zero (fun i => gpow add zero (F i) m) n)
        (gpow add zero (F n) m)
    rw [ringNsmul_add hR (foldF_mem (isCommMonoid_ringAdd hR) n (fun i _ => hF i)) (hF n) m,
      ringNsmul_foldF hR hF m n]

/-! ## The formal derivative

`(∑ aᵢxⁱ)' = ∑ (i+1)·a_{i+1} xⁱ`, with the coefficient acting by repeated
addition. It is a set function on `R[x]`, additive, and it lowers the support
bound by one, so `x^n - x` is squarefree in characteristic dividing `n`. -/

def polyDeriv (R add zero f : ZFSet.{u}) : ZFSet.{u} :=
  polyOfSeq R (fun i => gpow add zero (app f (ofNat.{u} (i + 1))) (i + 1))

/-! ## Leibniz

`(fg)' = f'g + fg'`. At the level of coefficients both sides are sums over
`j ≤ k+1` of `c·f_j·g_(k+1-j)`, with `c = j` on one side, `c = k+1-j` on the
other, and `j + (k+1-j) = k+1` recombining them. -/

/-- The common summand of the two sides. -/
def leibTerm (add mul zero one f g : ZFSet.{u}) (k j c : Nat) : ZFSet.{u} :=
  gpow add zero (opAt mul (app f (ofNat.{u} j)) (app g (ofNat.{u} (k + 1 - j)))) c

/-! ## Evaluation

`evalAt x f` is `∑_i f_i·x^i`. The sum has to stop somewhere, and where it stops
is not determined by `f` -- only that some bound works. So the value is named
the same way inverses are: it is the unique element that is the partial sum up
to any support bound. -/

def evalUpTo (R add mul zero one x f : ZFSet.{u}) (n : Nat) : ZFSet.{u} :=
  foldF add zero (fun i => opAt mul (app f (ofNat.{u} i)) (gpow mul one x i)) n

def IsEvalOf (R add mul zero one x f v : ZFSet.{u}) : Prop :=
  ∃ N : Nat, (∀ i : Nat, N ≤ i → app f (ofNat.{u} i) = zero) ∧
    v = evalUpTo R add mul zero one x f N

def evalAt (R add mul zero one x f : ZFSet.{u}) : ZFSet.{u} :=
  sUnion (sep (fun v => IsEvalOf R add mul zero one x f v) R)

theorem evalUpTo_mem {R add mul zero one x f : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hx : x ∈ R) (hf : IsPolyOver R zero f) (n : Nat) :
    evalUpTo R add mul zero one x f n ∈ R :=
  foldF_mem (isCommMonoid_ringAdd hR) n
    (fun i _ => mulAt_mem hR (coeff_mem hf (ofNat_mem_omega i)) (ringPow_mem hR hx i))

/-- Past a support bound the partial sums stop moving. -/
theorem evalUpTo_stable {R add mul zero one x f : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hx : x ∈ R) (hf : IsPolyOver R zero f) {N : Nat}
    (hN : ∀ i : Nat, N ≤ i → app f (ofNat.{u} i) = zero) {m : Nat} (hm : N ≤ m) :
    evalUpTo R add mul zero one x f m = evalUpTo R add mul zero one x f N :=
  foldF_trunc (isCommMonoid_ringAdd hR)
    (fun i _ => mulAt_mem hR (coeff_mem hf (ofNat_mem_omega i)) (ringPow_mem hR hx i))
    (fun i hi => by rw [hN i hi, ringZero_mul hR (ringPow_mem hR hx i)]) m hm

theorem evalAt_eq {R add mul zero one x f : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hx : x ∈ R) (hf : IsPolyOver R zero f) {N : Nat}
    (hN : ∀ i : Nat, N ≤ i → app f (ofNat.{u} i) = zero) :
    evalAt R add mul zero one x f = evalUpTo R add mul zero one x f N := by
  have hsingle : sep (fun v => IsEvalOf R add mul zero one x f v) R
      = singleton (evalUpTo R add mul zero one x f N) := by
    refine (ext_iff _ _).mpr (fun v => ⟨fun hv => ?_, fun hv => ?_⟩)
    · obtain ⟨-, M, hM, rfl⟩ := (mem_sep_iff _ _ _).mp hv
      refine (mem_singleton_iff _ _).mpr ?_
      rcases Nat.lt_or_ge M N with hlt | hge
      · rw [← evalUpTo_stable hR hx hf hM (show M ≤ N by omega)]
      · rw [evalUpTo_stable hR hx hf hN hge]
    · rw [(mem_singleton_iff _ _).mp hv]
      exact (mem_sep_iff _ _ _).mpr ⟨evalUpTo_mem hR hx hf N, N, hN, rfl⟩
  rw [evalAt, hsingle, sUnion_singleton]

theorem evalAt_mem {R add mul zero one x f : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hx : x ∈ R) (hf : IsPolyOver R zero f) : evalAt R add mul zero one x f ∈ R := by
  obtain ⟨N, hN⟩ := hf.right.right.right
  rw [evalAt_eq hR hx hf hN]
  exact evalUpTo_mem hR hx hf N

/-- A product's support bound is the sum of the factors'. The content is
`convCoeff_eq_zero`, which `isPolyOver_polyMul` already uses at `Nf + Ng` and
does not expose. -/
theorem polyMul_bound {R add mul zero one f g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) {Nf Ng : Nat}
    (hNf : ∀ i : Nat, Nf ≤ i → app f (ofNat.{u} i) = zero)
    (hNg : ∀ i : Nat, Ng ≤ i → app g (ofNat.{u} i) = zero) :
    ∀ k : Nat, Nf + Ng ≤ k → app (polyMul R add mul zero f g) (ofNat.{u} k) = zero := by
  intro k hk
  rw [app_polyMul hR hf hg k]
  exact convCoeff_eq_zero hR hf hg hNf hNg hk

/-- A power's support bound grows linearly. `L^k` vanishes above `k*M + 1`
when `L` vanishes above `M`; the `+1` is what makes `k = 0` (the constant `1`)
an instance rather than a case the caller carries. -/
theorem ringPow_bound {R add mul zero one L : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hL : L ∈ PolyRing R zero) {M : Nat}
    (hM : ∀ i : Nat, M ≤ i → app L (ofNat.{u} i) = zero) :
    ∀ k : Nat, ∀ j : Nat, k * M + 1 ≤ j →
      app (gpow (polyMulOp R add mul zero) (polyOne R zero one) L k) (ofNat.{u} j) = zero
  | 0 => by
    intro j hj
    show app (polyOne R zero one) (ofNat.{u} j) = zero
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    rw [app_polyOne hR (m + 1)]
    rfl
  | k + 1 => by
    intro j hj
    have hP := isRing_polyRing (one := one) hR
    have hpow : gpow (polyMulOp R add mul zero) (polyOne R zero one) L k ∈ PolyRing R zero :=
      ringPow_mem hP hL k
    show app (opAt (polyMulOp R add mul zero)
      (gpow (polyMulOp R add mul zero) (polyOne R zero one) L k) L) (ofNat.{u} j) = zero
    rw [opAt_polyMulOp hR hpow hL]
    have hsucc : (k + 1) * M = k * M + M := Nat.succ_mul k M
    refine polyMul_bound hR ((mem_polyRing_iff _ _ _).mp hpow)
      ((mem_polyRing_iff _ _ _).mp hL) (ringPow_bound hR hL hM k) hM j ?_
    omega

/-! ## Evaluation respects the operations -/

theorem evalAt_polyAdd {R add mul zero one x f g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hx : x ∈ R) (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) :
    evalAt R add mul zero one x (polyAdd R add f g)
      = opAt add (evalAt R add mul zero one x f) (evalAt R add mul zero one x g) := by
  obtain ⟨Nf, hNf⟩ := hf.right.right.right
  obtain ⟨Ng, hNg⟩ := hg.right.right.right
  have hNsum : ∀ i : Nat, Nf + Ng ≤ i → app (polyAdd R add f g) (ofNat.{u} i) = zero := by
    intro i hi
    rw [app_polyAdd hR hf hg (ofNat_mem_omega i), hNf i (by omega), hNg i (by omega),
      ringAdd_zero hR hR.addGroup.mem_e]
  rw [evalAt_eq hR hx (isPolyOver_polyAdd hR hf hg) hNsum,
    evalAt_eq hR hx hf (fun i hi => hNf i (by omega) : ∀ i : Nat, Nf + Ng ≤ i → _),
    evalAt_eq hR hx hg (fun i hi => hNg i (by omega) : ∀ i : Nat, Nf + Ng ≤ i → _),
    evalUpTo, foldF_congr (Nf + Ng) (fun i _ => by
      show opAt mul (app (polyAdd R add f g) (ofNat.{u} i)) (gpow mul one x i)
        = opAt add (opAt mul (app f (ofNat.{u} i)) (gpow mul one x i))
          (opAt mul (app g (ofNat.{u} i)) (gpow mul one x i))
      rw [app_polyAdd hR hf hg (ofNat_mem_omega i),
        ringRight_distrib hR (coeff_mem hf (ofNat_mem_omega i))
          (coeff_mem hg (ofNat_mem_omega i)) (ringPow_mem hR hx i)]),
    foldF_add (isCommMonoid_ringAdd hR) (Nf + Ng)
      (fun i _ => mulAt_mem hR (coeff_mem hf (ofNat_mem_omega i)) (ringPow_mem hR hx i))
      (fun i _ => mulAt_mem hR (coeff_mem hg (ofNat_mem_omega i)) (ringPow_mem hR hx i))]
  rfl

theorem evalAt_polyOne {R add mul zero one x : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hx : x ∈ R) : evalAt R add mul zero one x (polyOne R zero one) = one := by
  rw [evalAt_eq hR hx (isPolyOver_polyOne hR) (N := 1) (fun i hi => by
    rw [app_polyOne hR i]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rfl)]
  show opAt add zero (opAt mul (app (polyOne R zero one) (ofNat.{u} 0)) one) = one
  rw [app_polyOne hR 0]
  show opAt add zero (opAt mul one one) = one
  rw [ringZero_add hR (mulAt_mem hR hR.mem_one hR.mem_one)]
  exact hR.mul_one _ hR.mem_one

/-! ## Evaluation is multiplicative

The Cauchy product: expanding `(∑ f_a x^a)(∑ g_b x^b)` gives a rectangle of
terms, expanding `∑_k (fg)_k x^k` gives a triangle, and the two agree because
everything outside the rectangle vanishes. -/

theorem isCommMonoid_ringMul {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    IsCommMonoid R mul one :=
  ⟨hR.mulFun, hR.mulDom, hR.mulRan, hR.mem_one, hR.mulAssoc,
    fun a ha => ringOne_mul hR ha, hR.mulComm⟩

def evalTerm (mul one x f g : ZFSet.{u}) (a b : Nat) : ZFSet.{u} :=
  opAt mul (opAt mul (app f (ofNat.{u} a)) (app g (ofNat.{u} b))) (gpow mul one x (a + b))

theorem evalAt_polyMul {R add mul zero one x f g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hx : x ∈ R) (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) :
    evalAt R add mul zero one x (polyMul R add mul zero f g)
      = opAt mul (evalAt R add mul zero one x f) (evalAt R add mul zero one x g) := by
  have hM := isCommMonoid_ringAdd hR
  obtain ⟨Nf, hNf⟩ := hf.right.right.right
  obtain ⟨Ng, hNg⟩ := hg.right.right.right
  have hSmem : ∀ a b : Nat, evalTerm mul one x f g a b ∈ R := fun a b =>
    mulAt_mem hR (mulAt_mem hR (coeff_mem hf (ofNat_mem_omega a))
      (coeff_mem hg (ofNat_mem_omega b))) (ringPow_mem hR hx (a + b))
  -- the triangle side
  have hleft : evalAt R add mul zero one x (polyMul R add mul zero f g)
      = foldF add zero (fun k => foldF add zero
          (fun a => evalTerm mul one x f g a (k - a)) (k + 1)) (Nf + Ng + 1) := by
    rw [evalAt_eq hR hx (isPolyOver_polyMul hR hf hg) (N := Nf + Ng + 1) (fun i hi => by
      rw [app_polyMul hR hf hg i]
      exact convCoeff_eq_zero hR hf hg hNf hNg (by omega)), evalUpTo]
    refine foldF_congr (Nf + Ng + 1) (fun k hk => ?_)
    show opAt mul (app (polyMul R add mul zero f g) (ofNat.{u} k)) (gpow mul one x k) = _
    rw [app_polyMul hR hf hg k, convCoeff,
      foldF_mul_right hR (ringPow_mem hR hx k)
        (fun a => mulAt_mem hR (coeff_mem hf (ofNat_mem_omega a))
          (coeff_mem hg (ofNat_mem_omega (k - a)))) (k + 1)]
    refine foldF_congr (k + 1) (fun a ha => ?_)
    show opAt mul (opAt mul (app f (ofNat.{u} a)) (app g (ofNat.{u} (k - a))))
        (gpow mul one x k) = evalTerm mul one x f g a (k - a)
    rw [evalTerm, show a + (k - a) = k by omega]
  -- collapse the triangle to the rectangle
  have hrect : foldF add zero (fun a => foldF add zero
        (fun b => evalTerm mul one x f g a b) (Nf + Ng - a + 1)) (Nf + Ng + 1)
      = foldF add zero (fun a => foldF add zero
        (fun b => evalTerm mul one x f g a b) Ng) Nf := by
    rw [foldF_trunc hM (n := Nf) (fun a _ => foldF_mem hM _ (fun b _ => hSmem a b))
      (fun a ha => foldF_zeros hR _ (fun b _ => by
        rw [evalTerm, hNf a ha, ringZero_mul hR (coeff_mem hg (ofNat_mem_omega b)),
          ringZero_mul hR (ringPow_mem hR hx (a + b))]))
      (Nf + Ng + 1) (by omega)]
    refine foldF_congr Nf (fun a ha => ?_)
    exact foldF_trunc hM (n := Ng) (fun b _ => hSmem a b)
      (fun b hb => by
        rw [evalTerm, hNg b hb, mul_zero_of_isRing hR (coeff_mem hf (ofNat_mem_omega a)),
          ringZero_mul hR (ringPow_mem hR hx (a + b))])
      (Nf + Ng - a + 1) (by omega)
  -- the rectangle side
  have hright : opAt mul (evalAt R add mul zero one x f) (evalAt R add mul zero one x g)
      = foldF add zero (fun a => foldF add zero
        (fun b => evalTerm mul one x f g a b) Ng) Nf := by
    rw [evalAt_eq hR hx hf hNf, evalAt_eq hR hx hg hNg, evalUpTo, evalUpTo,
      foldF_mul_right hR (foldF_mem hM Ng (fun b _ => mulAt_mem hR
          (coeff_mem hg (ofNat_mem_omega b)) (ringPow_mem hR hx b)))
        (fun a => mulAt_mem hR (coeff_mem hf (ofNat_mem_omega a)) (ringPow_mem hR hx a)) Nf]
    refine foldF_congr Nf (fun a ha => ?_)
    show opAt mul (opAt mul (app f (ofNat.{u} a)) (gpow mul one x a))
        (foldF add zero (fun b => opAt mul (app g (ofNat.{u} b)) (gpow mul one x b)) Ng)
      = foldF add zero (fun b => evalTerm mul one x f g a b) Ng
    rw [foldF_mul_left hR (mulAt_mem hR (coeff_mem hf (ofNat_mem_omega a))
        (ringPow_mem hR hx a))
      (fun b => mulAt_mem hR (coeff_mem hg (ofNat_mem_omega b)) (ringPow_mem hR hx b)) Ng]
    refine foldF_congr Ng (fun b hb => ?_)
    show opAt mul (opAt mul (app f (ofNat.{u} a)) (gpow mul one x a))
        (opAt mul (app g (ofNat.{u} b)) (gpow mul one x b))
      = evalTerm mul one x f g a b
    rw [opAt_shuffle4 (isCommMonoid_ringMul hR) (coeff_mem hf (ofNat_mem_omega a))
      (ringPow_mem hR hx a) (coeff_mem hg (ofNat_mem_omega b)) (ringPow_mem hR hx b),
      evalTerm, ringPow_add hR hx a b]
  rw [hleft, foldF_triangle hM (S := evalTerm mul one x f g) hSmem (Nf + Ng), hrect, hright]

/-! ## A list of coefficients as a polynomial

`Poly.lean` evaluates a Lean-level list; this is the same data as a set, and
`evalAt_polyOfList` says the two evaluations agree, which carries
`poly_roots_lt` over to `R[x]`. -/

def listCoeff (zero : ZFSet.{u}) : List ZFSet.{u} → Nat → ZFSet.{u}
  | [], _ => zero
  | c :: _, 0 => c
  | _ :: cs, k + 1 => listCoeff zero cs k

theorem listCoeff_mem {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    ∀ (cs : List ZFSet.{u}), (∀ c, c ∈ cs → c ∈ R) → ∀ k : Nat, listCoeff zero cs k ∈ R
  | [], _, _ => hR.addGroup.mem_e
  | c :: cs, hcs, 0 => hcs c List.mem_cons_self
  | _ :: cs, hcs, k + 1 =>
    listCoeff_mem hR cs (fun d hd => hcs d (List.mem_cons_of_mem _ hd)) k

theorem listCoeff_eq_zero {zero : ZFSet.{u}} :
    ∀ (cs : List ZFSet.{u}) (k : Nat), cs.length ≤ k → listCoeff zero cs k = zero
  | [], _, _ => rfl
  | c :: cs, 0, h => absurd (show cs.length + 1 ≤ 0 from h) (by omega)
  | c :: cs, k + 1, h => by
    refine listCoeff_eq_zero cs k ?_
    have : cs.length + 1 ≤ k + 1 := h
    omega

def polyOfList (R zero : ZFSet.{u}) (cs : List ZFSet.{u}) : ZFSet.{u} :=
  polyOfSeq R (listCoeff zero cs)

theorem isPolyOver_polyOfList {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (cs : List ZFSet.{u}) (hcs : ∀ c, c ∈ cs → c ∈ R) :
    IsPolyOver R zero (polyOfList R zero cs) :=
  isPolyOver_polyOfSeq (listCoeff_mem hR cs hcs) (N := cs.length)
    (fun i hi => listCoeff_eq_zero cs i hi)

/-- The two evaluations agree. -/
theorem evalAt_polyOfList {R add mul zero one x : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hx : x ∈ R) :
    ∀ (cs : List ZFSet.{u}), (∀ c, c ∈ cs → c ∈ R) →
      evalAt R add mul zero one x (polyOfList R zero cs) = polyEval add mul zero cs x
  | [], _ => by
    rw [evalAt_eq hR hx (isPolyOver_polyOfList hR [] (fun c hc => absurd hc List.not_mem_nil))
      (N := 0) (fun i _ => by
        rw [polyOfList, app_polyOfSeq (listCoeff_mem hR [] (fun c hc =>
          absurd hc List.not_mem_nil)) i]
        rfl)]
    rfl
  | c :: cs, hcs => by
    have hc : c ∈ R := hcs c List.mem_cons_self
    have hrest : ∀ d, d ∈ cs → d ∈ R := fun d hd => hcs d (List.mem_cons_of_mem _ hd)
    have hmemC := listCoeff_mem hR (c :: cs) hcs
    have hmemR := listCoeff_mem hR cs hrest
    have hterm : ∀ i : Nat, opAt mul (listCoeff zero cs i) (gpow mul one x i) ∈ R :=
      fun i => mulAt_mem hR (hmemR i) (ringPow_mem hR hx i)
    -- the tail, in coefficient form
    have hIH : foldF add zero
        (fun i => opAt mul (listCoeff zero cs i) (gpow mul one x i)) cs.length
        = polyEval add mul zero cs x := by
      rw [← evalAt_polyOfList hR hx cs hrest,
        evalAt_eq hR hx (isPolyOver_polyOfList hR cs hrest) (N := cs.length) (fun i hi => by
          rw [polyOfList, app_polyOfSeq hmemR i]
          exact listCoeff_eq_zero cs i hi), evalUpTo]
      exact foldF_congr cs.length (fun i _ => by
        show opAt mul (listCoeff zero cs i) (gpow mul one x i)
          = opAt mul (app (polyOfList R zero cs) (ofNat.{u} i)) (gpow mul one x i)
        rw [polyOfList, app_polyOfSeq hmemR i])
    rw [evalAt_eq hR hx (isPolyOver_polyOfList hR (c :: cs) hcs) (N := cs.length + 1)
        (fun i hi => by
          rw [polyOfList, app_polyOfSeq hmemC i]
          exact listCoeff_eq_zero (c :: cs) i hi),
      evalUpTo, foldF_congr (cs.length + 1) (F := fun i =>
          opAt mul (app (polyOfList R zero (c :: cs)) (ofNat.{u} i)) (gpow mul one x i))
        (G := fun i => opAt mul (listCoeff zero (c :: cs) i) (gpow mul one x i))
        (fun i _ => by
          show opAt mul (app (polyOfList R zero (c :: cs)) (ofNat.{u} i)) (gpow mul one x i)
            = opAt mul (listCoeff zero (c :: cs) i) (gpow mul one x i)
          rw [polyOfList, app_polyOfSeq hmemC i]),
      foldF_cons (isCommMonoid_ringAdd hR) cs.length
        (fun i _ => mulAt_mem hR (hmemC i) (ringPow_mem hR hx i)),
      foldF_congr cs.length (F := fun i =>
          opAt mul (listCoeff zero (c :: cs) (i + 1)) (gpow mul one x (i + 1)))
        (G := fun i => opAt mul x (opAt mul (listCoeff zero cs i) (gpow mul one x i)))
        (fun i _ => by
          show opAt mul (listCoeff zero cs i) (opAt mul (gpow mul one x i) x)
            = opAt mul x (opAt mul (listCoeff zero cs i) (gpow mul one x i))
          rw [← hR.mulAssoc _ (hmemR i) _ (ringPow_mem hR hx i) _ hx,
            hR.mulComm _ (mulAt_mem hR (hmemR i) (ringPow_mem hR hx i)) _ hx]),
      ← foldF_mul_left hR hx hterm cs.length, hIH]
    show opAt add (opAt mul c one) _ = opAt add c (opAt mul x (polyEval add mul zero cs x))
    rw [hR.mul_one c hc]

/-! ## Reading a polynomial back as a list

The other direction: the first `N` coefficients of `f`, as a list. With it the
root bound of `Poly.lean` becomes a statement about `R[x]`. -/

/-- Reading a coefficient of a `polyOfList`.

`polyOfList` is `polyOfSeq` over `listCoeff`, so this is `app_polyOfSeq` with
the definition unfolded -- the step every caller was taking inline. -/
theorem app_polyOfList {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (cs : List ZFSet.{u})
    (hcs : ∀ c, c ∈ cs → c ∈ R) (k : Nat) :
    app (polyOfList R zero cs) (ofNat.{u} k) = listCoeff zero cs k := by
  rw [polyOfList, app_polyOfSeq (listCoeff_mem hR _ hcs) k]

/-! ## Degree

`IsDegOf f d` says `d` is the least support bound -- the number of
coefficients, one more than the classical degree for a non-zero polynomial and
`0` for the zero polynomial. `IsBoundOf f n` below is the weaker sibling, SOME
bound rather than the least, and `deg_unique` is what separates them: a
statement reading `IsDegOf zero f (d + 1)` is about the least bound, so the
`+ 1` is the gap between the top non-zero coefficient's INDEX and that bound,
not an off-by-one in the caller. Stating it costs nothing; producing it is another
matter. Finding the least bound means deciding, coefficient by coefficient,
whether it vanishes, and over a general ring that is not decidable. So degree is
a partial function here, available exactly when vanishing is decidable -- and
`deg_reverses` shows that is not an artefact of the proof: a degree for every
polynomial is a decision procedure for vanishing. -/

def IsBoundOf (zero f : ZFSet.{u}) (n : Nat) : Prop :=
  ∀ i : Nat, n ≤ i → app f (ofNat.{u} i) = zero

def IsDegOf (zero f : ZFSet.{u}) (d : Nat) : Prop :=
  IsBoundOf zero f d ∧ ∀ n : Nat, n < d → ¬ IsBoundOf zero f n

/-- A degree exists once vanishing is decidable. No ring structure: the argument
is a bounded search for the last non-zero coefficient, and the bound comes from
the polynomial's own support condition. -/
theorem exists_deg {R zero f : ZFSet.{u}}
    (hdec : DecidableVanishing R zero) (hf : IsPolyOver R zero f) :
    ∃ d : Nat, IsDegOf zero f d := by
  obtain ⟨N, hN⟩ := hf.right.right.right
  -- being a bound is decidable below `N`, and automatic above it
  have hQdec : ∀ n : Nat, IsBoundOf zero f n ∨ ¬ IsBoundOf zero f n := by
    intro n
    rcases exists_lt_or_not
      (Q := fun i => n ≤ i ∧ app f (ofNat.{u} i) ≠ zero)
      (fun i => by
        rcases Nat.lt_or_ge i n with hlt | hge
        · exact Or.inr (fun h => absurd h.left (by omega))
        · rcases hdec _ (coeff_mem hf (ofNat_mem_omega i)) with h | h
          · exact Or.inr (fun hc => hc.right h)
          · exact Or.inl ⟨hge, h⟩) N with ⟨i, hi, hni, hne⟩ | hno
    · exact Or.inr (fun hb => hne (hb i hni))
    · refine Or.inl (fun i hi => ?_)
      rcases Nat.lt_or_ge i N with hlt | hge
      · rcases hdec _ (coeff_mem hf (ofNat_mem_omega i)) with h | h
        · exact h
        · exact absurd ⟨hi, h⟩ (hno i hlt)
      · exact hN i hge
  obtain ⟨d, hd, hleast⟩ := exists_least hQdec N hN
  exact ⟨d, hd, hleast⟩

/-- Over a finite ring the hypothesis is free. -/
theorem decidableVanishing_of_finite {R zero : ZFSet.{u}} {n : Nat}
    (hR : Equinumerous R (ofNat.{u} n)) (hzero : zero ∈ R) : DecidableVanishing R zero :=
  fun a ha => eq_or_ne_of_finite hR ha hzero

/-! ## Division with remainder

Given `f` whose coefficient at `d` is invertible and which vanishes above `d`,
every `g` splits as `q·f + r` with `r` vanishing at and above `d`. The induction
is on a support bound for `g`: subtracting the right multiple of `f` by a
monomial kills the top coefficient. -/

def polySub (R add mul zero f g : ZFSet.{u}) : ZFSet.{u} :=
  polyAdd R add f (polyNeg R add zero g)

theorem isPolyOver_polySub {R add mul zero one f g : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) :
    IsPolyOver R zero (polySub R add mul zero f g) :=
  isPolyOver_polyAdd hR hf (isPolyOver_polyNeg hR hg)

theorem app_polySub {R add mul zero one f g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) {w : ZFSet.{u}}
    (hw : w ∈ omega.{u}) :
    app (polySub R add mul zero f g) w = ringSub R add zero (app f w) (app g w) := by
  rw [polySub, app_polyAdd hR hf (isPolyOver_polyNeg hR hg) hw, app_polyNeg hR hg hw]
  rfl

theorem polySub_add_cancel {R add mul zero one f g : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) :
    polyAdd R add (polySub R add mul zero f g) g = f := by
  refine poly_ext (isPolyOver_polyAdd hR (isPolyOver_polySub hR hf hg) hg) hf (fun w hw => ?_)
  rw [app_polyAdd hR (isPolyOver_polySub hR hf hg) hg hw, app_polySub hR hf hg hw]
  show opAt add (opAt add (app f w) (ringNeg R add zero (app g w))) (app g w) = app f w
  rw [ringAdd_assoc hR (coeff_mem hf hw) (ringNeg_mem hR (coeff_mem hg hw))
      (coeff_mem hg hw), ringNeg_add hR (coeff_mem hg hw),
    ringAdd_zero hR (coeff_mem hf hw)]

/-- Division with remainder. -/
theorem exists_polyDiv {R add mul zero one f : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) {d : Nat} (hfd : ∀ i : Nat, d < i → app f (ofNat.{u} i) = zero)
    {u : ZFSet.{u}} (hu : u ∈ R) (hlead : opAt mul (app f (ofNat.{u} d)) u = one) :
    ∀ N : Nat, ∀ g : ZFSet.{u}, IsPolyOver R zero g →
      (∀ i : Nat, N ≤ i → app g (ofNat.{u} i) = zero) →
      ∃ q r : ZFSet.{u}, IsPolyOver R zero q ∧ IsPolyOver R zero r ∧
        (∀ i : Nat, d ≤ i → app r (ofNat.{u} i) = zero) ∧
        g = polyAdd R add (polyMul R add mul zero q f) r := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro g hg hgN
    rcases Nat.lt_or_ge N (d + 1) with hsmall | hbig
    · -- `g` is already a remainder
      refine ⟨polyZero R zero, g, isPolyOver_polyZero hR, hg, fun i hi => hgN i (by omega), ?_⟩
      refine poly_ext hg (isPolyOver_polyAdd hR
        (isPolyOver_polyMul hR (isPolyOver_polyZero hR) hf) hg) (fun w hw => ?_)
      rw [app_polyAdd hR (isPolyOver_polyMul hR (isPolyOver_polyZero hR) hf) hg hw]
      obtain ⟨k, rfl⟩ := (mem_omega_iff w).mp hw
      rw [app_polyMul hR (isPolyOver_polyZero hR) hf k, convCoeff,
        foldF_zeros hR (k + 1) (fun j _ => by
          rw [app_polyZero hR (ofNat_mem_omega j),
            ringZero_mul hR (coeff_mem hf (ofNat_mem_omega (k - j)))]),
        ringZero_add hR (coeff_mem hg (ofNat_mem_omega k))]
    · -- kill the top coefficient of `g` with a multiple of `f`
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      have hMd : d ≤ M := by omega
      have hc : app g (ofNat.{u} M) ∈ R := coeff_mem hg (ofNat_mem_omega M)
      have hcu : opAt mul (app g (ofNat.{u} M)) u ∈ R := mulAt_mem hR hc hu
      have hmon := isPolyOver_monomial hR hcu (M - d)
      have hprod := isPolyOver_polyMul hR hmon hf
      have hg' := isPolyOver_polySub hR hg hprod
      -- the product agrees with `g` at `M` and vanishes above it
      have hprodval : ∀ i : Nat, M ≤ i →
          app (polyMul R add mul zero (monomial R zero (opAt mul (app g (ofNat.{u} M)) u)
            (M - d)) f) (ofNat.{u} i) = if i = M then app g (ofNat.{u} M) else zero := by
        intro i hi
        rw [app_polyMul hR hmon hf i, convCoeff_monomial hR hcu hf (M - d) i,
          if_pos (by omega)]
        rcases Nat.decEq i M with hne | rfl
        · rw [if_neg hne, hfd (i - (M - d)) (by omega),
            mul_zero_of_isRing hR hcu]
        · rw [if_pos rfl, show i - (i - d) = d by omega, hR.mulAssoc _ hc _ hu _
            (coeff_mem hf (ofNat_mem_omega d)), hR.mulComm u hu _
            (coeff_mem hf (ofNat_mem_omega d)), hlead, hR.mul_one _ hc]
      have hg'bound : ∀ i : Nat, M ≤ i →
          app (polySub R add mul zero g (polyMul R add mul zero
            (monomial R zero (opAt mul (app g (ofNat.{u} M)) u) (M - d)) f)) (ofNat.{u} i)
            = zero := by
        intro i hi
        rw [app_polySub hR hg hprod (ofNat_mem_omega i), hprodval i hi]
        rcases Nat.decEq i M with hne | rfl
        · rw [if_neg hne, hgN i (by omega), ringSub_self hR hR.addGroup.mem_e]
        · rw [if_pos rfl, ringSub_self hR hc]
      obtain ⟨q, r, hq, hr, hrbound, hsplit⟩ := ih M (by omega) _ hg' hg'bound
      -- put the monomial back
      refine ⟨polyAdd R add q (monomial R zero (opAt mul (app g (ofNat.{u} M)) u) (M - d)),
        r, isPolyOver_polyAdd hR hq hmon, hr, hrbound, ?_⟩
      have hexpand : polyMul R add mul zero
          (polyAdd R add q (monomial R zero (opAt mul (app g (ofNat.{u} M)) u) (M - d))) f
          = polyAdd R add (polyMul R add mul zero q f) (polyMul R add mul zero
            (monomial R zero (opAt mul (app g (ofNat.{u} M)) u) (M - d)) f) := by
        refine poly_ext_coeff (isPolyOver_polyMul hR (isPolyOver_polyAdd hR hq hmon) hf)
          (isPolyOver_polyAdd hR (isPolyOver_polyMul hR hq hf) hprod) (fun k => ?_)
        rw [app_polyMul hR (isPolyOver_polyAdd hR hq hmon) hf k,
          app_polyAdd hR (isPolyOver_polyMul hR hq hf) hprod (ofNat_mem_omega k),
          app_polyMul hR hq hf k, app_polyMul hR hmon hf k,
          convCoeff_comm hR (isPolyOver_polyAdd hR hq hmon) hf,
          convCoeff_comm hR hq hf, convCoeff_comm hR hmon hf,
          convCoeff_distrib hR hf hq hmon]
      rw [hexpand]
      -- `g = (qf + mf) + r`, from `g - mf = qf + r`
      refine Eq.trans (polySub_add_cancel hR hg hprod).symm ?_
      rw [hsplit]
      refine poly_ext (isPolyOver_polyAdd hR (isPolyOver_polyAdd hR
          (isPolyOver_polyMul hR hq hf) hr) hprod)
        (isPolyOver_polyAdd hR (isPolyOver_polyAdd hR (isPolyOver_polyMul hR hq hf) hprod) hr)
        (fun w hw => ?_)
      rw [app_polyAdd hR (isPolyOver_polyAdd hR (isPolyOver_polyMul hR hq hf) hr) hprod hw,
        app_polyAdd hR (isPolyOver_polyMul hR hq hf) hr hw,
        app_polyAdd hR (isPolyOver_polyAdd hR (isPolyOver_polyMul hR hq hf) hprod) hr hw,
        app_polyAdd hR (isPolyOver_polyMul hR hq hf) hprod hw,
        ringAdd_assoc hR (coeff_mem (isPolyOver_polyMul hR hq hf) hw) (coeff_mem hr hw)
          (coeff_mem hprod hw),
        ringAdd_assoc hR (coeff_mem (isPolyOver_polyMul hR hq hf) hw) (coeff_mem hprod hw)
          (coeff_mem hr hw),
        ringAdd_comm hR (coeff_mem hr hw) (coeff_mem hprod hw)]

/-! ## Leading coefficients

Over a ring where vanishing is decidable, a polynomial is either zero or has a
top non-zero coefficient, which is what division needs to be applicable and the
only place `DecidableVanishing` is used. -/

theorem eq_polyZero_of_coeffs {R add mul zero one p : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hp : IsPolyOver R zero p)
    (h : ∀ i : Nat, app p (ofNat.{u} i) = zero) : p = polyZero R zero := by
  refine poly_ext_coeff hp (isPolyOver_polyZero hR) (fun k => ?_)
  rw [h k, app_polyZero hR (ofNat_mem_omega k)]

theorem exists_lead {R add mul zero one p : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hdec : DecidableVanishing R zero) (hp : IsPolyOver R zero p) :
    ∀ N : Nat, (∀ i : Nat, N ≤ i → app p (ofNat.{u} i) = zero) →
      p = polyZero R zero ∨ ∃ d : Nat, d < N ∧ app p (ofNat.{u} d) ≠ zero ∧
        ∀ i : Nat, d < i → app p (ofNat.{u} i) = zero := by
  intro N
  induction N with
  | zero => exact fun hN => Or.inl (eq_polyZero_of_coeffs hR hp (fun i => hN i (by omega)))
  | succ N ih =>
    intro hN
    rcases hdec _ (coeff_mem hp (ofNat_mem_omega N)) with hz | hne
    · rcases ih (fun i hi => by
        rcases Nat.eq_or_lt_of_le hi with heq | hlt
        · rw [← heq]
          exact hz
        · exact hN i (by omega)) with h | ⟨d, hd, hdne, hdz⟩
      · exact Or.inl h
      · exact Or.inr ⟨d, by omega, hdne, hdz⟩
    · exact Or.inr ⟨N, by omega, hne, fun i hi => hN i (by omega)⟩

/-! ## Divisibility, in ring form

The Euclidean algorithm is easier stated with the ring operations of `R[x]` than
with `polyAdd`/`polyMul`, because then the generic ring toolkit applies. -/

theorem convCoeff_one_left {R add mul zero one g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hg : IsPolyOver R zero g) (k : Nat) :
    convCoeff R add mul zero (polyOne R zero one) g k = app g (ofNat.{u} k) := by
  have hz : ∀ j : Nat, j ≠ 0 → opAt mul (app (polyOne R zero one) (ofNat.{u} j))
      (app g (ofNat.{u} (k - j))) = zero := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [app_polyOne hR (i + 1)]
    show opAt mul zero (app g (ofNat.{u} (k - (i + 1)))) = zero
    exact ringZero_mul hR (coeff_mem hg (ofNat_mem_omega (k - (i + 1))))
  rw [convCoeff, foldF_single hR
    (T := fun j => opAt mul (app (polyOne R zero one) (ofNat.{u} j))
      (app g (ofNat.{u} (k - j)))) (k := 0)
    (mulAt_mem hR (coeff_mem (isPolyOver_polyOne hR) (ofNat_mem_omega 0))
      (coeff_mem hg (ofNat_mem_omega (k - 0)))) hz (k + 1) (by omega)]
  show opAt mul (app (polyOne R zero one) (ofNat.{u} 0)) (app g (ofNat.{u} (k - 0))) = _
  rw [app_polyOne hR 0, show k - 0 = k by omega]
  exact ringOne_mul hR (coeff_mem hg (ofNat_mem_omega k))

theorem polyMul_one_left {R add mul zero one g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hg : IsPolyOver R zero g) : polyMul R add mul zero (polyOne R zero one) g = g := by
  refine poly_ext_coeff (isPolyOver_polyMul hR (isPolyOver_polyOne hR) hg) hg (fun k => ?_)
  rw [app_polyMul hR (isPolyOver_polyOne hR) hg k]
  exact convCoeff_one_left hR hg k

def polyDvd (R add mul zero e g : ZFSet.{u}) : Prop :=
  ∃ q, q ∈ PolyRing R zero ∧ g = opAt (polyMulOp R add mul zero) q e

theorem polyDvd_refl {R add mul zero one e : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (he : e ∈ PolyRing R zero) : polyDvd R add mul zero e e := by
  refine ⟨polyOne R zero one, polyOne_mem hR, ?_⟩
  rw [opAt_polyMulOp hR (polyOne_mem hR) he,
    polyMul_one_left hR ((mem_polyRing_iff _ _ _).mp he)]

theorem polyDvd_zero {R add mul zero one e : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (he : e ∈ PolyRing R zero) : polyDvd R add mul zero e (polyZero R zero) := by
  have hP := isRing_polyRing (one := one) hR
  refine ⟨polyZero R zero, (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyZero hR), ?_⟩
  rw [hP.mulComm _ ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyZero hR)) _ he]
  exact (mul_zero_of_isRing hP he).symm

theorem polyDvd_add {R add mul zero one e u v : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (he : e ∈ PolyRing R zero) (hu : polyDvd R add mul zero e u)
    (hv : polyDvd R add mul zero e v) :
    polyDvd R add mul zero e (opAt (polyAddOp R add zero) u v) := by
  have hP := isRing_polyRing (one := one) hR
  obtain ⟨p, hp, rfl⟩ := hu
  obtain ⟨q, hq, rfl⟩ := hv
  exact ⟨opAt (polyAddOp R add zero) p q, opAt_mem hP.addGroup hp hq,
    (ringRight_distrib hP hp hq he).symm⟩

theorem polyDvd_mul {R add mul zero one e u w : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (he : e ∈ PolyRing R zero) (hw : w ∈ PolyRing R zero)
    (hu : polyDvd R add mul zero e u) :
    polyDvd R add mul zero e (opAt (polyMulOp R add mul zero) w u) := by
  have hP := isRing_polyRing (one := one) hR
  obtain ⟨p, hp, rfl⟩ := hu
  exact ⟨opAt (polyMulOp R add mul zero) w p, mulAt_mem hP hw hp,
    (hP.mulAssoc _ hw _ hp _ he).symm⟩

/-! ## Bézout in `F[x]`

The Euclidean algorithm, as a strong induction on a support bound for the second
argument: divide, recurse on the remainder, carry the coefficients back. Over a
field the leading coefficient is invertible, so `exists_polyDiv` always applies. -/

theorem exists_polyBezout {R add mul zero one : ZFSet.{u}} (hF : IsField R add mul zero one)
    (hdec : DecidableVanishing R zero) :
    ∀ N : Nat, ∀ a b : ZFSet.{u}, a ∈ PolyRing R zero → b ∈ PolyRing R zero →
      (∀ i : Nat, N ≤ i → app b (ofNat.{u} i) = zero) →
      ∃ e, e ∈ PolyRing R zero ∧ polyDvd R add mul zero e a ∧ polyDvd R add mul zero e b ∧
        ∃ x y, x ∈ PolyRing R zero ∧ y ∈ PolyRing R zero ∧
          e = opAt (polyAddOp R add zero) (opAt (polyMulOp R add mul zero) x a)
            (opAt (polyMulOp R add mul zero) y b) := by
  have hR := hF.ring
  have hP := isRing_polyRing (one := one) hR
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro a b ha hb hbN
    have haP := (mem_polyRing_iff _ _ _).mp ha
    have hbP := (mem_polyRing_iff _ _ _).mp hb
    have honeP : polyOne R zero one ∈ PolyRing R zero :=
      polyOne_mem hR
    have hzeroP : polyZero R zero ∈ PolyRing R zero :=
      (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyZero hR)
    rcases exists_lead hR hdec hbP N hbN with hzero | ⟨d, hdN, hlead, habove⟩
    · -- `b = 0`, so the gcd is `a`
      refine ⟨a, ha, polyDvd_refl (one := one) hR ha, ?_,
        polyOne R zero one, polyZero R zero, honeP, hzeroP, ?_⟩
      · rw [hzero]
        exact polyDvd_zero (one := one) hR ha
      · rw [hzero, hP.mulComm _ hzeroP _ hzeroP, mul_zero_of_isRing hP hzeroP,
          opAt_polyMulOp hR honeP ha, polyMul_one_left hR haP]
        exact (hP.addGroup.right_id a ha).symm
    · -- divide `a` by `b` and recurse on the remainder
      obtain ⟨u, hu, hlead'⟩ := hF.inverses _ (coeff_mem hbP (ofNat_mem_omega d)) hlead
      obtain ⟨Na, hNa⟩ := haP.right.right.right
      obtain ⟨q, r, hq, hr, hrb, hsplit⟩ :=
        exists_polyDiv hR hbP (fun i hi => habove i hi) hu hlead' Na a haP hNa
      have hqP : q ∈ PolyRing R zero := (mem_polyRing_iff _ _ _).mpr hq
      have hrP : r ∈ PolyRing R zero := (mem_polyRing_iff _ _ _).mpr hr
      obtain ⟨e, he, hedvd, herdvd, x, y, hx, hy, hbez⟩ :=
        ih d hdN b r hb hrP (fun i hi => hrb i hi)
      -- `a = qb + r`, so `e` divides `a` too
      have hqb : a = opAt (polyAddOp R add zero) (opAt (polyMulOp R add mul zero) q b) r := by
        rw [opAt_polyMulOp hR hqP hb, opAt_polyAddOp hR
          ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyMul hR hq hbP)) hrP]
        exact hsplit
      refine ⟨e, he, ?_, hedvd, ?_⟩
      · rw [hqb]
        exact polyDvd_add (one := one) hR he
          (polyDvd_mul (one := one) hR he hqP hedvd) herdvd
      · -- `e = xb + yr = ya + (x - yq)b`
        refine ⟨y, ringSub (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero) x
            (opAt (polyMulOp R add mul zero) y q),
          hy, ringSub_mem hP hx (mulAt_mem hP hy hqP), ?_⟩
        have hr_eq : r = ringSub (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero)
            a (opAt (polyMulOp R add mul zero) q b) := by
          rw [hqb]
          show _ = opAt (polyAddOp R add zero)
            (opAt (polyAddOp R add zero) (opAt (polyMulOp R add mul zero) q b) r)
            (ringNeg (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero)
              (opAt (polyMulOp R add mul zero) q b))
          rw [hP.addComm _ (mulAt_mem hP hqP hb) _ hrP,
            hP.addGroup.assoc _ hrP _ (mulAt_mem hP hqP hb) _
              (ringNeg_mem hP (mulAt_mem hP hqP hb)),
            ringAdd_neg hP (mulAt_mem hP hqP hb), hP.addGroup.right_id _ hrP]
        rw [hbez, hr_eq, ringMul_sub hP hy ha (mulAt_mem hP hqP hb),
          ringSub_def, ringSub_def,
          ringRight_distrib hP hx (ringNeg_mem hP (mulAt_mem hP hy hqP)) hb,
          ringNeg_mul hP (mulAt_mem hP hy hqP) hb,
          ← hP.mulAssoc _ hy _ hqP _ hb,
          ringAdd_left_comm hP (mulAt_mem hP hx hb) (mulAt_mem hP hy ha)
            (ringNeg_mem hP (mulAt_mem hP (mulAt_mem hP hy hqP) hb))]

/-! ## Tuples of coefficients

A polynomial supported below `d` is `d` coefficients, so the polynomials
supported below `d` are covered by the `d`-fold product of `R` with itself, so
`R[x]/(f)` is finite: division puts every class in that range. -/

def powSet (R : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => singleton empty.{u}
  | d + 1 => prod (powSet R d) R

def tupleOf (C : Nat → ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => empty.{u}
  | k + 1 => opair (tupleOf C k) (C k)

def tupleCoeff (t : ZFSet.{u}) : Nat → Nat → ZFSet.{u}
  | 0, _ => empty.{u}
  | d + 1, i => if i = d then snd t else tupleCoeff (fst t) d i

theorem tupleOf_mem {R : ZFSet.{u}} {C : Nat → ZFSet.{u}} :
    ∀ d : Nat, (∀ i, i < d → C i ∈ R) → tupleOf C d ∈ powSet R d
  | 0, _ => (mem_singleton_iff _ _).mpr rfl
  | d + 1, hC =>
    opair_mem_prod (tupleOf_mem d (fun i hi => hC i (by omega))) (hC d (by omega))

theorem tupleCoeff_tupleOf {C : Nat → ZFSet.{u}} :
    ∀ (d i : Nat), i < d → tupleCoeff (tupleOf C d) d i = C i
  | 0, _, hi => absurd hi (by omega)
  | d + 1, i, hi => by
    show (if i = d then snd (opair (tupleOf C d) (C d))
      else tupleCoeff (fst (opair (tupleOf C d) (C d))) d i) = C i
    rcases Nat.decEq i d with hne | rfl
    · rw [if_neg hne, fst_opair]
      exact tupleCoeff_tupleOf d i (by omega)
    · rw [if_pos rfl, snd_opair]

theorem tupleCoeff_mem {R : ZFSet.{u}} :
    ∀ (d : Nat) (t : ZFSet.{u}), t ∈ powSet R d → ∀ i : Nat, i < d → tupleCoeff t d i ∈ R
  | 0, _, _, _, hi => absurd hi (by omega)
  | d + 1, t, ht, i, hi => by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff t _ _).mp ht
    show (if i = d then snd (opair a b) else tupleCoeff (fst (opair a b)) d i) ∈ R
    rcases Nat.decEq i d with hne | rfl
    · rw [if_neg hne, fst_opair]
      exact tupleCoeff_mem d a ha i (by omega)
    · rw [if_pos rfl, snd_opair]
      exact hb

theorem equinumerous_powSet {R : ZFSet.{u}} {n : Nat} (hR : Equinumerous R (ofNat.{u} n)) :
    ∀ d : Nat, Equinumerous (powSet R d) (ofNat.{u} (n ^ d))
  | 0 => by
    show Equinumerous (singleton empty.{u}) (ofNat.{u} 1)
    exact equinumerous_singleton_one
  | d + 1 => by
    show Equinumerous (prod (powSet R d) R) (ofNat.{u} (n ^ d * n))
    exact equinumerous_trans (equinumerous_prod (equinumerous_powSet hR d) hR)
      (equinumerous_prod_ofNat _ _)

/-! ## The quotient `R[x]/(f)`

With `R[x]` a ring and the general ideal quotient in place, this is an
instantiation rather than a construction. The pieces are named first, so the
statements stay small enough to elaborate (HANDBOOK 63). -/

def polyIdeal (R add mul zero f : ZFSet.{u}) : ZFSet.{u} :=
  ringMultiples (PolyRing R zero) (polyMulOp R add mul zero) f

def polyQuotRel (R add mul zero f : ZFSet.{u}) : ZFSet.{u} :=
  idealRel (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero)
    (polyIdeal R add mul zero f)

def polyQuot (R add mul zero f : ZFSet.{u}) : ZFSet.{u} :=
  quotientSet (polyQuotRel R add mul zero f) (PolyRing R zero)

theorem isIdeal_polyIdeal {R add mul zero one f : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : f ∈ PolyRing R zero) :
    IsIdeal (polyIdeal R add mul zero f) (PolyRing R zero) (polyAddOp R add zero)
      (polyMulOp R add mul zero) (polyZero R zero) :=
  isIdeal_ringMultiples (isRing_polyRing hR) hf

/-- `R[x]/(f)` is a ring. -/
theorem isRing_polyQuot {R add mul zero one f : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : f ∈ PolyRing R zero) :
    IsRing (polyQuot R add mul zero f)
      (congOp (polyQuotRel R add mul zero f) (PolyRing R zero) (polyAddOp R add zero))
      (congOp (polyQuotRel R add mul zero f) (PolyRing R zero) (polyMulOp R add mul zero))
      (cls (polyQuotRel R add mul zero f) (PolyRing R zero) (polyZero R zero))
      (cls (polyQuotRel R add mul zero f) (PolyRing R zero) (polyOne R zero one)) :=
  isRing_quotientByIdeal (isRing_polyRing hR) (isIdeal_polyIdeal hR hf)

/-! ## The quotient is finite

Every class has a representative supported below `d`, and those are covered by
`powSet R d`. So the quotient is the image of a finite set. -/

def polyOfTuple (R zero t : ZFSet.{u}) (d : Nat) : ZFSet.{u} :=
  polyOfSeq R (fun i => if i < d then tupleCoeff t d i else zero)

theorem isPolyOver_polyOfTuple {R add mul zero one t : ZFSet.{u}}
    (hR : IsRing R add mul zero one) {d : Nat} (ht : t ∈ powSet R d) :
    IsPolyOver R zero (polyOfTuple R zero t d) := by
  refine isPolyOver_polyOfSeq (fun i => ?_) (N := d) (fun i hi => if_neg (by omega))
  rcases Nat.lt_or_ge i d with hlt | hge
  · rw [if_pos hlt]
    exact tupleCoeff_mem d t ht i hlt
  · rw [if_neg (by omega)]
    exact hR.addGroup.mem_e

theorem app_polyOfTuple {R add mul zero one t : ZFSet.{u}} (hR : IsRing R add mul zero one)
    {d : Nat} (ht : t ∈ powSet R d) (i : Nat) :
    app (polyOfTuple R zero t d) (ofNat.{u} i)
      = if i < d then tupleCoeff t d i else zero := by
  refine app_polyOfSeq (fun j => ?_) i
  rcases Nat.lt_or_ge j d with hlt | hge
  · rw [if_pos hlt]
    exact tupleCoeff_mem d t ht j hlt
  · rw [if_neg (by omega)]
    exact hR.addGroup.mem_e

/-- The coefficient tuple of `r` below degree `d`. -/
def tupleOfPoly (r : ZFSet.{u}) (d : Nat) : ZFSet.{u} :=
  tupleOf (fun i => app r (ofNat.{u} i)) d

/-- A polynomial's coefficients land in its own ring. -/
theorem tupleOfPoly_mem {R zero r : ZFSet.{u}} (hr : IsPolyOver R zero r) (d : Nat) :
    tupleOfPoly.{u} r d ∈ powSet R d :=
  tupleOf_mem d (fun i _ =>
    hr.right.right.left _ (app_mem_range hr.left
      (by rw [hr.right.left]; exact ofNat_mem_omega.{u} i)))

/-- Coordinates round-trip: `polyOfTuple` is surjective onto the polynomials
supported below `d`.

With `polyOfTuple_injective` this makes the coordinate map a bijection, which is
what the counting lemma's coverage hypothesis is stated over. The hypothesis is
the support bound and not `IsPolyOver`'s own `∃ N`, because the bound has to be
`d` exactly -- a polynomial vanishing above some larger `N` has coefficients the
`d`-tuple cannot carry. -/
theorem polyOfTuple_tupleOfPoly {R add mul zero one r : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hr : IsPolyOver R zero r) {d : Nat}
    (hd : ∀ i : Nat, d ≤ i → app r (ofNat.{u} i) = zero) :
    polyOfTuple R zero (tupleOfPoly.{u} r d) d = r := by
  refine poly_ext (isPolyOver_polyOfTuple hR (tupleOfPoly_mem hr d)) hr ?_
  intro w hw
  obtain ⟨i, rfl⟩ := (mem_omega_iff w).mp hw
  rw [app_polyOfTuple hR (tupleOfPoly_mem hr d) i]
  rcases Nat.lt_or_ge i d with hlt | hge
  · rw [if_pos hlt]
    exact tupleCoeff_tupleOf d i hlt
  · rw [if_neg (by omega)]
    exact (hd i hge).symm

#print axioms tupleOfPoly
#print axioms tupleOfPoly_mem
#print axioms polyOfTuple_tupleOfPoly
/-- A tuple's polynomial peels off its top monomial.

`polyOfTuple t (d+1)` is `polyOfTuple (fst t) d` plus `(snd t)·x^d`, which is
the induction step for reading a tuple as a linear combination of the monomials
below its length. Stated at the polynomial level: everything above happens in
`PolyRing`, so the quotient only has to be a ring homomorphism. -/
theorem polyOfTuple_succ {R add mul zero one t : ZFSet.{u}}
    (hR : IsRing R add mul zero one) {d : Nat} (ht : t ∈ powSet R (d + 1)) :
    polyOfTuple R zero t (d + 1)
      = polyAdd R add (polyOfTuple R zero (fst t) d) (monomial R zero (snd t) d) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff t _ _).mp ht
  rw [fst_opair, snd_opair]
  have hlow := isPolyOver_polyOfTuple hR (d := d) ha
  have hmon := isPolyOver_monomial hR hb d
  refine poly_ext_coeff (isPolyOver_polyOfTuple hR ht) (isPolyOver_polyAdd hR hlow hmon)
    (fun k => ?_)
  rw [app_polyAdd hR hlow hmon (ofNat_mem_omega k), app_polyOfTuple hR ht k,
    app_polyOfTuple hR ha k, app_monomial hR hb d k, monomialCoeff]
  rcases Nat.lt_trichotomy k d with hlt | heq | hgt
  · -- below the top: the monomial contributes zero
    rw [if_pos (by omega), if_pos hlt, if_neg (by omega),
      show tupleCoeff (opair a b) (d + 1) k = tupleCoeff a d k by
        show (if k = d then snd (opair a b) else tupleCoeff (fst (opair a b)) d k) = _
        rw [if_neg (by omega), fst_opair]]
    exact (ringAdd_zero hR (tupleCoeff_mem d a ha k hlt)).symm
  · -- at the top: the tuple's last entry, and the low part contributes zero
    subst heq
    rw [if_pos (by omega), if_neg (by omega), if_pos rfl,
      show tupleCoeff (opair a b) (k + 1) k = b by
        show (if k = k then snd (opair a b) else tupleCoeff (fst (opair a b)) k k) = _
        rw [if_pos rfl, snd_opair]]
    exact (ringZero_add hR hb).symm
  · -- above both
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact (ringAdd_zero hR hR.addGroup.mem_e).symm

/-- The same peel, downstairs in `R[x]/(f)`.

`polyOfTuple_succ` is an identity between polynomials, so the class map carries
it for free: this is that identity with `cls` applied, and it is the induction
step a power basis runs on -- each application strips one monomial class off the
top, so `d` applications express a class as a combination of the `d` monomial
classes below it. Nothing here is a new fact; the content is that the quotient's
addition is `congOp`, which agrees with `polyAdd` on classes. -/
theorem cls_polyOfTuple_succ {R add mul zero one f t : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hf : f ∈ PolyRing R zero)
    {d : Nat} (ht : t ∈ powSet R (d + 1)) :
    cls (polyQuotRel R add mul zero f) (PolyRing R zero) (polyOfTuple R zero t (d + 1))
      = opAt (congOp (polyQuotRel R add mul zero f) (PolyRing R zero)
          (polyAddOp R add zero))
          (cls (polyQuotRel R add mul zero f) (PolyRing R zero)
            (polyOfTuple R zero (fst t) d))
          (cls (polyQuotRel R add mul zero f) (PolyRing R zero)
            (monomial R zero (snd t) d)) := by
  -- `powSet R (d+1)` IS `prod (powSet R d) R`, so the two components come from
  -- `mem_prod_iff` gives them.
  obtain ⟨u, hu, v, hv, hsplit⟩ := (mem_prod_iff t _ _).mp ht
  have hfst : fst t ∈ powSet R d := by rw [hsplit, fst_opair]; exact hu
  have hsnd : snd t ∈ R := by rw [hsplit, snd_opair]; exact hv
  have hlowP : polyOfTuple R zero (fst t) d ∈ PolyRing R zero :=
    (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyOfTuple hR hfst)
  have hmonP : monomial R zero (snd t) d ∈ PolyRing R zero :=
    (mem_polyRing_iff _ _ _).mpr (isPolyOver_monomial hR hsnd d)
  -- `opAt_congOp` elaborates against `idealRel`, the goal shows `polyQuotRel`;
  -- they are definitionally equal, so `refine` unifies where `rw` would not.
  refine Eq.trans ?_ (opAt_congOp
    (fun x hx y hy => addAt_mem (isRing_polyRing hR) hx hy)
    (isCongruence_idealRel_add (isRing_polyRing hR) (isIdeal_polyIdeal hR hf))
    hlowP hmonP).symm
  rw [opAt_polyAddOp hR hlowP hmonP, ← polyOfTuple_succ hR ht]
  rfl

/-- Every polynomial supported below `d` comes from a tuple. -/
theorem exists_tuple {R add mul zero one p : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hp : IsPolyOver R zero p) {d : Nat} (hd : ∀ i : Nat, d ≤ i → app p (ofNat.{u} i) = zero) :
    ∃ t, t ∈ powSet R d ∧ polyOfTuple R zero t d = p := by
  refine ⟨tupleOf (fun i => app p (ofNat.{u} i)) d,
    tupleOf_mem d (fun i _ => coeff_mem hp (ofNat_mem_omega i)), ?_⟩
  refine poly_ext_coeff (isPolyOver_polyOfTuple hR
    (tupleOf_mem d (fun i _ => coeff_mem hp (ofNat_mem_omega i)))) hp (fun k => ?_)
  rw [app_polyOfTuple hR (tupleOf_mem d (fun i _ => coeff_mem hp (ofNat_mem_omega i))) k]
  rcases Nat.lt_or_ge k d with hlt | hge
  · rw [if_pos hlt, tupleCoeff_tupleOf d k hlt]
  · rw [if_neg (by omega), hd k hge]

/-- Every class in `R[x]/(f)` is the class of a polynomial below `f`'s
degree. Division with remainder, read as a statement about the quotient.

Stated separately because two consumers want it and neither wants the other's
conclusion: counting the quotient needs the representatives to form a FINITE
set, and a power basis needs them spanned by the monomials below `d`. Both are
this one fact. -/
theorem exists_polyQuot_rep_below {R add mul zero one f : ZFSet.{u}}
    (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) {d : Nat}
    (hfd : ∀ i : Nat, d < i → app f (ofNat.{u} i) = zero)
    {u : ZFSet.{u}} (hu : u ∈ R) (hlead : opAt mul (app f (ofNat.{u} d)) u = one)
    {A : ZFSet.{u}} (hA : A ∈ polyQuot R add mul zero f) :
    ∃ r, IsPolyOver R zero r ∧ (∀ i : Nat, d ≤ i → app r (ofNat.{u} i) = zero) ∧
      A = cls (polyQuotRel R add mul zero f) (PolyRing R zero) r := by
  have hfmem : f ∈ PolyRing R zero := (mem_polyRing_iff _ _ _).mpr hf
  obtain ⟨p, hp, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
  have hpP := (mem_polyRing_iff _ _ _).mp hp
  obtain ⟨N, hN⟩ := hpP.right.right.right
  obtain ⟨q, r, hq, hr, hrb, hsplit⟩ := exists_polyDiv hR hf hfd hu hlead N p hpP hN
  refine ⟨r, hr, hrb, ?_⟩
  -- `p` and `r` differ by a multiple of `f`, so they are the same class
  refine (cls_eq_cls_iff (isCongruence_idealRel_add (isRing_polyRing hR)
    (isIdeal_polyIdeal hR hfmem)).left hp
    ((mem_polyRing_iff _ _ _).mpr hr)).mpr ?_
  refine (opair_mem_idealRel_iff hp ((mem_polyRing_iff _ _ _).mpr hr)).mpr ?_
  have hqP : q ∈ PolyRing R zero := (mem_polyRing_iff _ _ _).mpr hq
  have hrP : r ∈ PolyRing R zero := (mem_polyRing_iff _ _ _).mpr hr
  have hqf : polyMul R add mul zero q f ∈ PolyRing R zero :=
    (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyMul hR hq hf)
  have hG := isGroup_polyAdd (one := one) hR
  have hpr : opAt (polyAddOp R add zero) (polyMul R add mul zero q f) r = p := by
    rw [opAt_polyAddOp hR hqf hrP]
    exact hsplit.symm
  have hsub : ringSub (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero) p r
      = polyMul R add mul zero q f := by
    show opAt (polyAddOp R add zero) p
      (ringNeg (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero) r) = _
    rw [← hpr, hG.assoc _ hqf _ hrP _ (ringNeg_mem (isRing_polyRing hR) hrP),
      ringAdd_neg (isRing_polyRing hR) hrP]
    exact hG.right_id _ hqf
  rw [hsub]
  refine (mem_ringMultiples_iff _ _ _ _).mpr ⟨hqf, q, hqP, ?_⟩
  rw [← (isRing_polyRing hR).mulComm _ hqP _ hfmem, opAt_polyMulOp hR hqP hfmem]

/-! ## Leading coefficients multiply

Over a ring with no zero divisors, the top coefficient of a product is the
product of the top coefficients. Everything about degrees follows from this. -/

theorem convCoeff_above {R add mul zero one g h : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hg : IsPolyOver R zero g) (hh : IsPolyOver R zero h) {dg dh : Nat}
    (hga : ∀ i : Nat, dg < i → app g (ofNat.{u} i) = zero)
    (hha : ∀ i : Nat, dh < i → app h (ofNat.{u} i) = zero)
    {k : Nat} (hk : dg + dh < k) : convCoeff R add mul zero g h k = zero := by
  refine foldF_zeros hR (k + 1) (fun j _ => ?_)
  rcases Nat.lt_or_ge dg j with hj | hj
  · rw [hga j hj, ringZero_mul hR (coeff_mem hh (ofNat_mem_omega (k - j)))]
  · rw [hha (k - j) (by omega), mul_zero_of_isRing hR (coeff_mem hg (ofNat_mem_omega j))]

theorem convCoeff_top {R add mul zero one g h : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hg : IsPolyOver R zero g) (hh : IsPolyOver R zero h) {dg dh : Nat}
    (hga : ∀ i : Nat, dg < i → app g (ofNat.{u} i) = zero)
    (hha : ∀ i : Nat, dh < i → app h (ofNat.{u} i) = zero) :
    convCoeff R add mul zero g h (dg + dh)
      = opAt mul (app g (ofNat.{u} dg)) (app h (ofNat.{u} dh)) := by
  have hz : ∀ j : Nat, j ≠ dg → opAt mul (app g (ofNat.{u} j))
      (app h (ofNat.{u} (dg + dh - j))) = zero := by
    intro j hj
    rcases Nat.lt_or_ge dg j with hlt | hge
    · rw [hga j hlt, ringZero_mul hR (coeff_mem hh (ofNat_mem_omega (dg + dh - j)))]
    · rw [hha (dg + dh - j) (by omega), mul_zero_of_isRing hR (coeff_mem hg (ofNat_mem_omega j))]
  rw [convCoeff, foldF_single hR
    (T := fun j => opAt mul (app g (ofNat.{u} j)) (app h (ofNat.{u} (dg + dh - j)))) (k := dg)
    (mulAt_mem hR (coeff_mem hg (ofNat_mem_omega dg))
      (coeff_mem hh (ofNat_mem_omega (dg + dh - dg)))) hz (dg + dh + 1) (by omega)]
  show opAt mul (app g (ofNat.{u} dg)) (app h (ofNat.{u} (dg + dh - dg))) = _
  rw [show dg + dh - dg = dh by omega]

/-- The degree of a product, from the TOP COEFFICIENT alone.

`polyMul_top` below asks that `R` have no zero divisors, and spends it at exactly
one step: showing the product's coefficient at `dg + dh` is non-zero. That step
needs only `lead(g)·lead(h) ≠ 0`, which is a fact about the two polynomials rather
than about `R`.

The distinction is what a MONIC modulus turns on -- `lead(h) = one` makes the
product's top coefficient `lead(g)`, so the degree is exact over any ring, and no
domain hypothesis is available or needed. -/
theorem polyMul_top_of_top {R add mul zero one g h : ZFSet.{u}}
    (hR : IsRing R add mul zero one)
    (hg : IsPolyOver R zero g) (hh : IsPolyOver R zero h) {dg dh : Nat}
    (hga : ∀ i : Nat, dg < i → app g (ofNat.{u} i) = zero)
    (hha : ∀ i : Nat, dh < i → app h (ofNat.{u} i) = zero)
    (htop : opAt mul (app g (ofNat.{u} dg)) (app h (ofNat.{u} dh)) ≠ zero) :
    (∀ i : Nat, dg + dh < i → app (polyMul R add mul zero g h) (ofNat.{u} i) = zero)
      ∧ app (polyMul R add mul zero g h) (ofNat.{u} (dg + dh)) ≠ zero := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [app_polyMul hR hg hh i]
    exact convCoeff_above hR hg hh hga hha hi
  · rw [app_polyMul hR hg hh (dg + dh), convCoeff_top hR hg hh hga hha]
    exact htop

#print axioms polyMul_top_of_top
/-- A monic modulus cancels, and nothing is decided.

`remainder_unique_monic` used to reach `p = 0` by asking whether `p` vanishes,
which is what a `DecidableVanishing` hypothesis pays for.

The leading coefficient need only be a UNIT, not `one`. Monicity is the case
a caller usually has, but nothing in the induction uses more than invertibility:
the surviving convolution term is `p N * lead(f)`, and multiplying by the
inverse recovers `p N`. Stating it at the weaker hypothesis costs one
destructuring of the witness and says where the decision is really unnecessary. The decision is avoidable:
if `p * f` has no coefficient at or above `f`'s degree `d`, then reading the
product at `N + d` picks out `p N * one` by ARITHMETIC on the indices --
`convCoeff_top` -- and an induction on `p`'s support bound walks it to zero. -/
theorem eq_polyZero_of_monic_mul {R add mul zero one p f : ZFSet.{u}}
    (hR : IsRing R add mul zero one)
    (hp : IsPolyOver R zero p) (hf : IsPolyOver R zero f) {d : Nat}
    (hfa : ∀ i : Nat, d < i → app f (ofNat.{u} i) = zero)
    (hunit : ∃ v, v ∈ R ∧ opAt mul (app f (ofNat.{u} d)) v = one)
    (hbound : ∀ i : Nat, d ≤ i →
      app (polyMul R add mul zero p f) (ofNat.{u} i) = zero) :
    ∀ N : Nat, (∀ i : Nat, N ≤ i → app p (ofNat.{u} i) = zero) →
      p = polyZero R zero := by
  obtain ⟨v, hv, hvu⟩ := hunit
  intro N
  induction N with
  | zero => exact fun hN => eq_polyZero_of_coeffs hR hp (fun i => hN i (Nat.zero_le i))
  | succ N ih =>
    intro hN
    have hpN : app p (ofNat.{u} N) = zero := by
      have hc := convCoeff_top (dg := N) (dh := d) hR hp hf
        (fun j hj => hN j (by omega)) hfa
      have h0 := hbound (N + d) (by omega)
      rw [app_polyMul hR hp hf (N + d), hc] at h0
      have hpm := coeff_mem hp (ofNat_mem_omega N)
      have hfm := coeff_mem hf (ofNat_mem_omega d)
      have := congrArg (fun z => opAt mul z v) h0
      simp only at this
      rw [hR.mulAssoc _ hpm _ hfm _ hv, hvu,
        hR.mul_one _ hpm, ringZero_mul hR hv] at this
      exact this
    refine ih (fun i hi => ?_)
    rcases eq_or_lt_of_le' hi with heq | hlt
    · rw [← heq]; exact hpN
    · exact hN i (by omega)

#print axioms eq_polyZero_of_monic_mul


/-- The top coefficient of a product, over a domain. -/
theorem polyMul_top {R add mul zero one g h : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hdom : ∀ a, a ∈ R → ∀ b, b ∈ R → a ≠ zero → b ≠ zero → opAt mul a b ≠ zero)
    (hg : IsPolyOver R zero g) (hh : IsPolyOver R zero h) {dg dh : Nat}
    (hga : ∀ i : Nat, dg < i → app g (ofNat.{u} i) = zero)
    (hha : ∀ i : Nat, dh < i → app h (ofNat.{u} i) = zero)
    (hgne : app g (ofNat.{u} dg) ≠ zero) (hhne : app h (ofNat.{u} dh) ≠ zero) :
    (∀ i : Nat, dg + dh < i → app (polyMul R add mul zero g h) (ofNat.{u} i) = zero)
      ∧ app (polyMul R add mul zero g h) (ofNat.{u} (dg + dh)) ≠ zero :=
  polyMul_top_of_top hR hg hh hga hha
    (hdom _ (coeff_mem hg (ofNat_mem_omega dg)) _
      (coeff_mem hh (ofNat_mem_omega dh)) hgne hhne)

/-- EISENSTEIN'S CRITERION: one factor is constant.

`f = g·h` vanishing above `n`, with `d` prime dividing every coefficient of `f`
below `n` and not dividing `h`'s constant term, forces `h` to be constant.

Three facts meet. `polyMul_top` puts the product's top index at `dg + dh` with a
non-zero coefficient there, so `dg + dh ≤ n`. `eisenstein_nonzero_high` gives
`g` a non-zero coefficient at some index at least `n`, and `g` vanishes above
`dg`, so `n ≤ dg`. Together `dg = n` and `dh = 0`.

The domain condition is a hypothesis, discharged for `ℤ` by `intMul_ne_zero`.
Nothing here reduces mod `d`. -/
theorem eisenstein_factor_constant {R add mul zero one d g h : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hd : d ∈ R)
    (hdom : ∀ a, a ∈ R -> ∀ b, b ∈ R -> a ≠ zero -> b ≠ zero ->
      opAt mul a b ≠ zero)
    (he : IsEisenstein R mul zero d g h)
    {n dg dh : Nat}
    (hga : ∀ i : Nat, dg < i -> app g (ofNat.{u} i) = zero)
    (hgne : app g (ofNat.{u} dg) ≠ zero)
    (hha : ∀ i : Nat, dh < i -> app h (ofNat.{u} i) = zero)
    (hhne : app h (ofNat.{u} dh) ≠ zero)
    (hlow : ∀ i, i < n -> ∃ c, c ∈ R ∧
      convCoeff R add mul zero g h i = opAt mul d c)
    (hfn : ∀ i : Nat, n < i ->
      app (polyMul R add mul zero g h) (ofNat.{u} i) = zero)
    {N : Nat} (hN : ¬ ∃ c, c ∈ R ∧ app g (ofNat.{u} N) = opAt mul d c) :
    dh = 0 := by
  obtain ⟨-, htop⟩ := polyMul_top hR hdom he.polyG he.polyH hga hha hgne hhne
  have hle : dg + dh <= n := by
    rcases Nat.lt_or_ge n (dg + dh) with hlt | hge
    · exact absurd (hfn _ hlt) htop
    · exact hge
  obtain ⟨k, hk, hkne⟩ := eisenstein_nonzero_high hR hd he n hlow hN
  have hkg : k <= dg := by
    rcases Nat.lt_or_ge dg k with hlt | hge
    · exact absurd (hga k hlt) hkne
    · exact hge
  omega

/-! ## The factor theorem

`x - a` divides `f` exactly when `a` is a root. Division by `x - a` always
applies: its coefficient at `1` is `one`, which is its own inverse. -/

def linearPoly (R add mul zero one a : ZFSet.{u}) : ZFSet.{u} :=
  polyOfList R zero [ringNeg R add zero a, one]

theorem coeffs_linearPoly {R add mul zero one a : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) : ∀ c, c ∈ [ringNeg R add zero a, one] → c ∈ R := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc'
  · exact ringNeg_mem hR ha
  · rcases List.mem_cons.mp hc' with rfl | hc''
    · exact hR.mem_one
    · exact absurd hc'' List.not_mem_nil

theorem isPolyOver_linearPoly {R add mul zero one a : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) : IsPolyOver R zero (linearPoly R add mul zero one a) :=
  isPolyOver_polyOfList hR _ (coeffs_linearPoly hR ha)

theorem app_linearPoly {R add mul zero one a : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (i : Nat) :
    app (linearPoly R add mul zero one a) (ofNat.{u} i)
      = listCoeff zero [ringNeg R add zero a, one] i :=
  app_polyOfSeq (listCoeff_mem hR _ (coeffs_linearPoly hR ha)) i

theorem evalAt_linearPoly {R add mul zero one a b : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) :
    evalAt R add mul zero one b (linearPoly R add mul zero one a)
      = ringSub R add zero b a := by
  rw [linearPoly, evalAt_polyOfList hR hb _ (coeffs_linearPoly hR ha)]
  show opAt add (ringNeg R add zero a) (opAt mul b (opAt add one (opAt mul b zero))) = _
  rw [mul_zero_of_isRing hR hb, ringAdd_zero hR hR.mem_one, hR.mul_one b hb, ringSub,
    ringAdd_comm hR (ringNeg_mem hR ha) hb]


/-! ## Irreducibility, and the field

An irreducible `f` makes `F[x]/(f)` a field: Bézout turns "`f` does not divide
`g`" into an inverse for the class of `g`. -/

def IsPolyUnit (R add mul zero one p : ZFSet.{u}) : Prop :=
  ∃ q, q ∈ PolyRing R zero ∧ opAt (polyMulOp R add mul zero) p q = polyOne R zero one

def IsPolyIrreducible (R add mul zero one f : ZFSet.{u}) : Prop :=
  f ∈ PolyRing R zero ∧ ¬ IsPolyUnit R add mul zero one f ∧
    ∀ e, e ∈ PolyRing R zero → polyDvd R add mul zero e f →
      IsPolyUnit R add mul zero one e ∨ polyDvd R add mul zero f e

/-! ## Units are the non-zero constants

A field has no zero divisors once vanishing is decidable, so the top index of a
product is the sum of the top indices; a product that is `1` therefore has both
indices zero. -/

/-- A unit of `F[x]` is supported below `1`. -/
theorem polyUnit_const {R add mul zero one p : ZFSet.{u}} (hF : IsField R add mul zero one)
    (hdec : DecidableVanishing R zero) (hp : p ∈ PolyRing R zero)
    (hu : IsPolyUnit R add mul zero one p) :
    ∀ i : Nat, 1 ≤ i → app p (ofNat.{u} i) = zero := by
  have hR := hF.ring
  obtain ⟨q, hq, hpq⟩ := hu
  have hpP := (mem_polyRing_iff _ _ _).mp hp
  have hqP := (mem_polyRing_iff _ _ _).mp hq
  obtain ⟨Np, hNp⟩ := hpP.right.right.right
  obtain ⟨Nq, hNq⟩ := hqP.right.right.right
  rw [opAt_polyMulOp hR hp hq] at hpq
  have hone0 : app (polyOne R zero one) (ofNat.{u} 0) = one := app_polyOne hR 0
  rcases exists_lead hR hdec hpP Np hNp with hzp | ⟨dp, -, hpne, hpa⟩
  · exfalso
    refine hF.zero_ne_one ?_
    rw [← hone0, ← hpq, app_polyMul hR hpP hqP 0, convCoeff]
    refine (foldF_zeros hR 1 (fun j _ => ?_)).symm
    rw [hzp, app_polyZero hR (ofNat_mem_omega j),
      ringZero_mul hR (coeff_mem hqP (ofNat_mem_omega (0 - j)))]
  rcases exists_lead hR hdec hqP Nq hNq with hzq | ⟨dq, -, hqne, hqa⟩
  · exfalso
    refine hF.zero_ne_one ?_
    rw [← hone0, ← hpq, app_polyMul hR hpP hqP 0, convCoeff]
    refine (foldF_zeros hR 1 (fun j _ => ?_)).symm
    rw [hzq, app_polyZero hR (ofNat_mem_omega (0 - j)),
      mul_zero_of_isRing hR (coeff_mem hpP (ofNat_mem_omega j))]
  obtain ⟨htopa, htopne⟩ := polyMul_top hR (field_no_zero_divisors_ne hF) hpP hqP
    hpa hqa hpne hqne
  rw [hpq] at htopa htopne
  have hzero : dp + dq = 0 := by
    rcases Nat.eq_zero_or_pos (dp + dq) with h | h
    · exact h
    · exfalso
      refine htopne ?_
      obtain ⟨j, hj⟩ : ∃ j, dp + dq = j + 1 := ⟨dp + dq - 1, by omega⟩
      rw [hj, app_polyOne hR (j + 1)]
      rfl
  intro i hi
  exact hpa i (by omega)

theorem polyDvd_trans {R add mul zero one c e g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hc : c ∈ PolyRing R zero) (he : e ∈ PolyRing R zero)
    (h₁ : polyDvd R add mul zero c e) (h₂ : polyDvd R add mul zero e g) :
    polyDvd R add mul zero c g := by
  have hP := isRing_polyRing (one := one) hR
  obtain ⟨p, hp, rfl⟩ := h₁
  obtain ⟨q, hq, rfl⟩ := h₂
  exact ⟨opAt (polyMulOp R add mul zero) q p, mulAt_mem hP hq hp,
    (hP.mulAssoc _ hq _ hp _ hc).symm⟩

theorem mem_polyIdeal_iff {R add mul zero one f w : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : f ∈ PolyRing R zero) :
    w ∈ polyIdeal R add mul zero f ↔ w ∈ PolyRing R zero ∧ polyDvd R add mul zero f w := by
  have hP := isRing_polyRing (one := one) hR
  refine Iff.trans (mem_ringMultiples_iff _ _ _ _) ⟨?_, ?_⟩
  · rintro ⟨hwP, y, hy, rfl⟩
    exact ⟨hwP, y, hy, hP.mulComm _ hf _ hy⟩
  · rintro ⟨hwP, q, hq, rfl⟩
    exact ⟨mulAt_mem hP hq hf, q, hq, hP.mulComm _ hq _ hf⟩

/-- A non-zero constant is a unit. -/
theorem polyUnit_of_const {R add mul zero one p : ZFSet.{u}} (hF : IsField R add mul zero one)
    (hp : p ∈ PolyRing R zero) (hbound : ∀ i : Nat, 1 ≤ i → app p (ofNat.{u} i) = zero)
    (hne : app p (ofNat.{u} 0) ≠ zero) : IsPolyUnit R add mul zero one p := by
  have hR := hF.ring
  have hpP := (mem_polyRing_iff _ _ _).mp hp
  obtain ⟨c, hc, hcp⟩ := hF.inverses _ (coeff_mem hpP (ofNat_mem_omega 0)) hne
  refine ⟨polyOfList R zero [c], (mem_polyRing_iff _ _ _).mpr
    (isPolyOver_polyOfList hR [c] (fun w hw => by
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact hc
      · exact absurd hw' List.not_mem_nil)), ?_⟩
  have hcmem : ∀ w, w ∈ [c] → w ∈ R := fun w hw => by
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact hc
    · exact absurd hw' List.not_mem_nil
  have hcP := isPolyOver_polyOfList hR [c] hcmem
  rw [opAt_polyMulOp hR hp ((mem_polyRing_iff _ _ _).mpr hcP)]
  refine poly_ext_coeff (isPolyOver_polyMul hR hpP hcP) (isPolyOver_polyOne hR) (fun k => ?_)
  rw [app_polyMul hR hpP hcP k, app_polyOne hR k]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · show convCoeff R add mul zero p (polyOfList R zero [c]) 0 = one
    rw [convCoeff_top (dg := 0) (dh := 0) hR hpP hcP (fun i hi => hbound i (by omega))
      (fun i hi => by
        rw [app_polyOfList hR [c] hcmem i]
        exact listCoeff_eq_zero [c] i (by simp; omega))]
    show opAt mul (app p (ofNat.{u} 0)) (app (polyOfList R zero [c]) (ofNat.{u} 0)) = one
    rw [app_polyOfList hR [c] hcmem 0]
    exact hcp
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    show convCoeff R add mul zero p (polyOfList R zero [c]) (j + 1) = _
    rw [convCoeff_above (dg := 0) (dh := 0) hR hpP hcP (fun i hi => hbound i (by omega))
      (fun i hi => by
        rw [app_polyOfList hR [c] hcmem i]
        exact listCoeff_eq_zero [c] i (by simp; omega)) (by omega)]
    rfl

/-! ## Uniqueness of the remainder

A non-zero multiple of `f` has top index at least `d`, so it cannot be a
remainder. That makes divisibility decidable, and with it equality of classes. -/

theorem polySub_zero_iff {R add mul zero one p q : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hp : p ∈ PolyRing R zero) (hq : q ∈ PolyRing R zero) :
    ringSub (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero) p q
      = polyZero R zero ↔ p = q :=
  ringSub_eq_zero_iff (isRing_polyRing (one := one) hR) hp hq

theorem ringNeg_polyRing {R add mul zero one p : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hp : p ∈ PolyRing R zero) :
    ringNeg (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero) p
      = polyNeg R add zero p := by
  have hP := isRing_polyRing (one := one) hR
  have hnp : polyNeg R add zero p ∈ PolyRing R zero :=
    polyNeg_mem hR ((mem_polyRing_iff _ _ _).mp hp)
  refine inv_unique hP.addGroup hp (ringNeg_mem hP hp) hnp (ringAdd_neg hP hp) ?_
  rw [opAt_polyAddOp hR hnp hp]
  refine poly_ext (isPolyOver_polyAdd hR (isPolyOver_polyNeg hR
    ((mem_polyRing_iff _ _ _).mp hp)) ((mem_polyRing_iff _ _ _).mp hp))
    (isPolyOver_polyZero hR) (fun w hw => ?_)
  rw [app_polyAdd hR (isPolyOver_polyNeg hR ((mem_polyRing_iff _ _ _).mp hp))
      ((mem_polyRing_iff _ _ _).mp hp) hw,
    app_polyNeg hR ((mem_polyRing_iff _ _ _).mp hp) hw, app_polyZero hR hw,
    ringNeg_add hR (coeff_mem ((mem_polyRing_iff _ _ _).mp hp) hw)]

/-- The remainder is `(s - q)` times the modulus.

Shared by all three uniqueness proofs -- field, domain and monic. It lets the
FIELD case stop delegating to the domain case, so that case drops its
decidability hypothesis.

Pure ring algebra: no field, no domain, no decision. -/
theorem remainder_eq_sub_mul {R add mul zero one f g q r s : ZFSet.{u}}
    (hR : IsRing R add mul zero one)
    (hf : f ∈ PolyRing R zero) (hq : q ∈ PolyRing R zero)
    (hr : r ∈ PolyRing R zero) (hs : s ∈ PolyRing R zero)
    (hsplit : g = opAt (polyAddOp R add zero) (opAt (polyMulOp R add mul zero) q f) r)
    (hmul : g = opAt (polyMulOp R add mul zero) s f) :
    r = opAt (polyMulOp R add mul zero)
      (ringSub (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero) s q) f := by
  have hP := isRing_polyRing (one := one) hR
  rw [ringSub_def, ringRight_distrib hP hs (ringNeg_mem hP hq) hf,
    ringNeg_mul hP hq hf, ← hmul, hsplit]
  show _ = opAt (polyAddOp R add zero) (opAt (polyAddOp R add zero)
    (opAt (polyMulOp R add mul zero) q f) r)
    (ringNeg (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero)
      (opAt (polyMulOp R add mul zero) q f))
  rw [hP.addComm _ (mulAt_mem hP hq hf) _ hr,
    hP.addGroup.assoc _ hr _ (mulAt_mem hP hq hf) _ (ringNeg_mem hP (mulAt_mem hP hq hf)),
    ringAdd_neg hP (mulAt_mem hP hq hf), hP.addGroup.right_id _ hr]

#print axioms remainder_eq_sub_mul

/-- Uniqueness of the remainder, over a DOMAIN.

The argument needs only that a product of non-zero polynomials has a non-zero
top coefficient, which the no-zero-divisors hypothesis gives directly -- so
this is the general statement, and `remainder_unique` below is the field case,
reading `field_no_zero_divisors_ne` as that hypothesis. `ℤ` is a domain and not
a field, so the weaker hypothesis is the useful one.

The leading coefficient is never inverted here, so monicity is not needed for
THIS half; what it buys is the division itself, one lemma down. -/
theorem remainder_unique_domain {R add mul zero one f g q r s : ZFSet.{u}}
    (hR : IsRing R add mul zero one)
    (hnzd : ∀ a, a ∈ R → ∀ b, b ∈ R → a ≠ zero → b ≠ zero → opAt mul a b ≠ zero)
    (hdec : DecidableVanishing R zero)
    (hf : f ∈ PolyRing R zero) {d : Nat}
    (hfa : ∀ i : Nat, d < i → app f (ofNat.{u} i) = zero)
    (hfne : app f (ofNat.{u} d) ≠ zero)
    (hq : q ∈ PolyRing R zero) (hr : r ∈ PolyRing R zero) (hs : s ∈ PolyRing R zero)
    (hrb : ∀ i : Nat, d ≤ i → app r (ofNat.{u} i) = zero)
    (hsplit : g = opAt (polyAddOp R add zero) (opAt (polyMulOp R add mul zero) q f) r)
    (hmul : g = opAt (polyMulOp R add mul zero) s f) : r = polyZero R zero := by
  have hP := isRing_polyRing (one := one) hR
  have hfP := (mem_polyRing_iff _ _ _).mp hf
  have hkey := remainder_eq_sub_mul (one := one) hR hf hq hr hs hsplit hmul
  have hdiff := ringSub_mem hP hs hq
  obtain ⟨Nd, hNd⟩ := ((mem_polyRing_iff _ _ _).mp hdiff).right.right.right
  rcases exists_lead hR hdec ((mem_polyRing_iff _ _ _).mp hdiff) Nd hNd with hz | ⟨e, -, hene, hea⟩
  · rw [hkey, hz, hP.mulComm _ ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyZero hR)) _ hf]
    exact mul_zero_of_isRing hP hf
  · exfalso
    have hprod := polyMul_top hR hnzd
      ((mem_polyRing_iff _ _ _).mp hdiff) hfP hea hfa hene hfne
    rw [← opAt_polyMulOp hR hdiff hf, ← hkey] at hprod
    exact hprod.right (hrb (e + d) (by omega))


/-- Uniqueness of the remainder over a field, the field case of
`remainder_unique_domain`: a field has no zero divisors. -/
theorem remainder_unique {R add mul zero one f g q r s : ZFSet.{u}}
    (hF : IsField R add mul zero one)
    (hf : f ∈ PolyRing R zero) {d : Nat}
    (hfa : ∀ i : Nat, d < i → app f (ofNat.{u} i) = zero)
    (hfne : app f (ofNat.{u} d) ≠ zero)
    (hq : q ∈ PolyRing R zero) (hr : r ∈ PolyRing R zero) (hs : s ∈ PolyRing R zero)
    (hrb : ∀ i : Nat, d ≤ i → app r (ofNat.{u} i) = zero)
    (hsplit : g = opAt (polyAddOp R add zero) (opAt (polyMulOp R add mul zero) q f) r)
    (hmul : g = opAt (polyMulOp R add mul zero) s f) : r = polyZero R zero :=
  by
  have hR := hF.ring
  have hP := isRing_polyRing (one := one) hR
  have hfP := (mem_polyRing_iff _ _ _).mp hf
  have hkey := remainder_eq_sub_mul (one := one) hR hf hq hr hs hsplit hmul
  have hdiff := ringSub_mem hP hs hq
  obtain ⟨Nd, hNd⟩ := ((mem_polyRing_iff _ _ _).mp hdiff).right.right.right
  have hz := eq_polyZero_of_monic_mul hR ((mem_polyRing_iff _ _ _).mp hdiff) hfP hfa
    (hF.inverses _ (coeff_mem hfP (ofNat_mem_omega d)) hfne)
    (fun i hi => by rw [← opAt_polyMulOp hR hdiff hf, ← hkey]; exact hrb i hi) Nd hNd
  rw [hkey, hz, hP.mulComm _ ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyZero hR)) _ hf]
  exact mul_zero_of_isRing hP hf

#print axioms remainder_unique_domain
#print axioms remainder_unique


/-- Uniqueness of the remainder, for a MONIC modulus over any ring. -/
theorem remainder_unique_monic {R add mul zero one f g q r s : ZFSet.{u}}
    (hR : IsRing R add mul zero one)
    (hf : f ∈ PolyRing R zero) {d : Nat}
    (hfa : ∀ i : Nat, d < i → app f (ofNat.{u} i) = zero)
    (hmonic : app f (ofNat.{u} d) = one)
    (hq : q ∈ PolyRing R zero) (hr : r ∈ PolyRing R zero) (hs : s ∈ PolyRing R zero)
    (hrb : ∀ i : Nat, d ≤ i → app r (ofNat.{u} i) = zero)
    (hsplit : g = opAt (polyAddOp R add zero) (opAt (polyMulOp R add mul zero) q f) r)
    (hmul : g = opAt (polyMulOp R add mul zero) s f) : r = polyZero R zero := by
  have hP := isRing_polyRing (one := one) hR
  have hfP := (mem_polyRing_iff _ _ _).mp hf
  have hkey := remainder_eq_sub_mul (one := one) hR hf hq hr hs hsplit hmul
  have hdiff := ringSub_mem hP hs hq
  obtain ⟨Nd, hNd⟩ := ((mem_polyRing_iff _ _ _).mp hdiff).right.right.right
  have hz := eq_polyZero_of_monic_mul hR ((mem_polyRing_iff _ _ _).mp hdiff) hfP hfa
    ⟨one, hR.mem_one, by rw [hmonic, hR.mul_one _ hR.mem_one]⟩
    (fun i hi => by rw [← opAt_polyMulOp hR hdiff hf, ← hkey]; exact hrb i hi) Nd hNd
  rw [hkey, hz, hP.mulComm _ ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyZero hR)) _ hf]
  exact mul_zero_of_isRing hP hf

#print axioms remainder_unique_monic


/-- Divisibility is decidable. -/
theorem polyDvd_or_not {R add mul zero one f g : ZFSet.{u}} (hF : IsField R add mul zero one)
    (hdec : DecidableVanishing R zero) (hf : f ∈ PolyRing R zero) {d : Nat}
    (hfa : ∀ i : Nat, d < i → app f (ofNat.{u} i) = zero)
    (hfne : app f (ofNat.{u} d) ≠ zero) (hg : g ∈ PolyRing R zero) :
    polyDvd R add mul zero f g ∨ ¬ polyDvd R add mul zero f g := by
  have hR := hF.ring
  have hP := isRing_polyRing (one := one) hR
  have hfP := (mem_polyRing_iff _ _ _).mp hf
  have hgP := (mem_polyRing_iff _ _ _).mp hg
  obtain ⟨w, hw, hlead⟩ := hF.inverses _ (coeff_mem hfP (ofNat_mem_omega d)) hfne
  obtain ⟨N, hN⟩ := hgP.right.right.right
  obtain ⟨q, r, hq, hr, hrb, hsplit⟩ := exists_polyDiv hR hfP hfa hw hlead N g hgP hN
  have hqP : q ∈ PolyRing R zero := (mem_polyRing_iff _ _ _).mpr hq
  have hrP : r ∈ PolyRing R zero := (mem_polyRing_iff _ _ _).mpr hr
  have hsplit' : g = opAt (polyAddOp R add zero) (opAt (polyMulOp R add mul zero) q f) r := by
    rw [opAt_polyMulOp hR hqP hf, opAt_polyAddOp hR
      ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyMul hR hq hfP)) hrP]
    exact hsplit
  obtain ⟨Nr, hNr⟩ := hr.right.right.right
  rcases exists_lead hR hdec hr Nr hNr with hz | ⟨e, -, hene, hea⟩
  · -- the remainder vanishes, so `f` divides `g`
    refine Or.inl ⟨q, hqP, ?_⟩
    rw [hsplit', hz]
    exact hP.addGroup.right_id _ (mulAt_mem hP hqP hf)
  · -- a non-zero remainder rules divisibility out
    refine Or.inr (fun ⟨s, hs, hmul⟩ => ?_)
    have := remainder_unique hF hf hfa hfne hqP hrP hs hrb hsplit' hmul
    rw [this] at hene
    exact hene (app_polyZero hR (ofNat_mem_omega e))

/-- Equality of classes is decidable. -/
theorem polyQuot_eq_or_ne {R add mul zero one f : ZFSet.{u}} (hF : IsField R add mul zero one)
    (hdec : DecidableVanishing R zero) (hf : f ∈ PolyRing R zero) {d : Nat}
    (hfa : ∀ i : Nat, d < i → app f (ofNat.{u} i) = zero)
    (hfne : app f (ofNat.{u} d) ≠ zero) :
    ∀ A, A ∈ polyQuot R add mul zero f → ∀ B, B ∈ polyQuot R add mul zero f →
      A = B ∨ A ≠ B := by
  have hR := hF.ring
  have hP := isRing_polyRing (one := one) hR
  have hI := isIdeal_polyIdeal (one := one) hR hf
  intro A hA B hB
  obtain ⟨p, hp, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
  obtain ⟨q, hq, rfl⟩ := (mem_quotientSet_iff _ _ B).mp hB
  have hiff : cls (polyQuotRel R add mul zero f) (PolyRing R zero) p
      = cls (polyQuotRel R add mul zero f) (PolyRing R zero) q
      ↔ polyDvd R add mul zero f
        (ringSub (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero) p q) := by
    refine Iff.trans (cls_eq_cls_iff (isCongruence_idealRel_add hP hI).left hp hq) ?_
    refine Iff.trans (opair_mem_idealRel_iff hp hq) ?_
    exact ⟨fun h => ((mem_polyIdeal_iff (one := one) hR hf).mp h).right,
      fun h => (mem_polyIdeal_iff (one := one) hR hf).mpr ⟨ringSub_mem hP hp hq, h⟩⟩
  rcases polyDvd_or_not hF hdec hf hfa hfne (ringSub_mem hP hp hq) with h | h
  · exact Or.inl (hiff.mpr h)
  · exact Or.inr (fun he => h (hiff.mp he))



/-! ## Counting the quotient

The tuples cover the quotient, and distinct tuples give distinct classes -- a
difference supported below `d` is a multiple of `f` only if it is zero. So the
quotient has exactly `|R|^d` elements. -/

/-- Vanishing is decided in `K[x]/(f)` if it is decided in `K`.

`polyQuot_eq_or_ne` at `B := [0]`. Small, and it lets a TOWER of simple
extensions be built: `isBasis_monoClsList` wants its base to decide vanishing,
and without this the base of the second storey could not. -/
theorem decidableVanishing_polyQuot {R add mul zero one f : ZFSet.{u}}
    (hF : IsField R add mul zero one) (hdec : DecidableVanishing R zero)
    (hf : f ∈ PolyRing R zero) {d : Nat}
    (hfa : ∀ i : Nat, d < i → app f (ofNat.{u} i) = zero)
    (hfne : app f (ofNat.{u} d) ≠ zero) :
    DecidableVanishing (polyQuot R add mul zero f)
      (cls (polyQuotRel R add mul zero f) (PolyRing R zero) (polyZero R zero)) :=
  fun A hA => polyQuot_eq_or_ne hF hdec hf hfa hfne A hA _
    (cls_mem_quotientSet ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyZero hF.ring)))

theorem powSet_ext {R : ZFSet.{u}} :
    ∀ (d : Nat) (t t' : ZFSet.{u}), t ∈ powSet R d → t' ∈ powSet R d →
      (∀ i : Nat, i < d → tupleCoeff t d i = tupleCoeff t' d i) → t = t'
  | 0, t, t', ht, ht', _ => by
    rw [(mem_singleton_iff _ _).mp ht, (mem_singleton_iff _ _).mp ht']
  | d + 1, t, t', ht, ht', h => by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff t _ _).mp ht
    obtain ⟨a', ha', b', hb', rfl⟩ := (mem_prod_iff t' _ _).mp ht'
    have hlast := h d (by omega)
    have hbb : b = b' := by
      have : (if d = d then snd (opair a b) else tupleCoeff (fst (opair a b)) d d)
          = (if d = d then snd (opair a' b') else tupleCoeff (fst (opair a' b')) d d) := hlast
      rw [if_pos rfl, if_pos rfl, snd_opair, snd_opair] at this
      exact this
    have haa : a = a' := by
      refine powSet_ext d a a' ha ha' (fun i hi => ?_)
      have := h i (by omega)
      have heq : (if i = d then snd (opair a b) else tupleCoeff (fst (opair a b)) d i)
          = (if i = d then snd (opair a' b') else tupleCoeff (fst (opair a' b')) d i) := this
      rw [if_neg (by omega), if_neg (by omega), fst_opair, fst_opair] at heq
      exact heq
    rw [haa, hbb]

theorem polyOfTuple_injective {R add mul zero one t t' : ZFSet.{u}}
    (hR : IsRing R add mul zero one) {d : Nat} (ht : t ∈ powSet R d) (ht' : t' ∈ powSet R d)
    (he : polyOfTuple R zero t d = polyOfTuple R zero t' d) : t = t' := by
  refine powSet_ext d t t' ht ht' (fun i hi => ?_)
  have h1 := app_polyOfTuple hR ht i
  have h2 := app_polyOfTuple hR ht' i
  rw [he, h2, if_pos hi] at h1
  rw [if_pos hi] at h1
  exact h1.symm

/-- The zero constant is the zero polynomial. -/
theorem monomial_zero_eq_polyZero {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) : monomial R zero zero 0 = polyZero R zero := by
  refine poly_ext_coeff (isPolyOver_monomial hR hR.addGroup.mem_e 0)
    (isPolyOver_polyZero hR) (fun k => ?_)
  rw [app_monomial hR hR.addGroup.mem_e 0 k, app_polyZero hR (ofNat_mem_omega k), monomialCoeff]
  rcases Nat.decEq k 0 with hne | heq
  · rw [if_neg hne]
  · rw [if_pos heq]

/-- A polynomial supported below `deg f` whose class is zero is zero.

The injective half of `equinumerous_polyQuot`, about one polynomial rather than
a difference of two: a multiple of `f` cannot be supported below `f`'s degree
unless it vanishes, which is `remainder_unique` read against `q = 0`. What wants
it is independence -- a vanishing linear combination of monomial classes must
have vanishing coefficients. -/
theorem poly_eq_zero_of_cls_zero {R add mul zero one f r : ZFSet.{u}}
    (hF : IsField R add mul zero one)
    (hf : f ∈ PolyRing R zero) {d : Nat}
    (hfa : ∀ i : Nat, d < i → app f (ofNat.{u} i) = zero)
    (hfne : app f (ofNat.{u} d) ≠ zero)
    (hr : r ∈ PolyRing R zero) (hrb : ∀ i : Nat, d ≤ i → app r (ofNat.{u} i) = zero)
    (he : cls (polyQuotRel R add mul zero f) (PolyRing R zero) r
        = cls (polyQuotRel R add mul zero f) (PolyRing R zero) (polyZero R zero)) :
    r = polyZero R zero := by
  have hR := hF.ring
  have hP := isRing_polyRing (one := one) hR
  have hzP : polyZero R zero ∈ PolyRing R zero :=
    (mem_polyRing_iff _ _ _).mpr (isPolyOver_polyZero hR)
  have hrel := (cls_eq_cls_iff (isCongruence_idealRel_add hP
    (isIdeal_polyIdeal (one := one) hR hf)).left hr hzP).mp he
  have hsub := (opair_mem_idealRel_iff hr hzP).mp hrel
  rw [ringSub_zero hP hr] at hsub
  obtain ⟨s, hs, hseq⟩ := ((mem_polyIdeal_iff (one := one) hR hf).mp hsub).right
  refine remainder_unique hF hf hfa hfne hzP hr hs hrb ?_ hseq
  rw [hP.mulComm _ hzP _ hf, mul_zero_of_isRing hP hf]
  exact (hP.addGroup.left_id _ hr).symm


/-- Every class is the class of a tuple. -/
theorem exists_tuple_cls {R add mul zero one f : ZFSet.{u}} (hF : IsField R add mul zero one)
    (hf : f ∈ PolyRing R zero) {d : Nat}
    (hfa : ∀ i : Nat, d < i → app f (ofNat.{u} i) = zero)
    (hfne : app f (ofNat.{u} d) ≠ zero) {A : ZFSet.{u}} (hA : A ∈ polyQuot R add mul zero f) :
    ∃ t, t ∈ powSet R d ∧ A = cls (polyQuotRel R add mul zero f) (PolyRing R zero)
      (polyOfTuple R zero t d) := by
  have hR := hF.ring
  have hfP := (mem_polyRing_iff _ _ _).mp hf
  obtain ⟨w, hw, hlead⟩ := hF.inverses _ (coeff_mem hfP (ofNat_mem_omega d)) hfne
  obtain ⟨r, hr, hrb, rfl⟩ := exists_polyQuot_rep_below hR hfP hfa hw hlead hA
  obtain ⟨t, ht, hteq⟩ := exists_tuple hR hr hrb
  exact ⟨t, ht, by rw [hteq]⟩

/-- The quotient has exactly `|R|^d` elements. -/
theorem equinumerous_polyQuot {R add mul zero one f : ZFSet.{u}}
    (hF : IsField R add mul zero one)
    (hf : f ∈ PolyRing R zero) {d : Nat}
    (hfa : ∀ i : Nat, d < i → app f (ofNat.{u} i) = zero)
    (hfne : app f (ofNat.{u} d) ≠ zero) :
    Equinumerous (powSet R d) (polyQuot R add mul zero f) := by
  have hR := hF.ring
  have hP := isRing_polyRing (one := one) hR
  have hmaps : ∀ t, t ∈ powSet R d →
      cls (polyQuotRel R add mul zero f) (PolyRing R zero) (polyOfTuple R zero t d)
        ∈ polyQuot R add mul zero f := fun t ht =>
    cls_mem_quotientSet ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyOfTuple hR ht))
  have happ : ∀ t, t ∈ powSet R d →
      app (graphOn (powSet R d) (polyQuot R add mul zero f)
        (fun t => cls (polyQuotRel R add mul zero f) (PolyRing R zero)
          (polyOfTuple R zero t d))) t
        = cls (polyQuotRel R add mul zero f) (PolyRing R zero)
          (polyOfTuple R zero t d) := fun t ht => app_graphOn hmaps ht
  refine ⟨_, ⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range,
    fun t ht t' ht' he => ?_⟩,
    ⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range, fun A hA => ?_⟩⟩
  · -- injective: the two remainders differ by a multiple of `f`, so they agree
    rw [happ t ht, happ t' ht'] at he
    have hpt := isPolyOver_polyOfTuple hR ht
    have hpt' := isPolyOver_polyOfTuple hR ht'
    have hdvd : polyDvd R add mul zero f
        (ringSub (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero)
          (polyOfTuple R zero t d) (polyOfTuple R zero t' d)) := by
      have := (cls_eq_cls_iff (isCongruence_idealRel_add hP
        (isIdeal_polyIdeal (one := one) hR hf)).left
        ((mem_polyRing_iff _ _ _).mpr hpt) ((mem_polyRing_iff _ _ _).mpr hpt')).mp he
      exact ((mem_polyIdeal_iff (one := one) hR hf).mp
        ((opair_mem_idealRel_iff ((mem_polyRing_iff _ _ _).mpr hpt)
          ((mem_polyRing_iff _ _ _).mpr hpt')).mp this)).right
    obtain ⟨s, hs, hseq⟩ := hdvd
    have hzero : ringSub (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero)
        (polyOfTuple R zero t d) (polyOfTuple R zero t' d) = polyZero R zero := by
      refine remainder_unique hF hf hfa hfne
        ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyZero hR))
        (ringSub_mem hP ((mem_polyRing_iff _ _ _).mpr hpt)
          ((mem_polyRing_iff _ _ _).mpr hpt')) hs (fun i hi => ?_) ?_ hseq
      · show app (ringSub (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero)
          (polyOfTuple R zero t d) (polyOfTuple R zero t' d)) (ofNat.{u} i) = zero
        rw [ringSub_def, ringNeg_polyRing hR ((mem_polyRing_iff _ _ _).mpr hpt'),
          opAt_polyAddOp hR ((mem_polyRing_iff _ _ _).mpr hpt)
            ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyNeg hR hpt')),
          app_polyAdd hR hpt (isPolyOver_polyNeg hR hpt') (ofNat_mem_omega i),
          app_polyNeg hR hpt' (ofNat_mem_omega i), app_polyOfTuple hR ht i,
          app_polyOfTuple hR ht' i, if_neg (by omega), if_neg (by omega),
          ringNeg_zero hR, ringAdd_zero hR hR.addGroup.mem_e]
      · rw [hP.mulComm _ ((mem_polyRing_iff _ _ _).mpr (isPolyOver_polyZero hR)) _ hf,
          mul_zero_of_isRing hP hf]
        exact (hP.addGroup.left_id _ (ringSub_mem hP ((mem_polyRing_iff _ _ _).mpr hpt)
          ((mem_polyRing_iff _ _ _).mpr hpt'))).symm
    exact polyOfTuple_injective hR ht ht'
      ((polySub_zero_iff (one := one) hR ((mem_polyRing_iff _ _ _).mpr hpt)
        ((mem_polyRing_iff _ _ _).mpr hpt')).mp hzero)
  · obtain ⟨t, ht, rfl⟩ := exists_tuple_cls hF hf hfa hfne hA
    exact ⟨t, ht, happ t ht⟩

/-! ## Squarefreeness

A repeated factor survives differentiation: if `g² ∣ f` then `g ∣ f'`. So a
polynomial sharing no factor with its derivative has no repeated factor. -/

theorem polyAdd_neg {R add mul zero one f : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) :
    polyAdd R add f (polyNeg R add zero f) = polyZero R zero := by
  refine poly_ext_coeff (isPolyOver_polyAdd hR hf (isPolyOver_polyNeg hR hf))
    (isPolyOver_polyZero hR) (fun k => ?_)
  rw [app_polyAdd hR hf (isPolyOver_polyNeg hR hf) (ofNat_mem_omega k),
    app_polyNeg hR hf (ofNat_mem_omega k), app_polyZero hR (ofNat_mem_omega k)]
  exact ringAdd_neg hR (coeff_mem hf (ofNat_mem_omega k))

theorem monomial_zero_add {R add mul zero one a b : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (ha : a ∈ R) (hb : b ∈ R) :
    monomial R zero (opAt add a b) 0
      = polyAdd R add (monomial R zero a 0) (monomial R zero b 0) := by
  refine poly_ext_coeff (isPolyOver_monomial hR (addAt_mem hR ha hb) 0)
    (isPolyOver_polyAdd hR (isPolyOver_monomial hR ha 0) (isPolyOver_monomial hR hb 0))
    (fun k => ?_)
  rw [app_monomial hR (addAt_mem hR ha hb) 0 k,
    app_polyAdd hR (isPolyOver_monomial hR ha 0) (isPolyOver_monomial hR hb 0)
      (ofNat_mem_omega k),
    app_monomial hR ha 0 k, app_monomial hR hb 0 k, monomialCoeff, monomialCoeff,
    monomialCoeff]
  rcases Nat.decEq k 0 with hne | heq
  · rw [if_neg hne, if_neg hne, if_neg hne, ringAdd_zero hR hR.addGroup.mem_e]
  · rw [if_pos heq, if_pos heq, if_pos heq]


/-- `x`, the polynomial. `polyX_pow` was written about `monomial R zero one 1`
before it had a name. -/
def polyX (R zero one : ZFSet.{u}) : ZFSet.{u} := monomial R zero one 1

/-- `polyNeg` is the additive inverse of the polynomial ring. -/
theorem polyNeg_eq_ringNeg {R add mul zero one f : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) :
    polyNeg R add zero f
      = ringNeg (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero) f := by
  have hP := isRing_polyRing (one := one) hR
  have hfm : f ∈ PolyRing R zero := (mem_polyRing_iff _ _ _).mpr hf
  have hnm : polyNeg R add zero f ∈ PolyRing R zero :=
    polyNeg_mem hR hf
  refine inv_unique hP.addGroup hfm hnm (ringNeg_mem hP hfm) ?_ (ringNeg_add hP hfm)
  rw [opAt_polyAddOp hR hfm hnm]
  exact polyAdd_neg hR hf


/-- `polySub` IS the ring's subtraction on `PolyRing`. Two spellings of one
operation, and until this existed nothing joined them: `app_polySub` gives the
coefficient formula for the first, and the quotient's relation produces the
second, because `opair_mem_idealRel_iff` is stated over an arbitrary ring.

The pieces were both present -- `opAt_polyAddOp` and `polyNeg_eq_ringNeg` --
and the gap was that neither is stated about SUBTRACTION, so a search shaped
around `polySub` finds neither. -/
theorem polySub_eq_ringSub {R add mul zero one f g : ZFSet.{u}}
    (hR : IsRing R add mul zero one)
    (hf : IsPolyOver R zero f) (hg : IsPolyOver R zero g) :
    polySub R add mul zero f g
      = ringSub (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero) f g := by
  have hfm : f ∈ PolyRing R zero := (mem_polyRing_iff _ _ _).mpr hf
  have hnm : polyNeg R add zero g ∈ PolyRing R zero :=
    polyNeg_mem hR hg
  rw [ringSub, ← polyNeg_eq_ringNeg (one := one) hR hg,
    opAt_polyAddOp (one := one) hR hfm hnm]
  rfl

#print axioms polySub_eq_ringSub


theorem monomial_zero {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (k : Nat) : monomial R zero zero k = polyZero R zero := by
  refine poly_ext_coeff (isPolyOver_monomial hR hR.addGroup.mem_e k)
    (isPolyOver_polyZero hR) (fun i => ?_)
  rw [app_monomial hR hR.addGroup.mem_e k i, app_polyZero hR (ofNat_mem_omega i), monomialCoeff]
  rcases Nat.decEq i k with hne | heq
  · rw [if_neg hne]
  · rw [if_pos heq]

theorem monomial_one_zero {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    monomial R zero one 0 = polyOne R zero one := by
  refine poly_ext_coeff (isPolyOver_monomial hR hR.mem_one 0) (isPolyOver_polyOne hR) (fun i => ?_)
  rw [app_monomial hR hR.mem_one 0 i, app_polyOne hR i, monomialCoeff]
  cases i with
  | zero => rw [if_pos rfl]; rfl
  | succ j => rw [if_neg (by omega : ¬ j + 1 = 0)]; rfl

theorem evalAt_monomial {R add mul zero one x a : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hx : x ∈ R) (ha : a ∈ R) (k : Nat) :
    evalAt R add mul zero one x (monomial R zero a k) = opAt mul a (gpow mul one x k) := by
  rw [evalAt_eq hR hx (isPolyOver_monomial hR ha k) (N := k + 1) (fun i hi => by
    rw [app_monomial hR ha k i, monomialCoeff, if_neg (by omega)])]
  have hz : ∀ i, i ≠ k →
      opAt mul (app (monomial R zero a k) (ofNat.{u} i)) (gpow mul one x i) = zero := by
    intro i hi
    rw [app_monomial hR ha k i, monomialCoeff, if_neg hi,
      ringZero_mul hR (ringPow_mem hR hx i)]
  have hTk : opAt mul (app (monomial R zero a k) (ofNat.{u} k)) (gpow mul one x k) ∈ R := by
    rw [app_monomial hR ha k k, monomialCoeff, if_pos rfl]
    exact mulAt_mem hR ha (ringPow_mem hR hx k)
  rw [evalUpTo, foldF_single hR hTk hz (k + 1) (by omega), app_monomial hR ha k k,
    monomialCoeff, if_pos rfl]


theorem evalAt_polyZero {R add mul zero one x : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hx : x ∈ R) : evalAt R add mul zero one x (polyZero R zero) = zero := by
  rw [evalAt_eq hR hx (isPolyOver_polyZero hR) (N := 0)
    (fun i _ => app_polyZero hR (ofNat_mem_omega i))]
  rfl


/-- Euclid's lemma in `F[x]`. An irreducible dividing a product divides a
factor. -/
theorem polyDvd_mul_of_irreducible {R add mul zero one f g h : ZFSet.{u}}
    (hF : IsField R add mul zero one) (hdec : DecidableVanishing R zero)
    (hirr : IsPolyIrreducible R add mul zero one f) {d : Nat}
    (hfa : ∀ i : Nat, d < i → app f (ofNat.{u} i) = zero)
    (hfne : app f (ofNat.{u} d) ≠ zero) (hg : g ∈ PolyRing R zero)
    (hh : h ∈ PolyRing R zero)
    (hdvd : polyDvd R add mul zero f (opAt (polyMulOp R add mul zero) g h)) :
    polyDvd R add mul zero f g ∨ polyDvd R add mul zero f h := by
  have hR := hF.ring
  have hP := isRing_polyRing (one := one) hR
  obtain ⟨hfP, hfnu, hfirr⟩ := hirr
  rcases polyDvd_or_not hF hdec hfP hfa hfne hg with hyes | hno
  · exact Or.inl hyes
  refine Or.inr ?_
  obtain ⟨N, hN⟩ := ((mem_polyRing_iff _ _ _).mp hg).right.right.right
  obtain ⟨e, he, hef, heg, x, y, hx, hy, hbez⟩ :=
    exists_polyBezout hF hdec N f g hfP hg hN
  rcases hfirr e he hef with ⟨w, hw, hwe⟩ | hfe
  · -- the gcd is a unit, so `1 = (xw)f + (yw)g`
    have hone : polyOne R zero one
        = opAt (polyAddOp R add zero)
          (opAt (polyMulOp R add mul zero) (opAt (polyMulOp R add mul zero) x w) f)
          (opAt (polyMulOp R add mul zero) (opAt (polyMulOp R add mul zero) y w) g) := by
      rw [hP.mulAssoc _ hx _ hw _ hfP, hP.mulComm _ hw _ hfP, ← hP.mulAssoc _ hx _ hfP _ hw,
        hP.mulAssoc _ hy _ hw _ hg, hP.mulComm _ hw _ hg, ← hP.mulAssoc _ hy _ hg _ hw,
        ← ringRight_distrib hP (mulAt_mem hP hx hfP) (mulAt_mem hP hy hg) hw, ← hbez]
      exact hwe.symm
    -- multiply through by `h`: both summands are divisible by `f`
    have hsplit : h = opAt (polyAddOp R add zero)
        (opAt (polyMulOp R add mul zero)
          (opAt (polyMulOp R add mul zero) (opAt (polyMulOp R add mul zero) x w) h) f)
        (opAt (polyMulOp R add mul zero) (opAt (polyMulOp R add mul zero) y w)
          (opAt (polyMulOp R add mul zero) g h)) := by
      have hxwf := mulAt_mem hP (mulAt_mem hP hx hw) hfP
      have hywg := mulAt_mem hP (mulAt_mem hP hy hw) hg
      have hstep : opAt (polyMulOp R add mul zero) (polyOne R zero one) h
          = opAt (polyMulOp R add mul zero) (opAt (polyAddOp R add zero)
              (opAt (polyMulOp R add mul zero) (opAt (polyMulOp R add mul zero) x w) f)
              (opAt (polyMulOp R add mul zero) (opAt (polyMulOp R add mul zero) y w) g)) h :=
        congrArg (fun t => opAt (polyMulOp R add mul zero) t h) hone
      rw [ringOne_mul hP hh, ringRight_distrib hP hxwf hywg hh,
        hP.mulAssoc _ (mulAt_mem hP hx hw) _ hfP _ hh, hP.mulComm _ hfP _ hh,
        ← hP.mulAssoc _ (mulAt_mem hP hx hw) _ hh _ hfP,
        hP.mulAssoc _ (mulAt_mem hP hy hw) _ hg _ hh] at hstep
      exact hstep
    rw [hsplit]
    exact polyDvd_add (one := one) hR hfP
      (polyDvd_mul (one := one) hR hfP (mulAt_mem hP (mulAt_mem hP hx hw) hh)
        (polyDvd_refl (one := one) hR hfP))
      (polyDvd_mul (one := one) hR hfP (mulAt_mem hP hy hw) hdvd)
  · exact absurd (polyDvd_trans (one := one) hR hfP he hfe heg) hno

/-! ## Towards uniqueness of the factorisation

Two facts. An associate of an irreducible is irreducible, so a unit can be
absorbed into a factor. And an irreducible dividing a product divides one of the
entries -- stated as a splitting of the list, because `List.erase` needs a
decidable equality that `ZFSet` does not have. -/

/-- A divisor of a unit is a unit. Membership of the unit is not needed: it is
the witness inside `IsPolyUnit` that the argument uses, not the unit itself. -/
theorem polyUnit_of_dvd_unit {R add mul zero one g u : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hg : g ∈ PolyRing R zero)
    (huu : IsPolyUnit R add mul zero one u) (hdvd : polyDvd R add mul zero g u) :
    IsPolyUnit R add mul zero one g := by
  have hP := isRing_polyRing (one := one) hR
  obtain ⟨v, hv, huv⟩ := huu
  obtain ⟨q, hq, hqe⟩ := hdvd
  refine ⟨opAt (polyMulOp R add mul zero) q v, mulAt_mem hP hq hv, ?_⟩
  rw [← hP.mulAssoc _ hg _ hq _ hv, hP.mulComm _ hg _ hq, ← hqe]
  exact huv

/-! ## Multiplicity

How often an irreducible divides a polynomial. Counting divisibility avoids
needing an equality test on factors: the multiplicity is the
largest `k` with `p^k ∣ f`, the search is bounded because `p^k` has top index
`k·dp`, and each test is decided by `polyDvd_or_not`. -/

#print axioms polyMul_bound
#print axioms ringPow_bound
/-- An irreducible generates a PRIME ideal, which is Euclid's lemma
packaged as `IsPrimeIdeal`. The missing link between
`polyDvd_mul_of_irreducible` and the quotient lemmas, which speak of prime
ideals rather than of irreducible elements. -/
theorem isPrimeIdeal_polyIdeal {R add mul zero one f : ZFSet.{u}}
    (hF : IsField R add mul zero one) (hdec : DecidableVanishing R zero)
    (hirr : IsPolyIrreducible R add mul zero one f) {d : Nat}
    (hfa : ∀ i : Nat, d < i → app f (ofNat.{u} i) = zero)
    (hfne : app f (ofNat.{u} d) ≠ zero) :
    IsPrimeIdeal (polyIdeal R add mul zero f) (PolyRing R zero)
      (polyAddOp R add zero) (polyMulOp R add mul zero)
      (polyZero R zero) (polyOne R zero one) := by
  have hR := hF.ring
  have hP := isRing_polyRing (one := one) hR
  obtain ⟨hfP, hfnu, -⟩ := id hirr
  refine ⟨isIdeal_polyIdeal hR hfP, ?_, ?_⟩
  · intro hmem
    obtain ⟨-, q, hq, hone⟩ := (mem_polyIdeal_iff hR hfP).mp hmem
    exact hfnu ⟨q, hq, by rw [hP.mulComm _ hfP _ hq]; exact hone.symm⟩
  · intro a ha b hb hab
    obtain ⟨-, hdvd⟩ := (mem_polyIdeal_iff hR hfP).mp hab
    rcases polyDvd_mul_of_irreducible hF hdec hirr hfa hfne ha hb hdvd with h | h
    · exact Or.inl ((mem_polyIdeal_iff hR hfP).mpr ⟨ha, h⟩)
    · exact Or.inr ((mem_polyIdeal_iff hR hfP).mpr ⟨hb, h⟩)

#print axioms isPrimeIdeal_polyIdeal
/-- Evaluation at a point, as a map `R[x] -> R`. -/
def evalPoint (R add mul zero one a : ZFSet.{u}) : ZFSet.{u} :=
  graphOn (PolyRing R zero) R (evalAt R add mul zero one a)

theorem app_evalPoint {R add mul zero one a f : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (ha : a ∈ R) (hf : f ∈ PolyRing R zero) :
    app (evalPoint R add mul zero one a) f = evalAt R add mul zero one a f :=
  app_graphOn (fun _ hg => evalAt_mem hR ha ((mem_polyRing_iff _ _ _).mp hg)) hf

/-- And it is a ring homomorphism. The three laws are `evalAt_polyAdd`,
`evalAt_polyMul` and `evalAt_polyOne`, which already existed -- so carrying a
curve's coefficients down to `R` by evaluating at a point costs no new
construction. -/
theorem isRingHom_evalPoint {R add mul zero one a : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (ha : a ∈ R) :
    IsRingHom (evalPoint R add mul zero one a) (PolyRing R zero)
      (polyAddOp R add zero) (polyMulOp R add mul zero) (polyOne R zero one)
      R add mul one := by
  have hP := isRing_polyRing (one := one) hR
  have hmaps : ∀ g, g ∈ PolyRing R zero → evalAt R add mul zero one a g ∈ R :=
    fun g hg => evalAt_mem hR ha ((mem_polyRing_iff _ _ _).mp hg)
  refine ⟨⟨graphOn_isFunction _ _ _, graphOn_domain hmaps, graphOn_range, ?_⟩, ?_, ?_⟩
  · intro f hf g hg
    rw [app_evalPoint hR ha (opAt_mem hP.addGroup hf hg), app_evalPoint hR ha hf,
      app_evalPoint hR ha hg, opAt_polyAddOp hR hf hg,
      evalAt_polyAdd hR ha ((mem_polyRing_iff _ _ _).mp hf)
        ((mem_polyRing_iff _ _ _).mp hg)]
  · intro f hf g hg
    rw [app_evalPoint hR ha (mulAt_mem hP hf hg), app_evalPoint hR ha hf,
      app_evalPoint hR ha hg, opAt_polyMulOp hR hf hg,
      evalAt_polyMul hR ha ((mem_polyRing_iff _ _ _).mp hf)
        ((mem_polyRing_iff _ _ _).mp hg)]
  · rw [app_evalPoint hR ha (polyOne_mem hR),
      evalAt_polyOne hR ha]

#print axioms evalPoint
#print axioms app_evalPoint
#print axioms isRingHom_evalPoint

/-- `F[x]/(f)` is a field for irreducible `f`. -/
theorem isField_polyQuot {R add mul zero one f : ZFSet.{u}} (hF : IsField R add mul zero one)
    (hdec : DecidableVanishing R zero) (hirr : IsPolyIrreducible R add mul zero one f) :
    IsField (polyQuot R add mul zero f)
      (congOp (polyQuotRel R add mul zero f) (PolyRing R zero) (polyAddOp R add zero))
      (congOp (polyQuotRel R add mul zero f) (PolyRing R zero) (polyMulOp R add mul zero))
      (cls (polyQuotRel R add mul zero f) (PolyRing R zero) (polyZero R zero))
      (cls (polyQuotRel R add mul zero f) (PolyRing R zero) (polyOne R zero one)) := by
  have hR := hF.ring
  have hP := isRing_polyRing (one := one) hR
  obtain ⟨hfP, hfnu, hfirr⟩ := hirr
  have hI := isIdeal_polyIdeal (one := one) hR hfP
  have honeP : polyOne R zero one ∈ PolyRing R zero :=
    polyOne_mem hR
  -- the class of a polynomial is zero exactly when `f` divides it
  have hclszero : ∀ g, g ∈ PolyRing R zero →
      (cls (polyQuotRel R add mul zero f) (PolyRing R zero) g
        = cls (polyQuotRel R add mul zero f) (PolyRing R zero) (polyZero R zero)
      ↔ polyDvd R add mul zero f g) := by
    intro g hg
    refine Iff.trans (cls_eq_zero_iff hP hI hg) ?_
    exact ⟨fun h => ((mem_polyIdeal_iff (one := one) hR hfP).mp h).right,
      fun h => (mem_polyIdeal_iff (one := one) hR hfP).mpr ⟨hg, h⟩⟩
  refine ⟨isRing_quotientByIdeal hP hI, fun he => ?_, fun A hA hAne => ?_⟩
  · -- `1` is in the ideal only if `f` is a unit
    obtain ⟨q, hq, hqe⟩ := (hclszero _ honeP).mp he.symm
    exact hfnu ⟨q, hq, by rw [hP.mulComm _ hfP _ hq]; exact hqe.symm⟩
  · obtain ⟨g, hg, rfl⟩ := (mem_quotientSet_iff _ _ A).mp hA
    have hnd : ¬ polyDvd R add mul zero f g := fun hd => hAne ((hclszero g hg).mpr hd)
    -- Bézout on `f` and `g`
    obtain ⟨N, hN⟩ := ((mem_polyRing_iff _ _ _).mp hg).right.right.right
    obtain ⟨e, he, hef, heg, x, y, hx, hy, hbez⟩ :=
      exists_polyBezout hF hdec N f g hfP hg hN
    -- `e` divides `f`, so it is a unit
    rcases hfirr e he hef with ⟨w, hw, hwe⟩ | hfe
    · -- `1 = (xw)f + (yw)g`, so `[g]·[yw] = [1]`
      refine ⟨cls (polyQuotRel R add mul zero f) (PolyRing R zero)
        (opAt (polyMulOp R add mul zero) y w), cls_mem_quotientSet (mulAt_mem hP hy hw), ?_⟩
      have hone : polyOne R zero one
          = opAt (polyAddOp R add zero)
            (opAt (polyMulOp R add mul zero) (opAt (polyMulOp R add mul zero) x w) f)
            (opAt (polyMulOp R add mul zero) (opAt (polyMulOp R add mul zero) y w) g) := by
        rw [hP.mulAssoc _ hx _ hw _ hfP, hP.mulComm _ hw _ hfP, ← hP.mulAssoc _ hx _ hfP _ hw,
          hP.mulAssoc _ hy _ hw _ hg, hP.mulComm _ hw _ hg, ← hP.mulAssoc _ hy _ hg _ hw,
          ← ringRight_distrib hP (mulAt_mem hP hx hfP) (mulAt_mem hP hy hg) hw, ← hbez]
        exact hwe.symm
      -- so `g·(yw) - 1` is a multiple of `f`
      rw [polyQuotRel, opAt_congOp (fun p hp q hq => mulAt_mem hP hp hq)
        (isCongruence_idealRel_mul hP hI) hg (mulAt_mem hP hy hw)]
      refine (cls_eq_cls_iff (isCongruence_idealRel_add hP hI).left
        (mulAt_mem hP hg (mulAt_mem hP hy hw)) honeP).mpr ?_
      refine (opair_mem_idealRel_iff (mulAt_mem hP hg (mulAt_mem hP hy hw)) honeP).mpr ?_
      refine (mem_polyIdeal_iff (one := one) hR hfP).mpr
        ⟨ringSub_mem hP (mulAt_mem hP hg (mulAt_mem hP hy hw)) honeP, ?_⟩
      -- `g·(yw) - 1 = -( (xw)·f )`
      have hcalc : ringSub (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero)
          (opAt (polyMulOp R add mul zero) g (opAt (polyMulOp R add mul zero) y w))
          (polyOne R zero one)
          = ringNeg (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero)
            (opAt (polyMulOp R add mul zero) (opAt (polyMulOp R add mul zero) x w) f) := by
        rw [hone, ringSub_def, ringNeg_addAt hP
            (mulAt_mem hP (mulAt_mem hP hx hw) hfP) (mulAt_mem hP (mulAt_mem hP hy hw) hg),
          ← ringAdd_assoc hP (mulAt_mem hP hg (mulAt_mem hP hy hw))
            (ringNeg_mem hP (mulAt_mem hP (mulAt_mem hP hx hw) hfP))
            (ringNeg_mem hP (mulAt_mem hP (mulAt_mem hP hy hw) hg)),
          ringAdd_comm hP (mulAt_mem hP hg (mulAt_mem hP hy hw))
            (ringNeg_mem hP (mulAt_mem hP (mulAt_mem hP hx hw) hfP)),
          ringAdd_assoc hP (ringNeg_mem hP (mulAt_mem hP (mulAt_mem hP hx hw) hfP))
            (mulAt_mem hP hg (mulAt_mem hP hy hw))
            (ringNeg_mem hP (mulAt_mem hP (mulAt_mem hP hy hw) hg)),
          hP.mulComm _ hg _ (mulAt_mem hP hy hw),
          ringAdd_neg hP (mulAt_mem hP (mulAt_mem hP hy hw) hg),
          ringAdd_zero hP (ringNeg_mem hP (mulAt_mem hP (mulAt_mem hP hx hw) hfP))]
      rw [hcalc]
      refine ⟨ringNeg (PolyRing R zero) (polyAddOp R add zero) (polyZero R zero)
        (opAt (polyMulOp R add mul zero) x w), ringNeg_mem hP (mulAt_mem hP hx hw), ?_⟩
      rw [ringNeg_mul hP (mulAt_mem hP hx hw) hfP]
    · -- an associate of `f` cannot divide `g` without `f` doing so
      exact absurd (polyDvd_trans (one := one) hR hfP he hfe heg) hnd

/-! ## The ring laws at the raw operations

`isRing_polyRing` states every law for `opAt (polyAddOp …)`, but the definitions
`polyAdd` and `polyMul` are what other files write, so every use round-trips
through `opAt_polyAddOp`. These state the laws where they are used. -/

theorem polyMul_comm {R add mul zero one f g : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : f ∈ PolyRing R zero) (hg : g ∈ PolyRing R zero) :
    polyMul R add mul zero f g = polyMul R add mul zero g f := by
  rw [← opAt_polyMulOp hR hf hg, ← opAt_polyMulOp hR hg hf]
  exact (isRing_polyRing (one := one) hR).mulComm _ hf _ hg


theorem polyMul_assoc {R add mul zero one f g h : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hf : f ∈ PolyRing R zero) (hg : g ∈ PolyRing R zero) (hh : h ∈ PolyRing R zero) :
    polyMul R add mul zero (polyMul R add mul zero f g) h
      = polyMul R add mul zero f (polyMul R add mul zero g h) := by
  have hP := isRing_polyRing (one := one) hR
  rw [← opAt_polyMulOp hR hf hg, ← opAt_polyMulOp hR hg hh,
    ← opAt_polyMulOp hR (mulAt_mem hP hf hg) hh,
    ← opAt_polyMulOp hR hf (mulAt_mem hP hg hh)]
  exact hP.mulAssoc _ hf _ hg _ hh

/-- The 2x2 determinant over a commutative ring.

A Lean-level function of four elements rather than a set function: every use
site applies it to named coefficients, so `graphOn` would put an `app` at each
one and buy nothing.

No order and no sign. Geometry's six sites use this three ways -- non-vanishing,
the Cramer expansions, and a sign they TAKE as a hypothesis rather than derive
-- and only the middle one is about the determinant itself. A determinant that
returned a sign would drag a locator into the four sites that do not want one
(over a construction base the sign DISJUNCTION is free and the sign as DATA is
not). -/
def det2 (R add mul zero a b a' b' : ZFSet.{u}) : ZFSet.{u} :=
  ringSub R add zero (opAt mul a b') (opAt mul a' b)

theorem det2_mem {R add mul zero one a b a' b' : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (ha : a ∈ R) (hb : b ∈ R)
    (ha' : a' ∈ R) (hb' : b' ∈ R) : det2 R add mul zero a b a' b' ∈ R :=
  ringSub_mem hR (mulAt_mem hR ha hb') (mulAt_mem hR ha' hb)

/-- Swapping the columns negates it. -/
theorem det2_swap {R add mul zero one a b a' b' : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (ha : a ∈ R) (hb : b ∈ R)
    (ha' : a' ∈ R) (hb' : b' ∈ R) :
    det2 R add mul zero b a b' a'
      = ringNeg R add zero (det2 R add mul zero a b a' b') := by
  rw [det2, det2,
    ringSub_swap hR (mulAt_mem hR ha hb') (mulAt_mem hR ha' hb),
    hR.mulComm b hb a' ha', hR.mulComm b' hb' a ha]

/-- The Cramer expansion along the shared column.

    a * det(c b c' b') + b * det(a c a' c') = c * det(a b a' b')

The identity geometry inlines at `cross_first` and `cross_second` over the
located reals. It is a RING identity -- both sides expand to the same six
products -- which is the argument for the determinant living here rather than
over an ordered field. -/
theorem det2_cramer {R add mul zero one a b c a' b' c' : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (ha : a ∈ R) (hb : b ∈ R) (hc : c ∈ R)
    (ha' : a' ∈ R) (hb' : b' ∈ R) (hc' : c' ∈ R) :
    opAt add (opAt mul a (det2 R add mul zero c b c' b'))
        (opAt mul b (det2 R add mul zero a c a' c'))
      = opAt mul c (det2 R add mul zero a b a' b') := by
  have hab' := mulAt_mem hR ha hb'
  have ha'b := mulAt_mem hR ha' hb
  have hcb' := mulAt_mem hR hc hb'
  have hc'b := mulAt_mem hR hc' hb
  have hac' := mulAt_mem hR ha hc'
  have ha'c := mulAt_mem hR ha' hc
  rw [det2, det2, det2, ringSub_def, ringSub_def, ringSub_def,
    hR.distrib a ha _ hcb' _ (ringNeg_mem hR hc'b),
    hR.distrib b hb _ hac' _ (ringNeg_mem hR ha'c),
    hR.distrib c hc _ hab' _ (ringNeg_mem hR ha'b),
    ringMul_neg hR ha hc'b, ringMul_neg hR hb ha'c,
    ringMul_neg hR hc ha'b]
  have hX : opAt mul c (opAt mul a b') = opAt mul a (opAt mul c b') := by
    rw [← hR.mulAssoc c hc a ha b' hb', ← hR.mulAssoc a ha c hc b' hb',
      hR.mulComm c hc a ha]
  have hY : opAt mul b (opAt mul a c') = opAt mul a (opAt mul c' b) := by
    rw [← hR.mulAssoc b hb a ha c' hc', ← hR.mulAssoc a ha c' hc' b hb,
      hR.mulComm b hb a ha, hR.mulAssoc a ha b hb c' hc',
      hR.mulComm b hb c' hc', ← hR.mulAssoc a ha c' hc' b hb]
  have hZ : opAt mul b (opAt mul a' c) = opAt mul c (opAt mul a' b) := by
    rw [← hR.mulAssoc b hb a' ha' c hc, ← hR.mulAssoc c hc a' ha' b hb,
      hR.mulComm b hb a' ha', hR.mulComm c hc a' ha',
      hR.mulAssoc a' ha' b hb c hc, hR.mulAssoc a' ha' c hc b hb,
      hR.mulComm b hb c hc]
  rw [hX, hY, hZ]
  have hxm := mulAt_mem hR ha hcb'
  have hym := mulAt_mem hR ha hc'b
  have hzm := mulAt_mem hR hc ha'b
  rw [hR.addGroup.assoc _ hxm _ (ringNeg_mem hR hym) _
        (opAt_mem hR.addGroup hym (ringNeg_mem hR hzm)),
    ← hR.addGroup.assoc _ (ringNeg_mem hR hym) _ hym _ (ringNeg_mem hR hzm),
    ringNeg_add hR hym, hR.addGroup.left_id _ (ringNeg_mem hR hzm)]

/-- The minor: drop row 0 and column `j`, as an entry function. -/
def matMinor (E : Nat → Nat → ZFSet.{u}) (j : Nat) : Nat → Nat → ZFSet.{u} :=
  fun i k => E (i + 1) (if k < j then k else k + 1)

/-- The determinant of an `n x n` entry function, by Laplace along row 0.

Over an ENTRY FUNCTION rather than a set-matrix, because the recursion needs to
drop a row and a column and `matEntry` reads a fixed `powSet` shape. A caller
with a matrix passes `matEntry A n n`.

The sign is Nat parity, not permutation parity. `j % 2 = 0` is decidable
arithmetic and computes; nothing is extracted from a Prop, so Laplace is free
here. That is sharper than Laplace never forms a sign -- it forms one, and
the one it forms costs nothing. -/
noncomputable def detN (R add mul zero one : ZFSet.{u})
    (E : Nat → Nat → ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => one
  | n + 1 =>
    foldF add zero
      (fun j =>
        let t := opAt mul (E 0 j) (detN R add mul zero one (matMinor E j) n)
        if j % 2 = 0 then t else ringNeg R add zero t)
      (n + 1)

/-! ## Audit

Nothing classical: a polynomial is a function with a support bound, and every
step is pointwise. -/

#print axioms foldF_multiple
#print axioms dvd_of_addAt_dvd
#print axioms convCoeff_split
#print axioms exists_least_not_dvd
/-- Eisenstein's data at `ℤ`, for a prime `p`. The first instance the family
has ever had: `dec` and `prime` are discharged from `Field.lean`'s integer
divisibility lemmas, and only the three clauses a caller genuinely supplies
remain as hypotheses.

The two spellings meet here -- `IsEisenstein` states divisibility with
`opAt mul` and the integer lemmas use `intMul`, so `opAt_intMulOp` converts at
each clause. -/
theorem isEisenstein_int {p : Nat} (hp : IsPrime p) {g h : ZFSet.{u}}
    (hg : IsPolyOver NumberTheory.Int.{u} intZero.{u} g)
    (hh : IsPolyOver NumberTheory.Int.{u} intZero.{u} h)
    (hconst : ¬ ∃ c, c ∈ NumberTheory.Int.{u} ∧
      app h (ofNat.{u} 0) = opAt intMulOp.{u} (intOfNat.{u} p) c) :
    IsEisenstein NumberTheory.Int.{u} intMulOp.{u} intZero.{u} (intOfNat.{u} p) g h where
  polyG := hg
  polyH := hh
  dec := fun i => by
    have hgi : app g (ofNat.{u} i) ∈ NumberTheory.Int.{u} := coeff_mem hg (ofNat_mem_omega _)
    have hcv : ∀ c, c ∈ NumberTheory.Int.{u} ->
        opAt intMulOp.{u} (intOfNat.{u} p) c = intMul (intOfNat.{u} p) c :=
      fun c hc => opAt_intMulOp (intOfNat_mem_Int p) hc
    rcases intDvd_decidable (a := p) hgi with hy | hn
    · exact Or.inl (by
        obtain ⟨c, hc, he⟩ := hy
        exact ⟨c, hc, by rw [hcv c hc, he]⟩)
    · exact Or.inr (fun hy => hn (by
        obtain ⟨c, hc, he⟩ := hy
        exact ⟨c, hc, by rw [he, hcv c hc]⟩))
  prime := fun a b ha hb hab => by
    have hcv : ∀ c, c ∈ NumberTheory.Int.{u} ->
        opAt intMulOp.{u} (intOfNat.{u} p) c = intMul (intOfNat.{u} p) c :=
      fun c hc => opAt_intMulOp (intOfNat_mem_Int p) hc
    have hab' : ∃ c, c ∈ NumberTheory.Int.{u} ∧
        intMul a b = intMul (intOfNat.{u} p) c := by
      obtain ⟨c, hc, he⟩ := hab
      exact ⟨c, hc, by rw [← opAt_intMulOp ha hb, he, hcv c hc]⟩
    exact (intPrime_divides_mul hp ha hb hab').imp
      (fun ⟨c, hc, he⟩ => ⟨c, hc, by rw [he, hcv c hc]⟩)
      (fun ⟨c, hc, he⟩ => ⟨c, hc, by rw [he, hcv c hc]⟩)
  const := hconst

#print axioms IsEisenstein
#print axioms isEisenstein_int
#print axioms eisenstein_least_index
#print axioms eisenstein_nonzero_high
#print axioms eisenstein_factor_constant
#print axioms not_dvd_convCoeff
#print axioms mem_polyRing_iff
#print axioms isGroup_polyAdd
#print axioms isAbelian_polyAdd
#print axioms isPolyOver_polyMul
#print axioms convCoeff_comm
#print axioms convCoeff_distrib
#print axioms isRing_polyRing
#print axioms evalAt_eq
#print axioms evalAt_polyAdd
#print axioms evalAt_polyMul

#print axioms evalAt_polyOfList
#print axioms exists_deg
#print axioms exists_polyDiv
#print axioms exists_polyBezout
#print axioms polyUnit_const
#print axioms polyDvd_or_not
#print axioms polyQuot_eq_or_ne
#print axioms equinumerous_polyQuot
#print axioms binomial
#print axioms polyDvd_mul_of_irreducible
#print axioms isField_polyQuot
#print axioms polyOfTuple_succ
#print axioms cls_polyOfTuple_succ
#print axioms exists_polyQuot_rep_below
#print axioms monomial_zero_eq_polyZero
#print axioms poly_eq_zero_of_cls_zero
#print axioms decidableVanishing_polyQuot
#print axioms isRing_polyQuot

#print axioms det2
#print axioms det2_mem
#print axioms det2_swap
#print axioms det2_cramer
#print axioms matMinor
#print axioms detN
end Algebra

#print axioms Algebra.polyOne_mem
#print axioms Algebra.polyNeg_mem
#print axioms Algebra.app_polyOfList
namespace ZFSet
export Algebra (IsBoundOf IsDegOf IsEisenstein IsEvalOf IsPolyIrreducible IsPolyOver IsPolyUnit PolyRing app_evalPoint app_foldF_polyAdd app_linearPoly app_monomial app_polyAdd app_polyAdd_semi app_polyMul app_polyMul_semi app_polyNeg app_polyOfList app_polyOfSeq app_polyOfTuple app_polyOne app_polyOne_semi app_polySub app_polyZero app_polyZero_semi binomShift binomShift_mem binomShift_mem_semi binomSum binomSum_mem binomSum_mem_semi binomSum_mul binomSum_mul_semi binomSum_recombine binomSum_recombine_semi binomSum_succ binomSum_succ_semi binomTerm binomTerm_eq_zero_of_gt binomTerm_mem binomTerm_mem_semi binomTerm_mul_left binomTerm_mul_left_semi binomTerm_mul_right binomTerm_mul_right_semi binomTerm_split binomTerm_split_semi binomTerm_succ binomTerm_succ_semi binomUp binomUp_mem binomUp_mem_semi binomUp_succ binomUp_succ_semi binomial binomial_semi cls_polyOfTuple_succ coeff_mem coeffs_linearPoly convCoeff convCoeff_above convCoeff_assoc_semi convCoeff_comm convCoeff_distrib convCoeff_distrib_right_semi convCoeff_distrib_semi convCoeff_eq_zero convCoeff_eq_zero_semi convCoeff_mem convCoeff_mem_semi convCoeff_monomial convCoeff_mul_left_semi convCoeff_mul_right_semi convCoeff_one convCoeff_one_left convCoeff_one_left_semi convCoeff_one_semi convCoeff_split convCoeff_top convCoeff_zero_left_semi convCoeff_zero_right_semi convTerm convTerm_mem_semi decidableVanishing_of_finite decidableVanishing_polyQuot det2 det2_cramer det2_mem det2_swap detN dvd_of_addAt_dvd eisenstein_factor_constant eisenstein_least_index eisenstein_nonzero_high eq_polyZero_of_coeffs eq_polyZero_of_monic_mul equinumerous_polyQuot equinumerous_powSet evalAt evalAt_eq evalAt_linearPoly evalAt_mem evalAt_monomial evalAt_polyAdd evalAt_polyMul evalAt_polyOfList evalAt_polyOne evalAt_polyZero evalPoint evalTerm evalUpTo evalUpTo_mem evalUpTo_stable exists_deg exists_lead exists_least_not_dvd exists_polyBezout exists_polyDiv exists_polyQuot_rep_below exists_tuple exists_tuple_cls foldF_extend foldF_last foldF_last_semi foldF_mul_left foldF_mul_left_lt foldF_mul_left_semi foldF_mul_right foldF_mul_right_lt foldF_mul_right_semi foldF_multiple foldF_single foldF_single_below foldF_telescope foldF_zeros foldF_zeros_semi isAbelian_polyAdd isAbelian_polyAdd_semi isCommMonoid_polyAdd_semi isCommMonoid_ringAdd isCommMonoid_ringMul isEisenstein_int isField_polyQuot isFunction_polyOfSeq isGroup_polyAdd isIdeal_polyIdeal isPolyOver_linearPoly isPolyOver_mono isPolyOver_monomial isPolyOver_polyAdd isPolyOver_polyAdd_semi isPolyOver_polyMul isPolyOver_polyMul_semi isPolyOver_polyNeg isPolyOver_polyOfList isPolyOver_polyOfSeq isPolyOver_polyOfTuple isPolyOver_polyOne isPolyOver_polyOne_semi isPolyOver_polySub isPolyOver_polyZero isPolyOver_polyZero_semi isPrimeIdeal_polyIdeal isRingHom_evalPoint isRing_polyQuot isRing_polyRing isSemiring_polyRing leibTerm linearPoly listCoeff listCoeff_eq_zero listCoeff_mem matMinor mem_polyIdeal_iff mem_polyOfSeq_iff mem_polyRing_iff monomial monomialCoeff monomialCoeff_mem monomial_mul_monomial monomial_one_zero monomial_zero monomial_zero_add monomial_zero_eq_polyOne monomial_zero_eq_polyZero not_dvd_convCoeff opAt_polyAddOp opAt_polyAddOp_semi opAt_polyMulOp opAt_polyMulOp_semi polyAdd polyAddOp polyAdd_neg polyDeriv polyDvd polyDvd_add polyDvd_mul polyDvd_mul_of_irreducible polyDvd_or_not polyDvd_refl polyDvd_trans polyDvd_zero polyIdeal polyMul polyMulOp polyMul_assoc polyMul_bound polyMul_comm polyMul_mem polyMul_mem_semi polyMul_one_left polyMul_top polyMul_top_of_top polyNeg polyNeg_eq_ringNeg polyNeg_mem polyOfList polyOfSeq polyOfTuple polyOfTuple_injective polyOfTuple_succ polyOfTuple_tupleOfPoly polyOne polyOne_mem polyOne_mem_semi polyQuot polyQuotRel polyQuot_eq_or_ne polySub polySub_add_cancel polySub_eq_ringSub polySub_zero_iff polyUnit_const polyUnit_of_const polyUnit_of_dvd_unit polyX polyZero poly_eq_zero_of_cls_zero poly_ext poly_ext_coeff powSet powSet_ext remainder_eq_sub_mul remainder_unique remainder_unique_domain remainder_unique_monic ringNeg_polyRing ringNsmul_foldF ringPow_bound tupleCoeff tupleCoeff_mem tupleCoeff_tupleOf tupleOf tupleOfPoly tupleOfPoly_mem tupleOf_mem unitCoeff unitCoeff_mem unitCoeff_mem_semi)
end ZFSet
