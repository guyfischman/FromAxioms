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

#print axioms polyMul_bound
#print axioms ringPow_bound
#print axioms foldF_multiple
#print axioms dvd_of_addAt_dvd
#print axioms convCoeff_split
#print axioms exists_least_not_dvd
#print axioms IsEisenstein
#print axioms eisenstein_least_index
#print axioms eisenstein_nonzero_high
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

#print axioms binomial
end Algebra

#print axioms Algebra.polyOne_mem
#print axioms Algebra.polyNeg_mem
namespace ZFSet
export Algebra (IsEisenstein IsEvalOf IsPolyOver PolyRing app_foldF_polyAdd app_monomial app_polyAdd app_polyAdd_semi app_polyMul app_polyMul_semi app_polyNeg app_polyOfSeq app_polyOne app_polyOne_semi app_polyZero app_polyZero_semi binomShift binomShift_mem binomShift_mem_semi binomSum binomSum_mem binomSum_mem_semi binomSum_mul binomSum_mul_semi binomSum_recombine binomSum_recombine_semi binomSum_succ binomSum_succ_semi binomTerm binomTerm_eq_zero_of_gt binomTerm_mem binomTerm_mem_semi binomTerm_mul_left binomTerm_mul_left_semi binomTerm_mul_right binomTerm_mul_right_semi binomTerm_split binomTerm_split_semi binomTerm_succ binomTerm_succ_semi binomUp binomUp_mem binomUp_mem_semi binomUp_succ binomUp_succ_semi binomial binomial_semi coeff_mem convCoeff convCoeff_assoc_semi convCoeff_comm convCoeff_distrib convCoeff_distrib_right_semi convCoeff_distrib_semi convCoeff_eq_zero convCoeff_eq_zero_semi convCoeff_mem convCoeff_mem_semi convCoeff_monomial convCoeff_mul_left_semi convCoeff_mul_right_semi convCoeff_one convCoeff_one_left_semi convCoeff_one_semi convCoeff_split convCoeff_zero_left_semi convCoeff_zero_right_semi convTerm convTerm_mem_semi dvd_of_addAt_dvd eisenstein_least_index eisenstein_nonzero_high evalAt evalAt_eq evalAt_mem evalAt_polyAdd evalAt_polyMul evalAt_polyOne evalTerm evalUpTo evalUpTo_mem evalUpTo_stable exists_least_not_dvd foldF_extend foldF_last foldF_last_semi foldF_mul_left foldF_mul_left_lt foldF_mul_left_semi foldF_mul_right foldF_mul_right_lt foldF_mul_right_semi foldF_multiple foldF_single foldF_single_below foldF_telescope foldF_zeros foldF_zeros_semi isAbelian_polyAdd isAbelian_polyAdd_semi isCommMonoid_polyAdd_semi isCommMonoid_ringAdd isCommMonoid_ringMul isFunction_polyOfSeq isGroup_polyAdd isPolyOver_mono isPolyOver_monomial isPolyOver_polyAdd isPolyOver_polyAdd_semi isPolyOver_polyMul isPolyOver_polyMul_semi isPolyOver_polyNeg isPolyOver_polyOfSeq isPolyOver_polyOne isPolyOver_polyOne_semi isPolyOver_polyZero isPolyOver_polyZero_semi isRing_polyRing isSemiring_polyRing leibTerm mem_polyOfSeq_iff mem_polyRing_iff monomial monomialCoeff monomialCoeff_mem monomial_mul_monomial monomial_zero_eq_polyOne not_dvd_convCoeff opAt_polyAddOp opAt_polyAddOp_semi opAt_polyMulOp opAt_polyMulOp_semi polyAdd polyAddOp polyDeriv polyMul polyMulOp polyMul_bound polyMul_mem polyMul_mem_semi polyNeg polyNeg_mem polyOfSeq polyOne polyOne_mem polyOne_mem_semi polyZero poly_ext poly_ext_coeff ringNsmul_foldF ringPow_bound unitCoeff unitCoeff_mem unitCoeff_mem_semi)
end ZFSet
