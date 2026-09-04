/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Modules over a ring.

A module is a set `V` with an abelian group structure and an action of a ring
`R` on it. The point of stating it abstractly is that the two things this
library wants to count are not tuple spaces: a field extension is a module over
its subfield, and `R^n` is only one instance.

A family of vectors is a Lean-level list, so a linear combination is a
structural recursion rather than a fold over an index set. The span is the set
of combinations; independence says the coefficients are unique, and that makes a
span of `d` independent vectors a copy of `R^d`.
-/

import FromAxioms.Algebra.PolyRing

universe u

open Core NumberTheory SetTheory
namespace Algebra

/-! ## The structure -/

/-- A module over a ring. -/
structure IsModule (R add mul zero one V vadd vzero smul : ZFSet.{u}) : Prop where
  ring : IsRing R add mul zero one
  group : IsGroup V vadd vzero
  comm : IsAbelian V vadd
  smulFun : IsFunction smul
  smulDom : domain smul = prod R V
  smulRan : range smul ⊆ V
  smul_add : ∀ c, c ∈ R → ∀ x, x ∈ V → ∀ y, y ∈ V →
    opAt smul c (opAt vadd x y) = opAt vadd (opAt smul c x) (opAt smul c y)
  add_smul : ∀ c, c ∈ R → ∀ d, d ∈ R → ∀ x, x ∈ V →
    opAt smul (opAt add c d) x = opAt vadd (opAt smul c x) (opAt smul d x)
  smul_smul : ∀ c, c ∈ R → ∀ d, d ∈ R → ∀ x, x ∈ V →
    opAt smul (opAt mul c d) x = opAt smul c (opAt smul d x)
  one_smul : ∀ x, x ∈ V → opAt smul one x = x

theorem smulAt_mem {R add mul zero one V vadd vzero smul c x : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (hc : c ∈ R) (hx : x ∈ V) :
    opAt smul c x ∈ V :=
  hM.smulRan _ (app_mem_range hM.smulFun (by rw [hM.smulDom]; exact opair_mem_prod hc hx))

theorem vaddAt_mem {R add mul zero one V vadd vzero smul x y : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (hx : x ∈ V) (hy : y ∈ V) :
    opAt vadd x y ∈ V := opAt_mem hM.group hx hy

/-! ## Quotients

The additive half of a quotient module is `isGroup_congQuotient`, which takes an
`IsCongruence` and hands back `IsGroup (quotientSet r G) (congOp r G op)`. What
`congOp` cannot supply is the SCALAR action: it descends a binary operation by
quotienting BOTH arguments, while a scalar action quotients only the second ---
the ring keeps its own elements.

    `congOp   r V vadd`  :  V/r  x  V/r  ->  V/r
    `congSmul r R V smul`:   R   x  V/r   ->  V/r
-/

/-- Scaling by zero is the zero vector: `(0 + 0)·x = 0·x` cancels. -/
theorem zero_smul {R add mul zero one V vadd vzero smul x : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (hx : x ∈ V) :
    opAt smul zero x = vzero := by
  have hz := hM.ring.addGroup.mem_e
  have hzx := smulAt_mem hM hz hx
  have hstep : opAt smul zero x = opAt vadd (opAt smul zero x) (opAt smul zero x) := by
    rw [← hM.add_smul _ hz _ hz _ hx, ringAdd_zero hM.ring hz]
  refine op_left_cancel hM.group hzx hzx hM.group.mem_e ?_
  rw [hM.group.right_id _ hzx]
  exact hstep.symm

theorem vadd_shuffle_pair {R add mul zero one V vadd vzero smul a b c d : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (ha : a ∈ V) (hb : b ∈ V)
    (hc : c ∈ V) (hd : d ∈ V) :
    opAt vadd (opAt vadd a b) (opAt vadd c d) = opAt vadd (opAt vadd a c) (opAt vadd b d) := by
  rw [hM.group.assoc _ ha _ hb _ (vaddAt_mem hM hc hd),
    ← hM.group.assoc _ hb _ hc _ hd, hM.comm _ hb _ hc, hM.group.assoc _ hc _ hb _ hd,
    ← hM.group.assoc _ ha _ hc _ (vaddAt_mem hM hb hd)]

/-- Cancelling on the right: `a + b = b` forces `a` to be the zero vector. -/
theorem vadd_right_cancel {R add mul zero one V vadd vzero smul a b : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (ha : a ∈ V) (hb : b ∈ V)
    (h : opAt vadd a b = b) : a = vzero := by
  refine op_left_cancel hM.group hb ha hM.group.mem_e ?_
  rw [hM.group.right_id _ hb, hM.comm _ hb _ ha]
  exact h

/-! ## Linear combinations and span -/

def lincomb (vadd smul vzero : ZFSet.{u}) :
    List ZFSet.{u} → List ZFSet.{u} → ZFSet.{u}
  | c :: cs, v :: vs => opAt vadd (opAt smul c v) (lincomb vadd smul vzero cs vs)
  | _, _ => vzero

theorem lincomb_nil_left (vadd smul vzero : ZFSet.{u}) (vs : List ZFSet.{u}) :
    lincomb vadd smul vzero [] vs = vzero := by
  cases vs <;> rfl

theorem lincomb_nil_right (vadd smul vzero : ZFSet.{u}) (cs : List ZFSet.{u}) :
    lincomb vadd smul vzero cs [] = vzero := by
  cases cs <;> rfl

theorem lincomb_cons (vadd smul vzero c v : ZFSet.{u}) (cs vs : List ZFSet.{u}) :
    lincomb vadd smul vzero (c :: cs) (v :: vs)
      = opAt vadd (opAt smul c v) (lincomb vadd smul vzero cs vs) := rfl

theorem lincomb_mem {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) :
    ∀ (cs vs : List ZFSet.{u}), (∀ c, c ∈ cs → c ∈ R) → (∀ v, v ∈ vs → v ∈ V) →
      lincomb vadd smul vzero cs vs ∈ V
  | [], vs, _, _ => by
    rw [lincomb_nil_left]
    exact hM.group.mem_e
  | c :: cs, [], _, _ => by
    rw [lincomb_nil_right]
    exact hM.group.mem_e
  | c :: cs, v :: vs, hcs, hvs => by
    rw [lincomb_cons]
    exact vaddAt_mem hM (smulAt_mem hM (hcs c List.mem_cons_self) (hvs v List.mem_cons_self))
      (lincomb_mem hM cs vs (fun d hd => hcs d (List.mem_cons_of_mem _ hd))
        (fun w hw => hvs w (List.mem_cons_of_mem _ hw)))


#print axioms IsModule

/-- The span of a list of vectors. -/
def spanSet (R V vadd smul vzero : ZFSet.{u}) (vs : List ZFSet.{u}) : ZFSet.{u} :=
  sep (fun w => ∃ cs : List ZFSet.{u}, (∀ c, c ∈ cs → c ∈ R) ∧
    w = lincomb vadd smul vzero cs vs) V

theorem mem_spanSet_iff {R V vadd smul vzero : ZFSet.{u}} {vs : List ZFSet.{u}}
    {w : ZFSet.{u}} :
    w ∈ spanSet R V vadd smul vzero vs ↔ w ∈ V ∧
      ∃ cs : List ZFSet.{u}, (∀ c, c ∈ cs → c ∈ R) ∧ w = lincomb vadd smul vzero cs vs :=
  mem_sep_iff _ _ _

theorem spanSet_subset {R V vadd smul vzero : ZFSet.{u}} {vs : List ZFSet.{u}} :
    spanSet R V vadd smul vzero vs ⊆ V := fun w hw => (mem_spanSet_iff.mp hw).left

/-- Adding two linear combinations adds their coefficients. -/
theorem lincomb_add {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) :
    ∀ (cs ds vs : List ZFSet.{u}), (∀ c, c ∈ cs → c ∈ R) → (∀ c, c ∈ ds → c ∈ R) →
      (∀ v, v ∈ vs → v ∈ V) →
      ∃ es : List ZFSet.{u}, (∀ c, c ∈ es → c ∈ R) ∧
        opAt vadd (lincomb vadd smul vzero cs vs) (lincomb vadd smul vzero ds vs)
          = lincomb vadd smul vzero es vs
  | [], ds, vs, _, hds, hvs => by
    refine ⟨ds, hds, ?_⟩
    rw [lincomb_nil_left]
    exact hM.group.left_id _ (lincomb_mem hM ds vs hds hvs)
  | c :: cs, [], vs, hcs, _, hvs => by
    refine ⟨c :: cs, hcs, ?_⟩
    rw [lincomb_nil_left]
    exact hM.group.right_id _ (lincomb_mem hM (c :: cs) vs hcs hvs)
  | c :: cs, d :: ds, [], _, _, _ => by
    refine ⟨[], fun e he => absurd he List.not_mem_nil, ?_⟩
    rw [lincomb_nil_right, lincomb_nil_right, lincomb_nil_right]
    exact hM.group.right_id _ hM.group.mem_e
  | c :: cs, d :: ds, v :: vs, hcs, hds, hvs => by
    have hc : c ∈ R := hcs c List.mem_cons_self
    have hd : d ∈ R := hds d List.mem_cons_self
    have hv : v ∈ V := hvs v List.mem_cons_self
    have hcs' : ∀ e, e ∈ cs → e ∈ R := fun e he => hcs e (List.mem_cons_of_mem _ he)
    have hds' : ∀ e, e ∈ ds → e ∈ R := fun e he => hds e (List.mem_cons_of_mem _ he)
    have hvs' : ∀ w, w ∈ vs → w ∈ V := fun w hw => hvs w (List.mem_cons_of_mem _ hw)
    obtain ⟨es, hes, hese⟩ := lincomb_add hM cs ds vs hcs' hds' hvs'
    refine ⟨opAt add c d :: es, fun e he => ?_, ?_⟩
    · rcases List.mem_cons.mp he with rfl | he'
      · exact addAt_mem hM.ring hc hd
      · exact hes e he'
    · rw [lincomb_cons, lincomb_cons, lincomb_cons, hM.add_smul _ hc _ hd _ hv, ← hese,
        vadd_shuffle_pair hM (smulAt_mem hM hc hv) (lincomb_mem hM cs vs hcs' hvs')
          (smulAt_mem hM hd hv) (lincomb_mem hM ds vs hds' hvs')]

/-! ## Independence

A list of vectors is independent when the only linear combination giving the
zero vector has all coefficients zero. What that buys is injectivity: two
coefficient lists giving the same vector agree entrywise, so a span with an
independent list is equinumerous with `R^d`. -/

def IsIndep (R zero vadd smul vzero : ZFSet.{u}) (vs : List ZFSet.{u}) : Prop :=
  ∀ cs : List ZFSet.{u}, cs.length = vs.length → (∀ c, c ∈ cs → c ∈ R) →
    lincomb vadd smul vzero cs vs = vzero → ∀ c, c ∈ cs → c = zero

/-- The entries of a coefficientwise difference stay in the ring. -/
theorem zipWith_sub_mem {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    ∀ cs ds : List ZFSet.{u}, (∀ c, c ∈ cs → c ∈ R) → (∀ d, d ∈ ds → d ∈ R) →
      ∀ x, x ∈ List.zipWith (ringSub R add zero) cs ds → x ∈ R
  | [], _, _, _, x, hx => by
      rw [List.zipWith_nil_left] at hx
      exact absurd hx List.not_mem_nil
  | _ :: _, [], _, _, x, hx => by
      rw [List.zipWith_nil_right] at hx
      exact absurd hx List.not_mem_nil
  | c :: cs, d :: ds, hcm, hdm, x, hx => by
      rw [List.zipWith_cons_cons] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ringSub_mem hR (hcm c List.mem_cons_self) (hdm d List.mem_cons_self)
      · exact zipWith_sub_mem hR cs ds (fun y hy => hcm y (List.mem_cons_of_mem _ hy))
          (fun y hy => hdm y (List.mem_cons_of_mem _ hy)) x hx'

/-- A list as long as a non-empty one is itself a cons. Extracted because the
splitting step recurs in every induction that walks a coefficient list beside a
vector list. -/
theorem exists_cons_of_length {cs : List ZFSet.{u}} {k : Nat} (h : cs.length = k + 1) :
    ∃ c cs', cs = c :: cs' := by
  cases cs with
  | nil => exact absurd h (by rw [List.length_nil]; omega)
  | cons c cs' => exact ⟨c, cs', rfl⟩

/-- The coefficientwise difference of two combinations is their difference. -/
theorem lincomb_zipWith_sub {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) :
    ∀ (vs cs ds : List ZFSet.{u}), cs.length = vs.length → ds.length = vs.length →
      (∀ c, c ∈ cs → c ∈ R) → (∀ c, c ∈ ds → c ∈ R) → (∀ v, v ∈ vs → v ∈ V) →
      opAt vadd
          (lincomb vadd smul vzero (List.zipWith (ringSub R add zero) cs ds) vs)
          (lincomb vadd smul vzero ds vs)
        = lincomb vadd smul vzero cs vs
  | [], cs, ds, _, _, _, _, _ => by
      rw [lincomb_nil_right, lincomb_nil_right, lincomb_nil_right]
      exact hM.group.right_id _ hM.group.mem_e
  | v :: vs, cs, ds, hcl, hdl, hcm, hdm, hvm => by
      obtain ⟨c, cs', rfl⟩ := exists_cons_of_length (cs := cs) hcl
      obtain ⟨d, ds', rfl⟩ := exists_cons_of_length (cs := ds) hdl
      have hcR : c ∈ R := hcm c List.mem_cons_self
      have hdR : d ∈ R := hdm d List.mem_cons_self
      have hvR : v ∈ V := hvm v List.mem_cons_self
      have hcs' : ∀ x, x ∈ cs' → x ∈ R := fun x hx => hcm x (List.mem_cons_of_mem _ hx)
      have hds' : ∀ x, x ∈ ds' → x ∈ R := fun x hx => hdm x (List.mem_cons_of_mem _ hx)
      have hvs' : ∀ w, w ∈ vs → w ∈ V := fun w hw => hvm w (List.mem_cons_of_mem _ hw)
      have hzipm := zipWith_sub_mem hM.ring cs' ds' hcs' hds'
      have hIH := lincomb_zipWith_sub hM vs cs' ds'
        (by rw [List.length_cons, List.length_cons] at hcl; omega)
        (by rw [List.length_cons, List.length_cons] at hdl; omega) hcs' hds' hvs'
      show opAt vadd (lincomb vadd smul vzero
          (ringSub R add zero c d :: List.zipWith (ringSub R add zero) cs' ds') (v :: vs)) _ = _
      rw [lincomb_cons, lincomb_cons, lincomb_cons,
        vadd_shuffle_pair hM (smulAt_mem hM (ringSub_mem hM.ring hcR hdR) hvR)
          (lincomb_mem hM _ vs hzipm hvs') (smulAt_mem hM hdR hvR)
          (lincomb_mem hM ds' vs hds' hvs'),
        hIH, ← hM.add_smul _ (ringSub_mem hM.ring hcR hdR) _ hdR _ hvR,
        ringSub_def, ringAdd_assoc hM.ring hcR (ringNeg_mem hM.ring hdR) hdR,
        ringNeg_add hM.ring hdR, ringAdd_zero hM.ring hcR]

/-- The coefficientwise sum of two combinations is their sum.

The additive counterpart of `lincomb_zipWith_sub`, and the one a coordinate
argument needs: `lincomb_add` gives only that SOME coefficient list works, which
is enough to know the span is closed and not enough to say which vector the
coordinates name.

Both zip the COEFFICIENTS against a fixed vector list. -/
theorem lincomb_zipWith_add {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) :
    ∀ (cs ds vs : List ZFSet.{u}), cs.length = ds.length →
      (∀ c, c ∈ cs → c ∈ R) → (∀ c, c ∈ ds → c ∈ R) → (∀ v, v ∈ vs → v ∈ V) →
      lincomb vadd smul vzero (List.zipWith (opAt add) cs ds) vs
        = opAt vadd (lincomb vadd smul vzero cs vs) (lincomb vadd smul vzero ds vs)
  | [], [], vs, _, _, _, _ => by
    rw [List.zipWith_nil_left, lincomb_nil_left]
    exact (hM.group.left_id _ hM.group.mem_e).symm
  | c :: cs, d :: ds, [], _, _, _, _ => by
    rw [lincomb_nil_right, lincomb_nil_right, lincomb_nil_right]
    exact (hM.group.left_id _ hM.group.mem_e).symm
  | c :: cs, d :: ds, v :: vs, hlen, hcs, hds, hvs => by
    have hc : c ∈ R := hcs c List.mem_cons_self
    have hd : d ∈ R := hds d List.mem_cons_self
    have hv : v ∈ V := hvs v List.mem_cons_self
    have hL : lincomb vadd smul vzero cs vs ∈ V :=
      lincomb_mem hM _ _ (fun a ha => hcs a (List.mem_cons_of_mem _ ha))
        (fun b hb => hvs b (List.mem_cons_of_mem _ hb))
    have hL' : lincomb vadd smul vzero ds vs ∈ V :=
      lincomb_mem hM _ _ (fun a ha => hds a (List.mem_cons_of_mem _ ha))
        (fun b hb => hvs b (List.mem_cons_of_mem _ hb))
    rw [List.zipWith_cons_cons, lincomb_cons, lincomb_cons, lincomb_cons,
      hM.add_smul _ hc _ hd _ hv,
      lincomb_zipWith_add hM cs ds vs (by simpa using hlen)
        (fun a ha => hcs a (List.mem_cons_of_mem _ ha))
        (fun a ha => hds a (List.mem_cons_of_mem _ ha))
        (fun b hb => hvs b (List.mem_cons_of_mem _ hb)),
      opAt_interchange hM.group hM.comm
        (smulAt_mem hM hc hv) (smulAt_mem hM hd hv) hL hL']

/-- Independence gives injectivity. Two coefficient lists of the right
length giving the same vector agree entrywise. -/
theorem lincomb_injective {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) {vs : List ZFSet.{u}}
    (hvm : ∀ v, v ∈ vs → v ∈ V) (hindep : IsIndep R zero vadd smul vzero vs) :
    ∀ cs ds : List ZFSet.{u}, cs.length = vs.length → ds.length = vs.length →
      (∀ c, c ∈ cs → c ∈ R) → (∀ c, c ∈ ds → c ∈ R) →
      lincomb vadd smul vzero cs vs = lincomb vadd smul vzero ds vs → cs = ds := by
  intro cs ds hcl hdl hcm hdm heq
  have hzipm := zipWith_sub_mem hM.ring cs ds hcm hdm
  have hzero : lincomb vadd smul vzero (List.zipWith (ringSub R add zero) cs ds) vs = vzero := by
    refine vadd_right_cancel hM (lincomb_mem hM _ vs hzipm hvm)
      (lincomb_mem hM ds vs hdm hvm) ?_
    rw [lincomb_zipWith_sub hM vs cs ds hcl hdl hcm hdm hvm]
    exact heq
  have hlen : (List.zipWith (ringSub R add zero) cs ds).length = vs.length := by
    rw [List.length_zipWith, hcl, hdl, Nat.min_self]
  have hall := hindep _ hlen hzipm hzero
  clear heq hzero hlen hzipm hindep
  induction cs generalizing ds vs with
  | nil =>
    cases ds with
    | nil => rfl
    | cons d ds' =>
      exact absurd (hdl.trans hcl.symm) (by rw [List.length_nil, List.length_cons]; omega)
  | cons c cs' ih =>
    cases ds with
    | nil => exact absurd (hdl.trans hcl.symm) (by rw [List.length_nil, List.length_cons]; omega)
    | cons d ds' =>
      have hcd : c = d := by
        have := hall (ringSub R add zero c d) (by
          rw [List.zipWith_cons_cons]
          exact List.mem_cons_self)
        exact (ringSub_eq_zero_iff hM.ring (hcm c List.mem_cons_self)
          (hdm d List.mem_cons_self)).mp this
      cases vs with
      | nil => exact absurd hcl (by rw [List.length_nil, List.length_cons]; omega)
      | cons v vs' =>
        rw [hcd, ih (vs := vs') (ds := ds') (fun w hw => hvm w (List.mem_cons_of_mem _ hw))
          (by rw [List.length_cons, List.length_cons] at hcl; omega)
          (by rw [List.length_cons, List.length_cons] at hdl; omega)
          (fun x hx => hcm x (List.mem_cons_of_mem _ hx))
          (fun x hx => hdm x (List.mem_cons_of_mem _ hx))
          (fun x hx => hall x (by rw [List.zipWith_cons_cons]; exact List.mem_cons_of_mem _ hx))]

/-! ## Counting a span

An independent list of length `d` puts the span in bijection with `R^d`: the
coefficients of a vector are unique and every tuple gives one. Coefficient lists
that are too short or too long are normalised first -- `lincomb` ignores
coefficients past the end of the vector list, and pads the missing ones with
zero. -/

def tupleToList (t : ZFSet.{u}) (d : Nat) : List ZFSet.{u} :=
  (List.range d).map (tupleCoeff t d)

theorem tupleToList_length (t : ZFSet.{u}) (d : Nat) : (tupleToList t d).length = d := by
  rw [tupleToList, List.length_map, List.length_range]

theorem tupleToList_getElem (t : ZFSet.{u}) (d i : Nat) (hi : i < (tupleToList t d).length) :
    (tupleToList t d)[i] = tupleCoeff t d i := by
  show ((List.range d).map (tupleCoeff t d))[i]'hi = _
  rw [List.getElem_map, List.getElem_range]

theorem tupleToList_mem {R : ZFSet.{u}} {d : Nat} {t : ZFSet.{u}} (ht : t ∈ powSet R d) :
    ∀ x, x ∈ tupleToList t d → x ∈ R := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact tupleCoeff_mem d t ht i (List.mem_range.mp hi)

theorem tupleToList_inj {R : ZFSet.{u}} {d : Nat} {t t' : ZFSet.{u}} (ht : t ∈ powSet R d)
    (ht' : t' ∈ powSet R d) (h : tupleToList t d = tupleToList t' d) : t = t' := by
  refine powSet_ext d t t' ht ht' (fun i hi => ?_)
  have hlen : i < (tupleToList t d).length := by rw [tupleToList_length]; exact hi
  have hlen' : i < (tupleToList t' d).length := by rw [tupleToList_length]; exact hi
  rw [← tupleToList_getElem t d i hlen, ← tupleToList_getElem t' d i hlen']
  exact List.getElem_of_eq h hlen

/-- Every coefficient list of the right length comes from a tuple. -/
theorem exists_tuple_of_list {R : ZFSet.{u}} {d : Nat} (cs : List ZFSet.{u})
    (hlen : cs.length = d) (hcm : ∀ c, c ∈ cs → c ∈ R) :
    ∃ t, t ∈ powSet R d ∧ tupleToList t d = cs := by
  refine ⟨tupleOf (fun i => cs.getD i empty.{u}) d, tupleOf_mem d (fun i hi => ?_), ?_⟩
  · rw [List.getD, List.getElem?_eq_getElem (show i < cs.length by omega)]
    exact hcm _ (List.getElem_mem _)
  · refine List.ext_getElem (by rw [tupleToList_length, hlen]) (fun i h₁ h₂ => ?_)
    rw [tupleToList_getElem _ d i h₁,
      tupleCoeff_tupleOf d i (by rw [tupleToList_length] at h₁; exact h₁),
      List.getD, List.getElem?_eq_getElem h₂]
    rfl

theorem lincomb_zeros {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) :
    ∀ (k : Nat) (vs : List ZFSet.{u}), (∀ v, v ∈ vs → v ∈ V) →
      lincomb vadd smul vzero (List.replicate k zero) vs = vzero
  | 0, vs, _ => by rw [List.replicate_zero, lincomb_nil_left]
  | k + 1, [], _ => by rw [lincomb_nil_right]
  | k + 1, v :: vs, hvm => by
    rw [List.replicate_succ, lincomb_cons,
      lincomb_zeros hM k vs (fun w hw => hvm w (List.mem_cons_of_mem _ hw)),
      zero_smul hM (hvm v List.mem_cons_self)]
    exact hM.group.right_id _ hM.group.mem_e

theorem lincomb_append_zeros {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) :
    ∀ (cs : List ZFSet.{u}) (k : Nat) (vs : List ZFSet.{u}),
      (∀ c, c ∈ cs → c ∈ R) → (∀ v, v ∈ vs → v ∈ V) →
      lincomb vadd smul vzero (cs ++ List.replicate k zero) vs
        = lincomb vadd smul vzero cs vs
  | [], k, vs, _, hvm => by
    rw [List.nil_append, lincomb_nil_left, lincomb_zeros hM k vs hvm]
  | c :: cs, k, [], _, _ => by rw [lincomb_nil_right, lincomb_nil_right]
  | c :: cs, k, v :: vs, hcm, hvm => by
    rw [List.cons_append, lincomb_cons, lincomb_cons,
      lincomb_append_zeros hM cs k vs (fun x hx => hcm x (List.mem_cons_of_mem _ hx))
        (fun w hw => hvm w (List.mem_cons_of_mem _ hw))]

theorem lincomb_take (vadd smul vzero : ZFSet.{u}) :
    ∀ (vs cs : List ZFSet.{u}),
      lincomb vadd smul vzero (cs.take vs.length) vs = lincomb vadd smul vzero cs vs
  | [], cs => by rw [lincomb_nil_right, lincomb_nil_right]
  | v :: vs, [] => by rw [List.take_nil]
  | v :: vs, c :: cs => by
    rw [List.length_cons, List.take_succ_cons, lincomb_cons, lincomb_cons,
      lincomb_take vadd smul vzero vs cs]

/-- Normalise a coefficient list to the length of the vector list. -/
def padTo (cs : List ZFSet.{u}) (zero : ZFSet.{u}) (d : Nat) : List ZFSet.{u} :=
  cs.take d ++ List.replicate (d - cs.length) zero

theorem padTo_length (cs : List ZFSet.{u}) (zero : ZFSet.{u}) (d : Nat) :
    (padTo cs zero d).length = d := by
  rw [padTo, List.length_append, List.length_take, List.length_replicate]
  omega

theorem padTo_mem {R : ZFSet.{u}} {cs : List ZFSet.{u}} {zero : ZFSet.{u}} (hz : zero ∈ R)
    (hcm : ∀ c, c ∈ cs → c ∈ R) (d : Nat) : ∀ x, x ∈ padTo cs zero d → x ∈ R := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact hcm x (List.mem_of_mem_take h)
  · rw [List.eq_of_mem_replicate h]
    exact hz

theorem lincomb_padTo {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (cs vs : List ZFSet.{u})
    (hcm : ∀ c, c ∈ cs → c ∈ R) (hvm : ∀ v, v ∈ vs → v ∈ V) :
    lincomb vadd smul vzero (padTo cs zero vs.length) vs = lincomb vadd smul vzero cs vs := by
  rw [padTo, lincomb_append_zeros hM _ _ vs (fun x hx => hcm x (List.mem_of_mem_take hx)) hvm,
    lincomb_take vadd smul vzero vs cs]

/-- The span of an independent list of length `d` is a copy of `R^d`. -/
theorem equinumerous_spanSet {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) {vs : List ZFSet.{u}}
    (hvm : ∀ v, v ∈ vs → v ∈ V) (hindep : IsIndep R zero vadd smul vzero vs) :
    Equinumerous (powSet R vs.length) (spanSet R V vadd smul vzero vs) := by
  have hval : ∀ t, t ∈ powSet R vs.length →
      lincomb vadd smul vzero (tupleToList t vs.length) vs ∈ spanSet R V vadd smul vzero vs := by
    intro t ht
    exact mem_spanSet_iff.mpr ⟨lincomb_mem hM _ vs (tupleToList_mem ht) hvm,
      tupleToList t vs.length, tupleToList_mem ht, rfl⟩
  refine ⟨graphOn (powSet R vs.length) (spanSet R V vadd smul vzero vs)
      (fun t => lincomb vadd smul vzero (tupleToList t vs.length) vs),
    ⟨graphOn_isFunction _ _ _, graphOn_domain hval, graphOn_range, ?_⟩,
    ⟨graphOn_isFunction _ _ _, graphOn_domain hval, graphOn_range, ?_⟩⟩
  · intro a ha b hb hab
    rw [app_graphOn hval ha, app_graphOn hval hb] at hab
    exact tupleToList_inj ha hb (lincomb_injective hM hvm hindep _ _
      (tupleToList_length a _) (tupleToList_length b _) (tupleToList_mem ha)
      (tupleToList_mem hb) hab)
  · intro w hw
    obtain ⟨hwm, cs, hcm, rfl⟩ := mem_spanSet_iff.mp hw
    obtain ⟨t, ht, hte⟩ := exists_tuple_of_list (R := R) (padTo cs zero vs.length)
      (padTo_length cs zero vs.length) (padTo_mem hM.ring.addGroup.mem_e hcm vs.length)
    refine ⟨t, ht, ?_⟩
    rw [app_graphOn hval ht, hte, lincomb_padTo hM cs vs hcm hvm]

/-- A span has `q^d` elements: `d` independent vectors over a ring with `q`
elements. -/
theorem equinumerous_spanSet_card {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) {q : Nat}
    (hRfin : Equinumerous R (ofNat.{u} q)) {vs : List ZFSet.{u}} (hvm : ∀ v, v ∈ vs → v ∈ V)
    (hindep : IsIndep R zero vadd smul vzero vs) :
    Equinumerous (spanSet R V vadd smul vzero vs) (ofNat.{u} (q ^ vs.length)) :=
  equinumerous_trans (equinumerous_symm (equinumerous_spanSet hM hvm hindep))
    (equinumerous_powSet hRfin vs.length)

/-! ## Extending an independent list

Over a field, a vector outside the span can be prepended and independence
survives: a combination using it with a non-zero coefficient could be solved for
it. That is the step of the greedy construction below. -/

theorem smul_vzero {R add mul zero one V vadd vzero smul c : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (hc : c ∈ R) :
    opAt smul c vzero = vzero := by
  have hcz := smulAt_mem hM hc hM.group.mem_e
  have h := hM.smul_add _ hc _ hM.group.mem_e _ hM.group.mem_e
  rw [hM.group.left_id _ hM.group.mem_e] at h
  exact vadd_right_cancel hM hcz hcz h.symm

theorem ginv_vzero {G op e : ZFSet.{u}} (hG : IsGroup G op e) : ginv G op e e = e := by
  have h := opAt_ginv hG hG.mem_e
  rw [hG.right_id _ (ginv_mem hG hG.mem_e)] at h
  exact h

theorem lincomb_smul {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) {b : ZFSet.{u}} (hb : b ∈ R) :
    ∀ (cs vs : List ZFSet.{u}), (∀ c, c ∈ cs → c ∈ R) → (∀ v, v ∈ vs → v ∈ V) →
      opAt smul b (lincomb vadd smul vzero cs vs)
        = lincomb vadd smul vzero (cs.map (opAt mul b)) vs
  | [], vs, _, _ => by
    rw [lincomb_nil_left, List.map_nil, lincomb_nil_left, smul_vzero hM hb]
  | c :: cs, [], _, _ => by
    rw [lincomb_nil_right, lincomb_nil_right, smul_vzero hM hb]
  | c :: cs, v :: vs, hcm, hvm => by
    have hc := hcm c List.mem_cons_self
    have hv := hvm v List.mem_cons_self
    have hcs' : ∀ x, x ∈ cs → x ∈ R := fun x hx => hcm x (List.mem_cons_of_mem _ hx)
    have hvs' : ∀ w, w ∈ vs → w ∈ V := fun w hw => hvm w (List.mem_cons_of_mem _ hw)
    rw [lincomb_cons, List.map_cons, lincomb_cons,
      hM.smul_add _ hb _ (smulAt_mem hM hc hv) _ (lincomb_mem hM cs vs hcs' hvs'),
      hM.smul_smul _ hb _ hc _ hv, lincomb_smul hM hb cs vs hcs' hvs']

/-- Negating every coefficient inverts the combination. -/
theorem lincomb_ginv {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) :
    ∀ (cs vs : List ZFSet.{u}), (∀ c, c ∈ cs → c ∈ R) → (∀ v, v ∈ vs → v ∈ V) →
      ginv V vadd vzero (lincomb vadd smul vzero cs vs)
        = lincomb vadd smul vzero (cs.map (ringNeg R add zero)) vs
  | [], vs, _, _ => by
    rw [lincomb_nil_left, List.map_nil, lincomb_nil_left, ginv_vzero hM.group]
  | c :: cs, [], _, _ => by
    rw [lincomb_nil_right, lincomb_nil_right, ginv_vzero hM.group]
  | c :: cs, v :: vs, hcm, hvm => by
    have hc := hcm c List.mem_cons_self
    have hv := hvm v List.mem_cons_self
    have hcs' : ∀ x, x ∈ cs → x ∈ R := fun x hx => hcm x (List.mem_cons_of_mem _ hx)
    have hvs' : ∀ w, w ∈ vs → w ∈ V := fun w hw => hvm w (List.mem_cons_of_mem _ hw)
    have hcv := smulAt_mem hM hc hv
    have hL := lincomb_mem hM cs vs hcs' hvs'
    have hnc := smulAt_mem hM (ringNeg_mem hM.ring hc) hv
    have hiL := ginv_mem hM.group hL
    have hsum := vaddAt_mem hM hcv hL
    rw [lincomb_cons, List.map_cons, lincomb_cons, ← lincomb_ginv hM cs vs hcs' hvs']
    refine inv_unique hM.group hsum (ginv_mem hM.group hsum) (vaddAt_mem hM hnc hiL) ?_ ?_
    · rw [hM.comm _ hsum _ (ginv_mem hM.group hsum)]
      exact opAt_ginv hM.group hsum
    · rw [vadd_shuffle_pair hM hnc hiL hcv hL,
        ← hM.add_smul _ (ringNeg_mem hM.ring hc) _ hc _ hv, ringNeg_add hM.ring hc,
        zero_smul hM hv, opAt_ginv hM.group hL, hM.group.left_id _ hM.group.mem_e]

/-- A vector outside the span extends an independent list. -/
theorem isIndep_cons {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (hF : IsField R add mul zero one)
    (hstab : StableVanishing R zero) {w : ZFSet.{u}} (hw : w ∈ V) {vs : List ZFSet.{u}}
    (hvm : ∀ v, v ∈ vs → v ∈ V) (hindep : IsIndep R zero vadd smul vzero vs)
    (hnot : w ∉ spanSet R V vadd smul vzero vs) :
    IsIndep R zero vadd smul vzero (w :: vs) := by
  intro cs hlen hcm hcomb
  obtain ⟨c, cs', rfl⟩ := exists_cons_of_length (cs := cs) hlen
  have hc := hcm c List.mem_cons_self
  have hcs' : ∀ x, x ∈ cs' → x ∈ R := fun x hx => hcm x (List.mem_cons_of_mem _ hx)
  have hL := lincomb_mem hM cs' vs hcs' hvm
  rw [lincomb_cons] at hcomb
  have hczero : c = zero := by
    refine hstab c hc ?_
    intro hne
    -- solving for `w` would put it in the span; the goal is already `False`,
    -- so the branch that refutes IS the proof stability asks for
    obtain ⟨b, hb, hbc⟩ := hF.inverses c hc hne
    have hcw : opAt smul c w = ginv V vadd vzero (lincomb vadd smul vzero cs' vs) :=
      inv_unique hM.group hL (smulAt_mem hM hc hw) (ginv_mem hM.group hL)
        (hM.comm _ hL _ (smulAt_mem hM hc hw) ▸ hcomb) (opAt_ginv hM.group hL)
    have hwe : w = lincomb vadd smul vzero
        ((cs'.map (ringNeg R add zero)).map (opAt mul b)) vs := by
      rw [← lincomb_smul hM hb _ vs (mem_map_of_maps _ (fun y hy => ringNeg_mem hM.ring (hcs' y hy))) hvm,
        ← lincomb_ginv hM cs' vs hcs' hvm, ← hcw, ← hM.smul_smul _ hb _ hc _ hw,
        hM.ring.mulComm _ hb _ hc, hbc, hM.one_smul _ hw]
    exact hnot (mem_spanSet_iff.mpr ⟨hw, _, fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      exact mulAt_mem hM.ring hb (ringNeg_mem hM.ring (hcs' z hz)), hwe⟩)
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact hczero
  · refine hindep cs' (by rw [List.length_cons, List.length_cons] at hlen; omega) hcs' ?_ x hx'
    rw [hczero, zero_smul hM hw, hM.group.left_id _ hL] at hcomb
    exact hcomb

/-! ## A basis, greedily

Over a finite field, a finite module has a basis: start from the empty list and
keep adding a vector from outside the current span. The span grows by a factor
of `q` each time, so the process stops, and it stops only when the span is
everything. -/

theorem isIndep_nil (R zero vadd smul vzero : ZFSet.{u}) :
    IsIndep R zero vadd smul vzero [] := by
  intro cs hlen _ _ x hx
  rw [List.length_nil] at hlen
  rw [List.eq_nil_of_length_eq_zero hlen] at hx
  exact absurd hx List.not_mem_nil

/-- A ring with `zero ≠ one` has at least two elements. Inverses play no
part: the two elements are `zero` and `one` themselves, and non-triviality is
exactly what keeps them apart.

The name is wider than the hypothesis: it says `of_isField`, and a ring
suffices. -/
theorem two_le_card_of_isField {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hne : zero ≠ one)
    {q : Nat} (hRfin : Equinumerous R (ofNat.{u} q)) :
    2 ≤ q := by
  have hsingle : Equinumerous (singleton zero) (ofNat.{u} 1) :=
    equinumerous_singleton_one
  have hpair := equinumerous_insert hsingle
    (fun hmem => hne ((mem_singleton_iff one zero).mp hmem).symm)
  have hsub : singleton zero ∪ singleton one ⊆ R := by
    intro a ha
    rcases (mem_union_iff a _ _).mp ha with h | h
    · rw [(mem_singleton_iff _ _).mp h]
      exact hR.addGroup.mem_e
    · rw [(mem_singleton_iff _ _).mp h]
      exact hR.mem_one
  exact dominates_ofNat_le 2 q (dominates_trans (dominates_of_equinumerous
    (equinumerous_symm hpair)) (dominates_ofNat_of_subset hsub hRfin))

/-- Either the span is everything, or something is outside it. -/
theorem spanSet_eq_or_exists_outside {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) {q m : Nat}
    (hRfin : Equinumerous R (ofNat.{u} q)) (hVfin : Equinumerous V (ofNat.{u} m))
    {vs : List ZFSet.{u}} (hvm : ∀ v, v ∈ vs → v ∈ V)
    (hindep : IsIndep R zero vadd smul vzero vs) :
    spanSet R V vadd smul vzero vs = V ∨
      ∃ w, w ∈ V ∧ w ∉ spanSet R V vadd smul vzero vs := by
  have hspan := equinumerous_spanSet_card hM hRfin hvm hindep
  have hdec : ∀ w, w ∈ V → w ∈ spanSet R V vadd smul vzero vs ∨
      w ∉ spanSet R V vadd smul vzero vs :=
    fun w hw => mem_or_not_mem_of_subset hVfin hspan spanSet_subset hw
  rcases exists_or_not_of_finite (P := fun w => w ∉ spanSet R V vadd smul vzero vs) m V hVfin
    (fun a ha => (hdec a ha).elim (fun h => Or.inr (fun hn => hn h)) Or.inl) with ⟨w, hw, hno⟩ | hall
  · exact Or.inr ⟨w, hw, hno⟩
  · refine Or.inl (ext _ _ (fun a => ⟨fun ha => spanSet_subset a ha, fun ha => ?_⟩))
    rcases hdec a ha with h | h
    · exact h
    · exact absurd ⟨a, ha, h⟩ hall

/-- One vector outside the span multiplies the count by at least `q`. -/
private theorem card_succ_le_of_outside {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) {q m : Nat}
    (hRfin : Equinumerous R (ofNat.{u} q)) (hVfin : Equinumerous V (ofNat.{u} m))
    {vs : List ZFSet.{u}} (hvm : ∀ v, v ∈ vs → v ∈ V)
    (hindep : IsIndep R zero vadd smul vzero vs) {w : ZFSet.{u}} (hw : w ∈ V)
    (hno : w ∉ spanSet R V vadd smul vzero vs) : q ^ vs.length + 1 ≤ m := by
  have hspan := equinumerous_spanSet_card hM hRfin hvm hindep
  have hins := equinumerous_insert hspan hno
  refine dominates_ofNat_le _ m (dominates_trans (dominates_of_equinumerous
    (equinumerous_symm hins)) (dominates_ofNat_of_subset (fun a ha => ?_) hVfin))
  rcases (mem_union_iff a _ _).mp ha with h | h
  · exact spanSet_subset a h
  · rw [(mem_singleton_iff _ _).mp h]
    exact hw

/-- Every finite module over a finite field has a basis. -/
theorem exists_basis {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (hF : IsField R add mul zero one)
    {q m : Nat} (hRfin : Equinumerous R (ofNat.{u} q)) (hVfin : Equinumerous V (ofNat.{u} m)) :
    ∃ vs : List ZFSet.{u}, (∀ v, v ∈ vs → v ∈ V) ∧ IsIndep R zero vadd smul vzero vs ∧
      spanSet R V vadd smul vzero vs = V := by
  have hdec := decidableVanishing_of_finite hRfin hF.ring.addGroup.mem_e
  have hq := two_le_card_of_isField hF.ring hF.zero_ne_one hRfin
  have key : ∀ k : Nat, ∀ vs : List ZFSet.{u}, (∀ v, v ∈ vs → v ∈ V) →
      IsIndep R zero vadd smul vzero vs → m ≤ q ^ vs.length + k →
      ∃ us : List ZFSet.{u}, (∀ v, v ∈ us → v ∈ V) ∧ IsIndep R zero vadd smul vzero us ∧
        spanSet R V vadd smul vzero us = V := by
    intro k
    induction k with
    | zero =>
      intro vs hvm hindep hbound
      rcases spanSet_eq_or_exists_outside hM hRfin hVfin hvm hindep with h | ⟨w, hw, hno⟩
      · exact ⟨vs, hvm, hindep, h⟩
      · exact absurd (card_succ_le_of_outside hM hRfin hVfin hvm hindep hw hno) (by omega)
    | succ k ih =>
      intro vs hvm hindep hbound
      rcases spanSet_eq_or_exists_outside hM hRfin hVfin hvm hindep with h | ⟨w, hw, hno⟩
      · exact ⟨vs, hvm, hindep, h⟩
      · have hgrow : q ^ vs.length + q ^ vs.length ≤ q ^ (w :: vs).length := by
          rw [List.length_cons, Nat.pow_succ]
          have h1 : 1 ≤ q ^ vs.length := Nat.pow_pos (by omega)
          calc q ^ vs.length + q ^ vs.length = q ^ vs.length * 2 := by omega
            _ ≤ q ^ vs.length * q := Nat.mul_le_mul_left _ hq
        have hpos : 1 ≤ q ^ vs.length := Nat.pow_pos (by omega)
        refine ih (w :: vs) (fun v hv => ?_)
          (isIndep_cons hM hF (stableVanishing_of_decidableVanishing hdec) hw hvm hindep hno) (by omega)
        rcases List.mem_cons.mp hv with rfl | hv'
        · exact hw
        · exact hvm v hv'
  exact key m [] (fun v hv => absurd hv List.not_mem_nil) (isIndep_nil _ _ _ _ _)
    (by rw [List.length_nil, Nat.pow_zero]; omega)

/-! ## Submodules

A subset closed under the operations, with the restricted action. Inverses come
free: `(-1)·a` is the inverse of `a`, so closure under scaling gives closure
under negation. -/

structure IsSubmodule (S R V vadd vzero smul : ZFSet.{u}) : Prop where
  sub : S ⊆ V
  mem_zero : vzero ∈ S
  add_closed : ∀ a, a ∈ S → ∀ b, b ∈ S → opAt vadd a b ∈ S
  smul_closed : ∀ c, c ∈ R → ∀ a, a ∈ S → opAt smul c a ∈ S

/-! ## Linear functionals, sublinear bounds, and the extension problem

THE ORDER IS A PARAMETER rather than fixed to the reals. Mathlib's
`exists_extension_of_le_sublinear` is stated for `ℝ`; carrying `le` covers that
case and any other ordered scalar ring. -/

/-- Scaling by `-1` inverts. -/
theorem neg_one_smul {R add mul zero one V vadd vzero smul a : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (ha : a ∈ V) :
    opAt smul (ringNeg R add zero one) a = ginv V vadd vzero a := by
  have hn := ringNeg_mem hM.ring hM.ring.mem_one
  refine inv_unique hM.group ha (smulAt_mem hM hn ha) (ginv_mem hM.group ha) ?_
    (opAt_ginv hM.group ha)
  have hsum : opAt vadd (opAt smul one a) (opAt smul (ringNeg R add zero one) a) = vzero := by
    rw [← hM.add_smul _ hM.ring.mem_one _ hn _ ha, ringAdd_neg hM.ring hM.ring.mem_one,
      zero_smul hM ha]
  exact (congrArg (fun z => opAt vadd z (opAt smul (ringNeg R add zero one) a))
    (hM.one_smul _ ha).symm).trans hsum

/-! ## Differences, and the quotient by a submodule

`idealRel R add zero I` (`Ring.lean`) is named for ideals but DEFINED as
`a - b in I` over an additive group and a subset, so it is already the right
relation for a module. What is not available is its congruence property:
`isCongruence_idealRel_add` demands `IsRingNC R add mul zero one`, and a
module's `V` has no multiplication to offer.

That hypothesis is spare rather than used. `ringSub_trans_nc`'s own docstring
says as much --- every step is a group fact --- so the three subtraction facts
are restated here over `IsGroup`. The ring versions are left untouched.
-/

theorem isModule_submodule {S R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul)
    (hS : IsSubmodule S R V vadd vzero smul) :
    IsModule R add mul zero one S (restrictOp vadd S) vzero (restrictLeft smul R S) := by
  have hdomV : ∀ x, x ∈ prod S S → x ∈ domain vadd := fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff x _ _).mp hx
    rw [hM.group.dom]
    exact opair_mem_prod (hS.sub _ ha) (hS.sub _ hb)
  have hdomS : ∀ x, x ∈ prod R S → x ∈ domain smul := fun x hx => by
    obtain ⟨c, hc, a, ha, rfl⟩ := (mem_prod_iff x _ _).mp hx
    rw [hM.smulDom]
    exact opair_mem_prod hc (hS.sub _ ha)
  have hA : ∀ {a b : ZFSet.{u}}, a ∈ S → b ∈ S → opAt (restrictOp vadd S) a b = opAt vadd a b :=
    fun ha hb => opAt_restrictOp hM.group.isFun hdomV hS.add_closed ha hb
  have hSm : ∀ {c a : ZFSet.{u}}, c ∈ R → a ∈ S →
      opAt (restrictLeft smul R S) c a = opAt smul c a :=
    fun hc ha => opAt_restrictLeft hM.smulFun hdomS hS.smul_closed hc ha
  have hginv : ∀ a, a ∈ S → ginv V vadd vzero a ∈ S := by
    intro a ha
    rw [← neg_one_smul hM (hS.sub _ ha)]
    exact hS.smul_closed _ (ringNeg_mem hM.ring hM.ring.mem_one) a ha
  refine ⟨hM.ring, ⟨⟨isFunction_restrictOp hM.group.isFun,
      restrictOp_domain hM.group.isFun hdomV hS.add_closed, restrictOp_range,
      hS.mem_zero, ?_, ?_, ?_⟩, ?_⟩, ?_, isFunction_restrictLeft hM.smulFun,
    restrictLeft_domain hM.smulFun hdomS hS.smul_closed, restrictLeft_range, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb c hc
    rw [hA ha hb, hA (hS.add_closed a ha b hb) hc, hA hb hc, hA ha (hS.add_closed b hb c hc)]
    exact hM.group.assoc _ (hS.sub _ ha) _ (hS.sub _ hb) _ (hS.sub _ hc)
  · intro a ha
    rw [hA hS.mem_zero ha]
    exact hM.group.left_id _ (hS.sub _ ha)
  · intro a ha
    rw [hA ha hS.mem_zero]
    exact hM.group.right_id _ (hS.sub _ ha)
  · intro a ha
    refine ⟨ginv V vadd vzero a, hginv a ha, ?_, ?_⟩
    · rw [hA ha (hginv a ha), hM.comm _ (hS.sub _ ha) _ (ginv_mem hM.group (hS.sub _ ha))]
      exact opAt_ginv hM.group (hS.sub _ ha)
    · rw [hA (hginv a ha) ha]
      exact opAt_ginv hM.group (hS.sub _ ha)
  · intro a ha b hb
    rw [hA ha hb, hA hb ha]
    exact hM.comm _ (hS.sub _ ha) _ (hS.sub _ hb)
  · intro c hc x hx y hy
    rw [hA hx hy, hSm hc (hS.add_closed x hx y hy), hSm hc hx, hSm hc hy,
      hA (hS.smul_closed c hc x hx) (hS.smul_closed c hc y hy)]
    exact hM.smul_add _ hc _ (hS.sub _ hx) _ (hS.sub _ hy)
  · intro c hc d hd x hx
    rw [hSm (addAt_mem hM.ring hc hd) hx, hSm hc hx, hSm hd hx,
      hA (hS.smul_closed c hc x hx) (hS.smul_closed d hd x hx)]
    exact hM.add_smul _ hc _ hd _ (hS.sub _ hx)
  · intro c hc d hd x hx
    rw [hSm (mulAt_mem hM.ring hc hd) hx, hSm hd hx, hSm hc (hS.smul_closed d hd x hx)]
    exact hM.smul_smul _ hc _ hd _ (hS.sub _ hx)
  · intro x hx
    rw [hSm hM.ring.mem_one hx]
    exact hM.one_smul _ (hS.sub _ hx)

/-! ## Combinations over pairs

`List.Perm` relates two lists, not two pairs of lists, so a permutation cannot
carry a coefficient list alongside the vectors. Zipping fixes that: a combination
over a list of `(coefficient, vector)` pairs is invariant under permutation, and
commutativity is all the proof needs. -/

def lincombP (vadd smul vzero : ZFSet.{u}) : List (ZFSet.{u} × ZFSet.{u}) → ZFSet.{u}
  | [] => vzero
  | p :: ps => opAt vadd (opAt smul p.1 p.2) (lincombP vadd smul vzero ps)

theorem lincombP_mem {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) :
    ∀ ps : List (ZFSet.{u} × ZFSet.{u}), (∀ p, p ∈ ps → p.1 ∈ R ∧ p.2 ∈ V) →
      lincombP vadd smul vzero ps ∈ V
  | [], _ => hM.group.mem_e
  | p :: ps, hps => by
    refine vaddAt_mem hM (smulAt_mem hM (hps p List.mem_cons_self).left
      (hps p List.mem_cons_self).right) ?_
    exact lincombP_mem hM ps (fun q hq => hps q (List.mem_cons_of_mem _ hq))

/-- A combination over pairs does not depend on the order. -/
theorem lincombP_perm {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul)
    {ps qs : List (ZFSet.{u} × ZFSet.{u})} (h : ps.Perm qs) :
    (∀ p, p ∈ ps → p.1 ∈ R ∧ p.2 ∈ V) →
      lincombP vadd smul vzero ps = lincombP vadd smul vzero qs := by
  induction h with
  | nil => intro _; rfl
  | cons p _ ih =>
    intro hmem
    show opAt vadd (opAt smul p.1 p.2) _ = opAt vadd (opAt smul p.1 p.2) _
    rw [ih (fun q hq => hmem q (List.mem_cons_of_mem _ hq))]
  | swap p q rest =>
    intro hmem
    have hp := hmem p (List.mem_cons_of_mem _ List.mem_cons_self)
    have hq := hmem q List.mem_cons_self
    have hrest : lincombP vadd smul vzero rest ∈ V :=
      lincombP_mem hM rest (fun r hr => hmem r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
    show opAt vadd (opAt smul q.1 q.2) (opAt vadd (opAt smul p.1 p.2) _)
      = opAt vadd (opAt smul p.1 p.2) (opAt vadd (opAt smul q.1 q.2) _)
    rw [← hM.group.assoc _ (smulAt_mem hM hq.left hq.right) _
        (smulAt_mem hM hp.left hp.right) _ hrest,
      hM.comm _ (smulAt_mem hM hq.left hq.right) _ (smulAt_mem hM hp.left hp.right),
      hM.group.assoc _ (smulAt_mem hM hp.left hp.right) _
        (smulAt_mem hM hq.left hq.right) _ hrest]
  | trans h₁ h₂ ih₁ ih₂ =>
    intro hmem
    rw [ih₁ hmem, ih₂ (fun q hq => hmem q (h₁.mem_iff.mpr hq))]

theorem lincomb_eq_lincombP (vadd smul vzero : ZFSet.{u}) :
    ∀ cs vs : List ZFSet.{u},
      lincomb vadd smul vzero cs vs = lincombP vadd smul vzero (cs.zip vs)
  | [], vs => by
    rw [lincomb_nil_left]
    cases vs <;> rfl
  | c :: cs, [] => by rw [lincomb_nil_right]; rfl
  | c :: cs, v :: vs => by
    rw [lincomb_cons, List.zip_cons_cons, lincomb_eq_lincombP vadd smul vzero cs vs]
    rfl

/-- A permutation of the vectors transports a coefficient list. -/
theorem perm_zip_exists : ∀ {vs ws : List ZFSet.{u}}, vs.Perm ws →
    ∀ ds : List ZFSet.{u}, ds.length = ws.length →
      ∃ cs : List ZFSet.{u}, cs.length = vs.length ∧ (cs.zip vs).Perm (ds.zip ws) := by
  intro vs ws h
  induction h with
  | nil =>
    intro ds hd
    obtain rfl : ds = [] := by
      cases ds with
      | nil => rfl
      | cons d ds' => exact absurd hd (by rw [List.length_cons, List.length_nil]; omega)
    exact ⟨[], rfl, List.Perm.refl _⟩
  | @cons v l₁ l₂ hperm ih =>
    intro ds hd
    obtain ⟨d, ds', rfl⟩ : ∃ d ds', ds = d :: ds' := by
      cases ds with
      | nil => exact absurd hd (by rw [List.length_nil, List.length_cons]; omega)
      | cons d ds' => exact ⟨d, ds', rfl⟩
    obtain ⟨cs, hcl, hcp⟩ := ih ds' (by rw [List.length_cons, List.length_cons] at hd; omega)
    refine ⟨d :: cs, by rw [List.length_cons, List.length_cons, hcl], ?_⟩
    rw [List.zip_cons_cons, List.zip_cons_cons]
    exact hcp.cons (d, v)
  | @swap x y l =>
    intro ds hd
    obtain ⟨d₁, d₂, ds', rfl⟩ : ∃ d₁ d₂ ds', ds = d₁ :: d₂ :: ds' := by
      cases ds with
      | nil => exact absurd hd (by rw [List.length_nil, List.length_cons, List.length_cons]; omega)
      | cons d₁ rest =>
        cases rest with
        | nil =>
          exact absurd hd (by
            rw [List.length_cons, List.length_nil, List.length_cons, List.length_cons]; omega)
        | cons d₂ ds' => exact ⟨d₁, d₂, ds', rfl⟩
    refine ⟨d₂ :: d₁ :: ds', by
      rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons] at hd ⊢
      omega, ?_⟩
    rw [List.zip_cons_cons, List.zip_cons_cons, List.zip_cons_cons, List.zip_cons_cons]
    exact List.Perm.swap _ _ _
  | @trans l₁ l₂ l₃ h₁ h₂ ih₁ ih₂ =>
    intro ds hd
    obtain ⟨es, hel, hep⟩ := ih₂ ds hd
    obtain ⟨cs, hcl, hcp⟩ := ih₁ es (by rw [hel])
    exact ⟨cs, hcl, hcp.trans hep⟩

/-- Independence does not depend on the order. -/
theorem isIndep_perm {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) {vs ws : List ZFSet.{u}}
    (hperm : vs.Perm ws) (hvm : ∀ v, v ∈ vs → v ∈ V)
    (h : IsIndep R zero vadd smul vzero vs) : IsIndep R zero vadd smul vzero ws := by
  intro ds hdl hdm hzero x hx
  obtain ⟨cs, hcl, hcp⟩ := perm_zip_exists hperm ds (by rw [hdl])
  have hlenvw : vs.length = ws.length := hperm.length_eq
  have hperm_cs : cs.Perm ds := by
    have hmapc : (cs.zip vs).map Prod.fst = cs := List.map_fst_zip (by omega)
    have hmapd : (ds.zip ws).map Prod.fst = ds := List.map_fst_zip (by omega)
    rw [← hmapc, ← hmapd]
    exact hcp.map Prod.fst
  have hcm : ∀ c, c ∈ cs → c ∈ R := fun c hc => hdm c (hperm_cs.mem_iff.mp hc)
  have hpairs : ∀ p, p ∈ cs.zip vs → p.1 ∈ R ∧ p.2 ∈ V := fun p hp =>
    ⟨hcm _ (List.of_mem_zip hp).left, hvm _ (List.of_mem_zip hp).right⟩
  have hval : lincomb vadd smul vzero cs vs = vzero := by
    rw [lincomb_eq_lincombP, lincombP_perm hM hcp hpairs, ← lincomb_eq_lincombP]
    exact hzero
  exact h cs hcl hcm hval x (hperm_cs.mem_iff.mpr hx)

/-! ## The span is a submodule

Which makes span transitive: a combination of vectors that are themselves
combinations of `ws` is a combination of `ws`. -/

theorem isSubmodule_spanSet {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) {vs : List ZFSet.{u}}
    (hvm : ∀ v, v ∈ vs → v ∈ V) :
    IsSubmodule (spanSet R V vadd smul vzero vs) R V vadd vzero smul := by
  refine ⟨fun w hw => (mem_spanSet_iff.mp hw).left,
    mem_spanSet_iff.mpr ⟨hM.group.mem_e, [], fun c hc => absurd hc List.not_mem_nil,
      (lincomb_nil_left vadd smul vzero vs).symm⟩, ?_, ?_⟩
  · intro w hw z hz
    obtain ⟨hwV, cs, hcm, rfl⟩ := mem_spanSet_iff.mp hw
    obtain ⟨hzV, ds, hdm, rfl⟩ := mem_spanSet_iff.mp hz
    obtain ⟨es, hem, hes⟩ := lincomb_add hM cs ds vs hcm hdm hvm
    exact mem_spanSet_iff.mpr ⟨vaddAt_mem hM hwV hzV, es, hem, hes⟩
  · intro c hc w hw
    obtain ⟨hwV, cs, hcm, rfl⟩ := mem_spanSet_iff.mp hw
    refine mem_spanSet_iff.mpr ⟨smulAt_mem hM hc hwV, cs.map (opAt mul c), ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact mulAt_mem hM.ring hc (hcm y hy)
    · exact lincomb_smul hM hc cs vs hcm hvm

/-- A combination of vectors from a submodule stays in it. -/
theorem lincomb_mem_submodule {R add mul zero one V vadd vzero smul S : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul)
    (hS : IsSubmodule S R V vadd vzero smul) :
    ∀ (cs vs : List ZFSet.{u}), (∀ c, c ∈ cs → c ∈ R) → (∀ v, v ∈ vs → v ∈ S) →
      lincomb vadd smul vzero cs vs ∈ S
  | [], vs, _, _ => by
    rw [lincomb_nil_left]
    exact hS.mem_zero
  | c :: cs, [], _, _ => by
    rw [lincomb_nil_right]
    exact hS.mem_zero
  | c :: cs, v :: vs, hcm, hvm => by
    rw [lincomb_cons]
    exact hS.add_closed _ (hS.smul_closed c (hcm c List.mem_cons_self) v
        (hvm v List.mem_cons_self)) _
      (lincomb_mem_submodule hM hS cs vs (fun x hx => hcm x (List.mem_cons_of_mem _ hx))
        (fun w hw => hvm w (List.mem_cons_of_mem _ hw)))

/-- Span is transitive. -/
theorem spanSet_subset_spanSet {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) {vs ws : List ZFSet.{u}}
    (hwm : ∀ w, w ∈ ws → w ∈ V)
    (hvs : ∀ v, v ∈ vs → v ∈ spanSet R V vadd smul vzero ws) :
    spanSet R V vadd smul vzero vs ⊆ spanSet R V vadd smul vzero ws := by
  intro z hz
  obtain ⟨-, cs, hcm, rfl⟩ := mem_spanSet_iff.mp hz
  exact lincomb_mem_submodule hM (isSubmodule_spanSet hM hwm) cs vs hcm hvs

/-! ## Exchange

Splitting the span of `v :: vs` into a multiple of `v` and something from the
span of `vs` is what lets one vector be swapped for another. -/

theorem lincomb_append {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) :
    ∀ (cs₁ vs₁ cs₂ vs₂ : List ZFSet.{u}), cs₁.length = vs₁.length →
      (∀ c, c ∈ cs₁ → c ∈ R) → (∀ v, v ∈ vs₁ → v ∈ V) →
      (∀ c, c ∈ cs₂ → c ∈ R) → (∀ v, v ∈ vs₂ → v ∈ V) →
      lincomb vadd smul vzero (cs₁ ++ cs₂) (vs₁ ++ vs₂)
        = opAt vadd (lincomb vadd smul vzero cs₁ vs₁) (lincomb vadd smul vzero cs₂ vs₂)
  | [], vs₁, cs₂, vs₂, hlen, _, _, hc2, hv2 => by
    obtain rfl : vs₁ = [] := by
      cases vs₁ with
      | nil => rfl
      | cons v vs => exact absurd hlen (by rw [List.length_nil, List.length_cons]; omega)
    rw [List.nil_append, List.nil_append, lincomb_nil_left]
    exact (hM.group.left_id _ (lincomb_mem hM cs₂ vs₂ hc2 hv2)).symm
  | c :: cs₁, vs₁, cs₂, vs₂, hlen, hc1, hv1, hc2, hv2 => by
    obtain ⟨v, vs₁', rfl⟩ := exists_cons_of_length (cs := vs₁) hlen.symm
    have hcR : c ∈ R := hc1 c List.mem_cons_self
    have hvV : v ∈ V := hv1 v List.mem_cons_self
    have hc1' : ∀ x, x ∈ cs₁ → x ∈ R := fun x hx => hc1 x (List.mem_cons_of_mem _ hx)
    have hv1' : ∀ w, w ∈ vs₁' → w ∈ V := fun w hw => hv1 w (List.mem_cons_of_mem _ hw)
    have hlen' : cs₁.length = vs₁'.length := by
      rw [List.length_cons, List.length_cons] at hlen
      omega
    rw [List.cons_append, List.cons_append, lincomb_cons, lincomb_cons,
      lincomb_append hM cs₁ vs₁' cs₂ vs₂ hlen' hc1' hv1' hc2 hv2,
      ← hM.group.assoc _ (smulAt_mem hM hcR hvV) _ (lincomb_mem hM cs₁ vs₁' hc1' hv1') _
        (lincomb_mem hM cs₂ vs₂ hc2 hv2)]

/-- Every vector of the family is in its span. -/
theorem subset_spanSet {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) {vs : List ZFSet.{u}}
    (hvm : ∀ v, v ∈ vs → v ∈ V) {v : ZFSet.{u}} (hv : v ∈ vs) :
    v ∈ spanSet R V vadd smul vzero vs := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hv
  have hpre : ∀ w, w ∈ pre → w ∈ V := fun w hw => hvm w (by
    rw [List.mem_append]
    exact Or.inl hw)
  have hpost : ∀ w, w ∈ post → w ∈ V := fun w hw => hvm w (by
    rw [List.mem_append]
    exact Or.inr (List.mem_cons_of_mem _ hw))
  have hvV : v ∈ V := hvm v (by
    rw [List.mem_append]
    exact Or.inr List.mem_cons_self)
  refine mem_spanSet_iff.mpr ⟨hvV,
    List.replicate pre.length zero ++ one :: List.replicate post.length zero, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · rw [List.eq_of_mem_replicate h]
      exact hM.ring.addGroup.mem_e
    · rcases List.mem_cons.mp h with rfl | h'
      · exact hM.ring.mem_one
      · rw [List.eq_of_mem_replicate h']
        exact hM.ring.addGroup.mem_e
  · rw [lincomb_append hM _ _ _ _ (List.length_replicate ..)
      (fun c hc => by rw [List.eq_of_mem_replicate hc]; exact hM.ring.addGroup.mem_e) hpre
      (fun c hc => by
        rcases List.mem_cons.mp hc with rfl | h'
        · exact hM.ring.mem_one
        · rw [List.eq_of_mem_replicate h']
          exact hM.ring.addGroup.mem_e)
      (fun w hw => hvm w (by
        rw [List.mem_append]
        exact Or.inr hw)),
    lincomb_zeros hM pre.length pre hpre, lincomb_cons,
    lincomb_zeros hM post.length post hpost, hM.one_smul _ hvV,
    hM.group.right_id _ hvV, hM.group.left_id _ hvV]

/-- Membership in the span of `v :: vs`, split into the `v` part and the rest. -/
theorem mem_spanSet_cons_iff {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) {v : ZFSet.{u}} (hv : v ∈ V)
    {vs : List ZFSet.{u}} (hvm : ∀ w, w ∈ vs → w ∈ V) {u : ZFSet.{u}} :
    u ∈ spanSet R V vadd smul vzero (v :: vs) ↔
      ∃ c, c ∈ R ∧ ∃ z, z ∈ spanSet R V vadd smul vzero vs ∧ u = opAt vadd (opAt smul c v) z := by
  have hcons : ∀ w, w ∈ v :: vs → w ∈ V := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact hv
    · exact hvm w hw'
  constructor
  · intro hu
    obtain ⟨huV, cs, hcm, rfl⟩ := mem_spanSet_iff.mp hu
    -- normalise the coefficient list to the length of `v :: vs`
    have hpad := lincomb_padTo hM cs (v :: vs) hcm hcons
    obtain ⟨c, cs', hsplit⟩ : ∃ c cs', padTo cs zero (v :: vs).length = c :: cs' := by
      have hlen := padTo_length cs zero (v :: vs).length
      cases hpadl : padTo cs zero (v :: vs).length with
      | nil =>
        rw [hpadl, List.length_nil, List.length_cons] at hlen
        exact absurd hlen (by omega)
      | cons c cs' => exact ⟨c, cs', rfl⟩
    have hpadm := padTo_mem (R := R) hM.ring.addGroup.mem_e hcm (v :: vs).length
    rw [hsplit] at hpad hpadm
    refine ⟨c, hpadm c List.mem_cons_self, lincomb vadd smul vzero cs' vs, ?_, ?_⟩
    · exact mem_spanSet_iff.mpr ⟨lincomb_mem hM cs' vs
        (fun x hx => hpadm x (List.mem_cons_of_mem _ hx)) hvm, cs',
        (fun x hx => hpadm x (List.mem_cons_of_mem _ hx)), rfl⟩
    · rw [← hpad, lincomb_cons]
  · rintro ⟨c, hc, z, hz, rfl⟩
    obtain ⟨hzV, ds, hdm, rfl⟩ := mem_spanSet_iff.mp hz
    exact mem_spanSet_iff.mpr ⟨vaddAt_mem hM (smulAt_mem hM hc hv) hzV, c :: ds,
      (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hc
        · exact hdm x hx'), rfl⟩

/-- The exchange step. A vector whose `v`-coefficient is invertible can take
the place of `v`. -/
theorem spanSet_exchange {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (hF : IsField R add mul zero one)
    {v u c z : ZFSet.{u}} (hv : v ∈ V) {vs : List ZFSet.{u}} (hvm : ∀ w, w ∈ vs → w ∈ V)
    (hc : c ∈ R) (hcne : c ≠ zero) (hz : z ∈ spanSet R V vadd smul vzero vs)
    (hu : u = opAt vadd (opAt smul c v) z) :
    spanSet R V vadd smul vzero (v :: vs) ⊆ spanSet R V vadd smul vzero (u :: vs) := by
  have hzV := (mem_spanSet_iff.mp hz).left
  have huV : u ∈ V := by
    rw [hu]
    exact vaddAt_mem hM (smulAt_mem hM hc hv) hzV
  have hcons : ∀ w, w ∈ u :: vs → w ∈ V := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact huV
    · exact hvm w hw'
  obtain ⟨b, hb, hcb⟩ := hF.inverses c hc hcne
  -- `v = b·u + (-b)·z`
  have hvmem : v ∈ spanSet R V vadd smul vzero (u :: vs) := by
    refine (mem_spanSet_cons_iff hM huV hvm).mpr ⟨b, hb,
      opAt smul (ringNeg R add zero b) z, ?_, ?_⟩
    · exact (isSubmodule_spanSet hM hvm).smul_closed _ (ringNeg_mem hM.ring hb) z hz
    · rw [hu, hM.smul_add _ hb _ (smulAt_mem hM hc hv) _ hzV,
        ← hM.smul_smul _ hb _ hc _ hv, hM.ring.mulComm _ hb _ hc, hcb, hM.one_smul _ hv,
        hM.group.assoc _ hv _ (smulAt_mem hM hb hzV) _
          (smulAt_mem hM (ringNeg_mem hM.ring hb) hzV),
        ← hM.add_smul _ hb _ (ringNeg_mem hM.ring hb) _ hzV,
        ringAdd_neg hM.ring hb, zero_smul hM hzV, hM.group.right_id _ hv]
  refine spanSet_subset_spanSet hM hcons (fun w hw => ?_)
  rcases List.mem_cons.mp hw with rfl | hw'
  · exact hvmem
  · exact subset_spanSet hM hcons (List.mem_cons_of_mem _ hw')

/-- Vectors in the span of `v :: vs` are `c·v` plus something from the span of
`vs`, uniformly: the whole list is the image of a list of pairs. -/
theorem exists_span_pairs {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) {v : ZFSet.{u}} (hv : v ∈ V)
    {vs : List ZFSet.{u}} (hvm : ∀ w, w ∈ vs → w ∈ V) :
    ∀ us : List ZFSet.{u}, (∀ u, u ∈ us → u ∈ spanSet R V vadd smul vzero (v :: vs)) →
      ∃ qs : List (ZFSet.{u} × ZFSet.{u}),
        (∀ q, q ∈ qs → q.1 ∈ R ∧ q.2 ∈ spanSet R V vadd smul vzero vs) ∧
        us = qs.map (fun q => opAt vadd (opAt smul q.1 v) q.2)
  | [], _ => ⟨[], fun q hq => absurd hq List.not_mem_nil, rfl⟩
  | u :: us, hus => by
    obtain ⟨c, hc, z, hz, hue⟩ :=
      (mem_spanSet_cons_iff hM hv hvm).mp (hus u List.mem_cons_self)
    obtain ⟨qs, hqs, hmap⟩ :=
      exists_span_pairs hM hv hvm us (fun w hw => hus w (List.mem_cons_of_mem _ hw))
    refine ⟨(c, z) :: qs, ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact ⟨hc, hz⟩
      · exact hqs q hq'
    · rw [List.map_cons, ← hmap, hue]

/-- With vanishing decidable, a list of ring elements is all zero or has a
non-zero entry. -/
theorem all_zero_or_exists_ne {R zero : ZFSet.{u}} (hdec : DecidableVanishing R zero) :
    ∀ qs : List (ZFSet.{u} × ZFSet.{u}), (∀ q, q ∈ qs → q.1 ∈ R) →
      (∀ q, q ∈ qs → q.1 = zero) ∨ ∃ q, q ∈ qs ∧ q.1 ≠ zero
  | [], _ => Or.inl (fun q hq => absurd hq List.not_mem_nil)
  | q :: qs, hqs => by
    rcases hdec q.1 (hqs q List.mem_cons_self) with hz | hnz
    · rcases all_zero_or_exists_ne hdec qs (fun r hr => hqs r (List.mem_cons_of_mem _ hr))
        with hall | ⟨r, hr, hrne⟩
      · refine Or.inl (fun r hr => ?_)
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact hz
        · exact hall r hr'
      · exact Or.inr ⟨r, List.mem_cons_of_mem _ hr, hrne⟩
    · exact Or.inr ⟨q, List.mem_cons_self, hnz⟩

/-- A combination of vectors of the form `a·u + w` is a multiple of `u` plus the
combination of the `w`s. -/
theorem lincomb_map_split {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) {u : ZFSet.{u}} (hu : u ∈ V) :
    ∀ (ds : List ZFSet.{u}) (qs : List (ZFSet.{u} × ZFSet.{u})), (∀ d, d ∈ ds → d ∈ R) →
      (∀ q, q ∈ qs → q.1 ∈ R ∧ q.2 ∈ V) →
      ∃ s, s ∈ R ∧
        lincomb vadd smul vzero ds (qs.map (fun q => opAt vadd (opAt smul q.1 u) q.2))
          = opAt vadd (opAt smul s u)
            (lincomb vadd smul vzero ds (qs.map (fun q => q.2)))
  | [], qs, _, _ => by
    refine ⟨zero, hM.ring.addGroup.mem_e, ?_⟩
    rw [lincomb_nil_left, lincomb_nil_left, zero_smul hM hu,
      hM.group.left_id _ hM.group.mem_e]
  | d :: ds, [], _, _ => by
    refine ⟨zero, hM.ring.addGroup.mem_e, ?_⟩
    show vzero = opAt vadd (opAt smul zero u) (lincomb vadd smul vzero (d :: ds) [])
    rw [lincomb_nil_right, zero_smul hM hu, hM.group.left_id _ hM.group.mem_e]
  | d :: ds, q :: qs, hdm, hqm => by
    have hd : d ∈ R := hdm d List.mem_cons_self
    have hq := hqm q List.mem_cons_self
    have hdm' : ∀ x, x ∈ ds → x ∈ R := fun x hx => hdm x (List.mem_cons_of_mem _ hx)
    have hqm' : ∀ r, r ∈ qs → r.1 ∈ R ∧ r.2 ∈ V := fun r hr => hqm r (List.mem_cons_of_mem _ hr)
    obtain ⟨s, hs, hrec⟩ := lincomb_map_split hM hu ds qs hdm' hqm'
    have hrest : lincomb vadd smul vzero ds (qs.map (fun r => r.2)) ∈ V :=
      lincomb_mem hM ds _ hdm' (mem_map_of_maps _ (fun r hr => (hqm' r hr).right))
    refine ⟨opAt add (opAt mul d q.1) s, addAt_mem hM.ring (mulAt_mem hM.ring hd hq.left) hs, ?_⟩
    rw [List.map_cons, List.map_cons, lincomb_cons, lincomb_cons, hrec,
      hM.smul_add _ hd _ (smulAt_mem hM hq.left hu) _ hq.right,
      ← hM.smul_smul _ hd _ hq.left _ hu,
      hM.group.assoc _ (smulAt_mem hM (mulAt_mem hM.ring hd hq.left) hu)
        _ (smulAt_mem hM hd hq.right) _ (vaddAt_mem hM (smulAt_mem hM hs hu) hrest),
      ← hM.group.assoc _ (smulAt_mem hM hd hq.right) _ (smulAt_mem hM hs hu) _ hrest,
      hM.comm _ (smulAt_mem hM hd hq.right) _ (smulAt_mem hM hs hu),
      hM.group.assoc _ (smulAt_mem hM hs hu) _ (smulAt_mem hM hd hq.right) _ hrest,
      ← hM.group.assoc _ (smulAt_mem hM (mulAt_mem hM.ring hd hq.left) hu)
        _ (smulAt_mem hM hs hu) _ (vaddAt_mem hM (smulAt_mem hM hd hq.right) hrest),
      ← hM.add_smul _ (mulAt_mem hM.ring hd hq.left) _ hs _ hu]

/-- Steinitz exchange. An independent list is no longer than a spanning one.
No finiteness is used: the induction is on the spanning list. -/
theorem exchange_le {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (hF : IsField R add mul zero one)
    (hdec : DecidableVanishing R zero) :
    ∀ (vs us : List ZFSet.{u}), (∀ v, v ∈ vs → v ∈ V) →
      (∀ u, u ∈ us → u ∈ spanSet R V vadd smul vzero vs) →
      IsIndep R zero vadd smul vzero us → us.length ≤ vs.length
  | [], us, _, hus, hindep => by
    -- everything in the span of nothing is zero, and a zero vector is dependent
    cases us with
    | nil => omega
    | cons u us' =>
      exfalso
      have huz : u = vzero := by
        obtain ⟨-, cs, -, he⟩ := mem_spanSet_iff.mp (hus u List.mem_cons_self)
        rw [he, lincomb_nil_right]
      have hcs : (one :: List.replicate us'.length zero).length = (u :: us').length := by
        rw [List.length_cons, List.length_cons, List.length_replicate]
      have hmem : ∀ c, c ∈ one :: List.replicate us'.length zero → c ∈ R := by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact hM.ring.mem_one
        · rw [List.eq_of_mem_replicate hc']
          exact hM.ring.addGroup.mem_e
      have hzero : lincomb vadd smul vzero (one :: List.replicate us'.length zero) (u :: us')
          = vzero := by
        rw [lincomb_cons, huz, hM.one_smul _ hM.group.mem_e,
          lincomb_zeros hM us'.length us' (fun w hw => (mem_spanSet_iff.mp
            (hus w (List.mem_cons_of_mem _ hw))).left),
          hM.group.left_id _ hM.group.mem_e]
      exact hF.zero_ne_one (hindep _ hcs hmem hzero one List.mem_cons_self).symm
  | v :: vs, us, hvm, hus, hindep => by
    have hv : v ∈ V := hvm v List.mem_cons_self
    have hvs : ∀ w, w ∈ vs → w ∈ V := fun w hw => hvm w (List.mem_cons_of_mem _ hw)
    have husV : ∀ u, u ∈ us → u ∈ V := fun u hu => (mem_spanSet_iff.mp (hus u hu)).left
    obtain ⟨qs, hqs, rfl⟩ := exists_span_pairs hM hv hvs us hus
    rcases all_zero_or_exists_ne hdec qs (fun q hq => (hqs q hq).left) with hall | ⟨q, hq, hqne⟩
    · -- no vector uses `v`, so they all lie in the smaller span
      have hsmall : ∀ u, u ∈ qs.map (fun q => opAt vadd (opAt smul q.1 v) q.2) →
          u ∈ spanSet R V vadd smul vzero vs := by
        intro u hu
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
        rw [hall r hr, zero_smul hM hv,
          hM.group.left_id _ (mem_spanSet_iff.mp (hqs r hr).right).left]
        exact (hqs r hr).right
      have := exchange_le hM hF hdec vs _ hvs hsmall hindep
      rw [List.length_cons]
      omega
    · -- one vector uses `v`; swap it in and drop `v`
      obtain ⟨pre, post, rfl⟩ := List.append_of_mem hq
      have hfront : (pre ++ q :: post).map (fun q => opAt vadd (opAt smul q.1 v) q.2)
          = (pre.map (fun q => opAt vadd (opAt smul q.1 v) q.2))
            ++ (opAt vadd (opAt smul q.1 v) q.2)
              :: (post.map (fun q => opAt vadd (opAt smul q.1 v) q.2)) := by
        rw [List.map_append, List.map_cons]
      obtain ⟨u₀, hu₀⟩ : ∃ x, x = opAt vadd (opAt smul q.1 v) q.2 := ⟨_, rfl⟩
      obtain ⟨rest, hrestdef⟩ : ∃ l, l = pre.map (fun q => opAt vadd (opAt smul q.1 v) q.2)
        ++ post.map (fun q => opAt vadd (opAt smul q.1 v) q.2) := ⟨_, rfl⟩
      have hperm : ((pre ++ q :: post).map
          (fun q => opAt vadd (opAt smul q.1 v) q.2)).Perm (u₀ :: rest) := by
        rw [hfront, hu₀, hrestdef]
        exact List.perm_middle
      have hindep' : IsIndep R zero vadd smul vzero (u₀ :: rest) :=
        isIndep_perm hM hperm husV hindep
      have hu₀V : u₀ ∈ V := husV u₀ (hperm.mem_iff.mpr List.mem_cons_self)
      have hrestV : ∀ w, w ∈ rest → w ∈ V := fun w hw =>
        husV w (hperm.mem_iff.mpr (List.mem_cons_of_mem _ hw))
      -- the exchanged family spans everything the old one did
      have hsub := spanSet_exchange hM hF hv hvs (hqs q hq).left hqne (hqs q hq).right hu₀
      have hrestspan : ∀ w, w ∈ rest → w ∈ spanSet R V vadd smul vzero (u₀ :: vs) :=
        fun w hw => hsub w (hus w (hperm.mem_iff.mpr (List.mem_cons_of_mem _ hw)))
      obtain ⟨ps, hps, hrestmap⟩ := exists_span_pairs hM hu₀V hvs rest hrestspan
      -- the remainders are independent and lie in the smaller span
      have hremV : ∀ w, w ∈ ps.map (fun p => p.2) → w ∈ V :=
        mem_map_of_maps _ (fun r hr => (mem_spanSet_iff.mp (hps r hr).right).left)
      have hremindep : IsIndep R zero vadd smul vzero (ps.map (fun p => p.2)) := by
        intro ds hdl hdm hzero x hx
        obtain ⟨s, hs, hsplit⟩ := lincomb_map_split hM hu₀V ds ps hdm
          (fun r hr => ⟨(hps r hr).left, (mem_spanSet_iff.mp (hps r hr).right).left⟩)
        have hlin : lincomb vadd smul vzero (ringNeg R add zero s :: ds) (u₀ :: rest) = vzero := by
          rw [lincomb_cons, hrestmap, hsplit, hzero,
            hM.group.right_id _ (smulAt_mem hM hs hu₀V),
            ← hM.add_smul _ (ringNeg_mem hM.ring hs) _ hs _ hu₀V,
            ringNeg_add hM.ring hs, zero_smul hM hu₀V]
        have hlen : (ringNeg R add zero s :: ds).length = (u₀ :: rest).length := by
          rw [List.length_cons, List.length_cons, hdl, hrestmap, List.length_map,
            List.length_map]
        have hmem : ∀ c, c ∈ ringNeg R add zero s :: ds → c ∈ R := by
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc'
          · exact ringNeg_mem hM.ring hs
          · exact hdm c hc'
        exact hindep' _ hlen hmem hlin x (List.mem_cons_of_mem _ hx)
      have hremspan : ∀ w, w ∈ ps.map (fun p => p.2) →
          w ∈ spanSet R V vadd smul vzero vs :=
        mem_map_of_maps _ (fun r hr => (hps r hr).right)
      have hIH := exchange_le hM hF hdec vs _ hvs hremspan hremindep
      rw [List.length_map] at hIH
      have hlens : rest.length = ps.length := by rw [hrestmap, List.length_map]
      have hall : ((pre ++ q :: post).map
          (fun q => opAt vadd (opAt smul q.1 v) q.2)).length = rest.length + 1 := by
        rw [hperm.length_eq, List.length_cons]
      rw [hall, List.length_cons]
      omega

/-! ## Dimension

Two bases of a finite module have the same length -- not by the exchange lemma,
but because each of them counts the module as `q^length`, and powers of `q`
determine their exponent. -/

def IsBasis (R zero V vadd vzero smul : ZFSet.{u}) (vs : List ZFSet.{u}) : Prop :=
  (∀ v, v ∈ vs → v ∈ V) ∧ IsIndep R zero vadd smul vzero vs ∧
    spanSet R V vadd smul vzero vs = V

/-- A basis spans with coefficient lists of its own length.

`mem_spanSet_iff` gives coefficients of ANY length --- `lincomb` ignores the
extra ones and pads the missing with zero --- while every tower lemma wants the
length pinned to the basis. `padTo` is that normalisation and `lincomb_padTo`
says it changes nothing. -/
theorem spanCoeffs_of_isBasis {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    {vs : List ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul)
    (hb : IsBasis R zero V vadd vzero smul vs) :
    ∀ x, x ∈ V → ∃ bs : List ZFSet.{u}, bs.length = vs.length ∧
      (∀ b, b ∈ bs → b ∈ R) ∧ x = lincomb vadd smul vzero bs vs := by
  intro x hx
  have hxs : x ∈ spanSet R V vadd smul vzero vs := by
    rw [hb.right.right]
    exact hx
  obtain ⟨-, cs, hcm, hce⟩ := mem_spanSet_iff.mp hxs
  refine ⟨padTo cs zero vs.length, padTo_length _ _ _,
    padTo_mem hM.ring.addGroup.mem_e hcm vs.length, ?_⟩
  rw [lincomb_padTo hM cs vs hcm hb.left]
  exact hce

#print axioms spanCoeffs_of_isBasis
#print axioms IsBasis

/-- A ring is one-dimensional over itself, with basis `[one]`. The scalars
act by multiplication restricted to the ring on the left, which is the shape
every tower statement here uses; the whole content is `a·1 = a`, read in both
directions -- once for independence and once for spanning. -/
theorem isBasis_singleton_one {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) :
    IsBasis R zero R add zero (restrictLeft mul R R) [one] := by
  have hlin : ∀ c, c ∈ R → lincomb add (restrictLeft mul R R) zero [c] [one] = c := by
    intro c hc
    show opAt add (opAt (restrictLeft mul R R) c one) zero = c
    rw [opAt_restrictLeft hR.mulFun (fun x hx => by rw [hR.mulDom]; exact hx)
      (fun x hx y hy => mulAt_mem hR hx hy) hc hR.mem_one, hR.mul_one c hc]
    exact ringAdd_zero hR hc
  refine ⟨fun v hv => ?_, fun cs hlen hcs hz c hc => ?_, ?_⟩
  · cases hv with
    | head => exact hR.mem_one
    | tail _ h => nomatch h
  · match cs, hlen, hcs, hz, hc with
    | [c'], _, hcs, hz, hc =>
      have hc' : c = c' := by cases hc with
        | head => rfl
        | tail _ h => nomatch h
      rw [hc', ← hlin c' (hcs c' (List.Mem.head _))]
      exact hz
  · refine ext _ _ fun w => ⟨fun hw => (mem_spanSet_iff.mp hw).left, fun hw => ?_⟩
    refine mem_spanSet_iff.mpr ⟨hw, [w], fun c hc => ?_, (hlin w hw).symm⟩
    cases hc with
    | head => exact hw
    | tail _ h => nomatch h

/-- Dimension is well defined without any finiteness, by exchange rather
than by counting. -/
theorem dim_unique_of_exchange {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (hF : IsField R add mul zero one)
    (hdec : DecidableVanishing R zero) {vs us : List ZFSet.{u}}
    (hvs : IsBasis R zero V vadd vzero smul vs) (hus : IsBasis R zero V vadd vzero smul us) :
    vs.length = us.length := by
  have h₁ : us.length ≤ vs.length :=
    exchange_le hM hF hdec vs us hvs.left
      (fun u hu => by rw [hvs.right.right]; exact hus.left u hu) hus.right.left
  have h₂ : vs.length ≤ us.length :=
    exchange_le hM hF hdec us vs hus.left
      (fun v hv => by rw [hus.right.right]; exact hvs.left v hv) hvs.right.left
  omega

/-- Dimension is well defined. -/
theorem dim_unique {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (hFR : IsRing R add mul zero one) (hFne : zero ≠ one)
    {q : Nat} (hRfin : Equinumerous R (ofNat.{u} q)) {vs us : List ZFSet.{u}}
    (hvs : IsBasis R zero V vadd vzero smul vs) (hus : IsBasis R zero V vadd vzero smul us) :
    vs.length = us.length := by
  have hq := two_le_card_of_isField hFR hFne hRfin
  have hv := equinumerous_spanSet_card hM hRfin hvs.left hvs.right.left
  have hu := equinumerous_spanSet_card hM hRfin hus.left hus.right.left
  rw [hvs.right.right] at hv
  rw [hus.right.right] at hu
  have hpow : q ^ vs.length = q ^ us.length := card_unique hv hu
  exact pow_right_injective (by omega) hpow

/-! ## A ring is a module over a subring

Multiplication restricted to `S × R` is the action, and the module laws are the
ring laws. With `exists_char` and the prime subfield this gives the order of a
finite field. -/

theorem isModule_of_subring {S R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one)
    (hS : IsSubring S R add mul zero one) :
    IsModule S (restrictOp add S) (restrictOp mul S) zero one R add zero
      (restrictLeft mul S R) := by
  have hdom : ∀ x, x ∈ prod S R → x ∈ domain mul := fun x hx => by
    obtain ⟨c, hc, d, hd, rfl⟩ := (mem_prod_iff x _ _).mp hx
    rw [hR.mulDom]
    exact opair_mem_prod (hS.sub _ hc) hd
  have hclosed : ∀ x, x ∈ S → ∀ y, y ∈ R → opAt mul x y ∈ R :=
    fun x hx y hy => mulAt_mem hR (hS.sub _ hx) hy
  have hL : ∀ {c x : ZFSet.{u}}, c ∈ S → x ∈ R →
      opAt (restrictLeft mul S R) c x = opAt mul c x :=
    fun hc hx => opAt_restrictLeft hR.mulFun hdom hclosed hc hx
  refine ⟨isRing_subring hR hS, hR.addGroup, hR.addComm, isFunction_restrictLeft hR.mulFun,
    restrictLeft_domain hR.mulFun hdom hclosed, restrictLeft_range, ?_, ?_, ?_, ?_⟩
  · intro c hc x hx y hy
    rw [hL hc (addAt_mem hR hx hy), hL hc hx, hL hc hy]
    exact hR.distrib _ (hS.sub _ hc) _ hx _ hy
  · intro c hc d hd x hx
    rw [opAt_subring_add hR hS hc hd, hL (hS.add_closed c hc d hd) hx, hL hc hx, hL hd hx]
    exact ringRight_distrib hR (hS.sub _ hc) (hS.sub _ hd) hx
  · intro c hc d hd x hx
    rw [opAt_subring_mul hR hS hc hd, hL (hS.mul_closed c hc d hd) hx, hL hd hx,
      hL hc (mulAt_mem hR (hS.sub _ hd) hx)]
    exact hR.mulAssoc _ (hS.sub _ hc) _ (hS.sub _ hd) _ hx
  · intro x hx
    rw [hL hS.mem_one hx]
    exact ringOne_mul hR hx

/-! ## Audit -/

#print axioms zero_smul
#print axioms lincomb_add
#print axioms exists_cons_of_length
#print axioms lincomb_zipWith_add
#print axioms lincomb_injective
#print axioms equinumerous_spanSet
#print axioms equinumerous_spanSet_card
#print axioms isIndep_cons

#print axioms exists_basis
#print axioms dim_unique
#print axioms lincombP_perm
#print axioms isIndep_perm
#print axioms mem_spanSet_cons_iff
#print axioms spanSet_exchange
#print axioms exchange_le

/-- An independent list extends to a basis, over an ARBITRARY field.

`exists_basis` is not this: it takes both carriers finite, which is the
finiteness a general Artin bound has to shed. What that finiteness actually buys
is the DECISION is `x` already in the span of `ws`, so this takes the decision
as `hspanDec` and asks nothing of either carrier.

The loop's fuel is `bs.length`: by `exchange_le` an independent list inside `V`
is never longer than a basis, so a vector outside the current span can be added
at most `bs.length` times. -/
theorem extend_to_basis {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul)
    (hF : IsField R add mul zero one)
    (hdec : DecidableVanishing R zero)
    {bs : List ZFSet.{u}} (hbs : IsBasis R zero V vadd vzero smul bs)
    (hspanDec : ∀ ws : List ZFSet.{u}, (∀ w, w ∈ ws → w ∈ V) →
      ∀ x, x ∈ V → x ∈ spanSet R V vadd smul vzero ws ∨
        x ∉ spanSet R V vadd smul vzero ws) :
    ∀ vs : List ZFSet.{u}, (∀ v, v ∈ vs → v ∈ V) →
      IsIndep R zero vadd smul vzero vs →
      ∃ us : List ZFSet.{u}, (∀ u, u ∈ us → u ∈ V) ∧
        IsBasis R zero V vadd vzero smul (us ++ vs) := by
  have hstab : StableVanishing R zero := stableVanishing_of_decidableVanishing hdec
  have hall : ∀ ws : List ZFSet.{u}, (∀ w, w ∈ ws → w ∈ V) →
      ∀ cs : List ZFSet.{u}, (∀ c, c ∈ cs → c ∈ V) →
      (∀ c, c ∈ cs → c ∈ spanSet R V vadd smul vzero ws) ∨
        ∃ c, c ∈ cs ∧ c ∉ spanSet R V vadd smul vzero ws := by
    intro ws hws cs
    induction cs with
    | nil => intro _; exact Or.inl (fun c hc => absurd hc List.not_mem_nil)
    | cons a t ih =>
      intro hcs
      rcases hspanDec ws hws a (hcs a List.mem_cons_self) with h | h
      · rcases ih (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) with hin | ⟨c, hc, hnc⟩
        · refine Or.inl (fun c hc => ?_)
          rcases List.mem_cons.mp hc with rfl | hc'
          · exact h
          · exact hin c hc'
        · exact Or.inr ⟨c, List.mem_cons_of_mem _ hc, hnc⟩
      · exact Or.inr ⟨a, List.mem_cons_self, h⟩
  have hdone : ∀ ws : List ZFSet.{u}, (∀ w, w ∈ ws → w ∈ V) →
      (∀ c, c ∈ bs → c ∈ spanSet R V vadd smul vzero ws) →
      spanSet R V vadd smul vzero ws = V := by
    intro ws hws hsub
    have h1 : spanSet R V vadd smul vzero bs ⊆ spanSet R V vadd smul vzero ws :=
      spanSet_subset_spanSet hM hws hsub
    rw [hbs.right.right] at h1
    exact ext _ _ fun z => ⟨fun hz => spanSet_subset z hz, fun hz => h1 z hz⟩
  have key : ∀ k : Nat, ∀ vs : List ZFSet.{u}, (∀ v, v ∈ vs → v ∈ V) →
      IsIndep R zero vadd smul vzero vs → bs.length ≤ vs.length + k →
      ∃ us : List ZFSet.{u}, (∀ u, u ∈ us → u ∈ V) ∧
        IsBasis R zero V vadd vzero smul (us ++ vs) := by
    intro k
    induction k with
    | zero =>
      intro vs hvm hindep hle
      rcases hall vs hvm bs hbs.left with hin | ⟨b, hb, hnb⟩
      · exact ⟨[], fun u hu => absurd hu List.not_mem_nil,
          hvm, hindep, hdone vs hvm hin⟩
      · exfalso
        have hbV : b ∈ V := hbs.left b hb
        have hcons : IsIndep R zero vadd smul vzero (b :: vs) :=
          isIndep_cons hM hF hstab hbV hvm hindep hnb
        have hlen : (b :: vs).length ≤ bs.length :=
          exchange_le hM hF hdec bs (b :: vs) hbs.left
            (fun u hu => by
              rw [hbs.right.right]
              rcases List.mem_cons.mp hu with rfl | hu'
              · exact hbV
              · exact hvm u hu')
            hcons
        rw [List.length_cons] at hlen
        omega
    | succ k ih =>
      intro vs hvm hindep hle
      rcases hall vs hvm bs hbs.left with hin | ⟨b, hb, hnb⟩
      · exact ⟨[], fun u hu => absurd hu List.not_mem_nil,
          hvm, hindep, hdone vs hvm hin⟩
      · have hbV : b ∈ V := hbs.left b hb
        have hcons : IsIndep R zero vadd smul vzero (b :: vs) :=
          isIndep_cons hM hF hstab hbV hvm hindep hnb
        have hcm : ∀ v, v ∈ b :: vs → v ∈ V := by
          intro v hv
          rcases List.mem_cons.mp hv with rfl | hv'
          · exact hbV
          · exact hvm v hv'
        obtain ⟨us, husV, husB⟩ := ih (b :: vs) hcm hcons (by
          rw [List.length_cons]; omega)
        refine ⟨us ++ [b], ?_, ?_⟩
        · intro u hu
          rcases List.mem_append.mp hu with hu' | hu'
          · exact husV u hu'
          · rcases List.mem_singleton.mp hu' with rfl
            exact hbV
        · rwa [List.append_assoc, List.singleton_append]
  intro vs hvm hindep
  exact key bs.length vs hvm hindep (by omega)

#print axioms extend_to_basis

/-- A finite spanning list contains a basis, over an ARBITRARY field.

The sibling of `extend_to_basis`, and the one a submodule actually hands you:
`submodule_powSet_fg` returns a finite SPANNING list, never an independent one.

`exists_basis` is not this either --- it takes both carriers finite. What that
finiteness buys is the DECISION is `x` already in the span of `ws`, so this
takes the decision as `hspanDec` and asks nothing of either carrier.

THE INVARIANT IS STRONGER THAN THE CONCLUSION, and has to be: walking `gs` left
to right, everything already KEPT stays in the span of the final answer, and so
does everything already SEEN. Carrying only the second fails, because the
recursive call returns a basis for a LONGER accumulator and nothing then gets
you back to the shorter one. -/
theorem basis_of_span {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul)
    (hF : IsField R add mul zero one)
    (hstab : StableVanishing R zero)
    (hspanDec : ∀ ws : List ZFSet.{u}, (∀ w, w ∈ ws → w ∈ V) →
      ∀ x, x ∈ V → x ∈ spanSet R V vadd smul vzero ws ∨
        x ∉ spanSet R V vadd smul vzero ws) :
    ∀ gs : List ZFSet.{u}, (∀ g, g ∈ gs → g ∈ V) →
      spanSet R V vadd smul vzero gs = V →
      ∃ bs : List ZFSet.{u}, IsBasis R zero V vadd vzero smul bs := by
  have key : ∀ gs : List ZFSet.{u}, (∀ g, g ∈ gs → g ∈ V) →
      ∀ acc : List ZFSet.{u}, (∀ a, a ∈ acc → a ∈ V) →
      IsIndep R zero vadd smul vzero acc →
      ∃ bs : List ZFSet.{u}, (∀ b, b ∈ bs → b ∈ V) ∧
        IsIndep R zero vadd smul vzero bs ∧
        (∀ a, a ∈ acc → a ∈ spanSet R V vadd smul vzero bs) ∧
        (∀ g, g ∈ gs → g ∈ spanSet R V vadd smul vzero bs) := by
    intro gs
    induction gs with
    | nil =>
      intro _ acc haccV haccI
      exact ⟨acc, haccV, haccI, fun a ha => subset_spanSet hM haccV ha,
        fun g hg => absurd hg List.not_mem_nil⟩
    | cons g rest ih =>
      intro hgsV acc haccV haccI
      have hgV : g ∈ V := hgsV g List.mem_cons_self
      have hrestV : ∀ x, x ∈ rest → x ∈ V :=
        fun x hx => hgsV x (List.mem_cons_of_mem _ hx)
      rcases hspanDec acc haccV g hgV with hin | hout
      · obtain ⟨bs, hbV, hbI, haccIn, hrestIn⟩ := ih hrestV acc haccV haccI
        refine ⟨bs, hbV, hbI, haccIn, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact spanSet_subset_spanSet hM hbV haccIn _ hin
        · exact hrestIn x hx'
      · have haccV' : ∀ a, a ∈ g :: acc → a ∈ V := by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha'
          · exact hgV
          · exact haccV a ha'
        have haccI' : IsIndep R zero vadd smul vzero (g :: acc) :=
          isIndep_cons hM hF hstab hgV haccV haccI hout
        obtain ⟨bs, hbV, hbI, haccIn', hrestIn⟩ := ih hrestV (g :: acc) haccV' haccI'
        refine ⟨bs, hbV, hbI,
          fun a ha => haccIn' a (List.mem_cons_of_mem _ ha), ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact haccIn' x List.mem_cons_self
        · exact hrestIn x hx'
  intro gs hgsV hspan
  obtain ⟨bs, hbV, hbI, -, hgsIn⟩ :=
    key gs hgsV [] (fun a ha => absurd ha List.not_mem_nil)
      (isIndep_nil R zero vadd smul vzero)
  refine ⟨bs, hbV, hbI, ?_⟩
  apply ext
  intro z
  constructor
  · intro hz
    exact spanSet_subset _ hz
  · intro hz
    -- NOT `rw [← hspan]`: that rewrites EVERY `V`, the carrier argument of the
    -- span on the right included, and then asks for
    -- `spanSet R (spanSet R V ..) .. bs`. Only the membership is rewritten.
    have hzg : z ∈ spanSet R V vadd smul vzero gs := by
      rw [hspan]; exact hz
    exact spanSet_subset_spanSet hM hbV hgsIn _ hzg

#print axioms basis_of_span


#print axioms isBasis_singleton_one
#print axioms dim_unique_of_exchange
#print axioms isSubmodule_spanSet
#print axioms spanSet_subset_spanSet
#print axioms isModule_submodule

/-- A combination is unchanged by cutting the operations down to a
submodule.

STRUCTURAL, not incidental. `IsModule` demands `domain vadd = prod W W`, so a
submodule carrier FORCES the restricted spelling that `isModule_submodule`
produces, while a span is most naturally stated in the operations it was formed
with. Neither is wrong and something has to cross.

`lincomb_restrictOp_sub` (GeomTower) is the ring version of this induction. The
head needs the ACTION's crossing (`opAt_restrictLeft`), the join needs the
ADDITION's (`opAt_restrictOp`), and the addition's needs the running combination
to have stayed inside `W`, which is `lincomb_mem_submodule`. Everything is about
elements already known to lie in `W`, where the two operations agree pointwise. -/
theorem lincomb_submodule
    {R add mul zero one V vadd vzero smul W : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul)
    (hW : IsSubmodule W R V vadd vzero smul) :
    ∀ cs vs : List ZFSet.{u}, (∀ c, c ∈ cs → c ∈ R) → (∀ v, v ∈ vs → v ∈ W) →
      lincomb (restrictOp vadd W) (restrictLeft smul R W) vzero cs vs
        = lincomb vadd smul vzero cs vs
  | [], vs, _, _ => by rw [lincomb_nil_left, lincomb_nil_left]
  | _ :: _, [], _, _ => by rw [lincomb_nil_right, lincomb_nil_right]
  | c :: cs, v :: vs, hcs, hvs => by
    have hc : c ∈ R := hcs c List.mem_cons_self
    have hv : v ∈ W := hvs v List.mem_cons_self
    have hcs' : ∀ x, x ∈ cs → x ∈ R := fun x hx => hcs x (List.mem_cons_of_mem _ hx)
    have hvs' : ∀ x, x ∈ vs → x ∈ W := fun x hx => hvs x (List.mem_cons_of_mem _ hx)
    have hdomS : ∀ x, x ∈ prod R W → x ∈ domain smul := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff x _ _).mp hx
      rw [hM.smulDom]
      exact opair_mem_prod ha (hW.sub _ hb)
    have hdomA : ∀ x, x ∈ prod W W → x ∈ domain vadd := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_prod_iff x _ _).mp hx
      rw [hM.group.dom]
      exact opair_mem_prod (hW.sub _ ha) (hW.sub _ hb)
    rw [lincomb_cons, lincomb_cons,
      opAt_restrictLeft hM.smulFun hdomS hW.smul_closed hc hv,
      lincomb_submodule hM hW cs vs hcs' hvs',
      opAt_restrictOp hM.group.isFun hdomA hW.add_closed
        (hW.smul_closed _ hc _ hv)
        (lincomb_mem_submodule hM hW cs vs hcs' hvs')]

#print axioms lincomb_submodule

/-- A ring is a module over itself. Every field is a ring axiom read at a
different name, and the two distributivity clauses are the ring's one clause
used twice -- once directly, once through commutativity.

What it buys: `spanSet R R add mul zero gs` is then the IDEAL generated by
`gs`, so finitely generated needs no new construction. -/
theorem isModule_self {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) :
    IsModule R add mul zero one R add zero mul where
  ring := hR
  group := hR.addGroup
  comm := hR.addComm
  smulFun := hR.mulFun
  smulDom := hR.mulDom
  smulRan := hR.mulRan
  smul_add := hR.distrib
  add_smul := by
    intro c hc d hd x hx
    rw [hR.mulComm _ (opAt_mem hR.addGroup hc hd) _ hx,
      hR.distrib _ hx _ hc _ hd, hR.mulComm _ hx _ hc, hR.mulComm _ hx _ hd]
  smul_smul := hR.mulAssoc
  one_smul := by
    intro x hx
    rw [hR.mulComm _ hR.mem_one _ hx]
    exact hR.mul_one _ hx

/-- Noetherian: every ideal is finitely generated. The generators are a
LIST -- data, not a cardinality claim -- and the ideal they generate is
`spanSet` with the ring acting on itself (`isModule_self`), so no new
construction is needed. -/
def IsNoetherian (R add mul zero : ZFSet.{u}) : Prop :=
  ∀ I, IsIdeal I R add mul zero →
    ∃ gs : List ZFSet.{u}, (∀ g, g ∈ gs → g ∈ I) ∧
      I = spanSet R R add mul zero gs

/-- Finite choice over `Nat`-indexed existentials, CONSTRUCTIVELY.

Given a witness for each `j` below `N`, assemble one matrix whose `j`-th column
is that witness. No `Classical.choice` is spent: the conclusion is an
existential, so each column is obtained INSIDE a proof rather than extracted
into data.

No `EM : Prop` argument lets you DEFINE data by cases, but ASSEMBLING data
inside an existential is free, since nothing escapes the proof. So a caller
needing a matrix as data -- `isIntegralOver_of_span_stable`, whose `A` is a
`Nat → Nat → ZFSet` -- can take its input from `IsNoetherian`, which says only
that coefficients exist.

Membership is carried in the conclusion: the columns past `N` carry no claim,
so a caller would otherwise patch them by hand and then reason about the patch. Padding with a member of `X` makes the
whole matrix land in `X` with nothing to case-split on. -/
theorem exists_matrix_of_forall_exists {P : Nat → (Nat → ZFSet.{u}) → Prop}
    {X d : ZFSet.{u}} (hd : d ∈ X) :
    ∀ N : Nat, (∀ j, j < N → ∃ f : Nat → ZFSet.{u}, (∀ i, f i ∈ X) ∧ P j f) →
      ∃ A : Nat → Nat → ZFSet.{u}, (∀ i j, A i j ∈ X) ∧
        ∀ j, j < N → P j (fun i => A i j)
  | 0, _ => ⟨fun _ _ => d, fun _ _ => hd, fun _ hj => absurd hj (by omega)⟩
  | N + 1, h => by
    obtain ⟨A, hAX, hA⟩ := exists_matrix_of_forall_exists hd N
      (fun j hj => h j (by omega))
    obtain ⟨f, hfX, hf⟩ := h N (by omega)
    refine ⟨fun i j => if j = N then f i else A i j, fun i j => ?_, fun j hj => ?_⟩
    · by_cases hjN : j = N
      · show (if j = N then f i else A i j) ∈ X
        rw [if_pos hjN]; exact hfX i
      · show (if j = N then f i else A i j) ∈ X
        rw [if_neg hjN]; exact hAX i j
    · by_cases hjN : j = N
      · subst hjN
        show P j (fun i => if j = j then f i else A i j)
        simpa only [if_pos rfl] using hf
      · show P j (fun i => if j = N then f i else A i j)
        have hcol : (fun i => if j = N then f i else A i j) = (fun i => A i j) := by
          funext i; rw [if_neg hjN]
        rw [hcol]
        exact hA j (by omega)

#print axioms exists_matrix_of_forall_exists

/-- A linear combination over LISTS is a fold over INDICES.

`lincomb` recurses on the head and `foldF` on the last index, so the two agree
only after the fold is re-associated -- which is `foldF_cons`. The
vector-valued version of exactly this is `coeff_lincomb`; this is the scalar
case, so a KERNEL VECTOR of a matrix reads as a vanishing combination. -/
theorem lincomb_eq_foldF {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) :
    ∀ (cs vs : List ZFSet.{u}) (k : Nat), cs.length = k → vs.length = k →
      (∀ c, c ∈ cs → c ∈ R) → (∀ v, v ∈ vs → v ∈ R) →
      lincomb add mul zero cs vs
        = foldF add zero
            (fun j => opAt mul (cs.getD j zero) (vs.getD j zero)) k
  | [], vs, k, hcl, _, _, _ => by
    obtain rfl : k = 0 := by rw [List.length_nil] at hcl; omega
    rw [lincomb_nil_left]
    rfl
  | c :: cs, [], k, _, hvl, _, _ => by
    obtain rfl : k = 0 := by rw [List.length_nil] at hvl; omega
    rw [lincomb_nil_right]
    rfl
  | c :: cs, v :: vs, k, hcl, hvl, hcm, hvm => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
      rw [List.length_cons] at hcl
      exact ⟨k - 1, by omega⟩
    have hcs' : ∀ x, x ∈ cs → x ∈ R := fun x hx => hcm x (List.mem_cons_of_mem _ hx)
    have hvs' : ∀ w, w ∈ vs → w ∈ R := fun w hw => hvm w (List.mem_cons_of_mem _ hw)
    rw [lincomb_cons,
      lincomb_eq_foldF hR cs vs k' (by rw [List.length_cons] at hcl; omega)
        (by rw [List.length_cons] at hvl; omega) hcs' hvs',
      foldF_cons (isCommMonoid_ringAdd hR) k' (fun j _ => mulAt_mem hR
        (by
          rcases Nat.decLt j (c :: cs).length with hge | hlt
          · rw [List.getD, List.getElem?_eq_none (by omega)]
            exact hR.addGroup.mem_e
          · rw [List.getD, List.getElem?_eq_getElem hlt]
            exact hcm _ (List.getElem_mem _))
        (by
          rcases Nat.decLt j (v :: vs).length with hge | hlt
          · rw [List.getD, List.getElem?_eq_none (by omega)]
            exact hR.addGroup.mem_e
          · rw [List.getD, List.getElem?_eq_getElem hlt]
            exact hvm _ (List.getElem_mem _)))]
    rfl

#print axioms lincomb_eq_foldF

/-- Span membership with a coefficient list of the RIGHT LENGTH.

`mem_spanSet_iff` promises coefficients but says nothing about how many:
`lincomb` pairs positionally and stops at the shorter list, so a witness may be
short or long. Every consumer that hands the coefficients to an indexed fold
needs the lengths to agree, and normalising them is `lincomb_append_zeros`
followed by `lincomb_take`. -/
theorem exists_coeffs_len_of_mem_spanSet {R add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul)
    {vs : List ZFSet.{u}} (hvs : ∀ v, v ∈ vs → v ∈ V)
    {w : ZFSet.{u}} (hw : w ∈ spanSet R V vadd smul vzero vs) :
    ∃ cs : List ZFSet.{u}, cs.length = vs.length ∧ (∀ c, c ∈ cs → c ∈ R) ∧
      w = lincomb vadd smul vzero cs vs := by
  obtain ⟨-, cs, hcs, rfl⟩ := mem_spanSet_iff.mp hw
  exact ⟨padTo cs zero vs.length, padTo_length cs zero vs.length,
    padTo_mem hM.ring.addGroup.mem_e hcs vs.length,
    (lincomb_padTo hM cs vs hcs hvs).symm⟩

#print axioms exists_coeffs_len_of_mem_spanSet

/-! ## A basis of a quotient

Splitting a basis of `V` as `cs ++ ds` makes the classes of `ds` a basis of
`V / span cs`. That is `dim(V/S) = dim V - dim S` in the form this tree states
dimension: a basis LIST, whose length is the dimension.

Both halves are stated over `spanSet` rather than over a basis of `S`, because
`IsBasis .. S` computes its span with `restrictOp`/`restrictLeft` and taking
`cs` as a basis in that sense would drag a restricted-operation reconciliation
through every step. The span over `V`'s own operations is what
`isSubmodule_spanSet` produces and what the consumer has.
-/

/-- A combination depends on the scalar action only through its VALUES.

Two actions agreeing on the coefficients and the vectors give the same
combination. `lincomb_restrictLeft_eq` is the `restrictLeft` instance of this;
stated generally it also carries a module's action across to an ambient
multiplication, which is what a subring's structure needs -- the module is over
`restrictLeft mul R S` while integrality speaks about `mul`. -/
theorem lincomb_smul_congr {R V vadd vzero smul smul' : ZFSet.{u}}
    (h : ∀ c, c ∈ R → ∀ x, x ∈ V → opAt smul c x = opAt smul' c x) :
    ∀ cs vs : List ZFSet.{u}, (∀ c, c ∈ cs → c ∈ R) → (∀ v, v ∈ vs → v ∈ V) →
      lincomb vadd smul vzero cs vs = lincomb vadd smul' vzero cs vs
  | [], vs, _, _ => by cases vs <;> rfl
  | _ :: _, [], _, _ => rfl
  | c :: cs, v :: vs, hcs, hvs => by
    show opAt vadd (opAt smul c v) (lincomb vadd smul vzero cs vs)
      = opAt vadd (opAt smul' c v) (lincomb vadd smul' vzero cs vs)
    rw [h c (hcs c (List.mem_cons_self ..)) v (hvs v (List.mem_cons_self ..)),
      lincomb_smul_congr h cs vs
        (fun x hx => hcs x (List.mem_cons_of_mem _ hx))
        (fun y hy => hvs y (List.mem_cons_of_mem _ hy))]

#print axioms lincomb_smul_congr


/-! ### `ACC` implies `IsNoetherian`, given a readout

The expensive direction, and the price is named rather than assumed. `ACC`
quantifies over a sequence and returns a bound; `IsNoetherian` must hand back a
LIST. Producing generators from a chain condition means asking, of a finite list
already inside the ideal, whether it spans -- and not yet in the span is
exactly the negative membership test this tower prices. -/

#print axioms isModule_self
#print axioms IsNoetherian
/-- A linear combination over two `below`-mapped lists is a fold over the
index.

`below n` descends and `foldF` ascends, so the two enumerate the same index set
in opposite orders -- and over a COMMUTATIVE monoid that is the whole
difference. `lincomb` peels the head, which is the TOP index; `foldF` peels the
last, which is also the top; so the induction lines up and one `comm` closes
each step.

Wanted whenever a combination is built by mapping over an index range rather
than by exhibiting a list, which is what `powerList` does -- and it is why
`powerList` is defined as `(below n).map` rather than by its own recursion: two
lists built from the SAME `below` zip index-by-index with nothing to reconcile. -/
theorem lincomb_map_below {M op e smul : ZFSet.{u}} (hM : IsCommMonoid M op e)
    {c v : Nat → ZFSet.{u}} (hmem : ∀ k, opAt smul (c k) (v k) ∈ M) :
    ∀ n : Nat, lincomb op smul e ((below n).map c) ((below n).map v)
      = foldF op e (fun k => opAt smul (c k) (v k)) n
  | 0 => rfl
  | n + 1 => by
    show opAt op (opAt smul (c n) (v n))
        (lincomb op smul e ((below n).map c) ((below n).map v))
      = opAt op (foldF op e (fun k => opAt smul (c k) (v k)) n)
          (opAt smul (c n) (v n))
    rw [lincomb_map_below hM hmem n]
    exact hM.comm _ (hmem n) _ (foldF_mem hM n (fun k _ => hmem k))

#print axioms lincomb_map_below

/-- The last coefficient of a tuple is its second component. -/
theorem tupleCoeff_last {v : ZFSet.{u}} (n : Nat) :
    tupleCoeff v (n + 1) n = snd v := by
  simp [tupleCoeff]

#print axioms tupleCoeff_last

/-- Below the last index, a tuple's coefficients are its first component's.
Stated here rather than in `LinAlg` or `HahnBanachModule`, which are siblings:
each had proved it because the other was unreachable. -/
theorem tupleCoeff_fst {v : ZFSet.{u}} {n i : Nat} (hi : i < n) :
    tupleCoeff v (n + 1) i = tupleCoeff (fst v) n i := by
  simp [tupleCoeff, Nat.ne_of_lt hi]

#print axioms tupleCoeff_fst

/-- The first component of a tuple one longer. -/
theorem fst_mem_powSet_succ {R v : ZFSet.{u}} {n : Nat}
    (hv : v ∈ powSet R (n + 1)) : fst v ∈ powSet R n :=
  fst_mem_of_mem_prod hv

#print axioms fst_mem_powSet_succ

theorem getD_append_of_lt_length {α : Type v} (dflt : α) :
    ∀ (s t : List α) (i : Nat), i < s.length →
      (s ++ t).getD i dflt = s.getD i dflt
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: s, t, i + 1, h =>
    getD_append_of_lt_length dflt s t i (Nat.lt_of_succ_lt_succ h)

#print axioms getD_append_of_lt_length


/-- Reading a list out of range gives the default, so a list whose members lie
in `X` has every `List.getD` in `X` provided the default does. -/
theorem getD_mem_of_mem {l : List ZFSet.{u}} {X d : ZFSet.{u}}
    (hl : ∀ x, x ∈ l → x ∈ X) (hd : d ∈ X) (i : Nat) : l.getD i d ∈ X := by
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.decLt i l.length with hge | hlt
  · rw [List.getElem?_eq_none (by omega)]
    exact hd
  · rw [List.getElem?_eq_getElem hlt]
    exact hl _ (List.getElem_mem _)

#print axioms getD_mem_of_mem


/-- `getD` on a list mapped over `below`.

The index is REVERSED: `below (n+1)` puts `n` first, so entry `k` is
`f (n - 1 - k)` and not `f k`. A caller assuming the straight order selects the
wrong element and the mistake type-checks.

Wanted for any family carried as `(below n).map f` -- the embedded zeta powers
that `spanSet_zeta_eq` is stated over are one, and
`isIntegralOver_of_stabilises_span` (`Integral` 1134) asks for
`gs.getD k zero ≠ zero`, which cannot be discharged without this readout. -/
theorem map_below_getD {f : Nat → ZFSet.{u}} {dflt : ZFSet.{u}} :
    ∀ (n k : Nat), k < n →
      ((below n).map f).getD k dflt = f (n - 1 - k)
  | 0, _, hk => absurd hk (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | n + 1, k + 1, hk => by
    show ((below n).map f).getD k dflt = f (n + 1 - 1 - (k + 1))
    rw [map_below_getD n k (by omega)]
    congr 1
    omega

#print axioms map_below_getD


/-- Two functions agreeing below `n` give the same `below`-map. -/
theorem map_below_congr {f g : Nat → ZFSet.{u}} :
    ∀ n : Nat, (∀ k, k < n → f k = g k) → (below n).map f = (below n).map g
  | 0, _ => rfl
  | n + 1, h => by
    show f n :: (below n).map f = g n :: (below n).map g
    rw [h n (by omega), map_below_congr n (fun k hk => h k (by omega))]

#print axioms map_below_congr

/-- A list is the `below`-map of its own entries, read in descending order.

The `rfl` at the end is not decoration: after the rewrites the goal is
`(a :: t).getD 0 dflt :: t = a :: t`, and `rw`'s trailing `rfl` runs at
reducible transparency and will not take `getD` on a literal cons. -/
theorem eq_map_below (dflt : ZFSet.{u}) :
    ∀ l : List ZFSet.{u},
      (below l.length).map (fun k => l.getD (l.length - 1 - k) dflt) = l
  | [] => rfl
  | a :: t => by
    show (a :: t).getD (t.length + 1 - 1 - t.length) dflt
        :: (below t.length).map (fun k => (a :: t).getD (t.length + 1 - 1 - k) dflt)
      = a :: t
    rw [show t.length + 1 - 1 - t.length = 0 by omega]
    -- every tail index is at least one, so the head is stepped over
    rw [map_below_congr (f := fun k => (a :: t).getD (t.length + 1 - 1 - k) dflt)
        (g := fun k => t.getD (t.length - 1 - k) dflt) t.length
      (fun k hk => by
        show (a :: t).getD (t.length - k) dflt = t.getD (t.length - 1 - k) dflt
        rw [show t.length - k = (t.length - 1 - k) + 1 by omega]
        rfl),
      eq_map_below dflt t]
    rfl

#print axioms eq_map_below




/-- A linear combination as a fold over the index, for a MODULE.

`lincomb_eq_foldF` is the RING version -- coefficients and vectors in one `R`,
joined by `mul`. This is the module case, with a separate action.

`lincomb_map_below` is close but takes both lists ALREADY in `(below n).map`
form. `Algebra.eq_map_below` puts them there, and its index map REVERSES --
`below 3 = [2,1,0]` -- so the fold lands on `n - 1 - k`. `foldF_reverse` is
what a caller wanting the straight index applies next.

Rewriting happens in the HYPOTHESIS, not the goal. This dialect has neither
`conv` nor `calc`, and rewriting `vs` in the goal would also hit the `vs.getD`
on the right-hand side, changing the shape being proved. The length is a
separate binder `n` for the same reason. -/
theorem lincomb_eq_foldF_module {M vadd vzero smul : ZFSet.{u}}
    (hM : IsCommMonoid M vadd vzero)
    {cs vs : List ZFSet.{u}} {n : Nat}
    (hcs : cs.length = n) (hvs : vs.length = n)
    (hmem : ∀ k, opAt smul (cs.getD (n - 1 - k) vzero)
      (vs.getD (n - 1 - k) vzero) ∈ M) :
    lincomb vadd smul vzero cs vs
      = foldF vadd vzero
          (fun k => opAt smul (cs.getD (n - 1 - k) vzero)
            (vs.getD (n - 1 - k) vzero)) n := by
  have h1 : (below n).map (fun k => cs.getD (n - 1 - k) vzero) = cs := by
    rw [← hcs]; exact eq_map_below vzero cs
  have h2 : (below n).map (fun k => vs.getD (n - 1 - k) vzero) = vs := by
    rw [← hvs]; exact eq_map_below vzero vs
  have key := lincomb_map_below hM
    (c := fun k => cs.getD (n - 1 - k) vzero)
    (v := fun k => vs.getD (n - 1 - k) vzero) hmem n
  rw [h1, h2] at key
  exact key

#print axioms lincomb_eq_foldF_module


/-- A scalar distributes over a finite module sum.
`IsModule` carries `smul_add` as the TWO-TERM case; this is the iterate, with
`smul_vzero` at the base. -/
theorem smul_foldF {R add mul zero one V vadd vzero smul c : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (hc : c ∈ R)
    {F : Nat → ZFSet.{u}} :
    ∀ n : Nat, (∀ i, i < n → F i ∈ V) →
      opAt smul c (foldF vadd vzero F n)
        = foldF vadd vzero (fun i => opAt smul c (F i)) n
  | 0, _ => smul_vzero hM hc
  | n + 1, hF => by
    have hlow : ∀ i, i < n → F i ∈ V := fun i hi => hF i (by omega)
    show opAt smul c (opAt vadd (foldF vadd vzero F n) (F n))
      = opAt vadd (foldF vadd vzero (fun i => opAt smul c (F i)) n)
          (opAt smul c (F n))
    rw [hM.smul_add c hc _ (foldF_mem (isCommMonoid_of_isGroup hM.group hM.comm)
        n (fun i hi => hlow i hi)) _ (hF n (by omega)),
      smul_foldF hM hc n hlow]

#print axioms smul_foldF

/-- A sum of scalars acting on one vector -- the mirror of
`Algebra.smul_foldF`. `add_smul` is its two-term case, equally un-iterated. The
base case is a DIFFERENT lemma, `zero_smul`: the zero SCALAR on a vector rather
than a scalar on the zero vector. -/
theorem foldF_smul_left {R add mul zero one V vadd vzero smul v : ZFSet.{u}}
    (hM : IsModule R add mul zero one V vadd vzero smul) (hv : v ∈ V)
    {C : Nat → ZFSet.{u}} :
    ∀ n : Nat, (∀ i, i < n → C i ∈ R) →
      opAt smul (foldF add zero C n) v
        = foldF vadd vzero (fun i => opAt smul (C i) v) n
  | 0, _ => zero_smul hM hv
  | n + 1, hC => by
    have hlow : ∀ i, i < n → C i ∈ R := fun i hi => hC i (by omega)
    show opAt smul (opAt add (foldF add zero C n) (C n)) v
      = opAt vadd (foldF vadd vzero (fun i => opAt smul (C i) v) n)
          (opAt smul (C n) v)
    rw [hM.add_smul _ (foldF_mem (isCommMonoid_ringAdd hM.ring) n
        (fun i hi => hlow i hi)) _ (hC n (by omega)) _ hv,
      foldF_smul_left hM hv n hlow]

#print axioms foldF_smul_left


/-- The coordinate matrices of two bases multiply to the identity --
C3c-i-5g's last obligation, and exactly `matTrace_conj`'s (`IdealCount` 5310)
`hinv`.

    v j  =  Σ_k Q k j · w k                   (Q represents)
         =  Σ_k Q k j · (Σ_i P i k · v i)     (P represents)
         =  Σ_i (Σ_k P i k * Q k j) · v i     (distribute, exchange)

and `v j = Σ_i δ_ij · v i` trivially, so uniqueness of the coefficients against
`v` forces `P * Q = I`.

Uniqueness is a HYPOTHESIS in family form, not derived from `IsIndep` here.
`IsIndep` quantifies over coefficient LISTS while every fold here is indexed by
a `Nat → ZFSet` family, and the conversion carries `below`'s reversal. Keeping
it out leaves two tractable pieces instead of one long one.

`w` needs no membership: the proof rewrites it away through its own
representation before anything is asked of it. -/
theorem coordMat_mul_eq_id
    {K add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule K add mul zero one V vadd vzero smul)
    {v w : Nat → ZFSet.{u}} {n : Nat}
    (hv : ∀ i, i < n → v i ∈ V)
    {P Q : Nat → Nat → ZFSet.{u}}
    (hP : ∀ i j, P i j ∈ K) (hQ : ∀ i j, Q i j ∈ K)
    (hPrep : ∀ k, k < n →
      w k = foldF vadd vzero (fun i => opAt smul (P i k) (v i)) n)
    (hQrep : ∀ j, j < n →
      v j = foldF vadd vzero (fun k => opAt smul (Q k j) (w k)) n)
    (huniq : ∀ C D : Nat → ZFSet.{u},
      (∀ i, i < n → C i ∈ K) → (∀ i, i < n → D i ∈ K) →
      foldF vadd vzero (fun i => opAt smul (C i) (v i)) n
        = foldF vadd vzero (fun i => opAt smul (D i) (v i)) n →
      ∀ i, i < n → C i = D i) :
    ∀ i j, i < n → j < n →
      matMulOn add mul zero P Q n i j = idMat zero one i j := by
  have hcmV : IsCommMonoid V vadd vzero :=
    isCommMonoid_of_isGroup hM.group hM.comm
  intro i j hi hj
  refine huniq (fun i' => matMulOn add mul zero P Q n i' j)
    (fun i' => idMat zero one i' j) ?_ ?_ ?_ i hi
  · intro i' _
    exact foldF_mem (isCommMonoid_ringAdd hM.ring) n
      (fun k _ => mulAt_mem hM.ring (hP i' k) (hQ k j))
  · intro i' _
    show (if i' = j then one else zero) ∈ K
    by_cases hij : i' = j
    · rw [if_pos hij]; exact hM.ring.mem_one
    · rw [if_neg hij]; exact hM.ring.addGroup.mem_e
  -- both sides are `v j`
  · have hRHS : foldF vadd vzero
        (fun i' => opAt smul (idMat zero one i' j) (v i')) n = v j := by
      refine (foldF_single_below_monoid hcmV
        (T := fun i' => opAt smul (idMat zero one i' j) (v i'))
        (k := j) ?_ n hj ?_).trans ?_
      · show opAt smul (if j = j then one else zero) (v j) ∈ V
        rw [if_pos rfl]
        exact smulAt_mem hM hM.ring.mem_one (hv j hj)
      · intro i' _ hne
        show opAt smul (if i' = j then one else zero) (v i') = vzero
        rw [if_neg hne]
        exact zero_smul hM (hv i' (by omega))
      · show opAt smul (if j = j then one else zero) (v j) = v j
        rw [if_pos rfl]
        exact hM.one_smul _ (hv j hj)
    rw [hRHS]
    -- and the left side unwinds to `v j` through the two representations
    have hstep : foldF vadd vzero
        (fun i' => opAt smul (matMulOn add mul zero P Q n i' j) (v i')) n
      = foldF vadd vzero
          (fun k => opAt smul (Q k j) (w k)) n := by
      have hL : ∀ i', i' < n →
          opAt smul (matMulOn add mul zero P Q n i' j) (v i')
            = foldF vadd vzero
                (fun k => opAt smul (Q k j) (opAt smul (P i' k) (v i'))) n := by
        intro i' hi'
        show opAt smul (foldF add zero
          (fun k => opAt mul (P i' k) (Q k j)) n) (v i') = _
        rw [foldF_smul_left hM (hv i' hi')
          (C := fun k => opAt mul (P i' k) (Q k j)) n
          (fun k _ => mulAt_mem hM.ring (hP i' k) (hQ k j))]
        refine foldF_congr n (fun k _ => ?_)
        rw [hM.ring.mulComm _ (hP i' k) _ (hQ k j),
          hM.smul_smul _ (hQ k j) _ (hP i' k) _ (hv i' hi')]
      rw [foldF_congr n hL,
        foldF_swap hcmV n n
          (fun i' k hi' hk => smulAt_mem hM (hQ k j)
            (smulAt_mem hM (hP i' k) (hv i' hi')))]
      refine foldF_congr n (fun k hk => ?_)
      rw [← smul_foldF hM (hQ k j)
        (F := fun i' => opAt smul (P i' k) (v i')) n
        (fun i' hi' => smulAt_mem hM (hP i' k) (hv i' hi')), ← hPrep k hk]
    rw [hstep, ← hQrep j hj]

#print axioms coordMat_mul_eq_id

/-- Coordinate uniqueness, in FAMILY form.

`lincomb_injective` (`Module` 295) supplies it about coefficient LISTS;
`Algebra.coordMat_mul_eq_id` wants it about `Nat → ZFSet` families. This is the
conversion, and it is where `below`'s reversal is paid.

The list is built with the index ALREADY REVERSED.
`Algebra.lincomb_eq_foldF_module` reads a combination as a fold over `n - 1 - k`,
and `Algebra.map_below_getD` reads `(below n).map f` at `m` as `f (n - 1 - m)`.
Composing them naively leaves a reversal on the coefficients; taking the list as
`(below n).map (fun m => C (n - 1 - m))` makes the two CANCEL, so the fold comes
out on the straight index and `getD` at `i` is `C i`. -/
theorem coord_uniq_family
    {K add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule K add mul zero one V vadd vzero smul)
    {vs : List ZFSet.{u}} (hvm : ∀ v, v ∈ vs → v ∈ V)
    (hindep : IsIndep K zero vadd smul vzero vs)
    {n : Nat} (hlen : vs.length = n) :
    ∀ C D : Nat → ZFSet.{u},
      (∀ i, i < n → C i ∈ K) → (∀ i, i < n → D i ∈ K) →
      foldF vadd vzero (fun i => opAt smul (C i) (vs.getD i vzero)) n
        = foldF vadd vzero (fun i => opAt smul (D i) (vs.getD i vzero)) n →
      ∀ i, i < n → C i = D i := by
  have hcm : IsCommMonoid V vadd vzero :=
    isCommMonoid_of_isGroup hM.group hM.comm
  intro C D hC hD heq i hi
  -- the reversed list, so the two reversals cancel
  have hfold : ∀ E : Nat → ZFSet.{u}, (∀ k, k < n → E k ∈ K) →
      lincomb vadd smul vzero ((below n).map (fun m => E (n - 1 - m))) vs
        = foldF vadd vzero (fun k => opAt smul (E k) (vs.getD k vzero)) n := by
    intro E hE
    have hElen : ((below n).map (fun m => E (n - 1 - m))).length = n := by
      rw [List.length_map, length_below]
    have hmem : ∀ k, opAt smul
        (((below n).map (fun m => E (n - 1 - m))).getD (n - 1 - k) vzero)
        (vs.getD (n - 1 - k) vzero) ∈ V := by
      intro k
      rcases Nat.lt_or_ge (n - 1 - k) n with hk | hk
      · rw [map_below_getD n (n - 1 - k) hk]
        exact smulAt_mem hM (hE _ (by omega))
          (getD_mem_of_mem hvm hM.group.mem_e _)
      · exact absurd hk (by omega)
    rw [lincomb_eq_foldF_module hcm hElen hlen hmem]
    refine (foldF_congr n (fun k hk => ?_)).trans
      (foldF_reverse hcm n (fun k hk => smulAt_mem hM (hE k hk)
        (getD_mem_of_mem hvm hM.group.mem_e k))).symm
    rw [map_below_getD n (n - 1 - k) (by omega)]
    congr 2
    omega
  have hlists := lincomb_injective hM hvm hindep
    ((below n).map (fun m => C (n - 1 - m)))
    ((below n).map (fun m => D (n - 1 - m)))
    (by rw [List.length_map, length_below, hlen])
    (by rw [List.length_map, length_below, hlen])
    (fun c hc => by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hc
      exact hC _ (by have := mem_below.mp hm; omega))
    (fun d hd => by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hd
      exact hD _ (by have := mem_below.mp hm; omega))
    ((hfold C hC).trans (heq.trans (hfold D hD).symm))
  -- read at `i` itself: the list's own reversal already cancelled the map's,
  -- so `getD` at `i` IS `C i`
  have := congrArg (fun l => List.getD l i vzero) hlists
  simp only [] at this
  rw [map_below_getD n i hi, map_below_getD n i hi] at this
  have hii : n - 1 - (n - 1 - i) = i := by omega
  rw [hii] at this
  exact this

#print axioms coord_uniq_family


/-- `getD`'s default is unreachable below the length, so any two defaults
agree there.

Not a convenience. `lincomb_eq_foldF_module` writes the COEFFICIENT list's
default as `vzero`, and `∀ i, f i ∈ K` forces `zero` --- `vzero` lives in `V`.
The two terms are equal at every index a fold of length `bs.length` visits and
unequal past it, so nothing definitional bridges them and `rw` spins.

`getD_mem` (TowerLaw.lean) proves its own statement this way and fixes the
default to `empty`; this is the same three rewrites with the default free. -/
theorem getD_default_agree {l : List ZFSet.{u}} {i : Nat} (hi : i < l.length)
    (d e : ZFSet.{u}) : l.getD i d = l.getD i e := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl


/-- A basis coordinate column, at the DIRECT index.

`spanCoeffs_of_isBasis` gives a coefficient LIST and `lincomb_eq_foldF_module`
turns it into a fold whose index is REVERSED --- `cs.getD (n-1-k)` paired with
`vs.getD (n-1-k)`. `coordMat_mul_eq_id` consumes `fun i => opAt smul (P i k)
(v i)`, direct. This is the bridge, and it is obligation 1b of the determinant
route: the same pairing, enumerated the other way, which `foldF_reverse` settles
because `V` under `vadd` is a commutative monoid.

Stated as an EXISTENTIAL over a function rather than over a list, because
`exists_matrix_of_forall_exists` wants exactly that shape per column and cannot
consume a `List`. -/
theorem exists_coordColumn {K add mul zero one V vadd vzero smul x : ZFSet.{u}}
    (hM : IsModule K add mul zero one V vadd vzero smul)
    {vs : List ZFSet.{u}} (hb : IsBasis K zero V vadd vzero smul vs)
    (hx : x ∈ V) :
    ∃ f : Nat → ZFSet.{u}, (∀ i, f i ∈ K) ∧
      x = foldF vadd vzero
        (fun i => opAt smul (f i) (vs.getD i vzero)) vs.length := by
  obtain ⟨bs, hlen, hmem, heq⟩ := spanCoeffs_of_isBasis hM hb x hx
  have hcm : IsCommMonoid V vadd vzero := isCommMonoid_of_isGroup hM.group hM.comm
  have hvm : ∀ v, v ∈ vs → v ∈ V := hb.left
  refine ⟨fun i => bs.getD i zero, fun i => getD_mem_of_mem hmem hM.ring.addGroup.mem_e i, ?_⟩
  -- THE EMPTY BASIS IS A REAL CASE, not a formality. `lincomb_eq_foldF_module`
  -- wants its membership at EVERY `k`, and the reversed index `n - 1 - k` is
  -- below `n` only when `n > 0` --- at `n = 0` Nat subtraction pins it to `0`,
  -- where `bs` is empty and the `vzero` default escapes `K`. So the zero-length
  -- basis is discharged first and separately, on `foldF _ _ _ 0 = vzero`.
  rcases Nat.eq_zero_or_pos vs.length with h0 | hpos
  · rw [h0] at hlen ⊢
    rw [heq, List.length_eq_zero_iff.mp hlen, List.length_eq_zero_iff.mp h0]
    rfl
  have hterm : ∀ k, opAt smul (bs.getD (vs.length - 1 - k) vzero)
      (vs.getD (vs.length - 1 - k) vzero) ∈ V := by
    intro k
    have hlt : vs.length - 1 - k < vs.length := by omega
    refine smulAt_mem hM ?_ (getD_mem_of_mem hvm hM.group.mem_e _)
    rw [← getD_default_agree (l := bs) (i := vs.length - 1 - k) (by omega) zero vzero]
    exact getD_mem_of_mem hmem hM.ring.addGroup.mem_e _
  have hdir : ∀ i, i < vs.length →
      opAt smul (bs.getD i vzero) (vs.getD i vzero) ∈ V := by
    intro i hi
    refine smulAt_mem hM ?_ (getD_mem_of_mem hvm hM.group.mem_e i)
    rw [← getD_default_agree (l := bs) (i := i) (by omega) zero vzero]
    exact getD_mem_of_mem hmem hM.ring.addGroup.mem_e i
  rw [heq, lincomb_eq_foldF_module hcm hlen rfl hterm]
  rw [(foldF_reverse hcm vs.length (fun i hi => hdir i hi)).symm]
  -- `show` BEFORE `rw`: the goal carries an unreduced `(fun i => bs.getD i zero) i`
  -- and `rw` matches syntactically, so it cannot see the redex. Stating the
  -- beta-reduced form is what puts the pattern where the rewrite can find it.
  exact (foldF_congr vs.length (fun i hi => by
    show opAt smul (bs.getD i zero) (vs.getD i vzero)
      = opAt smul (bs.getD i vzero) (vs.getD i vzero)
    rw [getD_default_agree (l := bs) (i := i) (by omega) zero vzero])).symm


/-- A coordinate matrix at an ARBITRARY column count.

This is the lemma the determinant route needed and could not get.
`exists_coordMat_of_isBasis` indexes EVERYTHING by the basis's own length, so
applied to the shorter basis it constrains `j < vs.length` and cannot reach the
longer one's columns. Here the width `N` is free: `exists_coordColumn` supplies
one column per `j`, and `exists_matrix_of_forall_exists` turns a per-column
existential into a matrix by recursion on `N` --- finite choice, no principle.

Obligation 1b of `dim_unique_of_detN`. `Q` for the longer basis expressed in the
shorter one is exactly this at `N := us.length`, `vs := vs`. -/
theorem exists_coordMat_wide {K add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule K add mul zero one V vadd vzero smul)
    {vs : List ZFSet.{u}} (hb : IsBasis K zero V vadd vzero smul vs)
    {w : Nat → ZFSet.{u}} {N : Nat} (hw : ∀ j, j < N → w j ∈ V) :
    ∃ Q : Nat → Nat → ZFSet.{u}, (∀ i j, Q i j ∈ K) ∧
      ∀ j, j < N → w j = foldF vadd vzero
        (fun i => opAt smul (Q i j) (vs.getD i vzero)) vs.length :=
  exists_matrix_of_forall_exists (X := K) (d := zero) hM.ring.addGroup.mem_e N
    (fun j hj => exists_coordColumn hM hb (hw j hj))


/-- A fold extends past its range when the added terms are the identity.

DUPLICATED DELIBERATELY. The same lemma is proved in the TREE's
`ProbeDimUnique.lean`; a mirror probe cannot see a tree probe, and the two
worktrees elaborate independently. Only ONE of them lands --- when this goes into
the library it goes in once, and the other probe cites it.

`foldF_extend` (PolyRing.lean) is the RING version; the module carrier is a
commutative monoid without being a ring's additive group by that route. -/
theorem foldF_extend_monoid {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e)
    {F : Nat → ZFSet.{u}} (hF : ∀ i, F i ∈ M) (m d : Nat)
    (hz : ∀ i, i < d → F (m + i) = e) :
    foldF op e F (m + d) = foldF op e F m := by
  -- `foldF_split` was GENERALISED upstream 2026-08-28: its membership
  -- hypothesis moved from an unbounded first argument to a BOUNDED last one,
  -- `∀ i, i < a + b → F i ∈ M`. Strictly the better lemma, and it breaks every
  -- caller written against the old shape --- this call is updated to match.
  rw [foldF_split hM m d (fun i _ => hF i), foldF_zeros_monoid hM d hz,
    right_id_monoid hM (foldF_mem hM m (fun i _ => hF i))]


/-- The padded fold at the longer length equals the plain fold at the shorter.

The last bridge of obligation 1c, and it joins the two lemmas that could not meet
directly: `exists_coordMat_wide` produces a fold over `vs.length` against
`vs.getD`, while `coordMat_mul_eq_id` consumes one over `us.length` against the
PADDED family. Two steps, in this order:

  `foldF_extend_monoid`  drops `m` to `vs.length`, the discarded terms being
                         `opAt smul (Q k) vzero`, each `vzero` by `smul_vzero`
  `foldF_congr`          rewrites the padding away BELOW the cut, where
                         `vzeroPadP_lt` says it is the list entry

Note the order: extend first, congr second. Doing it the other way asks
`foldF_congr` for a pointwise equality at indices where the padding is `vzero`
and the list entry does not exist, which is false. -/
theorem foldF_pad_to_short {K add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule K add mul zero one V vadd vzero smul)
    {vs : List ZFSet.{u}} (hvm : ∀ v, v ∈ vs → v ∈ V)
    {Q : Nat → ZFSet.{u}} (hQ : ∀ k, Q k ∈ K) {m : Nat} (hle : vs.length ≤ m) :
    foldF vadd vzero
        (fun k => opAt smul (Q k)
          (if k < vs.length then vs.getD k vzero else vzero)) m
      = foldF vadd vzero
        (fun k => opAt smul (Q k) (vs.getD k vzero)) vs.length := by
  -- THE PADDING IS INLINED, not `vzeroPadP`. Writing the `if` directly keeps
  -- this lemma self-contained, and the named definition is not coming: the
  -- mirror probe holding it was rescued and then declined, so no second
  -- definition of the padding is pending anywhere.
  have hcm : IsCommMonoid V vadd vzero := isCommMonoid_of_isGroup hM.group hM.comm
  have hpad : ∀ k, (if k < vs.length then vs.getD k vzero else vzero) ∈ V := by
    intro k
    by_cases h : k < vs.length
    · rw [if_pos h]; exact getD_mem_of_mem hvm hM.group.mem_e k
    · rw [if_neg h]; exact hM.group.mem_e
  have hmem : ∀ k, opAt smul (Q k)
      (if k < vs.length then vs.getD k vzero else vzero) ∈ V :=
    fun k => smulAt_mem hM (hQ k) (hpad k)
  obtain ⟨d, hd⟩ : ∃ d, m = vs.length + d := ⟨m - vs.length, by omega⟩
  subst hd
  rw [foldF_extend_monoid hcm hmem vs.length d (fun i _ => by
    rw [if_neg (by omega)]
    exact smul_vzero hM (hQ _))]
  exact foldF_congr vs.length (fun i hi => by
    show opAt smul (Q i) (if i < vs.length then vs.getD i vzero else vzero)
      = opAt smul (Q i) (vs.getD i vzero)
    rw [if_pos hi])


/-- Truncating a matrix's rows above a cut leaves the padded fold unchanged.

`exists_coordMat_wide` hands back an OPAQUE `Q`; the determinant argument needs
one whose rows vanish above `vs.length`, because that zero row is what
`detN_row_zero` consumes. Truncation is free here: above the cut the padded
family is `vzero`, so the term is `opAt smul _ vzero = vzero` whatever the
coefficient was, and both matrices give the same fold. -/
theorem foldF_pad_truncate {K add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule K add mul zero one V vadd vzero smul)
    {vs : List ZFSet.{u}} {Q : Nat → ZFSet.{u}} (hQ : ∀ k, Q k ∈ K) (m : Nat) :
    foldF vadd vzero
        (fun k => opAt smul (if k < vs.length then Q k else zero)
          (if k < vs.length then vs.getD k vzero else vzero)) m
      = foldF vadd vzero
        (fun k => opAt smul (Q k)
          (if k < vs.length then vs.getD k vzero else vzero)) m :=
  foldF_congr m (fun i _ => by
    by_cases h : i < vs.length
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, smul_vzero hM hM.ring.addGroup.mem_e,
        smul_vzero hM (hQ i)])


/-- Two bases of different lengths give an identity with a zero row.

The assembly, and the whole determinant argument minus the determinants. Both
matrices come from `exists_coordMat_wide` --- `P` expressing the PADDED shorter
basis in the longer one, `Q` expressing the longer in the shorter --- and the
instantiation is at `us`, the LONGER basis, because `coord_uniq_family` supplies
uniqueness for a BASIS and the padded family is not one.

`Q` is truncated above the cut afterwards rather than chosen that way: the
existential hands back an opaque matrix, and `foldF_pad_truncate` says the
truncation costs nothing because the padded family is `vzero` there. -/
theorem exists_coordPair_of_lt {K add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule K add mul zero one V vadd vzero smul)
    {vs us : List ZFSet.{u}}
    (hvs : IsBasis K zero V vadd vzero smul vs)
    (hus : IsBasis K zero V vadd vzero smul us)
    (hlt : vs.length < us.length) :
    ∃ P Q : Nat → Nat → ZFSet.{u},
      (∀ i j, P i j ∈ K) ∧ (∀ i j, Q i j ∈ K) ∧
      (∀ k j, vs.length ≤ k → Q k j = zero) ∧
      ∀ i j, i < us.length → j < us.length →
        matMulOn add mul zero P Q us.length i j = idMat zero one i j := by
  have hvmU : ∀ v, v ∈ us → v ∈ V := hus.left
  have hvmV : ∀ v, v ∈ vs → v ∈ V := hvs.left
  -- The padded family is written out at each use, which is also the form the
  -- fold lemmas take.
  have hpadV : ∀ k, (if k < vs.length then vs.getD k vzero else vzero) ∈ V := by
    intro k
    by_cases h : k < vs.length
    · rw [if_pos h]; exact getD_mem_of_mem hvmV hM.group.mem_e k
    · rw [if_neg h]; exact hM.group.mem_e
  -- P: the padded SHORTER basis, expressed in the longer one.
  obtain ⟨P, hP, hPrep⟩ :=
    exists_coordMat_wide hM hus (w := fun k => if k < vs.length then vs.getD k vzero else vzero)
      (N := us.length) (fun j _ => hpadV j)
  -- Q0: the LONGER basis, expressed in the shorter one, at width us.length ---
  -- which is exactly the indexing `exists_coordMat_of_isBasis` cannot reach.
  obtain ⟨Q0, hQ0, hQ0rep⟩ :=
    exists_coordMat_wide hM hvs (w := fun j => us.getD j vzero) (N := us.length)
      (fun j _ => getD_mem_of_mem hvmU hM.group.mem_e j)
  have hQt : ∀ i j, (if i < vs.length then Q0 i j else zero) ∈ K := by
    intro i j
    by_cases h : i < vs.length
    · rw [if_pos h]; exact hQ0 i j
    · rw [if_neg h]; exact hM.ring.addGroup.mem_e
  refine ⟨P, fun k j => if k < vs.length then Q0 k j else zero, hP, ?_, ?_, ?_⟩
  · exact fun i j => hQt i j
  · intro k j hk
    show (if k < vs.length then Q0 k j else zero) = zero
    rw [if_neg (by omega)]
  · refine coordMat_mul_eq_id hM (v := fun i => us.getD i vzero)
      (w := fun k => if k < vs.length then vs.getD k vzero else vzero)
      (fun i _ => getD_mem_of_mem hvmU hM.group.mem_e i) hP ?_ hPrep ?_ ?_
    · exact fun i j => hQt i j
    · intro j hj
      -- `show` first: the goal carries two unreduced redexes, one from `v` and
      -- one from `w`, and both rewrites below match syntactically.
      show us.getD j vzero = foldF vadd vzero
        (fun k => opAt smul (if k < vs.length then Q0 k j else zero)
          (if k < vs.length then vs.getD k vzero else vzero)) us.length
      rw [foldF_pad_truncate hM (Q := fun k => Q0 k j) (fun k => hQ0 k j) us.length,
        foldF_pad_to_short hM hvmV (Q := fun k => Q0 k j) (fun k => hQ0 k j)
          (Nat.le_of_lt hlt)]
      exact hQ0rep j hj
    · exact coord_uniq_family hM hus.left hus.right.left rfl


/-- Two bases of DIFFERENT lengths force `one = zero`.

The determinant half, and the point of the whole route: no decidability anywhere.
`P * Q = I` at the longer length `m`, so `det P * det Q = one`; but `Q`'s rows
vanish above `vs.length`, so `detN_row_zero` makes `det Q = zero` and the product
collapses. `detN_congr_lt` is what lets the pointwise identity --- which holds
only BELOW `m` --- be used under a determinant computed from the whole matrix. -/
theorem one_eq_zero_of_basis_length_lt
    {K add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule K add mul zero one V vadd vzero smul)
    {vs us : List ZFSet.{u}}
    (hvs : IsBasis K zero V vadd vzero smul vs)
    (hus : IsBasis K zero V vadd vzero smul us)
    (hlt : vs.length < us.length) :
    one = zero := by
  obtain ⟨P, Q, hP, hQ, hQz, hid⟩ := exists_coordPair_of_lt hM hvs hus hlt
  have hR : IsRing K add mul zero one := hM.ring
  have hpos : 0 < us.length := by omega
  -- the product's determinant is `one`, through the pointwise identity
  have h1 : detN K add mul zero one (matMulOn add mul zero P Q us.length) us.length
      = one := by
    rw [detN_congr_lt us.length (fun i m hi hm => hid i m hi hm)]
    exact detN_idMat hR us.length
  -- and it factors
  have h2 : detN K add mul zero one (matMulOn add mul zero P Q us.length) us.length
      = opAt mul (detN K add mul zero one P us.length)
        (detN K add mul zero one Q us.length) :=
    detN_mul hR hP hQ hpos
  -- `Q`'s row at `vs.length` is zero, and `vs.length + d + 1 = us.length`
  obtain ⟨d, hd⟩ : ∃ d, us.length = vs.length + d + 1 :=
    ⟨us.length - vs.length - 1, by omega⟩
  have h3 : detN K add mul zero one Q us.length = zero := by
    rw [hd]
    exact detN_row_zero hR vs.length d hQ (fun m => hQz vs.length m (Nat.le_refl _))
  -- `mul_zero_of_isRing`, found by STATEMENT. `ringMul_zero` does not exist ---
  -- the tree has `ringZero_mul` for the other side --- and the name has a
  -- sibling `mul_zero_of_isRingNC` over another encoding, which is the pair a
  -- name search picks wrongly between.
  rw [h2, h3, mul_zero_of_isRing hR (detN_mem hR hP us.length)] at h1
  exact h1.symm


/-- Two bases of a module over a field have the same length --- with NO
decidability hypothesis.

`dim_unique_of_exchange` takes `DecidableVanishing K zero`, spent at ONE line of
`exchange_le` deciding whether a coefficient vanishes in order to pivot. The
statement never needed it: `IsIndep` is a universally quantified implication with
no decision in it, so what was expensive was the argument. This is the argument
that does not pay.

It is also not `dim_unique`, which is free but wants the ring FINITE
(`Equinumerous R (ofNat q)`, counting the module as `q ^ length`). Neither
dominates the other; this one covers an INFINITE field, which is where `RealL`
lives and where the degree row's `refined` witness sits.

The `Nat` trichotomy is decidable arithmetic and costs nothing. -/
theorem dim_unique_of_detN {K add mul zero one V vadd vzero smul : ZFSet.{u}}
    (hM : IsModule K add mul zero one V vadd vzero smul)
    (hF : IsField K add mul zero one)
    {vs us : List ZFSet.{u}}
    (hvs : IsBasis K zero V vadd vzero smul vs)
    (hus : IsBasis K zero V vadd vzero smul us) :
    vs.length = us.length := by
  rcases Nat.lt_trichotomy vs.length us.length with h | h | h
  · exact absurd (one_eq_zero_of_basis_length_lt hM hvs hus h) (Ne.symm hF.zero_ne_one)
  · exact h
  · exact absurd (one_eq_zero_of_basis_length_lt hM hus hvs h) (Ne.symm hF.zero_ne_one)

#print axioms getD_default_agree
#print axioms exists_coordColumn
#print axioms exists_coordMat_wide
#print axioms foldF_extend_monoid
#print axioms foldF_pad_to_short
#print axioms foldF_pad_truncate
#print axioms exists_coordPair_of_lt
#print axioms one_eq_zero_of_basis_length_lt
#print axioms dim_unique_of_detN

-- Shifting a witness by `X^s` moves its top coefficient from index `d` to
-- index `d + s`, unchanged, so the SAME generators serve at every index past
-- `N`: the coefficient ideal has stopped growing, so the coefficients still
-- span, and the polynomials witnessing them need only be shifted to have the
-- right bound.
end Algebra


namespace ZFSet
export Algebra (IsBasis IsIndep IsModule IsNoetherian IsSubmodule all_zero_or_exists_ne coordMat_mul_eq_id coord_uniq_family dim_unique dim_unique_of_detN dim_unique_of_exchange eq_map_below equinumerous_spanSet equinumerous_spanSet_card exchange_le exists_basis exists_coeffs_len_of_mem_spanSet exists_cons_of_length exists_coordColumn exists_coordMat_wide exists_coordPair_of_lt exists_matrix_of_forall_exists exists_span_pairs exists_tuple_of_list foldF_extend_monoid foldF_pad_to_short foldF_pad_truncate foldF_smul_left fst_mem_powSet_succ getD_append_of_lt_length getD_default_agree getD_mem_of_mem ginv_vzero isBasis_singleton_one isIndep_cons isIndep_nil isIndep_perm isModule_of_subring isModule_self isModule_submodule isSubmodule_spanSet lincomb lincombP lincombP_mem lincombP_perm lincomb_add lincomb_append lincomb_append_zeros lincomb_cons lincomb_eq_foldF lincomb_eq_foldF_module lincomb_eq_lincombP lincomb_ginv lincomb_injective lincomb_map_below lincomb_map_split lincomb_mem lincomb_mem_submodule lincomb_nil_left lincomb_nil_right lincomb_padTo lincomb_smul lincomb_smul_congr lincomb_take lincomb_zeros lincomb_zipWith_add lincomb_zipWith_sub map_below_congr map_below_getD mem_spanSet_cons_iff mem_spanSet_iff neg_one_smul one_eq_zero_of_basis_length_lt padTo padTo_length padTo_mem perm_zip_exists smulAt_mem smul_foldF smul_vzero spanCoeffs_of_isBasis spanSet spanSet_eq_or_exists_outside spanSet_exchange spanSet_subset spanSet_subset_spanSet subset_spanSet tupleCoeff_fst tupleCoeff_last tupleToList tupleToList_getElem tupleToList_inj tupleToList_length tupleToList_mem two_le_card_of_isField vaddAt_mem vadd_right_cancel vadd_shuffle_pair zero_smul zipWith_sub_mem)
end ZFSet
