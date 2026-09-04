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

open NumberTheory SetTheory
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

#print axioms zero_smul
#print axioms lincomb_add
#print axioms exists_cons_of_length
#print axioms lincomb_zipWith_add
#print axioms lincomb_injective
#print axioms equinumerous_spanSet
#print axioms equinumerous_spanSet_card
#print axioms isIndep_cons

#print axioms exists_basis
#print axioms lincombP_perm
#print axioms isIndep_perm
#print axioms mem_spanSet_cons_iff
#print axioms spanSet_exchange
#print axioms isSubmodule_spanSet
#print axioms spanSet_subset_spanSet
#print axioms isModule_submodule

end Algebra


namespace ZFSet
export Algebra (IsIndep IsModule IsSubmodule equinumerous_spanSet equinumerous_spanSet_card exists_basis exists_cons_of_length exists_tuple_of_list ginv_vzero isIndep_cons isIndep_nil isIndep_perm isModule_submodule isSubmodule_spanSet lincomb lincombP lincombP_mem lincombP_perm lincomb_add lincomb_append lincomb_append_zeros lincomb_cons lincomb_eq_lincombP lincomb_ginv lincomb_injective lincomb_mem lincomb_mem_submodule lincomb_nil_left lincomb_nil_right lincomb_padTo lincomb_smul lincomb_take lincomb_zeros lincomb_zipWith_add lincomb_zipWith_sub mem_spanSet_cons_iff mem_spanSet_iff neg_one_smul padTo padTo_length padTo_mem perm_zip_exists smulAt_mem smul_vzero spanSet spanSet_eq_or_exists_outside spanSet_exchange spanSet_subset spanSet_subset_spanSet subset_spanSet tupleToList tupleToList_getElem tupleToList_inj tupleToList_length tupleToList_mem two_le_card_of_isField vaddAt_mem vadd_right_cancel vadd_shuffle_pair zero_smul zipWith_sub_mem)
end ZFSet
