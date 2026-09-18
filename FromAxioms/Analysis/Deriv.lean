/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The derivative, in the located reals

Every estimate here has the shape "this real is within that rational of zero".
In the located encoding `WithinOf z (realLOf c)` says that `c` is missing from
the lower half of `z` and `-c` from the upper half: two non-memberships rather
than an order chase. Bounds are monotone in the bound, additive and
multiplicative, and the rest of the file is written in that algebra.

Multiplication is the hard case, and the one that uses locatedness. A product
`x·y` has, for its lower half, the rationals below all four corners of some
bracket; `mulLower_tight` says the bracket may be taken as narrow as asked, and
the margin that makes this enough comes from the lower half being open: a
rational in it always has a larger one in it, and that gap is the `η` the box
estimate has to fit inside.
-/

import FromAxioms.Analysis.IVT

universe u

open NumberTheory SetTheory
namespace Analysis

/-! ## Bounds by a rational

Through `realLOf_lt_iff_mem_lower` and `lt_realLOf_iff_mem_upper`,
`WithinOf z (realLOf c)` is a statement about two rationals not being in two
sets. -/

/-- A rational bracket, read as two non-memberships. -/
theorem withinOf_realLOf_iff {x c : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hc : c ∈ NumberTheory.Rat.{u}) :
    WithinOf x (realLOf c) ↔ ¬ c ∈ fst x ∧ ¬ ratNeg c ∈ snd x := by
  have hneg : realLNeg (realLOf c) = realLOf (ratNeg c) := realLOf_neg hc
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hm => h2 ((realLOf_lt_iff_mem_lower hx hc).mpr hm), fun hm => h1 ?_⟩
    rw [hneg]
    exact (lt_realLOf_iff_mem_upper hx (ratNeg_mem_Rat hc)).mpr hm
  · rintro ⟨h1, h2⟩
    refine ⟨fun hlt => h2 ?_, fun hlt => h1 ((realLOf_lt_iff_mem_lower hx hc).mp hlt)⟩
    rw [hneg] at hlt
    exact (lt_realLOf_iff_mem_upper hx (ratNeg_mem_Rat hc)).mp hlt

/-- A bound may always be weakened. -/
theorem withinOf_mono {x c d : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hc : c ∈ NumberTheory.Rat.{u})
    (hd : d ∈ NumberTheory.Rat.{u}) (hcd : ratLe c d) (h : WithinOf x (realLOf c)) :
    WithinOf x (realLOf d) := by
  have hnc := ratNeg_mem_Rat hc
  have hnd := ratNeg_mem_Rat hd
  refine ⟨?_, ?_⟩
  · rw [realLOf_neg hd]
    refine realLLe_trans (realLOf_mem hnd) (realLOf_mem hnc) hx ?_ ?_
    · exact (realLOf_le_realLOf hnd hnc).mpr ((ratNeg_le_neg_iff hd hc).mpr hcd)
    · have := h.left
      rwa [realLOf_neg hc] at this
  · exact realLLe_trans hx (realLOf_mem hc) (realLOf_mem hd) h.right
      ((realLOf_le_realLOf hc hd).mpr hcd)

/-- Zero is within every non-negative bound. -/
theorem withinOf_zero {c : ZFSet.{u}} (hc : c ∈ NumberTheory.Rat.{u}) (hc0 : ratLe ratZero.{u} c) :
    WithinOf realLZero.{u} (realLOf c) := by
  refine ⟨?_, ?_⟩
  · rw [realLOf_neg hc]
    refine (realLOf_le_realLOf (ratNeg_mem_Rat hc) ratZero_mem_Rat).mpr ?_
    have := (ratNeg_le_neg_iff hc ratZero_mem_Rat).mpr hc0
    rwa [ratNeg_zero] at this
  · exact (realLOf_le_realLOf ratZero_mem_Rat hc).mpr hc0

/-- A non-negative rational is within itself. -/
theorem withinOf_self {c : ZFSet.{u}} (hc : c ∈ NumberTheory.Rat.{u}) (hc0 : ratLe ratZero.{u} c) :
    WithinOf (realLOf c) (realLOf c) := by
  have hnc := ratNeg_mem_Rat hc
  refine ⟨?_, realLLe_refl (realLOf_mem hc)⟩
  rw [realLOf_neg hc]
  refine (realLOf_le_realLOf hnc hc).mpr (ratLe_trans hnc ratZero_mem_Rat hc ?_ hc0)
  have := (ratNeg_le_neg_iff hc ratZero_mem_Rat).mpr hc0
  rwa [ratNeg_zero] at this

/-- An anchor and the point one step back are close at that step. -/
theorem close_realLOf_sub_self {r d : ZFSet.{u}} (hr : r ∈ NumberTheory.Rat.{u})
    (hd : d ∈ NumberTheory.Rat.{u}) (hd0 : ratLe ratZero.{u} d) :
    Close (realLOf r) (realLOf (ratAdd r (ratNeg d))) (realLOf d) := by
  have hnd := ratNeg_mem_Rat hd
  have hid : realLAdd (realLOf r) (realLNeg (realLOf (ratAdd r (ratNeg d))))
      = realLOf d := by
    rw [realLOf_add hr hnd, realLNeg_realLAdd (realLOf_mem hr)
        (realLOf_mem hnd),
      ← realLAdd_assoc (realLOf_mem hr) (realLNeg_mem (realLOf_mem hr))
        (realLNeg_mem (realLOf_mem hnd)),
      realLAdd_neg (realLOf_mem hr),
      realLAdd_comm realLZero_mem (realLNeg_mem (realLOf_mem hnd)),
      realLAdd_zero (realLNeg_mem (realLOf_mem hnd)),
      realLOf_neg hnd, ratNeg_ratNeg hd]
  show WithinOf (realLAdd (realLOf r)
    (realLNeg (realLOf (ratAdd r (ratNeg d))))) (realLOf d)
  rw [hid]
  exact withinOf_self hd hd0

#print axioms Analysis.close_realLOf_sub_self

/-- Bounds add, for rational bounds. The general form is `withinOf_add_real`;
this is its specialisation to `realLOf (c + d)`. -/
theorem withinOf_add {x y c d : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (hc : c ∈ NumberTheory.Rat.{u}) (hd : d ∈ NumberTheory.Rat.{u}) (h₁ : WithinOf x (realLOf c))
    (h₂ : WithinOf y (realLOf d)) :
    WithinOf (realLAdd x y) (realLOf (ratAdd c d)) := by
  have h := withinOf_add_real hx hy (realLOf_mem hc) (realLOf_mem hd) h₁ h₂
  rwa [← realLOf_add hc hd] at h

theorem withinOf_neg {x c : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hc : c ∈ NumberTheory.Rat.{u})
    (h : WithinOf x (realLOf c)) : WithinOf (realLNeg x) (realLOf c) := by
  have hnc := ratNeg_mem_Rat hc
  refine ⟨?_, ?_⟩
  · rw [realLOf_neg hc]
    intro hlt
    refine h.right ?_
    have := realLNeg_lt_neg (realLNeg_mem hx) (realLOf_mem hnc) hlt
    rw [realLNeg_realLNeg hx, realLOf_neg hnc, ratNeg_ratNeg hc] at this
    exact this
  · intro hlt
    refine h.left ?_
    have := realLNeg_lt_neg (realLOf_mem hc) (realLNeg_mem hx) hlt
    rw [realLNeg_realLNeg hx, realLOf_neg hc] at this
    rwa [realLOf_neg hc]

/-! ## The box estimate

A bracket of width `e ≤ 1` around a real bounded by `a` sits inside
`[-(a+e), a+e]`, so a corner product of two such brackets is at most
`(a+e)(b+e)`. That number exceeds `a·b` by `(b + (a+1))·e` at worst -- linear
in `e`, so a small enough `e` beats any prescribed margin. -/

/-- `(a+e)(b+e) ≤ a·b + (b + (a+1))·e`, for `0 ≤ e ≤ 1`. Only the square term
needs the upper bound on `e`; the rest is the distributive law. -/
private theorem box_le {a b e : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u}) (hb : b ∈ NumberTheory.Rat.{u})
    (he : e ∈ NumberTheory.Rat.{u}) (he0 : ratLe ratZero.{u} e) (he1 : ratLe e ratOne.{u}) :
    ratLe (ratMul (ratAdd a e) (ratAdd b e))
      (ratAdd (ratMul a b) (ratMul (ratAdd b (ratAdd a ratOne.{u})) e)) := by
  have hae := ratAdd_mem_Rat ha he
  have ha1 := ratAdd_mem_Rat ha ratOne_mem_Rat
  rw [ratMul_add hae hb he, ratAdd_mul ha he hb, ratAdd_mul hb ha1 he,
    ratAdd_assoc (ratMul_mem_Rat ha hb) (ratMul_mem_Rat he hb) (ratMul_mem_Rat hae he),
    ratMul_comm he hb]
  refine (ratAdd_le_add_left_iff (ratMul_mem_Rat ha hb)
    (ratAdd_mem_Rat (ratMul_mem_Rat hb he) (ratMul_mem_Rat hae he))
    (ratAdd_mem_Rat (ratMul_mem_Rat hb he) (ratMul_mem_Rat ha1 he))).mpr ?_
  refine (ratAdd_le_add_left_iff (ratMul_mem_Rat hb he) (ratMul_mem_Rat hae he)
    (ratMul_mem_Rat ha1 he)).mpr ?_
  exact ratMul_le_mul_right hae ha1 he
    ((ratAdd_le_add_left_iff ha he ratOne_mem_Rat).mpr he1) he0

/-- A box narrow enough that its corner bound beats a prescribed margin. -/
private theorem small_box {a b η : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u}) (hb : b ∈ NumberTheory.Rat.{u})
    (hη : η ∈ NumberTheory.Rat.{u}) (ha0 : ratLe ratZero.{u} a) (hb0 : ratLe ratZero.{u} b)
    (hη0 : ratLt ratZero.{u} η) :
    ∃ e, e ∈ NumberTheory.Rat.{u} ∧ ratLt ratZero.{u} e ∧
      ratLt (ratMul (ratAdd a e) (ratAdd b e)) (ratAdd (ratMul a b) η) := by
  have hK := ratAdd_mem_Rat hb (ratAdd_mem_Rat ha ratOne_mem_Rat)
  have hK0 : ratLe ratZero.{u} (ratAdd b (ratAdd a ratOne.{u})) := by
    refine ratLe_trans ratZero_mem_Rat hb hK hb0 ?_
    have := (ratAdd_le_add_left_iff hb ratZero_mem_Rat
      (ratAdd_mem_Rat ha ratOne_mem_Rat)).mpr
      (ratLe_trans ratZero_mem_Rat ha (ratAdd_mem_Rat ha ratOne_mem_Rat) ha0
        (by
          have := (ratAdd_le_add_left_iff ha ratZero_mem_Rat ratOne_mem_Rat).mpr
            ratZero_lt_one.left
          rwa [ratAdd_zero ha] at this))
    rwa [ratAdd_zero hb] at this
  obtain ⟨D, hDQ, hD0, hKD⟩ := exists_mul_lt hK hη hK0 hη0
  refine ⟨ratMin D ratOne.{u}, ratMin_mem_Rat hDQ ratOne_mem_Rat,
    ratMin_pos hDQ ratOne_mem_Rat hD0 ratZero_lt_one, ?_⟩
  have heQ := ratMin_mem_Rat hDQ ratOne_mem_Rat
  have he0 : ratLe ratZero.{u} (ratMin D ratOne.{u}) :=
    (ratMin_pos hDQ ratOne_mem_Rat hD0 ratZero_lt_one).left
  have he1 : ratLe (ratMin D ratOne.{u}) ratOne.{u} := ratMin_le_right hDQ ratOne_mem_Rat
  have hbox := box_le ha hb heQ he0 he1
  have hstep : ratLe (ratMul (ratAdd b (ratAdd a ratOne.{u})) (ratMin D ratOne.{u}))
      (ratMul (ratAdd b (ratAdd a ratOne.{u})) D) := by
    rw [ratMul_comm hK heQ, ratMul_comm hK hDQ]
    exact ratMul_le_mul_right heQ hDQ hK (ratMin_le_left hDQ ratOne_mem_Rat) hK0
  refine ratLt_of_le_of_lt (ratMul_mem_Rat (ratAdd_mem_Rat ha heQ)
    (ratAdd_mem_Rat hb heQ))
    (ratAdd_mem_Rat (ratMul_mem_Rat ha hb) (ratMul_mem_Rat hK heQ))
    (ratAdd_mem_Rat (ratMul_mem_Rat ha hb) hη) hbox ?_
  refine ratLt_of_le_of_lt (ratAdd_mem_Rat (ratMul_mem_Rat ha hb) (ratMul_mem_Rat hK heQ))
    (ratAdd_mem_Rat (ratMul_mem_Rat ha hb) (ratMul_mem_Rat hK hDQ))
    (ratAdd_mem_Rat (ratMul_mem_Rat ha hb) hη)
    ((ratAdd_le_add_left_iff (ratMul_mem_Rat ha hb) (ratMul_mem_Rat hK heQ)
      (ratMul_mem_Rat hK hDQ)).mpr hstep) ?_
  exact (ratAdd_lt_add_left_iff (ratMul_mem_Rat ha hb) (ratMul_mem_Rat hK hDQ) hη).mpr hKD

/-- A bracket around a real bounded by `a` is itself bounded by `a + e`, where
`e` is the bracket's width. The lower end is exact -- it cannot reach `a`,
because `a` is not in the lower half -- and only the upper end pays the width. -/
private theorem bracket_bounds {L U a e q q' : ZFSet.{u}} (h : IsLocated L U)
    (ha : a ∈ NumberTheory.Rat.{u}) (he : e ∈ NumberTheory.Rat.{u}) (he0 : ratLe ratZero.{u} e)
    (hb : WithinOf (opair L U) (realLOf a)) (hq : q ∈ L) (hq' : q' ∈ U)
    (hw : ratLt q' (ratAdd q e)) :
    ratLe (ratNeg (ratAdd a e)) q ∧ ratLe q (ratAdd a e) := by
  have hxm : opair L U ∈ RealL.{u} := (mem_RealL_iff _).mpr ⟨L, U, rfl, h⟩
  obtain ⟨hnl, hnu⟩ := (withinOf_realLOf_iff hxm ha).mp hb
  rw [fst_opair] at hnl
  rw [snd_opair] at hnu
  have hqQ := h.lower_subset q hq
  have hq'Q := h.upper_subset q' hq'
  have hae := ratAdd_mem_Rat ha he
  have hqa : ratLe q a :=
    ratLe_of_not_lt hqQ ha (fun hlt => hnl (h.lower_down q hq a ha hlt))
  have hnaq' : ratLe (ratNeg a) q' :=
    ratLe_of_not_lt (ratNeg_mem_Rat ha) hq'Q
      (fun hlt => hnu (h.upper_up q' hq' (ratNeg a) (ratNeg_mem_Rat ha) hlt))
  refine ⟨?_, ratLe_trans hqQ ha hae hqa ?_⟩
  · -- `-a ≤ q' < q + e`, so `-(a+e) < q`
    have h1 : ratLt (ratNeg a) (ratAdd q e) :=
      ratLt_of_le_of_lt (ratNeg_mem_Rat ha) hq'Q (ratAdd_mem_Rat hqQ he) hnaq' hw
    have h2 := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat he) (ratNeg_mem_Rat ha)
      (ratAdd_mem_Rat hqQ he)).mpr h1
    rw [ratAdd_assoc hqQ he (ratNeg_mem_Rat he), ratAdd_neg he, ratAdd_zero hqQ,
      ← ratNeg_add ha he] at h2
    exact h2.left
  · have := (ratAdd_le_add_left_iff ha ratZero_mem_Rat he).mpr he0
    rwa [ratAdd_zero ha] at this


/-- Bounds multiply. Membership in the lower half of a product is an
open condition, so a rational there has a strictly larger one `p` beside it,
and the box estimate is fitted inside that gap. -/
theorem withinOf_mul {x y a b : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (ha : a ∈ NumberTheory.Rat.{u}) (hb : b ∈ NumberTheory.Rat.{u}) (ha0 : ratLe ratZero.{u} a)
    (hb0 : ratLe ratZero.{u} b) (hxa : WithinOf x (realLOf a))
    (hyb : WithinOf y (realLOf b)) :
    WithinOf (realLMul x y) (realLOf (ratMul a b)) := by
  have hxy := realLMul_mem hx hy
  obtain ⟨L₁, U₁, rfl, h₁⟩ := (mem_RealL_iff x).mp hx
  obtain ⟨L₂, U₂, rfl, h₂⟩ := (mem_RealL_iff y).mp hy
  have hab := ratMul_mem_Rat ha hb
  have hmul := isLocated_mul h₁ h₂
  have hprod : realLMul (opair L₁ U₁) (opair L₂ U₂)
      = opair (mulLower L₁ U₁ L₂ U₂) (mulUpper L₁ U₁ L₂ U₂) := by
    rw [realLMul, fst_opair, snd_opair, fst_opair, snd_opair]
  refine (withinOf_realLOf_iff hxy hab).mpr ⟨?_, ?_⟩
  · rw [hprod, fst_opair]
    intro hmem
    obtain ⟨p, hp, hltp⟩ := hmul.lower_open _ hmem
    have hpQ := hmul.lower_subset p hp
    have hηQ := ratAdd_mem_Rat hpQ (ratNeg_mem_Rat hab)
    have hη0 : ratLt ratZero.{u} (ratAdd p (ratNeg (ratMul a b))) := by
      have := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat hab) hab hpQ).mpr hltp
      rwa [ratAdd_neg hab] at this
    obtain ⟨e, heQ, he0, hbox⟩ := small_box ha hb hηQ ha0 hb0 hη0
    obtain ⟨q, hq, q', hq', r, hr, r', hr', hwq, hwr, c₁, -, -, -⟩ :=
      mulLower_tight h₁ h₂ heQ he0 hp
    obtain ⟨bq1, bq2⟩ := bracket_bounds h₁ ha heQ he0.left hxa hq hq' hwq
    obtain ⟨br1, br2⟩ := bracket_bounds h₂ hb heQ he0.left hyb hr hr' hwr
    have hae := ratAdd_mem_Rat ha heQ
    have hbe := ratAdd_mem_Rat hb heQ
    have hae0 : ratLe ratZero.{u} (ratAdd a e) :=
      ratLe_trans ratZero_mem_Rat ha hae ha0
        (by
          have := (ratAdd_le_add_left_iff ha ratZero_mem_Rat heQ).mpr he0.left
          rwa [ratAdd_zero ha] at this)
    have hcorner : ratLe (ratMul q r) (ratMul (ratAdd a e) (ratAdd b e)) :=
      mul_le_of_bounds (h₁.lower_subset q hq) (h₂.lower_subset r hr) hae hbe
        bq1 bq2 br1 br2 hae0
    have hlt : ratLt p (ratAdd (ratMul a b) (ratAdd p (ratNeg (ratMul a b)))) :=
      ratLt_trans hpQ (ratMul_mem_Rat hae hbe) (ratAdd_mem_Rat hab hηQ)
        (ratLt_of_lt_of_le hpQ
          (ratMul_mem_Rat (h₁.lower_subset q hq) (h₂.lower_subset r hr))
          (ratMul_mem_Rat hae hbe) c₁ hcorner) hbox
    rw [ratAdd_sub_cancel hpQ hab] at hlt
    exact ratLt_irrefl hlt
  · rw [hprod, snd_opair]
    intro hmem
    obtain ⟨p, hp, hltp⟩ := hmul.upper_open _ hmem
    have hpQ := hmul.upper_subset p hp
    have hnp := ratNeg_mem_Rat hpQ
    have hηQ := ratAdd_mem_Rat hnp (ratNeg_mem_Rat hab)
    have hη0 : ratLt ratZero.{u} (ratAdd (ratNeg p) (ratNeg (ratMul a b))) := by
      have := (ratAdd_lt_add_right_iff hnp hpQ (ratNeg_mem_Rat hab)).mpr hltp
      rw [ratAdd_neg hpQ, ratAdd_comm (ratNeg_mem_Rat hab) hnp] at this
      exact this
    obtain ⟨e, heQ, he0, hbox⟩ := small_box ha hb hηQ ha0 hb0 hη0
    obtain ⟨q, hq, q', hq', r, hr, r', hr', hwq, hwr, c₁, -, -, -⟩ :=
      mulUpper_tight h₁ h₂ heQ he0 hp
    obtain ⟨bq1, bq2⟩ := bracket_bounds h₁ ha heQ he0.left hxa hq hq' hwq
    obtain ⟨br1, br2⟩ := bracket_bounds h₂ hb heQ he0.left hyb hr hr' hwr
    have hqQ := h₁.lower_subset q hq
    have hrQ := h₂.lower_subset r hr
    have hae := ratAdd_mem_Rat ha heQ
    have hbe := ratAdd_mem_Rat hb heQ
    have hae0 : ratLe ratZero.{u} (ratAdd a e) :=
      ratLe_trans ratZero_mem_Rat ha hae ha0
        (by
          have := (ratAdd_le_add_left_iff ha ratZero_mem_Rat heQ).mpr he0.left
          rwa [ratAdd_zero ha] at this)
    -- the same box bound, applied to `-q`
    have hnq1 : ratLe (ratNeg (ratAdd a e)) (ratNeg q) :=
      (ratNeg_le_neg_iff hae hqQ).mpr bq2
    have hnq2 : ratLe (ratNeg q) (ratAdd a e) := by
      have := (ratNeg_le_neg_iff hqQ (ratNeg_mem_Rat hae)).mpr bq1
      rwa [ratNeg_ratNeg hae] at this
    have hswap : ratMul (ratNeg q) r = ratNeg (ratMul q r) := by
      rw [ratMul_comm (ratNeg_mem_Rat hqQ) hrQ, ratMul_neg hrQ hqQ, ratMul_comm hrQ hqQ]
    have hcorner : ratLe (ratNeg (ratMul q r)) (ratMul (ratAdd a e) (ratAdd b e)) := by
      have := mul_le_of_bounds (ratNeg_mem_Rat hqQ) hrQ hae hbe hnq1 hnq2 br1 br2 hae0
      rwa [hswap] at this
    have hlt : ratLt (ratNeg (ratMul q r))
        (ratAdd (ratMul a b) (ratAdd (ratNeg p) (ratNeg (ratMul a b)))) :=
      ratLt_of_le_of_lt (ratNeg_mem_Rat (ratMul_mem_Rat hqQ hrQ))
        (ratMul_mem_Rat hae hbe) (ratAdd_mem_Rat hab hηQ) hcorner hbox
    rw [ratAdd_sub_cancel hnp hab] at hlt
    exact ratLt_irrefl (ratLt_trans (ratMul_mem_Rat hqQ hrQ) hpQ
      (ratMul_mem_Rat hqQ hrQ) c₁
      ((ratNeg_lt_neg_iff (ratMul_mem_Rat hqQ hrQ) hpQ).mp hlt))

/-- The triangle inequality, in the rational-bound form: two reals each near
`A` are near each other. -/
theorem close_of_close_close {A B C c d : ZFSet.{u}} (hA : A ∈ RealL.{u})
    (hB : B ∈ RealL.{u}) (hC : C ∈ RealL.{u}) (hc : c ∈ NumberTheory.Rat.{u}) (hd : d ∈ NumberTheory.Rat.{u})
    (h₁ : Close A B (realLOf c)) (h₂ : Close A C (realLOf d)) :
    Close B C (realLOf (ratAdd c d)) := by
  have hBA : WithinOf (realLAdd B (realLNeg A)) (realLOf c) := by
    have := withinOf_neg (realLAdd_mem hA (realLNeg_mem hB)) hc h₁
    rwa [realLNeg_sub hA hB] at this
  have := withinOf_add (realLAdd_mem hB (realLNeg_mem hA))
    (realLAdd_mem hA (realLNeg_mem hC)) hc hd hBA h₂
  rwa [realLSub_add_sub hA hB hC] at this

/-! ## The derivative -/

/-- `F` has derivative `L` at `a`, on `[p, q]`: for every scale `n` there is a
scale `m` such that a point within a rational `w ≤ 1/(m+1)` of `a` has its value
within `w/(n+1)` of the linear approximation at `a`. -/
def HasDerivAt (F : ZFSet.{u} → ZFSet.{u}) (p q a L : ZFSet.{u}) : Prop :=
  ∀ n : Nat, ∃ m : Nat, ∀ w x, w ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} w →
    ratLe w (invWidth (ofNat.{u} m)) → x ∈ realLIcc p q → Close x a (realLOf w) →
      Close (F x) (realLAdd (F a) (realLMul L (realLAdd x (realLNeg a))))
        (realLOf (ratMul (invWidth (ofNat.{u} n)) w))

#print axioms HasDerivAt

/-- Two copies of a fine enough scale fit inside a given one. Every rule
below spends its error budget in two halves. By Archimedes, through
`exists_invWidth_lt`, not by division. -/
theorem exists_invWidth_add_self_lt (n : Nat) :
    ∃ m : Nat, ratLt (ratAdd (invWidth (ofNat.{u} m)) (invWidth (ofNat.{u} m)))
      (invWidth (ofNat.{u} n)) := by
  have htQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
  obtain ⟨d, hdQ, hd0, hdlt⟩ := exists_add_self_lt htQ (invWidth_pos (ofNat_mem_omega.{u} n))
  obtain ⟨N, hN, hNd⟩ := exists_invWidth_lt hdQ hd0
  obtain ⟨m, rfl⟩ := (mem_omega_iff N).mp hN
  have hmQ := invWidth_mem_Rat (ofNat_mem_omega.{u} m)
  exact ⟨m, ratLt_trans (ratAdd_mem_Rat hmQ hmQ) (ratAdd_mem_Rat hdQ hdQ) htQ
    (ratAdd_lt_add hmQ hdQ hmQ hdQ hNd hNd) hdlt⟩

/-- Every located real has a rational bound, and it is read off a bracket
rather than chosen: locatedness hands over `lo < x < hi`, and any rational above
both `hi` and `-lo` will do. -/
theorem exists_rat_bound {x : ZFSet.{u}} (hx : x ∈ RealL.{u}) :
    ∃ K, K ∈ NumberTheory.Rat.{u} ∧ ratLe ratZero.{u} K ∧ WithinOf x (realLOf K) := by
  obtain ⟨lo, hi, hloQ, hhiQ, hlt1, hlt2, -⟩ :=
    exists_rat_bracket hx ratOne_mem_Rat ratZero_lt_one
  obtain ⟨k, hkQ, hkhi, hklo⟩ := exists_gt_two hhiQ (ratNeg_mem_Rat hloQ)
  obtain ⟨K, hKQ, hKk, hK0⟩ := exists_gt_two hkQ ratZero_mem_Rat
  have hhiK : ratLt hi K := ratLt_trans hhiQ hkQ hKQ hkhi hKk
  have hloK : ratLt (ratNeg lo) K := ratLt_trans (ratNeg_mem_Rat hloQ) hkQ hKQ hklo hKk
  refine ⟨K, hKQ, hK0.left, ?_, ?_⟩
  · rw [realLOf_neg hKQ]
    refine realLLe_of_lt (realLOf_mem (ratNeg_mem_Rat hKQ)) hx
      (realLLt_trans (realLOf_mem (ratNeg_mem_Rat hKQ)) (realLOf_mem hloQ) hx ?_ hlt1)
    refine (realLOf_lt_realLOf (ratNeg_mem_Rat hKQ) hloQ).mpr ?_
    have := (ratNeg_lt_neg_iff hKQ (ratNeg_mem_Rat hloQ)).mpr hloK
    rwa [ratNeg_ratNeg hloQ] at this
  · exact realLLe_of_lt hx (realLOf_mem hKQ)
      (realLLt_trans hx (realLOf_mem hhiQ) (realLOf_mem hKQ) hlt2
        ((realLOf_lt_realLOf hhiQ hKQ).mpr hhiK))

/-- Every scale is at most `1`. -/
theorem invWidth_le_one (n : Nat) : ratLe (invWidth (ofNat.{u} n)) ratOne.{u} := by
  have h := invWidth_antitone (ofNat_mem_omega.{u} 0) (ofNat_mem_omega.{u} n)
    ((ofNat_subset_iff 0 n).mpr (Nat.zero_le n))
  rwa [invWidth_ofNat 0, ratNat_one_one] at h

/-- A fine enough scale survives being multiplied by a fixed non-negative
rational. -/
theorem exists_invWidth_mul_lt {K : ZFSet.{u}} (hK : K ∈ NumberTheory.Rat.{u})
    (hK0 : ratLe ratZero.{u} K) (n : Nat) :
    ∃ j : Nat, ratLt (ratMul K (invWidth (ofNat.{u} j))) (invWidth (ofNat.{u} n)) := by
  obtain ⟨D, hDQ, hD0, hKD⟩ := exists_mul_lt hK (invWidth_mem_Rat (ofNat_mem_omega.{u} n))
    hK0 (invWidth_pos (ofNat_mem_omega.{u} n))
  obtain ⟨N, hN, hND⟩ := exists_invWidth_lt hDQ hD0
  obtain ⟨j, rfl⟩ := (mem_omega_iff N).mp hN
  have hjQ := invWidth_mem_Rat (ofNat_mem_omega.{u} j)
  refine ⟨j, ratLt_of_le_of_lt (ratMul_mem_Rat hK hjQ) (ratMul_mem_Rat hK hDQ)
    (invWidth_mem_Rat (ofNat_mem_omega.{u} n)) ?_ hKD⟩
  rw [ratMul_comm hK hjQ, ratMul_comm hK hDQ]
  exact ratMul_le_mul_right hjQ hDQ hK hND.left hK0


/-- A step fine enough for a coarse modulus is fine enough for every finer
index. Combining two moduli by taking the larger index is how every rule below
serves both of its hypotheses at once. -/
theorem ratLe_invWidth_of_le {w : ZFSet.{u}} (hw : w ∈ NumberTheory.Rat.{u}) {i k : Nat}
    (hik : i ≤ k) (h : ratLe w (invWidth (ofNat.{u} k))) :
    ratLe w (invWidth (ofNat.{u} i)) :=
  ratLe_trans hw (invWidth_mem_Rat (ofNat_mem_omega.{u} k))
    (invWidth_mem_Rat (ofNat_mem_omega.{u} i)) h
    (invWidth_antitone (ofNat_mem_omega.{u} i) (ofNat_mem_omega.{u} k)
      ((ofNat_subset_iff i k).mpr hik))

/-- The sum rule, with the analysis done once. Two estimates at the same
step, each with slack `e·w`, combine into one with slack `f·w` for any `f`
above `e + e` -- and the linear parts combine because `RealL` distributes. Both
the pointwise and the uniform sum rule are this lemma plus a choice of
moduli. -/
theorem close_add_lin {Fx Gx Fa Ga L M h e f w : ZFSet.{u}}
    (hFx : Fx ∈ RealL.{u}) (hGx : Gx ∈ RealL.{u}) (hFa : Fa ∈ RealL.{u})
    (hGa : Ga ∈ RealL.{u}) (hL : L ∈ RealL.{u}) (hM : M ∈ RealL.{u})
    (hh : h ∈ RealL.{u}) (he : e ∈ NumberTheory.Rat.{u}) (hf : f ∈ NumberTheory.Rat.{u}) (hw : w ∈ NumberTheory.Rat.{u})
    (hw0 : ratLe ratZero.{u} w) (hef : ratLe (ratAdd e e) f)
    (h₁ : Close Fx (realLAdd Fa (realLMul L h)) (realLOf (ratMul e w)))
    (h₂ : Close Gx (realLAdd Ga (realLMul M h)) (realLOf (ratMul e w))) :
    Close (realLAdd Fx Gx) (realLAdd (realLAdd Fa Ga) (realLMul (realLAdd L M) h))
      (realLOf (ratMul f w)) := by
  have hLh := realLMul_mem hL hh
  have hMh := realLMul_mem hM hh
  have hsum := withinOf_add (realLAdd_mem hFx (realLNeg_mem (realLAdd_mem hFa hLh)))
    (realLAdd_mem hGx (realLNeg_mem (realLAdd_mem hGa hMh)))
    (ratMul_mem_Rat he hw) (ratMul_mem_Rat he hw) h₁ h₂
  rw [← realLAdd_sub_add hFx hGx (realLAdd_mem hFa hLh) (realLAdd_mem hGa hMh),
    realLAdd_interchange hFa hLh hGa hMh, ← realLAdd_mul hL hM hh,
    ← ratAdd_mul he he hw] at hsum
  exact withinOf_mono (realLAdd_mem (realLAdd_mem hFx hGx)
      (realLNeg_mem (realLAdd_mem (realLAdd_mem hFa hGa)
        (realLMul_mem (realLAdd_mem hL hM) hh))))
    (ratMul_mem_Rat (ratAdd_mem_Rat he he) hw) (ratMul_mem_Rat hf hw)
    (ratMul_le_mul_right (ratAdd_mem_Rat he he) hf hw hef hw0) hsum

/-! ## The product rule

The identity is the whole of it: with `U = F x - F a` and `V = G x - G a`,

    (A+U)(B+V) - (A·B + (A·M + B·L)·h)
      = A·(V - M·h) + B·(U - L·h) + U·V

so the slack of the product is a bounded multiple of each factor's slack, plus
the term `U·V` -- which is quadratic in the step and therefore beaten by a
fine enough modulus rather than by a fine enough scale. -/

/-- The abelian-group half of the product identity, isolated so the ring half is
readable. -/
private theorem group_shuffle {Z al be ga si ta : ZFSet.{u}} (hZ : Z ∈ RealL.{u})
    (hal : al ∈ RealL.{u}) (hbe : be ∈ RealL.{u}) (hga : ga ∈ RealL.{u})
    (hsi : si ∈ RealL.{u}) (hta : ta ∈ RealL.{u}) :
    realLAdd (realLAdd (realLAdd Z al) (realLAdd be ga))
        (realLNeg (realLAdd Z (realLAdd si ta)))
      = realLAdd (realLAdd (realLAdd al (realLNeg si))
          (realLAdd be (realLNeg ta))) ga := by
  have hnsi := realLNeg_mem hsi
  have hnta := realLNeg_mem hta
  rw [realLAdd_assoc hZ hal (realLAdd_mem hbe hga),
    realLAdd_sub_cancel_left hZ (realLAdd_mem hal (realLAdd_mem hbe hga))
      (realLAdd_mem hsi hta),
    realLNeg_realLAdd hsi hta,
    realLAdd_interchange hal (realLAdd_mem hbe hga) hnsi hnta,
    realLAdd_assoc hbe hga hnta, realLAdd_comm hga hnta,
    ← realLAdd_assoc hbe hnta hga,
    ← realLAdd_assoc (realLAdd_mem hal hnsi) (realLAdd_mem hbe hnta) hga]


/-- The product decomposition. -/
theorem product_slack {A B U V L M h : ZFSet.{u}} (hA : A ∈ RealL.{u})
    (hB : B ∈ RealL.{u}) (hU : U ∈ RealL.{u}) (hV : V ∈ RealL.{u})
    (hL : L ∈ RealL.{u}) (hM : M ∈ RealL.{u}) (hh : h ∈ RealL.{u}) :
    realLAdd (realLMul (realLAdd A U) (realLAdd B V))
        (realLNeg (realLAdd (realLMul A B)
          (realLMul (realLAdd (realLMul A M) (realLMul B L)) h)))
      = realLAdd (realLAdd (realLMul A (realLAdd V (realLNeg (realLMul M h))))
          (realLMul B (realLAdd U (realLNeg (realLMul L h))))) (realLMul U V) := by
  have hMh := realLMul_mem hM hh
  have hLh := realLMul_mem hL hh
  -- expand the product, and the linear part
  rw [realLAdd_mul hA hU (realLAdd_mem hB hV), realLMul_distrib hA hB hV,
    realLMul_distrib hU hB hV,
    realLAdd_mul (realLMul_mem hA hM) (realLMul_mem hB hL) hh,
    realLMul_assoc hA hM hh, realLMul_assoc hB hL hh]
  -- expand the two scaled slacks
  rw [realLMul_distrib hA hV (realLNeg_mem hMh),
    realLMul_comm hA (realLNeg_mem hMh), realLNeg_realLMul hMh hA,
    realLMul_comm hMh hA,
    realLMul_distrib hB hU (realLNeg_mem hLh),
    realLMul_comm hB (realLNeg_mem hLh), realLNeg_realLMul hLh hB,
    realLMul_comm hLh hB, realLMul_comm hU hB]
  exact group_shuffle (realLMul_mem hA hB) (realLMul_mem hA hV) (realLMul_mem hB hU)
    (realLMul_mem hU hV) (realLMul_mem hA hMh) (realLMul_mem hB hLh)

#print axioms product_slack

/-- The increment is bounded by `(scale + |slope|)` times the step. The
slack contributes its scale and the linear part its slope's bound. Keeping the
scale rather than `1` in the constant lets the mean value inequality conclude
with `K`, not `K + 1`. -/
theorem withinOf_increment_sharp {Y Ya Sl h K w : ZFSet.{u}} {j : Nat}
    (hY : Y ∈ RealL.{u}) (hYa : Ya ∈ RealL.{u}) (hSl : Sl ∈ RealL.{u})
    (hh : h ∈ RealL.{u}) (hK : K ∈ NumberTheory.Rat.{u}) (hw : w ∈ NumberTheory.Rat.{u})
    (hK0 : ratLe ratZero.{u} K) (hw0 : ratLe ratZero.{u} w)
    (hKb : WithinOf Sl (realLOf K)) (hhb : WithinOf h (realLOf w))
    (hslack : WithinOf (realLAdd Y (realLNeg (realLAdd Ya (realLMul Sl h))))
      (realLOf (ratMul (invWidth (ofNat.{u} j)) w))) :
    WithinOf (realLAdd Y (realLNeg Ya))
      (realLOf (ratMul (ratAdd (invWidth (ofNat.{u} j)) K) w)) := by
  have hjQ := invWidth_mem_Rat (ofNat_mem_omega.{u} j)
  have hSh := realLMul_mem hSl hh
  have hb := withinOf_add (realLAdd_mem hY (realLNeg_mem (realLAdd_mem hYa hSh))) hSh
    (ratMul_mem_Rat hjQ hw) (ratMul_mem_Rat hK hw) hslack
    (withinOf_mul hSl hh hK hw hK0 hw0 hKb hhb)
  rwa [slack_add_lin hY hYa hSh, ← ratAdd_mul hjQ hK hw] at hb

/-- The same, relaxed to a constant that does not mention the scale. Every rule
that has to control a factor it is not differentiating uses this form. -/
theorem withinOf_increment {Y Ya Sl h K w : ZFSet.{u}} {j : Nat}
    (hY : Y ∈ RealL.{u}) (hYa : Ya ∈ RealL.{u}) (hSl : Sl ∈ RealL.{u})
    (hh : h ∈ RealL.{u}) (hK : K ∈ NumberTheory.Rat.{u}) (hw : w ∈ NumberTheory.Rat.{u})
    (hK0 : ratLe ratZero.{u} K) (hw0 : ratLe ratZero.{u} w)
    (hKb : WithinOf Sl (realLOf K)) (hhb : WithinOf h (realLOf w))
    (hslack : WithinOf (realLAdd Y (realLNeg (realLAdd Ya (realLMul Sl h))))
      (realLOf (ratMul (invWidth (ofNat.{u} j)) w))) :
    WithinOf (realLAdd Y (realLNeg Ya)) (realLOf (ratMul (ratAdd ratOne.{u} K) w)) := by
  have hjQ := invWidth_mem_Rat (ofNat_mem_omega.{u} j)
  refine withinOf_mono (realLAdd_mem hY (realLNeg_mem hYa))
    (ratMul_mem_Rat (ratAdd_mem_Rat hjQ hK) hw)
    (ratMul_mem_Rat (ratAdd_mem_Rat ratOne_mem_Rat hK) hw) ?_
    (withinOf_increment_sharp hY hYa hSl hh hK hw hK0 hw0 hKb hhb hslack)
  exact ratMul_le_mul_right (ratAdd_mem_Rat hjQ hK) (ratAdd_mem_Rat ratOne_mem_Rat hK) hw
    ((ratAdd_le_add_right_iff hK hjQ ratOne_mem_Rat).mpr (invWidth_le_one j)) hw0

/-- The product rule. -/
theorem hasDerivAt_mul {F G : ZFSet.{u} → ZFSet.{u}} {p q a L M : ZFSet.{u}}
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ RealL.{u})
    (hGm : ∀ x, x ∈ realLIcc p q → G x ∈ RealL.{u})
    (ha : a ∈ realLIcc p q) (hL : L ∈ RealL.{u}) (hM : M ∈ RealL.{u})
    (hF : HasDerivAt F p q a L) (hG : HasDerivAt G p q a M) :
    HasDerivAt (fun x => realLMul (F x) (G x)) p q a
      (realLAdd (realLMul (F a) M) (realLMul (G a) L)) := by
  have haM := ((mem_realLIcc_iff p q a).mp ha).left
  have hFa := hFm a ha
  have hGa := hGm a ha
  obtain ⟨KA, hKAQ, hKA0, hKA⟩ := exists_rat_bound hFa
  obtain ⟨KB, hKBQ, hKB0, hKB⟩ := exists_rat_bound hGa
  obtain ⟨KL, hKLQ, hKL0, hKLb⟩ := exists_rat_bound hL
  obtain ⟨KM, hKMQ, hKM0, hKMb⟩ := exists_rat_bound hM
  have hnn : ∀ c d : ZFSet.{u}, c ∈ NumberTheory.Rat.{u} → d ∈ NumberTheory.Rat.{u} → ratLe ratZero.{u} c →
      ratLe ratZero.{u} d → ratLe ratZero.{u} (ratAdd c d) := by
    intro c d hc hd hc0 hd0
    have := ratAdd_le_add ratZero_mem_Rat hc ratZero_mem_Rat hd hc0 hd0
    rwa [ratAdd_zero ratZero_mem_Rat] at this
  have hCUQ := ratAdd_mem_Rat ratOne_mem_Rat hKLQ
  have hCVQ := ratAdd_mem_Rat ratOne_mem_Rat hKMQ
  have hCU0 := hnn _ _ ratOne_mem_Rat hKLQ ratZero_lt_one.left hKL0
  have hCV0 := hnn _ _ ratOne_mem_Rat hKMQ ratZero_lt_one.left hKM0
  intro n
  obtain ⟨i, hi2⟩ := exists_invWidth_add_self_lt.{u} n
  have hiQ := invWidth_mem_Rat (ofNat_mem_omega.{u} i)
  obtain ⟨j, hjlt⟩ := exists_invWidth_mul_lt (ratAdd_mem_Rat hKAQ hKBQ)
    (hnn _ _ hKAQ hKBQ hKA0 hKB0) i
  have hjQ := invWidth_mem_Rat (ofNat_mem_omega.{u} j)
  obtain ⟨m₁, hb₁⟩ := hF j
  obtain ⟨m₂, hb₂⟩ := hG j
  obtain ⟨m₃, hm3⟩ := exists_invWidth_mul_lt (ratMul_mem_Rat hCUQ hCVQ)
    (ratZero_le_mul hCUQ hCVQ hCU0 hCV0) i
  refine ⟨Nat.max (Nat.max m₁ m₂) m₃, fun w x hwQ hw0 hwle hx hclose => ?_⟩
  have hεQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
  have hxM := ((mem_realLIcc_iff p q x).mp hx).left
  have hFx := hFm x hx
  have hGx := hGm x hx
  have hhM := realLAdd_mem hxM (realLNeg_mem haM)
  have hLh := realLMul_mem hL hhM
  have hMh := realLMul_mem hM hhM
  have hfine : ∀ k : Nat, k ≤ Nat.max (Nat.max m₁ m₂) m₃ →
      ratLe w (invWidth (ofNat.{u} k)) := fun k hk =>
    ratLe_invWidth_of_le hwQ hk hwle
  have c₁ := hb₁ w x hwQ hw0
    (hfine m₁ (Nat.le_trans (Nat.le_max_left m₁ m₂) (Nat.le_max_left _ m₃))) hx hclose
  have c₂ := hb₂ w x hwQ hw0
    (hfine m₂ (Nat.le_trans (Nat.le_max_right m₁ m₂) (Nat.le_max_left _ m₃))) hx hclose
  have hSF := realLAdd_mem hFx (realLNeg_mem (realLAdd_mem hFa hLh))
  have hSG := realLAdd_mem hGx (realLNeg_mem (realLAdd_mem hGa hMh))
  have hU := realLAdd_mem hFx (realLNeg_mem hFa)
  have hV := realLAdd_mem hGx (realLNeg_mem hGa)
  -- each increment is bounded by `(1 + |slope|)` times the step
  have hUb := withinOf_increment hFx hFa hL hhM hKLQ hwQ hKL0 hw0.left hKLb hclose c₁
  have hVb := withinOf_increment hGx hGa hM hhM hKMQ hwQ hKM0 hw0.left hKMb hclose c₂
  -- the three pieces
  have hjw0 := ratZero_le_mul hjQ hwQ (invWidth_pos (ofNat_mem_omega.{u} j)).left hw0.left
  have bA := withinOf_mul hFa hSG hKAQ (ratMul_mem_Rat hjQ hwQ) hKA0 hjw0 hKA c₂
  have bB := withinOf_mul hGa hSF hKBQ (ratMul_mem_Rat hjQ hwQ) hKB0 hjw0 hKB c₁
  have bUV := withinOf_mul hU hV (ratMul_mem_Rat hCUQ hwQ) (ratMul_mem_Rat hCVQ hwQ)
    (ratZero_le_mul hCUQ hwQ hCU0 hw0.left) (ratZero_le_mul hCVQ hwQ hCV0 hw0.left) hUb hVb
  have btot := withinOf_add (realLAdd_mem (realLMul_mem hFa hSG) (realLMul_mem hGa hSF))
    (realLMul_mem hU hV)
    (ratAdd_mem_Rat (ratMul_mem_Rat hKAQ (ratMul_mem_Rat hjQ hwQ))
      (ratMul_mem_Rat hKBQ (ratMul_mem_Rat hjQ hwQ)))
    (ratMul_mem_Rat (ratMul_mem_Rat hCUQ hwQ) (ratMul_mem_Rat hCVQ hwQ))
    (withinOf_add (realLMul_mem hFa hSG) (realLMul_mem hGa hSF)
      (ratMul_mem_Rat hKAQ (ratMul_mem_Rat hjQ hwQ))
      (ratMul_mem_Rat hKBQ (ratMul_mem_Rat hjQ hwQ)) bA bB)
    bUV
  -- and they assemble into the slack of the product
  have hkey := product_slack hFa hGa hU hV hL hM hhM
  rw [realLAdd_comm hFa hU, realLSub_add_cancel hFx hFa,
    realLAdd_comm hGa hV, realLSub_add_cancel hGx hGa,
    realLSub_sub hGx hGa hMh, realLSub_sub hFx hFa hLh] at hkey
  rw [← hkey] at btot
  show WithinOf (realLAdd (realLMul (F x) (G x)) (realLNeg (realLAdd (realLMul (F a) (G a))
    (realLMul (realLAdd (realLMul (F a) M) (realLMul (G a) L))
      (realLAdd x (realLNeg a)))))) _
  refine withinOf_mono (realLAdd_mem (realLMul_mem hFx hGx)
    (realLNeg_mem (realLAdd_mem (realLMul_mem hFa hGa)
      (realLMul_mem (realLAdd_mem (realLMul_mem hFa hM) (realLMul_mem hGa hL)) hhM))))
    (ratAdd_mem_Rat (ratAdd_mem_Rat (ratMul_mem_Rat hKAQ (ratMul_mem_Rat hjQ hwQ))
      (ratMul_mem_Rat hKBQ (ratMul_mem_Rat hjQ hwQ)))
      (ratMul_mem_Rat (ratMul_mem_Rat hCUQ hwQ) (ratMul_mem_Rat hCVQ hwQ)))
    (ratMul_mem_Rat hεQ hwQ) ?_ btot
  -- the arithmetic: two terms, each below `1/(i+1)` times the step
  have r1 : ratAdd (ratMul KA (ratMul (invWidth (ofNat.{u} j)) w))
      (ratMul KB (ratMul (invWidth (ofNat.{u} j)) w))
      = ratMul (ratMul (ratAdd KA KB) (invWidth (ofNat.{u} j))) w := by
    rw [← ratMul_assoc hKAQ hjQ hwQ, ← ratMul_assoc hKBQ hjQ hwQ,
      ← ratAdd_mul (ratMul_mem_Rat hKAQ hjQ) (ratMul_mem_Rat hKBQ hjQ) hwQ,
      ← ratAdd_mul hKAQ hKBQ hjQ]
  have r2 : ratMul (ratMul (ratAdd ratOne.{u} KL) w) (ratMul (ratAdd ratOne.{u} KM) w)
      = ratMul (ratMul (ratMul (ratAdd ratOne.{u} KL) (ratAdd ratOne.{u} KM)) w) w := by
    rw [ratMul_assoc hCUQ hwQ (ratMul_mem_Rat hCVQ hwQ),
      ← ratMul_assoc hwQ hCVQ hwQ, ratMul_comm hwQ hCVQ,
      ← ratMul_assoc hCUQ (ratMul_mem_Rat hCVQ hwQ) hwQ,
      ← ratMul_assoc hCUQ hCVQ hwQ]
  rw [r1, r2]
  have s1 : ratLe (ratMul (ratMul (ratAdd KA KB) (invWidth (ofNat.{u} j))) w)
      (ratMul (invWidth (ofNat.{u} i)) w) :=
    ratMul_le_mul_right (ratMul_mem_Rat (ratAdd_mem_Rat hKAQ hKBQ) hjQ) hiQ hwQ
      hjlt.left hw0.left
  have s2 : ratLe (ratMul (ratMul (ratMul (ratAdd ratOne.{u} KL) (ratAdd ratOne.{u} KM)) w) w)
      (ratMul (invWidth (ofNat.{u} i)) w) := by
    refine ratMul_le_mul_right (ratMul_mem_Rat (ratMul_mem_Rat hCUQ hCVQ) hwQ) hiQ hwQ ?_
      hw0.left
    refine ratLe_trans (ratMul_mem_Rat (ratMul_mem_Rat hCUQ hCVQ) hwQ)
      (ratMul_mem_Rat (ratMul_mem_Rat hCUQ hCVQ)
        (invWidth_mem_Rat (ofNat_mem_omega.{u} m₃))) hiQ ?_ hm3.left
    · rw [ratMul_comm (ratMul_mem_Rat hCUQ hCVQ) hwQ,
        ratMul_comm (ratMul_mem_Rat hCUQ hCVQ) (invWidth_mem_Rat (ofNat_mem_omega.{u} m₃))]
      exact ratMul_le_mul_right hwQ (invWidth_mem_Rat (ofNat_mem_omega.{u} m₃))
        (ratMul_mem_Rat hCUQ hCVQ) (hfine m₃ (Nat.le_max_right _ m₃))
        (ratZero_le_mul hCUQ hCVQ hCU0 hCV0)
  refine ratLe_trans (ratAdd_mem_Rat (ratMul_mem_Rat (ratMul_mem_Rat
      (ratAdd_mem_Rat hKAQ hKBQ) hjQ) hwQ)
      (ratMul_mem_Rat (ratMul_mem_Rat (ratMul_mem_Rat hCUQ hCVQ) hwQ) hwQ))
    (ratAdd_mem_Rat (ratMul_mem_Rat hiQ hwQ) (ratMul_mem_Rat hiQ hwQ))
    (ratMul_mem_Rat hεQ hwQ)
    (ratAdd_le_add (ratMul_mem_Rat (ratMul_mem_Rat (ratAdd_mem_Rat hKAQ hKBQ) hjQ) hwQ)
      (ratMul_mem_Rat hiQ hwQ)
      (ratMul_mem_Rat (ratMul_mem_Rat (ratMul_mem_Rat hCUQ hCVQ) hwQ) hwQ)
      (ratMul_mem_Rat hiQ hwQ) s1 s2) ?_
  rw [← ratAdd_mul hiQ hiQ hwQ]
  exact ratMul_le_mul_right (ratAdd_mem_Rat hiQ hiQ) hεQ hwQ hi2.left hw0.left

/-! ## The chain rule

The usual obstruction is that the classical proof divides by `F x - F a`, which
may vanish however close `x` is to `a`, and constructively cannot even be
decided to be non-zero. The Carathéodory reformulation exists to avoid that
division.

It is not needed here. The definition above never divides in the first place, so
the composite's slack splits by substitution: apply `G`'s estimate at the point
`F x` with step bound `(1 + |L|)·w`, which is the bound the increment of `F`
already carries, and add `M` times the slack of `F`. No inner difference is ever
inverted, and nothing is decided. -/


/-- The chain rule, with no Carathéodory detour and no division. -/
theorem hasDerivAt_comp {F G : ZFSet.{u} → ZFSet.{u}} {p q p' q' a L M : ZFSet.{u}}
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ realLIcc p' q')
    (hGm : ∀ y, y ∈ realLIcc p' q' → G y ∈ RealL.{u})
    (ha : a ∈ realLIcc p q) (hL : L ∈ RealL.{u}) (hM : M ∈ RealL.{u})
    (hF : HasDerivAt F p q a L) (hG : HasDerivAt G p' q' (F a) M) :
    HasDerivAt (fun x => G (F x)) p q a (realLMul M L) := by
  have haM := ((mem_realLIcc_iff p q a).mp ha).left
  have hFaI := hFm a ha
  have hFa := ((mem_realLIcc_iff p' q' (F a)).mp hFaI).left
  have hGFa := hGm _ hFaI
  obtain ⟨KL, hKLQ, hKL0, hKLb⟩ := exists_rat_bound hL
  obtain ⟨KM, hKMQ, hKM0, hKMb⟩ := exists_rat_bound hM
  have hCQ := ratAdd_mem_Rat ratOne_mem_Rat hKLQ
  have hC1 : ratLe ratOne.{u} (ratAdd ratOne.{u} KL) := by
    have := (ratAdd_le_add_left_iff ratOne_mem_Rat ratZero_mem_Rat hKLQ).mpr hKL0
    rwa [ratAdd_zero ratOne_mem_Rat] at this
  have hC0 : ratLt ratZero.{u} (ratAdd ratOne.{u} KL) :=
    ratLt_of_lt_of_le ratZero_mem_Rat ratOne_mem_Rat hCQ ratZero_lt_one hC1
  intro n
  obtain ⟨i, hi2⟩ := exists_invWidth_add_self_lt.{u} n
  have hiQ := invWidth_mem_Rat (ofNat_mem_omega.{u} i)
  obtain ⟨jG, hjG⟩ := exists_invWidth_mul_lt hCQ hC0.left i
  obtain ⟨jF, hjF⟩ := exists_invWidth_mul_lt hKMQ hKM0 i
  have hjGQ := invWidth_mem_Rat (ofNat_mem_omega.{u} jG)
  have hjFQ := invWidth_mem_Rat (ofNat_mem_omega.{u} jF)
  obtain ⟨mG, hbG⟩ := hG jG
  obtain ⟨mF, hbF⟩ := hF jF
  obtain ⟨m₄, hm4⟩ := exists_invWidth_mul_lt hCQ hC0.left mG
  refine ⟨Nat.max mF m₄, fun w x hwQ hw0 hwle hx hclose => ?_⟩
  have hεQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
  have hxM := ((mem_realLIcc_iff p q x).mp hx).left
  have hFxI := hFm x hx
  have hFx := ((mem_realLIcc_iff p' q' (F x)).mp hFxI).left
  have hGFx := hGm _ hFxI
  have hhM := realLAdd_mem hxM (realLNeg_mem haM)
  have hLh := realLMul_mem hL hhM
  have hfine : ∀ k : Nat, k ≤ Nat.max mF m₄ → ratLe w (invWidth (ofNat.{u} k)) :=
    fun k hk => ratLe_invWidth_of_le hwQ hk hwle
  have cF := hbF w x hwQ hw0 (hfine mF (Nat.le_max_left mF m₄)) hx hclose
  have hSF := realLAdd_mem hFx (realLNeg_mem (realLAdd_mem hFa hLh))
  have hU := realLAdd_mem hFx (realLNeg_mem hFa)
  -- the increment of `F` is bounded by `(1 + |L|)` times the step
  have hUb := withinOf_increment hFx hFa hL hhM hKLQ hwQ hKL0 hw0.left hKLb hclose cF
  -- so `G`'s estimate applies at `F x`, with that bound as its step
  have hw'Q := ratMul_mem_Rat hCQ hwQ
  have hw'0 : ratLt ratZero.{u} (ratMul (ratAdd ratOne.{u} KL) w) := ratMul_pos hCQ hwQ hC0 hw0
  have hw'le : ratLe (ratMul (ratAdd ratOne.{u} KL) w) (invWidth (ofNat.{u} mG)) := by
    refine ratLe_trans hw'Q (ratMul_mem_Rat hCQ (invWidth_mem_Rat (ofNat_mem_omega.{u} m₄)))
      (invWidth_mem_Rat (ofNat_mem_omega.{u} mG)) ?_ hm4.left
    rw [ratMul_comm hCQ hwQ,
      ratMul_comm hCQ (invWidth_mem_Rat (ofNat_mem_omega.{u} m₄))]
    exact ratMul_le_mul_right hwQ (invWidth_mem_Rat (ofNat_mem_omega.{u} m₄)) hCQ
      (hfine m₄ (Nat.le_max_right mF m₄)) hC0.left
  have cG := hbG _ _ hw'Q hw'0 hw'le hFxI hUb
  -- the two pieces, and the identity that assembles them
  have bMS := withinOf_mul hM hSF hKMQ (ratMul_mem_Rat hjFQ hwQ) hKM0
    (ratZero_le_mul hjFQ hwQ (invWidth_pos (ofNat_mem_omega.{u} jF)).left hw0.left) hKMb cF
  have btot := withinOf_add (realLAdd_mem hGFx (realLNeg_mem
      (realLAdd_mem hGFa (realLMul_mem hM hU))))
    (realLMul_mem hM hSF) (ratMul_mem_Rat hjGQ hw'Q) (ratMul_mem_Rat hKMQ
      (ratMul_mem_Rat hjFQ hwQ)) cG bMS
  rw [← realLSub_sub hFx hFa hLh,
    chain_slack hGFx hGFa hM hU hL hhM] at btot
  show WithinOf (realLAdd (G (F x)) (realLNeg (realLAdd (G (F a))
    (realLMul (realLMul M L) (realLAdd x (realLNeg a)))))) _
  rw [realLMul_assoc hM hL hhM]
  refine withinOf_mono (realLAdd_mem hGFx (realLNeg_mem (realLAdd_mem hGFa
      (realLMul_mem hM hLh))))
    (ratAdd_mem_Rat (ratMul_mem_Rat hjGQ hw'Q)
      (ratMul_mem_Rat hKMQ (ratMul_mem_Rat hjFQ hwQ))) (ratMul_mem_Rat hεQ hwQ) ?_ btot
  -- both terms are below `1/(i+1)` times the step
  have r1 : ratMul (invWidth (ofNat.{u} jG)) (ratMul (ratAdd ratOne.{u} KL) w)
      = ratMul (ratMul (ratAdd ratOne.{u} KL) (invWidth (ofNat.{u} jG))) w := by
    rw [← ratMul_assoc hjGQ hCQ hwQ, ratMul_comm hjGQ hCQ]
  have r2 : ratMul KM (ratMul (invWidth (ofNat.{u} jF)) w)
      = ratMul (ratMul KM (invWidth (ofNat.{u} jF))) w := (ratMul_assoc hKMQ hjFQ hwQ).symm
  rw [r1, r2]
  refine ratLe_trans (ratAdd_mem_Rat (ratMul_mem_Rat (ratMul_mem_Rat hCQ hjGQ) hwQ)
      (ratMul_mem_Rat (ratMul_mem_Rat hKMQ hjFQ) hwQ))
    (ratAdd_mem_Rat (ratMul_mem_Rat hiQ hwQ) (ratMul_mem_Rat hiQ hwQ))
    (ratMul_mem_Rat hεQ hwQ)
    (ratAdd_le_add (ratMul_mem_Rat (ratMul_mem_Rat hCQ hjGQ) hwQ) (ratMul_mem_Rat hiQ hwQ)
      (ratMul_mem_Rat (ratMul_mem_Rat hKMQ hjFQ) hwQ) (ratMul_mem_Rat hiQ hwQ)
      (ratMul_le_mul_right (ratMul_mem_Rat hCQ hjGQ) hiQ hwQ hjG.left hw0.left)
      (ratMul_le_mul_right (ratMul_mem_Rat hKMQ hjFQ) hiQ hwQ hjF.left hw0.left)) ?_
  rw [← ratAdd_mul hiQ hiQ hwQ]
  exact ratMul_le_mul_right (ratAdd_mem_Rat hiQ hiQ) hεQ hwQ hi2.left hw0.left





/-- `F'` is a slope function for `F` on `[p, q]`, uniformly in the base point. -/
def HasDerivOn (F F' : ZFSet.{u} → ZFSet.{u}) (p q : ZFSet.{u}) : Prop :=
  ∀ n : Nat, ∃ m : Nat, ∀ w x y, w ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} w →
    ratLe w (invWidth (ofNat.{u} m)) → x ∈ realLIcc p q → y ∈ realLIcc p q →
    Close x y (realLOf w) →
      Close (F x) (realLAdd (F y) (realLMul (F' y) (realLAdd x (realLNeg y))))
        (realLOf (ratMul (invWidth (ofNat.{u} n)) w))

/-- A closed interval inside a closed interval. -/
theorem realLIcc_mono {p q c d : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (hc : c ∈ NumberTheory.Rat.{u}) (hd : d ∈ NumberTheory.Rat.{u}) (hpc : ratLe p c) (hdq : ratLe d q) :
    realLIcc c d ⊆ realLIcc p q := by
  intro x hx
  obtain ⟨hxM, hcx, hxd⟩ := (mem_realLIcc_iff c d x).mp hx
  refine (mem_realLIcc_iff p q x).mpr ⟨hxM, ?_, ?_⟩
  · exact realLLe_trans (realLOf_mem hp) (realLOf_mem hc) hxM
      ((realLOf_le_realLOf hp hc).mpr hpc) hcx
  · exact realLLe_trans hxM (realLOf_mem hd) (realLOf_mem hq) hxd
      ((realLOf_le_realLOf hd hq).mpr hdq)

/-- The local mean value estimate. Two points of the interval within `w` of
each other have values within `(1/(n+1) + K)·w`, where `K` bounds the slope.
This is the mean value inequality for points close enough to be reached in one
step. -/
theorem hasDerivOn_step {F F' : ZFSet.{u} → ZFSet.{u}} {p q K : ZFSet.{u}}
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ RealL.{u})
    (hF'm : ∀ x, x ∈ realLIcc p q → F' x ∈ RealL.{u})
    (hd : HasDerivOn F F' p q) (hK : K ∈ NumberTheory.Rat.{u}) (hK0 : ratLe ratZero.{u} K)
    (hbd : ∀ x, x ∈ realLIcc p q → WithinOf (F' x) (realLOf K)) (n : Nat) :
    ∃ m : Nat, ∀ w x y, w ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} w →
      ratLe w (invWidth (ofNat.{u} m)) → x ∈ realLIcc p q → y ∈ realLIcc p q →
      Close x y (realLOf w) →
        Close (F x) (F y) (realLOf (ratMul (ratAdd (invWidth (ofNat.{u} n)) K) w)) := by
  obtain ⟨m, hm⟩ := hd n
  refine ⟨m, fun w x y hwQ hw0 hwle hx hy hclose => ?_⟩
  have hxM := ((mem_realLIcc_iff p q x).mp hx).left
  have hyM := ((mem_realLIcc_iff p q y).mp hy).left
  exact withinOf_increment_sharp (hFm x hx) (hFm y hy) (hF'm y hy)
    (realLAdd_mem hxM (realLNeg_mem hyM)) hK hwQ hK0 hw0.left (hbd y hy) hclose
    (hm w x y hwQ hw0 hwle hx hy hclose)


/-- Deciding whether a real vanishes, as data rather than as a disjunction. -/
structure VanishReadout : Type (u + 1) where
  bit : ZFSet.{u} → ZFSet.{u}
  mem_two : ∀ z, z ∈ RealL.{u} → bit z ∈ ofNat.{u} 2
  zero : ∀ z, z ∈ RealL.{u} → bit z = empty.{u} → z = realLZero.{u}
  apart : ∀ z, z ∈ RealL.{u} → bit z = ofNat.{u} 1 → realLApart realLZero.{u} z

/-- Uniform continuity on `[p, q]`, with the modulus quantified per scale. -/
def UniformlyContinuousOn (H : ZFSet.{u} → ZFSet.{u}) (p q : ZFSet.{u}) : Prop :=
  ∀ n : Nat, ∃ m : Nat, ∀ w x y, w ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} w →
    ratLe w (invWidth (ofNat.{u} m)) → x ∈ realLIcc p q → y ∈ realLIcc p q →
    Close x y (realLOf w) → Close (H x) (H y) (realLOf (invWidth (ofNat.{u} n)))


/-- A rational between the endpoints names a point of the interval. -/
theorem realLOf_mem_realLIcc {p q x : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (hx : x ∈ NumberTheory.Rat.{u}) (hpx : ratLe p x) (hxq : ratLe x q) :
    realLOf x ∈ realLIcc p q :=
  (mem_realLIcc_iff p q _).mpr ⟨realLOf_mem hx, (realLOf_le_realLOf hp hx).mpr hpx,
    (realLOf_le_realLOf hx hq).mpr hxq⟩

#print axioms HasDerivOn


/-- The point a fraction `t` of the way from `a` to `x`. -/
def segment (a x t : ZFSet.{u}) : ZFSet.{u} :=
  realLAdd a (realLMul t (realLAdd x (realLNeg a)))

/-- The diameter bound. The difference of two points of `[p, q]` is within
`q - p`, with no sign decided: each side of the bracket is the sum of the two
one-sided estimates. -/
theorem withinOf_diam {p q z y : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (hz : z ∈ realLIcc p q) (hy : y ∈ realLIcc p q) :
    WithinOf (realLAdd z (realLNeg y)) (realLOf (ratAdd q (ratNeg p))) := by
  obtain ⟨hzR, hpz, hzq⟩ := (mem_realLIcc_iff p q z).mp hz
  obtain ⟨hyR, hpy, hyq⟩ := (mem_realLIcc_iff p q y).mp hy
  have hnp := ratNeg_mem_Rat hp
  have hnq := ratNeg_mem_Rat hq
  have hQ := ratAdd_mem_Rat hq hnp
  constructor
  · have h := realLLe_add (realLOf_mem hp) hzR (realLNeg_mem (realLOf_mem hq))
      (realLNeg_mem hyR) hpz (realLNeg_le_neg hyR (realLOf_mem hq) hyq)
    have hid : realLNeg (realLOf (ratAdd q (ratNeg p)))
        = realLAdd (realLOf p) (realLNeg (realLOf q)) := by
      rw [realLOf_neg hQ, ratNeg_add hq hnp, ratNeg_ratNeg hp,
        ratAdd_comm hnq hp, realLOf_add hp hnq, realLOf_neg hq]
    rw [hid]
    exact h
  · have h := realLLe_add hzR (realLOf_mem hq) (realLNeg_mem hyR)
      (realLNeg_mem (realLOf_mem hp)) hzq (realLNeg_le_neg (realLOf_mem hp) hyR hpy)
    rw [realLOf_add hq hnp, ← realLOf_neg hp]
    exact h

/-! ## Tagged partitions

`tag_ge` and `tag_le` are the load-bearing fields. The per-cell error from
subtracting two estimates at the tag is `eps * (|u - t| + |v - t|)`, which is
`eps * (v - u)` exactly when the tag lies in its cell, and is bounded below by
a constant when it does not. An integral quantifies over shrinking widths, so a
tag that is merely near its cell gives a sum that diverges. -/

/-- A tagged partition of `[c, d]` by rational cut points, each cell carrying a
tag inside it. `pt` and `tag` are total functions; only the first `len` cells
are used, and the fields are stated for every index so that constructing one
needs no bounds bookkeeping. -/
structure TaggedPartition (c d : ZFSet.{u}) : Type (u + 1) where
  len : Nat
  pt : Nat → ZFSet.{u}
  tag : Nat → ZFSet.{u}
  pt_mem : ∀ i, pt i ∈ NumberTheory.Rat.{u}
  tag_mem : ∀ i, tag i ∈ NumberTheory.Rat.{u}
  pt_zero : pt 0 = c
  pt_len : pt len = d
  mono : ∀ i, ratLe (pt i) (pt (i + 1))
  tag_ge : ∀ i, ratLe (pt i) (tag i)
  tag_le : ∀ i, ratLe (tag i) (pt (i + 1))

#print axioms withinOf_realLOf_iff
#print axioms withinOf_mono
#print axioms withinOf_self
#print axioms withinOf_add
#print axioms withinOf_neg
#print axioms withinOf_mul
#print axioms close_of_close_close
#print axioms withinOf_zero
#print axioms exists_invWidth_add_self_lt
#print axioms exists_invWidth_mul_lt
#print axioms ratLe_invWidth_of_le
#print axioms close_add_lin
#print axioms exists_rat_bound
#print axioms invWidth_le_one
#print axioms withinOf_increment_sharp
#print axioms withinOf_increment
#print axioms hasDerivAt_mul
#print axioms hasDerivAt_comp
#print axioms realLIcc_mono
#print axioms hasDerivOn_step
#print axioms realLOf_mem_realLIcc
#print axioms withinOf_diam

/-- From `Close A B e`: `A ≤ B + e`. `[propext, Quot.sound]`. -/
theorem le_add_radius_of_close {A B e : ZFSet.{u}} (hA : A ∈ RealL.{u})
    (hB : B ∈ RealL.{u}) (he : e ∈ RealL.{u}) (h : Close A B e) :
    realLLe A (realLAdd B e) := by
  have hstep := realLLe_add_right (realLAdd_mem hA (realLNeg_mem hB)) he hB
    h.right
  rw [realLSub_add_cancel hA hB] at hstep
  rwa [realLAdd_comm he hB] at hstep

#print axioms le_add_radius_of_close

#print axioms box_le
#print axioms small_box
#print axioms bracket_bounds
#print axioms group_shuffle
end Analysis

namespace ZFSet
export Analysis (HasDerivAt HasDerivOn TaggedPartition UniformlyContinuousOn VanishReadout close_add_lin close_of_close_close close_realLOf_sub_self exists_invWidth_add_self_lt exists_invWidth_mul_lt exists_rat_bound hasDerivAt_comp hasDerivAt_mul hasDerivOn_step invWidth_le_one product_slack ratLe_invWidth_of_le realLIcc_mono realLOf_mem_realLIcc segment withinOf_add withinOf_diam withinOf_increment withinOf_increment_sharp withinOf_mono withinOf_mul withinOf_neg withinOf_realLOf_iff withinOf_self withinOf_zero)
end ZFSet
