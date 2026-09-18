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

/-! ## The mean value inequality

What survives is the inequality, `|F d - F c| ≤ K·(d - c)` when `K` bounds
the slope, and applications of the mean value theorem need no more. Nothing is
located: the estimate is chained along the grid of `IVT.lean`, each step
bounded in terms of its own width rather than the mesh, so the widths telescope
to `d - c` exactly. The scale `1/(n+1)` left over at each step is then sent to
zero, which `withinOf_of_margins` does. -/

theorem ratSub_add_sub {a b c : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u}) (hb : b ∈ NumberTheory.Rat.{u})
    (hc : c ∈ NumberTheory.Rat.{u}) :
    ratAdd (ratAdd b (ratNeg a)) (ratAdd a (ratNeg c)) = ratAdd b (ratNeg c) := by
  rw [ratAdd_assoc hb (ratNeg_mem_Rat ha) (ratAdd_mem_Rat ha (ratNeg_mem_Rat hc)),
    ← ratAdd_assoc (ratNeg_mem_Rat ha) ha (ratNeg_mem_Rat hc),
    ratAdd_comm (ratNeg_mem_Rat ha) ha, ratAdd_neg ha,
    ratZero_add (ratNeg_mem_Rat hc)]

/-- A bound that holds up to every scale holds. The margin is a rational, so
the witness separating `z` from `b` is a rational too, and a fine enough scale
fits inside the gap it leaves. -/
theorem withinOf_of_margins {z b : ZFSet.{u}} (hb : b ∈ NumberTheory.Rat.{u})
    (h : ∀ k : Nat, WithinOf z (realLOf (ratAdd b (invWidth (ofNat.{u} k))))) :
    WithinOf z (realLOf b) := by
  constructor
  · rintro ⟨t, htU, htL⟩
    rw [realLOf_neg hb, realLOf, fst_opair] at htL
    obtain ⟨htQ, htb⟩ := (mem_ratCut_iff _ t).mp htL
    -- `t < -b`, so a scale below the gap puts `t` under `-(b + 1/(k+1))`
    have hgap : ratLt ratZero.{u} (ratAdd (ratNeg b) (ratNeg t)) := by
      have := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat htQ) htQ (ratNeg_mem_Rat hb)).mpr htb
      rw [ratAdd_neg htQ] at this
      exact this
    obtain ⟨N, hN, hNlt⟩ := exists_invWidth_lt
      (ratAdd_mem_Rat (ratNeg_mem_Rat hb) (ratNeg_mem_Rat htQ)) hgap
    obtain ⟨k, rfl⟩ := (mem_omega_iff N).mp hN
    refine (h k).left ?_
    rw [realLOf_neg (ratAdd_mem_Rat hb (invWidth_mem_Rat (ofNat_mem_omega.{u} k)))]
    refine ⟨t, htU, ?_⟩
    rw [realLOf, fst_opair]
    refine (mem_ratCut_iff _ t).mpr ⟨htQ, ?_⟩
    -- `1/(k+1) < -b - t` rearranges to `t < -(b + 1/(k+1))`
    have hkQ := invWidth_mem_Rat (ofNat_mem_omega.{u} k)
    have hstep := (ratAdd_lt_add_right_iff htQ hkQ
      (ratAdd_mem_Rat (ratNeg_mem_Rat hb) (ratNeg_mem_Rat htQ))).mpr hNlt
    rw [ratAdd_assoc (ratNeg_mem_Rat hb) (ratNeg_mem_Rat htQ) htQ,
      ratAdd_comm (ratNeg_mem_Rat htQ) htQ, ratAdd_neg htQ,
      ratAdd_zero (ratNeg_mem_Rat hb)] at hstep
    have hfinal := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat hkQ)
      (ratAdd_mem_Rat hkQ htQ) (ratNeg_mem_Rat hb)).mpr hstep
    rw [ratAdd_comm hkQ htQ, ratAdd_assoc htQ hkQ (ratNeg_mem_Rat hkQ),
      ratAdd_neg hkQ, ratAdd_zero htQ, ← ratNeg_add hb hkQ] at hfinal
    exact hfinal
  · rintro ⟨t, htU, htL⟩
    rw [realLOf, snd_opair] at htU
    obtain ⟨htQ, hbt⟩ := (mem_sep_iff _ t _).mp htU
    have hgap : ratLt ratZero.{u} (ratAdd t (ratNeg b)) := by
      have := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat hb) hb htQ).mpr hbt
      rwa [ratAdd_neg hb] at this
    obtain ⟨N, hN, hNlt⟩ := exists_invWidth_lt
      (ratAdd_mem_Rat htQ (ratNeg_mem_Rat hb)) hgap
    obtain ⟨k, rfl⟩ := (mem_omega_iff N).mp hN
    have hkQ := invWidth_mem_Rat (ofNat_mem_omega.{u} k)
    refine (h k).right ⟨t, ?_, htL⟩
    rw [realLOf, snd_opair]
    refine (mem_sep_iff _ t _).mpr ⟨htQ, ?_⟩
    have hstep := (ratAdd_lt_add_right_iff hb hkQ
      (ratAdd_mem_Rat htQ (ratNeg_mem_Rat hb))).mpr hNlt
    rw [ratAdd_assoc htQ (ratNeg_mem_Rat hb) hb,
      ratAdd_comm (ratNeg_mem_Rat hb) hb, ratAdd_neg hb, ratAdd_zero htQ] at hstep
    rwa [ratAdd_comm hkQ hb] at hstep

/-- A grid step either goes nowhere -- the walk has reached the right endpoint --
or is positive and no wider than the mesh. Rational trichotomy decides which,
which costs nothing. -/
theorem gridPoint_succ_cases {c d : ZFSet.{u}} (hc : c ∈ NumberTheory.Rat.{u}) (hd : d ∈ NumberTheory.Rat.{u})
    (m i : Nat) :
    gridPoint c d m (i + 1) = gridPoint c d m i ∨
      (ratLt ratZero.{u} (ratAdd (gridPoint c d m (i + 1)) (ratNeg (gridPoint c d m i))) ∧
        ratLe (ratAdd (gridPoint c d m (i + 1)) (ratNeg (gridPoint c d m i)))
          (invWidth (ofNat.{u} m))) := by
  have hgi := gridPoint_mem_Rat hc hd m i
  have hgi' := gridPoint_mem_Rat hc hd m (i + 1)
  have hsQ := ratAdd_mem_Rat hgi' (ratNeg_mem_Rat hgi)
  have hs0 : ratLe ratZero.{u} (ratAdd (gridPoint c d m (i + 1))
      (ratNeg (gridPoint c d m i))) := by
    have := (ratAdd_le_add_right_iff (ratNeg_mem_Rat hgi) hgi hgi').mpr
      (gridPoint_le_succ hc hd m i)
    rwa [ratAdd_neg hgi] at this
  rcases ratLt_trichotomy ratZero_mem_Rat hsQ with hpos | heq | hneg
  · refine Or.inr ⟨hpos, ?_⟩
    exact (sub_le_iff_le_add hgi' hgi (invWidth_mem_Rat (ofNat_mem_omega.{u} m))).mpr
      (gridPoint_step_le hc hd m i)
  · refine Or.inl ?_
    have h1 := sub_add_cancel hgi' hgi
    rw [← heq, ratZero_add hgi] at h1
    exact h1.symm
  · exact absurd hs0 (fun hle => ratLt_irrefl
      (ratLt_of_le_of_lt ratZero_mem_Rat hsQ ratZero_mem_Rat hle hneg))

/-- Consecutive grid points are within their own step of each other. -/
theorem gridPoint_close_step {c d : ZFSet.{u}} (hc : c ∈ NumberTheory.Rat.{u}) (hd : d ∈ NumberTheory.Rat.{u})
    (m i : Nat) (hs : ratLt ratZero.{u}
      (ratAdd (gridPoint c d m (i + 1)) (ratNeg (gridPoint c d m i)))) :
    Close (realLOf (gridPoint c d m (i + 1))) (realLOf (gridPoint c d m i))
      (realLOf (ratAdd (gridPoint c d m (i + 1)) (ratNeg (gridPoint c d m i)))) := by
  have hgi := gridPoint_mem_Rat hc hd m i
  have hgi' := gridPoint_mem_Rat hc hd m (i + 1)
  have hsQ := ratAdd_mem_Rat hgi' (ratNeg_mem_Rat hgi)
  refine close_realLOf hgi' hgi hsQ ?_ (ratLe_refl hsQ)
  refine ratLe_trans (ratNeg_mem_Rat hsQ) ratZero_mem_Rat hsQ ?_ hs.left
  have := (ratNeg_le_neg_iff hsQ ratZero_mem_Rat).mpr hs.left
  rwa [ratNeg_zero] at this

/-- One grid step, bounded by its own width rather than by the mesh, so the
widths telescope. The step may be zero, because clamping at the
right endpoint makes it so, and that case is decided by rational trichotomy. -/
private theorem mvi_step {F : ZFSet.{u} → ZFSet.{u}} {p q c d C : ZFSet.{u}} {m : Nat}
    (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hc : c ∈ NumberTheory.Rat.{u}) (hd : d ∈ NumberTheory.Rat.{u})
    (hpc : ratLe p c) (hdq : ratLe d q) (hcd : ratLe c d)
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ RealL.{u}) (hC : C ∈ NumberTheory.Rat.{u})
    (hstep : ∀ w x y, w ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} w →
      ratLe w (invWidth (ofNat.{u} m)) → x ∈ realLIcc p q → y ∈ realLIcc p q →
      Close x y (realLOf w) → Close (F x) (F y) (realLOf (ratMul C w)))
    (i : Nat) :
    WithinOf (realLAdd (F (realLOf (gridPoint c d m (i + 1))))
        (realLNeg (F (realLOf (gridPoint c d m i)))))
      (realLOf (ratMul C (ratAdd (gridPoint c d m (i + 1))
        (ratNeg (gridPoint c d m i))))) := by
  have hgi := gridPoint_mem_Rat hc hd m i
  have hgi' := gridPoint_mem_Rat hc hd m (i + 1)
  have hsQ := ratAdd_mem_Rat hgi' (ratNeg_mem_Rat hgi)
  have hin : ∀ k : Nat, realLOf (gridPoint c d m k) ∈ realLIcc p q := fun k =>
    realLIcc_mono hp hq hc hd hpc hdq _ (gridPoint_mem_Icc hc hd hcd m k)
  rcases gridPoint_succ_cases hc hd m i with hEq | ⟨hpos, hle⟩
  · rw [hEq, realLAdd_neg (hFm _ (hin i)), ratAdd_neg hgi, ratMul_zero hC]
    exact withinOf_zero ratZero_mem_Rat (ratLe_refl ratZero_mem_Rat)
  · exact hstep _ _ _ hsQ hpos hle (hin (i + 1)) (hin i)
      (gridPoint_close_step hc hd m i hpos)

/-- The chained estimate, along the grid. -/
private theorem mvi_grid {F : ZFSet.{u} → ZFSet.{u}} {p q c d C : ZFSet.{u}} {m : Nat}
    (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hc : c ∈ NumberTheory.Rat.{u}) (hd : d ∈ NumberTheory.Rat.{u})
    (hpc : ratLe p c) (hdq : ratLe d q) (hcd : ratLt c d)
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ RealL.{u}) (hC : C ∈ NumberTheory.Rat.{u})
    (hstep : ∀ w x y, w ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} w →
      ratLe w (invWidth (ofNat.{u} m)) → x ∈ realLIcc p q → y ∈ realLIcc p q →
      Close x y (realLOf w) → Close (F x) (F y) (realLOf (ratMul C w))) :
    ∀ i : Nat, WithinOf (realLAdd (F (realLOf (gridPoint c d m i)))
        (realLNeg (F (realLOf c))))
      (realLOf (ratMul C (ratAdd (gridPoint c d m i) (ratNeg c)))) := by
  have hin : ∀ k : Nat, realLOf (gridPoint c d m k) ∈ realLIcc p q := fun k =>
    realLIcc_mono hp hq hc hd hpc hdq _ (gridPoint_mem_Icc hc hd hcd.left m k)
  intro i
  induction i with
  | zero =>
    rw [gridPoint_zero hc hcd m, realLAdd_neg (hFm _ (by
      have := hin 0
      rwa [gridPoint_zero hc hcd m] at this)), ratAdd_neg hc, ratMul_zero hC]
    exact withinOf_zero ratZero_mem_Rat (ratLe_refl ratZero_mem_Rat)
  | succ i ih =>
    have hgi := gridPoint_mem_Rat hc hd m i
    have hgi' := gridPoint_mem_Rat hc hd m (i + 1)
    have hFc : F (realLOf c) ∈ RealL.{u} := hFm _ (by
      have := hin 0
      rwa [gridPoint_zero hc hcd m] at this)
    have hb := withinOf_add
      (realLAdd_mem (hFm _ (hin (i + 1))) (realLNeg_mem (hFm _ (hin i))))
      (realLAdd_mem (hFm _ (hin i)) (realLNeg_mem hFc))
      (ratMul_mem_Rat hC (ratAdd_mem_Rat hgi' (ratNeg_mem_Rat hgi)))
      (ratMul_mem_Rat hC (ratAdd_mem_Rat hgi (ratNeg_mem_Rat hc)))
      (mvi_step hp hq hc hd hpc hdq hcd.left hFm hC hstep i) ih
    rw [realLSub_add_sub (hFm _ (hin i)) (hFm _ (hin (i + 1))) hFc,
      ← ratMul_add hC (ratAdd_mem_Rat hgi' (ratNeg_mem_Rat hgi))
        (ratAdd_mem_Rat hgi (ratNeg_mem_Rat hc)),
      ratSub_add_sub hgi hgi' hc] at hb
    exact hb

/-- The mean value inequality. A function whose slope is bounded by `K` on
`[p, q]` moves by at most `K` times the distance -- and no point is located, so
no principle is spent. -/
theorem hasDerivOn_mvi {F F' : ZFSet.{u} → ZFSet.{u}} {p q c d K : ZFSet.{u}}
    (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hc : c ∈ NumberTheory.Rat.{u}) (hd : d ∈ NumberTheory.Rat.{u})
    (hpc : ratLe p c) (hdq : ratLe d q) (hcd : ratLt c d)
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ RealL.{u})
    (hF'm : ∀ x, x ∈ realLIcc p q → F' x ∈ RealL.{u})
    (hderiv : HasDerivOn F F' p q) (hK : K ∈ NumberTheory.Rat.{u}) (hK0 : ratLe ratZero.{u} K)
    (hbd : ∀ x, x ∈ realLIcc p q → WithinOf (F' x) (realLOf K)) :
    WithinOf (realLAdd (F (realLOf d)) (realLNeg (F (realLOf c))))
      (realLOf (ratMul K (ratAdd d (ratNeg c)))) := by
  have hgapQ := ratAdd_mem_Rat hd (ratNeg_mem_Rat hc)
  have hgap0 : ratLe ratZero.{u} (ratAdd d (ratNeg c)) := by
    have := (ratAdd_le_add_right_iff (ratNeg_mem_Rat hc) hc hd).mpr hcd.left
    rwa [ratAdd_neg hc] at this
  refine withinOf_of_margins (ratMul_mem_Rat hK hgapQ) (fun k => ?_)
  -- a scale whose contribution over the whole interval is below `1/(k+1)`
  obtain ⟨n, hn⟩ := exists_invWidth_mul_lt hgapQ hgap0 k
  have hnQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
  obtain ⟨m, hstep⟩ := hasDerivOn_step hFm hF'm hderiv hK hK0 hbd n
  obtain ⟨N, hN⟩ := exists_ladder_ge hc hd m
  have hgrid := mvi_grid hp hq hc hd hpc hdq hcd hFm (ratAdd_mem_Rat hnQ hK) hstep N
  rw [gridPoint_eq_right hN] at hgrid
  refine withinOf_mono (realLAdd_mem (hFm _ (realLIcc_mono hp hq hc hd hpc hdq _
      (right_mem_realLIcc hc hd hcd.left)))
    (realLNeg_mem (hFm _ (realLIcc_mono hp hq hc hd hpc hdq _
      (left_mem_realLIcc hc hd hcd.left)))))
    (ratMul_mem_Rat (ratAdd_mem_Rat hnQ hK) hgapQ)
    (ratAdd_mem_Rat (ratMul_mem_Rat hK hgapQ)
      (invWidth_mem_Rat (ofNat_mem_omega.{u} k))) ?_ hgrid
  -- `(1/(n+1) + K)·(d - c) = K·(d - c) + (1/(n+1))·(d - c) ≤ K·(d - c) + 1/(k+1)`
  rw [ratAdd_mul hnQ hK hgapQ, ratAdd_comm (ratMul_mem_Rat hnQ hgapQ)
    (ratMul_mem_Rat hK hgapQ)]
  refine (ratAdd_le_add_left_iff (ratMul_mem_Rat hK hgapQ) (ratMul_mem_Rat hnQ hgapQ)
    (invWidth_mem_Rat (ofNat_mem_omega.{u} k))).mpr ?_
  rw [ratMul_comm hnQ hgapQ]
  exact hn.left

/-- A function with zero slope is constant, at the endpoints of every
rational subinterval. The `K = 0` case of the inequality. -/
theorem eq_of_hasDerivOn_zero {F F' : ZFSet.{u} → ZFSet.{u}} {p q c d : ZFSet.{u}}
    (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hc : c ∈ NumberTheory.Rat.{u}) (hd : d ∈ NumberTheory.Rat.{u})
    (hpc : ratLe p c) (hdq : ratLe d q) (hcd : ratLt c d)
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ RealL.{u})
    (hF'm : ∀ x, x ∈ realLIcc p q → F' x ∈ RealL.{u})
    (hderiv : HasDerivOn F F' p q)
    (hzero : ∀ x, x ∈ realLIcc p q → F' x = realLZero.{u}) :
    F (realLOf d) = F (realLOf c) := by
  have hFd := hFm _ (realLIcc_mono hp hq hc hd hpc hdq _
    (right_mem_realLIcc hc hd hcd.left))
  have hFc := hFm _ (realLIcc_mono hp hq hc hd hpc hdq _
    (left_mem_realLIcc hc hd hcd.left))
  have hbd : ∀ x, x ∈ realLIcc p q → WithinOf (F' x) (realLOf ratZero.{u}) := by
    intro x hx
    rw [hzero x hx]
    exact withinOf_zero ratZero_mem_Rat (ratLe_refl ratZero_mem_Rat)
  have hmvi := hasDerivOn_mvi hp hq hc hd hpc hdq hcd hFm hF'm hderiv
    ratZero_mem_Rat (ratLe_refl ratZero_mem_Rat) hbd
  rw [ratZero_mul (ratAdd_mem_Rat hd (ratNeg_mem_Rat hc))] at hmvi
  have hdiff : realLAdd (F (realLOf d)) (realLNeg (F (realLOf c))) = realLZero.{u} :=
    eq_zero_of_within_all (realLAdd_mem hFd (realLNeg_mem hFc)) (fun j =>
      withinOf_mono (realLAdd_mem hFd (realLNeg_mem hFc)) ratZero_mem_Rat
        (invWidth_mem_Rat (ofNat_mem_omega.{u} j))
        (invWidth_pos (ofNat_mem_omega.{u} j)).left hmvi)
  refine realLAdd_right_cancel hFd hFc (realLNeg_mem hFc) ?_
  rw [realLAdd_neg hFc]
  exact hdiff

/-! ## Monotonicity

The one-sided companion of the inequality, and the first statement here whose
conclusion is an order fact about `F` rather than a bound on it. The chain is
the same grid; what changes is that the slack is spent on one side only, so a
non-negative slope survives it. -/


/-- An order bound that holds up to every scale holds. The real analogue of
`withinOf_of_margins`; the gap is a positive real rather than a rational, so it
takes `exists_pos_lower` to name a rational inside it first. -/
theorem realLLe_of_margins {z b : ZFSet.{u}} (hz : z ∈ RealL.{u}) (hb : b ∈ RealL.{u})
    (h : ∀ k : Nat, realLLe z (realLAdd b (realLOf (invWidth (ofNat.{u} k))))) :
    realLLe z b := by
  rintro ⟨t, htU, htL⟩
  have htQ : t ∈ NumberTheory.Rat.{u} := ((mem_Real_iff _).mp (toCut_mem hz)).subset t htL
  have hbt : realLLt b (realLOf t) := (lt_realLOf_iff_mem_upper hb htQ).mpr htU
  have htz : realLLt (realLOf t) z := (realLOf_lt_iff_mem_lower hz htQ).mpr htL
  -- a positive rational inside the gap between `b` and `t`
  have hgapM := realLAdd_mem (realLOf_mem htQ) (realLNeg_mem hb)
  obtain ⟨e, heL, he0⟩ := exists_pos_lower ((realLLt_sub_pos hb (realLOf_mem htQ)).mp hbt)
  have heQ : e ∈ NumberTheory.Rat.{u} := ((mem_Real_iff _).mp (toCut_mem hgapM)).subset e heL
  obtain ⟨N, hN, hNe⟩ := exists_invWidth_lt heQ he0
  obtain ⟨k, rfl⟩ := (mem_omega_iff N).mp hN
  have hkQ := invWidth_mem_Rat (ofNat_mem_omega.{u} k)
  have hlt1 : realLLt (realLOf (invWidth (ofNat.{u} k)))
      (realLAdd (realLOf t) (realLNeg b)) :=
    realLLt_trans (realLOf_mem hkQ) (realLOf_mem heQ) hgapM
      ((realLOf_lt_realLOf hkQ heQ).mpr hNe)
      ((realLOf_lt_iff_mem_lower hgapM heQ).mpr heL)
  have hstep := realLLt_add_right (realLOf_mem hkQ) hgapM hb hlt1
  rw [realLSub_add_cancel (realLOf_mem htQ) hb,
    realLAdd_comm (realLOf_mem hkQ) hb] at hstep
  exact h k (realLLt_trans (realLAdd_mem hb (realLOf_mem hkQ)) (realLOf_mem htQ) hz
    hstep htz)



/-- Shifting by a constant leaves the difference alone. -/
theorem close_shift {x y k δ : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hk : k ∈ RealL.{u})
    (h : Close x y δ) :
    Close (realLAdd x k) (realLAdd y k) δ := by
  show WithinOf (realLAdd (realLAdd x k) (realLNeg (realLAdd y k))) δ
  have hid : realLAdd (realLAdd x k) (realLNeg (realLAdd y k))
      = realLAdd x (realLNeg y) := by
    rw [realLNeg_realLAdd hy hk,
      realLAdd_interchange hx hk (realLNeg_mem hy) (realLNeg_mem hk),
      realLAdd_neg hk, realLAdd_zero (realLAdd_mem hx (realLNeg_mem hy))]
  rw [hid]
  exact h


/-- The chained one-sided estimate: the slack accumulates on one side, so a
non-negative slope survives it. -/
private theorem mono_grid {F F' : ZFSet.{u} → ZFSet.{u}} {p q c d : ZFSet.{u}} {m n : Nat}
    (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hc : c ∈ NumberTheory.Rat.{u}) (hd : d ∈ NumberTheory.Rat.{u})
    (hpc : ratLe p c) (hdq : ratLe d q) (hcd : ratLt c d)
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ RealL.{u})
    (hF'm : ∀ x, x ∈ realLIcc p q → F' x ∈ RealL.{u})
    (hnn : ∀ i : Nat, realLLe realLZero.{u} (F' (realLOf (gridPoint c d m i))))
    (hm : ∀ w x y, w ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} w →
      ratLe w (invWidth (ofNat.{u} m)) → x ∈ realLIcc p q → y ∈ realLIcc p q →
      Close x y (realLOf w) →
      Close (F x) (realLAdd (F y) (realLMul (F' y) (realLAdd x (realLNeg y))))
        (realLOf (ratMul (invWidth (ofNat.{u} n)) w))) :
    ∀ i : Nat, realLLe (F (realLOf c))
      (realLAdd (F (realLOf (gridPoint c d m i)))
        (realLOf (ratMul (invWidth (ofNat.{u} n))
          (ratAdd (gridPoint c d m i) (ratNeg c))))) := by
  have hnQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
  have hin : ∀ k : Nat, realLOf (gridPoint c d m k) ∈ realLIcc p q := fun k =>
    realLIcc_mono hp hq hc hd hpc hdq _ (gridPoint_mem_Icc hc hd hcd.left m k)
  have hcin : realLOf c ∈ realLIcc p q := by
    have := hin 0
    rwa [gridPoint_zero hc hcd m] at this
  have hFc := hFm _ hcin
  intro i
  induction i with
  | zero =>
    rw [gridPoint_zero hc hcd m, ratAdd_neg hc, ratMul_zero hnQ]
    show realLLe (F (realLOf c)) (realLAdd (F (realLOf c)) realLZero.{u})
    rw [realLAdd_zero hFc]
    exact realLLe_refl hFc
  | succ i ih =>
    have hgi := gridPoint_mem_Rat hc hd m i
    have hgi' := gridPoint_mem_Rat hc hd m (i + 1)
    have hsQ := ratAdd_mem_Rat hgi' (ratNeg_mem_Rat hgi)
    have hA := hFm _ (hin i)
    have hB := hFm _ (hin (i + 1))
    have hM := realLOf_mem (ratMul_mem_Rat hnQ (ratAdd_mem_Rat hgi (ratNeg_mem_Rat hc)))
    rcases gridPoint_succ_cases hc hd m i with hEq | ⟨hpos, hle⟩
    · rw [hEq]
      exact ih
    · have hE := realLOf_mem (ratMul_mem_Rat hnQ hsQ)
      have hest := hm _ _ _ hsQ hpos hle (hin (i + 1)) (hin i)
        (gridPoint_close_step hc hd m i hpos)
      rw [realLOf_neg hgi, ← realLOf_add hgi' (ratNeg_mem_Rat hgi)] at hest
      have hP := realLMul_mem (hF'm _ (hin i)) (realLOf_mem hsQ)
      -- the linear part is non-negative, so it can be dropped
      have hP0 : realLLe realLZero.{u} (realLMul (F' (realLOf (gridPoint c d m i)))
          (realLOf (ratAdd (gridPoint c d m (i + 1)) (ratNeg (gridPoint c d m i))))) :=
        realLMul_nonneg (hF'm _ (hin i)) (realLOf_mem hsQ) (hnn i)
          ((realLOf_le_realLOf ratZero_mem_Rat hsQ).mpr hpos.left)
      have hAP : realLLe (F (realLOf (gridPoint c d m i)))
          (realLAdd (F (realLOf (gridPoint c d m i)))
            (realLMul (F' (realLOf (gridPoint c d m i)))
              (realLOf (ratAdd (gridPoint c d m (i + 1))
                (ratNeg (gridPoint c d m i)))))) := by
        have := realLLe_add_right realLZero_mem hP hA hP0
        rwa [realLAdd_comm realLZero_mem hA, realLAdd_zero hA,
          realLAdd_comm hP hA] at this
      have hstep : realLLe (F (realLOf (gridPoint c d m i)))
          (realLAdd (F (realLOf (gridPoint c d m (i + 1))))
            (realLOf (ratMul (invWidth (ofNat.{u} n))
              (ratAdd (gridPoint c d m (i + 1)) (ratNeg (gridPoint c d m i)))))) :=
        realLLe_trans hA (realLAdd_mem hA hP) (realLAdd_mem hB hE) hAP
          (le_add_of_neg_le_sub' hB (realLAdd_mem hA hP) hE hest.left)
      -- chain it onto the induction hypothesis and add the two margins
      have hchain := realLLe_trans hFc (realLAdd_mem hA hM)
        (realLAdd_mem (realLAdd_mem hB hE) hM) ih
        (realLLe_add_right hA (realLAdd_mem hB hE) hM hstep)
      rw [realLAdd_assoc hB hE hM, ← realLOf_add (ratMul_mem_Rat hnQ hsQ)
          (ratMul_mem_Rat hnQ (ratAdd_mem_Rat hgi (ratNeg_mem_Rat hc))),
        ← ratMul_add hnQ hsQ (ratAdd_mem_Rat hgi (ratNeg_mem_Rat hc)),
        ratSub_add_sub hgi hgi' hc] at hchain
      exact hchain

/-- A non-negative slope makes the function non-decreasing. No point is
located and no order on the reals is decided: the estimate is chained along the
grid, and `realLLe_of_margins` disposes of the accumulated scale. -/
theorem hasDerivOn_mono {F F' : ZFSet.{u} → ZFSet.{u}} {p q c d : ZFSet.{u}}
    (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hc : c ∈ NumberTheory.Rat.{u}) (hd : d ∈ NumberTheory.Rat.{u})
    (hpc : ratLe p c) (hdq : ratLe d q) (hcd : ratLt c d)
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ RealL.{u})
    (hF'm : ∀ x, x ∈ realLIcc p q → F' x ∈ RealL.{u})
    (hderiv : HasDerivOn F F' p q)
    (hnn : ∀ x, x ∈ realLIcc p q → realLLe realLZero.{u} (F' x)) :
    realLLe (F (realLOf c)) (F (realLOf d)) := by
  have hgapQ := ratAdd_mem_Rat hd (ratNeg_mem_Rat hc)
  have hgap0 : ratLe ratZero.{u} (ratAdd d (ratNeg c)) := by
    have := (ratAdd_le_add_right_iff (ratNeg_mem_Rat hc) hc hd).mpr hcd.left
    rwa [ratAdd_neg hc] at this
  have hFd := hFm _ (realLIcc_mono hp hq hc hd hpc hdq _
    (right_mem_realLIcc hc hd hcd.left))
  have hFc := hFm _ (realLIcc_mono hp hq hc hd hpc hdq _
    (left_mem_realLIcc hc hd hcd.left))
  refine realLLe_of_margins hFc hFd (fun k => ?_)
  obtain ⟨n, hn⟩ := exists_invWidth_mul_lt hgapQ hgap0 k
  have hnQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
  obtain ⟨m, hm⟩ := hderiv n
  obtain ⟨N, hN⟩ := exists_ladder_ge hc hd m
  have hgrid := mono_grid hp hq hc hd hpc hdq hcd hFm hF'm
    (fun i => hnn _ (realLIcc_mono hp hq hc hd hpc hdq _
      (gridPoint_mem_Icc hc hd hcd.left m i))) hm N
  rw [gridPoint_eq_right hN] at hgrid
  refine realLLe_trans hFc (realLAdd_mem hFd (realLOf_mem (ratMul_mem_Rat hnQ hgapQ)))
    (realLAdd_mem hFd (realLOf_mem (invWidth_mem_Rat (ofNat_mem_omega.{u} k))))
    hgrid ?_
  rw [realLAdd_comm hFd (realLOf_mem (ratMul_mem_Rat hnQ hgapQ)),
    realLAdd_comm hFd (realLOf_mem (invWidth_mem_Rat (ofNat_mem_omega.{u} k)))]
  refine realLLe_add_right (realLOf_mem (ratMul_mem_Rat hnQ hgapQ))
    (realLOf_mem (invWidth_mem_Rat (ofNat_mem_omega.{u} k))) hFd ?_
  refine (realLOf_le_realLOf (ratMul_mem_Rat hnQ hgapQ)
    (invWidth_mem_Rat (ofNat_mem_omega.{u} k))).mpr ?_
  rw [ratMul_comm hnQ hgapQ]
  exact hn.left

/-! ## The rules, uniformly

The same three rules again, with the base point quantified inside the modulus.
They are not corollaries of the pointwise ones -- a modulus that serves each
point separately need not serve them all -- but the analysis is the same lemma,
`close_add_lin`, so only the bookkeeping is repeated.

They build one function, `B·x - F x`, whose slope is `B - F'`. Through it
`hasDerivOn_mono` gives the one-sided inequality with a real bound, which
`hasDerivOn_mvi`, whose bound is rational, does not. -/

/-- A linear function has its constant as slope, with zero slack at every
scale. -/
theorem hasDerivOn_linear {p q B : ZFSet.{u}} (hB : B ∈ RealL.{u}) :
    HasDerivOn (fun x => realLMul B x) (fun _ => B) p q := by
  refine fun n => ⟨0, fun w x y hwQ hw0 _ hx hy _ => ?_⟩
  have hxM := ((mem_realLIcc_iff p q x).mp hx).left
  have hyM := ((mem_realLIcc_iff p q y).mp hy).left
  have hεQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
  show WithinOf (realLAdd (realLMul B x) (realLNeg (realLAdd (realLMul B y)
    (realLMul B (realLAdd x (realLNeg y)))))) _
  rw [realLMul_distrib hB hxM (realLNeg_mem hyM),
    ← realLAdd_assoc (realLMul_mem hB hyM) (realLMul_mem hB hxM)
      (realLMul_mem hB (realLNeg_mem hyM)),
    realLAdd_comm (realLMul_mem hB hyM) (realLMul_mem hB hxM),
    realLAdd_assoc (realLMul_mem hB hxM) (realLMul_mem hB hyM)
      (realLMul_mem hB (realLNeg_mem hyM)),
    realLMul_comm hB (realLNeg_mem hyM), realLNeg_realLMul hyM hB,
    realLMul_comm hyM hB, realLAdd_neg (realLMul_mem hB hyM),
    realLAdd_zero (realLMul_mem hB hxM), realLAdd_neg (realLMul_mem hB hxM)]
  exact withinOf_zero (ratMul_mem_Rat hεQ hwQ)
    (ratZero_le_mul hεQ hwQ (invWidth_pos (ofNat_mem_omega.{u} n)).left hw0.left)

/-- A constant has zero slope, uniformly. `eq_of_hasDerivOn_zero` is the
converse. -/
theorem hasDerivOn_const {c p q : ZFSet.{u}} (hc : c ∈ RealL.{u}) :
    HasDerivOn (fun _ => c) (fun _ => realLZero.{u}) p q := by
  refine fun n => ⟨0, fun w x y hwQ hw0 _ hx hy _ => ?_⟩
  have hxM := ((mem_realLIcc_iff p q x).mp hx).left
  have hyM := ((mem_realLIcc_iff p q y).mp hy).left
  have hxy := realLAdd_mem hxM (realLNeg_mem hyM)
  have hεQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
  show WithinOf (realLAdd c (realLNeg (realLAdd c
    (realLMul realLZero.{u} (realLAdd x (realLNeg y)))))) _
  rw [realLMul_comm realLZero_mem hxy, realLMul_zero hxy, realLAdd_zero hc,
    realLAdd_neg hc]
  exact withinOf_zero (ratMul_mem_Rat hεQ hwQ)
    (ratMul_pos hεQ hwQ (invWidth_pos (ofNat_mem_omega.{u} n)) hw0).left

/-- Negation negates the slope. -/
theorem hasDerivOn_neg {F F' : ZFSet.{u} → ZFSet.{u}} {p q : ZFSet.{u}}
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ RealL.{u})
    (hF'm : ∀ x, x ∈ realLIcc p q → F' x ∈ RealL.{u}) (hd : HasDerivOn F F' p q) :
    HasDerivOn (fun x => realLNeg (F x)) (fun x => realLNeg (F' x)) p q := by
  intro n
  obtain ⟨m, hm⟩ := hd n
  refine ⟨m, fun w x y hwQ hw0 hwle hx hy hclose => ?_⟩
  have hxM := ((mem_realLIcc_iff p q x).mp hx).left
  have hyM := ((mem_realLIcc_iff p q y).mp hy).left
  have hhM := realLAdd_mem hxM (realLNeg_mem hyM)
  have hFx := hFm x hx
  have hFy := hFm y hy
  have hSh := realLMul_mem (hF'm y hy) hhM
  have hneg := withinOf_neg (realLAdd_mem hFx (realLNeg_mem (realLAdd_mem hFy hSh)))
    (ratMul_mem_Rat (invWidth_mem_Rat (ofNat_mem_omega.{u} n)) hwQ)
    (hm w x y hwQ hw0 hwle hx hy hclose)
  show WithinOf (realLAdd (realLNeg (F x)) (realLNeg (realLAdd (realLNeg (F y))
    (realLMul (realLNeg (F' y)) (realLAdd x (realLNeg y)))))) _
  rw [realLNeg_realLMul (hF'm y hy) hhM, ← realLNeg_realLAdd hFy hSh,
    realLNeg_realLNeg (realLAdd_mem hFy hSh),
    realLAdd_comm (realLNeg_mem hFx) (realLAdd_mem hFy hSh),
    ← realLNeg_sub hFx (realLAdd_mem hFy hSh)]
  exact hneg

/-- The uniform sum rule. -/
theorem hasDerivOn_add {F F' G G' : ZFSet.{u} → ZFSet.{u}} {p q : ZFSet.{u}}
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ RealL.{u})
    (hGm : ∀ x, x ∈ realLIcc p q → G x ∈ RealL.{u})
    (hF'm : ∀ x, x ∈ realLIcc p q → F' x ∈ RealL.{u})
    (hG'm : ∀ x, x ∈ realLIcc p q → G' x ∈ RealL.{u})
    (hF : HasDerivOn F F' p q) (hG : HasDerivOn G G' p q) :
    HasDerivOn (fun x => realLAdd (F x) (G x)) (fun x => realLAdd (F' x) (G' x)) p q := by
  intro n
  obtain ⟨j, hhalf⟩ := exists_invWidth_add_self_lt.{u} n
  obtain ⟨m₁, hb₁⟩ := hF j
  obtain ⟨m₂, hb₂⟩ := hG j
  refine ⟨Nat.max m₁ m₂, fun w x y hwQ hw0 hwle hx hy hclose => ?_⟩
  exact close_add_lin (hFm x hx) (hGm x hx) (hFm y hy) (hGm y hy)
    (hF'm y hy) (hG'm y hy)
    (realLAdd_mem ((mem_realLIcc_iff p q x).mp hx).left
      (realLNeg_mem ((mem_realLIcc_iff p q y).mp hy).left))
    (invWidth_mem_Rat (ofNat_mem_omega.{u} j))
    (invWidth_mem_Rat (ofNat_mem_omega.{u} n)) hwQ hw0.left hhalf.left
    (hb₁ w x y hwQ hw0 (ratLe_invWidth_of_le hwQ (Nat.le_max_left m₁ m₂) hwle)
      hx hy hclose)
    (hb₂ w x y hwQ hw0 (ratLe_invWidth_of_le hwQ (Nat.le_max_right m₁ m₂) hwle)
      hx hy hclose)

/-- The uniform chain rule. The pointwise estimate survives with the base
point quantified inside the modulus, because every scale `hasDerivAt_comp`
chooses depends only on the two rational slope bounds -- and those, read off a
single point by `exists_rat_bound` there, must be hypotheses here: a bound
serving the whole interval is a supremum, which is exactly what cannot be
extracted. -/
theorem hasDerivOn_comp {F F' G G' : ZFSet.{u} → ZFSet.{u}}
    {p q p' q' KL KM : ZFSet.{u}}
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ realLIcc p' q')
    (hF'm : ∀ x, x ∈ realLIcc p q → F' x ∈ RealL.{u})
    (hGm : ∀ z, z ∈ realLIcc p' q' → G z ∈ RealL.{u})
    (hG'm : ∀ z, z ∈ realLIcc p' q' → G' z ∈ RealL.{u})
    (hKLQ : KL ∈ NumberTheory.Rat.{u}) (hKL0 : ratLe ratZero.{u} KL)
    (hKLb : ∀ x, x ∈ realLIcc p q → WithinOf (F' x) (realLOf KL))
    (hKMQ : KM ∈ NumberTheory.Rat.{u}) (hKM0 : ratLe ratZero.{u} KM)
    (hKMb : ∀ z, z ∈ realLIcc p' q' → WithinOf (G' z) (realLOf KM))
    (hF : HasDerivOn F F' p q) (hG : HasDerivOn G G' p' q') :
    HasDerivOn (fun x => G (F x)) (fun x => realLMul (G' (F x)) (F' x)) p q := by
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
  refine ⟨Nat.max mF m₄, fun w x y hwQ hw0 hwle hx hy hclose => ?_⟩
  have hεQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
  have hyM := ((mem_realLIcc_iff p q y).mp hy).left
  have hFyI := hFm y hy
  have hFy := ((mem_realLIcc_iff p' q' (F y)).mp hFyI).left
  have hGFy := hGm _ hFyI
  have hL := hF'm y hy
  have hM := hG'm _ hFyI
  have hxM := ((mem_realLIcc_iff p q x).mp hx).left
  have hFxI := hFm x hx
  have hFx := ((mem_realLIcc_iff p' q' (F x)).mp hFxI).left
  have hGFx := hGm _ hFxI
  have hhM := realLAdd_mem hxM (realLNeg_mem hyM)
  have hLh := realLMul_mem hL hhM
  have hfine : ∀ k : Nat, k ≤ Nat.max mF m₄ → ratLe w (invWidth (ofNat.{u} k)) :=
    fun k hk => ratLe_invWidth_of_le hwQ hk hwle
  have cF := hbF w x y hwQ hw0 (hfine mF (Nat.le_max_left mF m₄)) hx hy hclose
  have hSF := realLAdd_mem hFx (realLNeg_mem (realLAdd_mem hFy hLh))
  have hU := realLAdd_mem hFx (realLNeg_mem hFy)
  -- the increment of `F` is bounded by `(1 + KL)` times the step
  have hUb := withinOf_increment hFx hFy hL hhM hKLQ hwQ hKL0 hw0.left
    (hKLb y hy) hclose cF
  -- so `G`'s estimate applies between `F x` and `F y`, with that bound as its step
  have hw'Q := ratMul_mem_Rat hCQ hwQ
  have hw'0 : ratLt ratZero.{u} (ratMul (ratAdd ratOne.{u} KL) w) :=
    ratMul_pos hCQ hwQ hC0 hw0
  have hw'le : ratLe (ratMul (ratAdd ratOne.{u} KL) w) (invWidth (ofNat.{u} mG)) := by
    refine ratLe_trans hw'Q (ratMul_mem_Rat hCQ (invWidth_mem_Rat (ofNat_mem_omega.{u} m₄)))
      (invWidth_mem_Rat (ofNat_mem_omega.{u} mG)) ?_ hm4.left
    rw [ratMul_comm hCQ hwQ,
      ratMul_comm hCQ (invWidth_mem_Rat (ofNat_mem_omega.{u} m₄))]
    exact ratMul_le_mul_right hwQ (invWidth_mem_Rat (ofNat_mem_omega.{u} m₄)) hCQ
      (hfine m₄ (Nat.le_max_right mF m₄)) hC0.left
  have cG := hbG _ _ _ hw'Q hw'0 hw'le hFxI hFyI hUb
  -- the two pieces, and the identity that assembles them
  have bMS := withinOf_mul hM hSF hKMQ (ratMul_mem_Rat hjFQ hwQ) hKM0
    (ratZero_le_mul hjFQ hwQ (invWidth_pos (ofNat_mem_omega.{u} jF)).left hw0.left)
    (hKMb _ hFyI) cF
  have btot := withinOf_add (realLAdd_mem hGFx (realLNeg_mem
      (realLAdd_mem hGFy (realLMul_mem hM hU))))
    (realLMul_mem hM hSF) (ratMul_mem_Rat hjGQ hw'Q) (ratMul_mem_Rat hKMQ
      (ratMul_mem_Rat hjFQ hwQ)) cG bMS
  rw [← realLSub_sub hFx hFy hLh,
    chain_slack hGFx hGFy hM hU hL hhM] at btot
  show WithinOf (realLAdd (G (F x)) (realLNeg (realLAdd (G (F y))
    (realLMul (realLMul (G' (F y)) (F' y)) (realLAdd x (realLNeg y)))))) _
  rw [realLMul_assoc hM hL hhM]
  refine withinOf_mono (realLAdd_mem hGFx (realLNeg_mem (realLAdd_mem hGFy
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

/-- Uniform differentiability respects pointwise agreement on the interval:
every clause evaluates inside it. -/
theorem hasDerivOn_congr {F F' G G' : ZFSet.{u} → ZFSet.{u}} {p q : ZFSet.{u}}
    (hFG : ∀ z, z ∈ realLIcc p q → F z = G z)
    (hF'G' : ∀ z, z ∈ realLIcc p q → F' z = G' z)
    (h : HasDerivOn F F' p q) : HasDerivOn G G' p q := by
  intro n
  obtain ⟨m, hm⟩ := h n
  refine ⟨m, fun w x y hwQ hw0 hwle hx hy hclose => ?_⟩
  have hb := hm w x y hwQ hw0 hwle hx hy hclose
  rwa [hFG x hx, hFG y hy, hF'G' y hy] at hb

/-- The uniform product rule. As with `hasDerivOn_comp`, the pointwise
proof survives with the base point quantified inside the modulus: every scale
`hasDerivAt_mul` chooses depends only on the four rational bounds -- two
function bounds, two slope bounds -- and those become interval hypotheses,
because a supremum cannot be extracted. -/
theorem hasDerivOn_mul {F F' G G' : ZFSet.{u} → ZFSet.{u}}
    {p q KA KB KL KM : ZFSet.{u}}
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ RealL.{u})
    (hGm : ∀ x, x ∈ realLIcc p q → G x ∈ RealL.{u})
    (hF'm : ∀ x, x ∈ realLIcc p q → F' x ∈ RealL.{u})
    (hG'm : ∀ x, x ∈ realLIcc p q → G' x ∈ RealL.{u})
    (hKAQ : KA ∈ NumberTheory.Rat.{u}) (hKA0 : ratLe ratZero.{u} KA)
    (hKAb : ∀ x, x ∈ realLIcc p q → WithinOf (F x) (realLOf KA))
    (hKBQ : KB ∈ NumberTheory.Rat.{u}) (hKB0 : ratLe ratZero.{u} KB)
    (hKBb : ∀ x, x ∈ realLIcc p q → WithinOf (G x) (realLOf KB))
    (hKLQ : KL ∈ NumberTheory.Rat.{u}) (hKL0 : ratLe ratZero.{u} KL)
    (hKLb : ∀ x, x ∈ realLIcc p q → WithinOf (F' x) (realLOf KL))
    (hKMQ : KM ∈ NumberTheory.Rat.{u}) (hKM0 : ratLe ratZero.{u} KM)
    (hKMb : ∀ x, x ∈ realLIcc p q → WithinOf (G' x) (realLOf KM))
    (hF : HasDerivOn F F' p q) (hG : HasDerivOn G G' p q) :
    HasDerivOn (fun x => realLMul (F x) (G x))
      (fun x => realLAdd (realLMul (F x) (G' x)) (realLMul (G x) (F' x))) p q := by
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
  refine ⟨Nat.max (Nat.max m₁ m₂) m₃, fun w x y hwQ hw0 hwle hx hy hclose => ?_⟩
  have hεQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
  have hyM := ((mem_realLIcc_iff p q y).mp hy).left
  have hFy := hFm y hy
  have hGy := hGm y hy
  have hL := hF'm y hy
  have hM := hG'm y hy
  have hxM := ((mem_realLIcc_iff p q x).mp hx).left
  have hFx := hFm x hx
  have hGx := hGm x hx
  have hhM := realLAdd_mem hxM (realLNeg_mem hyM)
  have hLh := realLMul_mem hL hhM
  have hMh := realLMul_mem hM hhM
  have hfine : ∀ k : Nat, k ≤ Nat.max (Nat.max m₁ m₂) m₃ →
      ratLe w (invWidth (ofNat.{u} k)) := fun k hk =>
    ratLe_invWidth_of_le hwQ hk hwle
  have c₁ := hb₁ w x y hwQ hw0
    (hfine m₁ (Nat.le_trans (Nat.le_max_left m₁ m₂) (Nat.le_max_left _ m₃))) hx hy hclose
  have c₂ := hb₂ w x y hwQ hw0
    (hfine m₂ (Nat.le_trans (Nat.le_max_right m₁ m₂) (Nat.le_max_left _ m₃))) hx hy hclose
  have hSF := realLAdd_mem hFx (realLNeg_mem (realLAdd_mem hFy hLh))
  have hSG := realLAdd_mem hGx (realLNeg_mem (realLAdd_mem hGy hMh))
  have hU := realLAdd_mem hFx (realLNeg_mem hFy)
  have hV := realLAdd_mem hGx (realLNeg_mem hGy)
  -- each increment is bounded by `(1 + |slope|)` times the step
  have hUb := withinOf_increment hFx hFy hL hhM hKLQ hwQ hKL0 hw0.left
    (hKLb y hy) hclose c₁
  have hVb := withinOf_increment hGx hGy hM hhM hKMQ hwQ hKM0 hw0.left
    (hKMb y hy) hclose c₂
  -- the three pieces
  have hjw0 := ratZero_le_mul hjQ hwQ (invWidth_pos (ofNat_mem_omega.{u} j)).left hw0.left
  have bA := withinOf_mul hFy hSG hKAQ (ratMul_mem_Rat hjQ hwQ) hKA0 hjw0
    (hKAb y hy) c₂
  have bB := withinOf_mul hGy hSF hKBQ (ratMul_mem_Rat hjQ hwQ) hKB0 hjw0
    (hKBb y hy) c₁
  have bUV := withinOf_mul hU hV (ratMul_mem_Rat hCUQ hwQ) (ratMul_mem_Rat hCVQ hwQ)
    (ratZero_le_mul hCUQ hwQ hCU0 hw0.left) (ratZero_le_mul hCVQ hwQ hCV0 hw0.left) hUb hVb
  have btot := withinOf_add (realLAdd_mem (realLMul_mem hFy hSG) (realLMul_mem hGy hSF))
    (realLMul_mem hU hV)
    (ratAdd_mem_Rat (ratMul_mem_Rat hKAQ (ratMul_mem_Rat hjQ hwQ))
      (ratMul_mem_Rat hKBQ (ratMul_mem_Rat hjQ hwQ)))
    (ratMul_mem_Rat (ratMul_mem_Rat hCUQ hwQ) (ratMul_mem_Rat hCVQ hwQ))
    (withinOf_add (realLMul_mem hFy hSG) (realLMul_mem hGy hSF)
      (ratMul_mem_Rat hKAQ (ratMul_mem_Rat hjQ hwQ))
      (ratMul_mem_Rat hKBQ (ratMul_mem_Rat hjQ hwQ)) bA bB)
    bUV
  -- and they assemble into the slack of the product
  have hkey := product_slack hFy hGy hU hV hL hM hhM
  rw [realLAdd_comm hFy hU, realLSub_add_cancel hFx hFy,
    realLAdd_comm hGy hV, realLSub_add_cancel hGx hGy,
    realLSub_sub hGx hGy hMh, realLSub_sub hFx hFy hLh] at hkey
  rw [← hkey] at btot
  show WithinOf (realLAdd (realLMul (F x) (G x)) (realLNeg (realLAdd (realLMul (F y) (G y))
    (realLMul (realLAdd (realLMul (F y) (G' y)) (realLMul (G y) (F' y)))
      (realLAdd x (realLNeg y)))))) _
  refine withinOf_mono (realLAdd_mem (realLMul_mem hFx hGx)
    (realLNeg_mem (realLAdd_mem (realLMul_mem hFy hGy)
      (realLMul_mem (realLAdd_mem (realLMul_mem hFy hM) (realLMul_mem hGy hL)) hhM))))
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

/-- The one-sided mean value inequality, with a real bound. A slope below
`B` moves the function by at most `B` times the distance. The proof is
`hasDerivOn_mono` applied to `B·x - F x`, whose slope is `B - F'` and therefore
non-negative -- so the tilt does all the work and no new estimate is needed. -/
theorem hasDerivOn_le_of_slope_le {F F' : ZFSet.{u} → ZFSet.{u}}
    {p q c d B : ZFSet.{u}}
    (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u}) (hc : c ∈ NumberTheory.Rat.{u}) (hd : d ∈ NumberTheory.Rat.{u})
    (hpc : ratLe p c) (hdq : ratLe d q) (hcd : ratLt c d) (hB : B ∈ RealL.{u})
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ RealL.{u})
    (hF'm : ∀ x, x ∈ realLIcc p q → F' x ∈ RealL.{u})
    (hderiv : HasDerivOn F F' p q)
    (hle : ∀ x, x ∈ realLIcc p q → realLLe (F' x) B) :
    realLLe (realLAdd (F (realLOf d)) (realLNeg (F (realLOf c))))
      (realLMul B (realLAdd (realLOf d) (realLNeg (realLOf c)))) := by
  have hcin := realLIcc_mono hp hq hc hd hpc hdq _ (left_mem_realLIcc hc hd hcd.left)
  have hdin := realLIcc_mono hp hq hc hd hpc hdq _ (right_mem_realLIcc hc hd hcd.left)
  have hFc := hFm _ hcin
  have hFd := hFm _ hdin
  have hGm : ∀ x, x ∈ realLIcc p q →
      realLAdd (realLMul B x) (realLNeg (F x)) ∈ RealL.{u} := fun x hx =>
    realLAdd_mem (realLMul_mem hB ((mem_realLIcc_iff p q x).mp hx).left)
      (realLNeg_mem (hFm x hx))
  have hG'm : ∀ x, x ∈ realLIcc p q → realLAdd B (realLNeg (F' x)) ∈ RealL.{u} :=
    fun x hx => realLAdd_mem hB (realLNeg_mem (hF'm x hx))
  have hGderiv := hasDerivOn_add
    (fun x hx => realLMul_mem hB ((mem_realLIcc_iff p q x).mp hx).left)
    (fun x hx => realLNeg_mem (hFm x hx)) (fun _ _ => hB)
    (fun x hx => realLNeg_mem (hF'm x hx))
    (hasDerivOn_linear hB) (hasDerivOn_neg hFm hF'm hderiv)
  have hGnn : ∀ x, x ∈ realLIcc p q →
      realLLe realLZero.{u} (realLAdd B (realLNeg (F' x))) := fun x hx =>
    (realLLe_sub_nonneg (hF'm x hx) hB).mp (hle x hx)
  have hmono := hasDerivOn_mono hp hq hc hd hpc hdq hcd hGm hG'm hGderiv hGnn
  -- `B·c - F c ≤ B·d - F d` rearranges to the claim
  have hBc := realLMul_mem hB (realLOf_mem hc)
  have hBd := realLMul_mem hB (realLOf_mem hd)
  have hstep := (realLLe_sub_nonneg (realLAdd_mem hBc (realLNeg_mem hFc))
    (realLAdd_mem hBd (realLNeg_mem hFd))).mp hmono
  rw [realLAdd_sub_add hBd (realLNeg_mem hFd) hBc (realLNeg_mem hFc),
    realLNeg_realLNeg hFc] at hstep
  refine (realLLe_sub_nonneg (realLAdd_mem hFd (realLNeg_mem hFc))
    (realLMul_mem hB (realLAdd_mem (realLOf_mem hd)
      (realLNeg_mem (realLOf_mem hc))))).mpr ?_
  rw [realLNeg_realLAdd hFd (realLNeg_mem hFc), realLNeg_realLNeg hFc,
    realLMul_distrib hB (realLOf_mem hd) (realLNeg_mem (realLOf_mem hc)),
    realLMul_comm hB (realLNeg_mem (realLOf_mem hc)),
    realLNeg_realLMul (realLOf_mem hc) hB, realLMul_comm (realLOf_mem hc) hB]
  exact hstep



/-- The mean slope over `[p, q]`. The reciprocal is of a rational, so it is the
one `Rational.lean` already has. -/
def meanSlope (F : ZFSet.{u} → ZFSet.{u}) (p q : ZFSet.{u}) : ZFSet.{u} :=
  realLMul (realLAdd (F (realLOf q)) (realLNeg (F (realLOf p))))
    (realLOf (ratInv (ratAdd q (ratNeg p))))


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


/-- Continuity at a single point of `[p, q]`, in the same shape as
`UniformlyContinuousOn` with the second argument pinned. -/
def ContinuousAtOn (H : ZFSet.{u} → ZFSet.{u}) (p q a : ZFSet.{u}) : Prop :=
  ∀ n : Nat, ∃ m : Nat, ∀ w x, w ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} w →
    ratLe w (invWidth (ofNat.{u} m)) → x ∈ realLIcc p q →
    Close x a (realLOf w) → Close (H x) (H a) (realLOf (invWidth (ofNat.{u} n)))

/-- A pointwise modulus valued in `omega`: `PointwiseModulus` with the index in
`omega` rather than `Nat`. The Archimedean index `invWidthIndex` is
`omega`-valued, and converting it to `Nat` needs an `eq : Nat → ZFSet → Bool`
readout, which this development takes as a hypothesis and never discharges.
Consumers read the modulus only through `invWidth (ofNat ·)`, to learn that the
width is a positive rational, and `invWidth_mem_Rat` and `invWidth_pos` supply
that from `omega`-membership. -/
def PointwiseModulusW (H : ZFSet.{u} → ZFSet.{u}) (p q : ZFSet.{u})
    (μ : ZFSet.{u} → Nat → ZFSet.{u}) : Prop :=
  ∀ a, a ∈ realLIcc p q → ∀ n : Nat, ∀ w x, w ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} w →
    ratLe w (invWidth (μ a n)) → x ∈ realLIcc p q →
    Close x a (realLOf w) → Close (H x) (H a) (realLOf (invWidth (ofNat.{u} n)))

/-- A pointwise modulus, carried as data. `ContinuousAtOn` at every point is
`∀ a, ∀ n, ∃ m`: the index exists but cannot be released into `Type`. Here the
index is a function `μ` of the point, which a proof may evaluate. -/
def PointwiseModulus (H : ZFSet.{u} → ZFSet.{u}) (p q : ZFSet.{u})
    (μ : ZFSet.{u} → Nat → Nat) : Prop :=
  ∀ a, a ∈ realLIcc p q → ∀ n : Nat, ∀ w x, w ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} w →
    ratLe w (invWidth (ofNat.{u} (μ a n))) → x ∈ realLIcc p q →
    Close x a (realLOf w) → Close (H x) (H a) (realLOf (invWidth (ofNat.{u} n)))

/-- Forgetting the function recovers continuity at each point, so the carrier
is a strengthening rather than a change of subject. -/
theorem continuousAtOn_of_pointwiseModulus {H : ZFSet.{u} → ZFSet.{u}}
    {p q a : ZFSet.{u}} {μ : ZFSet.{u} → Nat → Nat} (ha : a ∈ realLIcc p q)
    (h : PointwiseModulus H p q μ) : ContinuousAtOn H p q a :=
  fun n => ⟨μ a n, fun w x hw hw0 hwm hx hclose => h a ha n w x hw hw0 hwm hx hclose⟩

/-- A point is close to itself at any non-negative distance. -/
theorem close_self {z w : ZFSet.{u}} (hz : z ∈ RealL.{u}) (hw : w ∈ NumberTheory.Rat.{u})
    (hw0 : ratLe ratZero.{u} w) : Close z z (realLOf w) := by
  show WithinOf (realLAdd z (realLNeg z)) (realLOf w)
  rw [realLAdd_neg hz]
  exact withinOf_zero hw hw0

/-- A constant is uniformly continuous: its differences are zero. -/
theorem uniformlyContinuousOn_const {c p q : ZFSet.{u}} (hc : c ∈ RealL.{u}) :
    UniformlyContinuousOn (fun _ => c) p q := by
  intro n
  refine ⟨0, fun w x y hwQ hw0 _ _ _ _ => ?_⟩
  show WithinOf (realLAdd c (realLNeg c)) (realLOf (invWidth (ofNat.{u} n)))
  rw [realLAdd_neg hc]
  exact withinOf_zero (invWidth_mem_Rat (ofNat_mem_omega.{u} n))
    (invWidth_pos (ofNat_mem_omega.{u} n)).left

/-- A sum of uniformly continuous functions is uniformly continuous: the
difference splits summand by summand, and the error budget halves. -/
theorem uniformlyContinuousOn_add {F G : ZFSet.{u} → ZFSet.{u}} {p q : ZFSet.{u}}
    (hFm : ∀ z, z ∈ realLIcc p q → F z ∈ RealL.{u})
    (hGm : ∀ z, z ∈ realLIcc p q → G z ∈ RealL.{u})
    (hF : UniformlyContinuousOn F p q) (hG : UniformlyContinuousOn G p q) :
    UniformlyContinuousOn (fun z => realLAdd (F z) (G z)) p q := by
  intro n
  obtain ⟨j, hj⟩ := exists_invWidth_add_self_lt.{u} n
  have hjQ := invWidth_mem_Rat (ofNat_mem_omega.{u} j)
  obtain ⟨m₁, hb₁⟩ := hF j
  obtain ⟨m₂, hb₂⟩ := hG j
  refine ⟨Nat.max m₁ m₂, fun w x y hwQ hw0 hwle hx hy hclose => ?_⟩
  have c₁ := hb₁ w x y hwQ hw0
    (ratLe_invWidth_of_le hwQ (Nat.le_max_left m₁ m₂) hwle) hx hy hclose
  have c₂ := hb₂ w x y hwQ hw0
    (ratLe_invWidth_of_le hwQ (Nat.le_max_right m₁ m₂) hwle) hx hy hclose
  have hsum := withinOf_add (realLAdd_mem (hFm x hx) (realLNeg_mem (hFm y hy)))
    (realLAdd_mem (hGm x hx) (realLNeg_mem (hGm y hy))) hjQ hjQ c₁ c₂
  show WithinOf (realLAdd (realLAdd (F x) (G x))
    (realLNeg (realLAdd (F y) (G y)))) (realLOf (invWidth (ofNat.{u} n)))
  rw [realLAdd_sub_add (hFm x hx) (hGm x hx) (hFm y hy) (hGm y hy)]
  exact withinOf_mono (realLAdd_mem
      (realLAdd_mem (hFm x hx) (realLNeg_mem (hFm y hy)))
      (realLAdd_mem (hGm x hx) (realLNeg_mem (hGm y hy))))
    (ratAdd_mem_Rat hjQ hjQ) (invWidth_mem_Rat (ofNat_mem_omega.{u} n))
    hj.left hsum

/-- A differentiable function with bounded slope is uniformly continuous.
The local estimate already says the increment is at most `(1 + K)` times the
step; all that is left is to make the step small enough that the product is
below the scale asked for. -/
theorem uniformlyContinuousOn_of_hasDerivOn {F F' : ZFSet.{u} → ZFSet.{u}}
    {p q K : ZFSet.{u}}
    (hFm : ∀ x, x ∈ realLIcc p q → F x ∈ RealL.{u})
    (hF'm : ∀ x, x ∈ realLIcc p q → F' x ∈ RealL.{u})
    (hd : HasDerivOn F F' p q) (hK : K ∈ NumberTheory.Rat.{u}) (hK0 : ratLe ratZero.{u} K)
    (hbd : ∀ x, x ∈ realLIcc p q → WithinOf (F' x) (realLOf K)) :
    UniformlyContinuousOn F p q := by
  intro n
  have hCQ := ratAdd_mem_Rat ratOne_mem_Rat hK
  have hC0 : ratLe ratZero.{u} (ratAdd ratOne.{u} K) := by
    have := ratAdd_le_add ratZero_mem_Rat ratOne_mem_Rat ratZero_mem_Rat hK
      ratZero_lt_one.left hK0
    rwa [ratAdd_zero ratZero_mem_Rat] at this
  obtain ⟨m₁, hm₁⟩ := hasDerivOn_step hFm hF'm hd hK hK0 hbd 0
  obtain ⟨m₂, hm₂⟩ := exists_invWidth_mul_lt hCQ hC0 n
  refine ⟨Nat.max m₁ m₂, fun w x y hwQ hw0 hwle hx hy hclose => ?_⟩
  have hstep := hm₁ w x y hwQ hw0
    (ratLe_invWidth_of_le hwQ (Nat.le_max_left m₁ m₂) hwle) hx hy hclose
  refine withinOf_mono (realLAdd_mem (hFm x hx) (realLNeg_mem (hFm y hy)))
    (ratMul_mem_Rat (ratAdd_mem_Rat (invWidth_mem_Rat (ofNat_mem_omega.{u} 0)) hK) hwQ)
    (invWidth_mem_Rat (ofNat_mem_omega.{u} n)) ?_ hstep
  -- `(1 + K)·w ≤ (1 + K)/(m₂+1) < 1/(n+1)`, and `1/(0+1) = 1`
  have hone : invWidth (ofNat.{u} 0) = ratOne.{u} := by
    rw [invWidth_ofNat 0, ratNat_one_one]
  rw [hone]
  refine ratLe_trans (ratMul_mem_Rat hCQ hwQ)
    (ratMul_mem_Rat hCQ (invWidth_mem_Rat (ofNat_mem_omega.{u} m₂)))
    (invWidth_mem_Rat (ofNat_mem_omega.{u} n)) ?_ hm₂.left
  rw [ratMul_comm hCQ hwQ,
    ratMul_comm hCQ (invWidth_mem_Rat (ofNat_mem_omega.{u} m₂))]
  exact ratMul_le_mul_right hwQ (invWidth_mem_Rat (ofNat_mem_omega.{u} m₂)) hCQ
    (ratLe_invWidth_of_le hwQ (Nat.le_max_right m₁ m₂) hwle) hC0


/-- `F` with the mean line subtracted. -/
def tilt (F : ZFSet.{u} → ZFSet.{u}) (p q x : ZFSet.{u}) : ZFSet.{u} :=
  realLAdd (F x) (realLNeg (realLMul (meanSlope F p q) x))


/-- A rational between the endpoints names a point of the interval. -/
theorem realLOf_mem_realLIcc {p q x : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (hx : x ∈ NumberTheory.Rat.{u}) (hpx : ratLe p x) (hxq : ratLe x q) :
    realLOf x ∈ realLIcc p q :=
  (mem_realLIcc_iff p q _).mpr ⟨realLOf_mem hx, (realLOf_le_realLOf hp hx).mpr hpx,
    (realLOf_le_realLOf hx hq).mpr hxq⟩


/-- A positive factor cancels from a two-sided bracket. `withinOf_mul`
multiplies two bounds; this undoes one of them when the factor is positive, so
an estimate on `(φ x - L)·(x - a)` reads as an estimate on `φ x - L` without
dividing. Both halves are `realLLe_of_mul_le_mul_right`; the lower one needs
`-(c·y)` recognised as `(-c)·y` first. -/
theorem withinOf_of_withinOf_mul {z y c : ZFSet.{u}} (hz : z ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hc : c ∈ RealL.{u}) (hy0 : realLLt realLZero.{u} y)
    (h : WithinOf (realLMul z y) (realLMul c y)) : WithinOf z c := by
  refine ⟨?_, realLLe_of_mul_le_mul_right hz hc hy hy0 h.right⟩
  refine realLLe_of_mul_le_mul_right (realLNeg_mem hc) hz hy hy0 ?_
  have hlo := h.left
  rwa [← realLNeg_realLMul hc hy] at hlo

/-- The rationals are dense in the located reals. `realLLt` is defined as a
shared rational -- one in the upper cut of the smaller and the lower cut of the
larger -- so this is that definition read back as an order statement, which is
the form every argument below wants. `exists_between_of_realLApart` says the same
for apartness, where the side is unknown; here the side is given. -/
theorem exists_rat_between {x y : ZFSet.{u}} (hx : x ∈ RealL.{u}) (hy : y ∈ RealL.{u})
    (h : realLLt x y) :
    ∃ p, p ∈ NumberTheory.Rat.{u} ∧ realLLt x (realLOf p) ∧ realLLt (realLOf p) y := by
  obtain ⟨p, hpU, hpL⟩ := h
  have hpQ : p ∈ NumberTheory.Rat.{u} := by
    obtain ⟨L, U, he, hloc⟩ := (mem_RealL_iff x).mp hx
    rw [he, snd_opair] at hpU
    exact hloc.upper_subset p hpU
  exact ⟨p, hpQ, (lt_realLOf_iff_mem_upper hx hpQ).mpr hpU,
    (realLOf_lt_iff_mem_lower hy hpQ).mpr hpL⟩

#print axioms HasDerivOn


/-- Every point of the interval has a rational of the interval within any
asked distance. The bracket supplies a rational below within `w`; if it falls
left of `p`, the left endpoint itself serves, because `z` is trapped between
`p` and the bracket's ceiling. Rational trichotomy decides which, and costs
nothing. -/
theorem exists_rat_near_in_Icc {p q z w : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u})
    (hq : q ∈ NumberTheory.Rat.{u}) (hz : z ∈ realLIcc p q) (hw : w ∈ NumberTheory.Rat.{u})
    (hw0 : ratLt ratZero.{u} w) :
    ∃ r, r ∈ NumberTheory.Rat.{u} ∧ ratLe p r ∧ ratLe r q ∧ Close z (realLOf r) (realLOf w) := by
  obtain ⟨hzR, hpz, hzq⟩ := (mem_realLIcc_iff p q z).mp hz
  obtain ⟨lo, hi, hloQ, hhiQ, hlo, hhi, hwidth⟩ := exists_rat_bracket hzR hw hw0
  have hnw0 : ratLe (ratNeg w) ratZero.{u} := by
    have := (ratAdd_le_add_right_iff (ratNeg_mem_Rat hw) ratZero_mem_Rat hw).mpr
      hw0.left
    rwa [ratZero_add (ratNeg_mem_Rat hw), ratAdd_neg hw] at this
  have hnegw : realLLe (realLNeg (realLOf w)) realLZero.{u} := by
    rw [realLOf_neg hw]
    exact (realLOf_le_realLOf (ratNeg_mem_Rat hw) ratZero_mem_Rat).mpr hnw0
  have key : ∀ s, s ∈ NumberTheory.Rat.{u} → realLLe (realLOf s) z →
      realLLt z (realLOf (ratAdd s w)) → Close z (realLOf s) (realLOf w) := by
    intro s hsQ hsz hzsw
    refine ⟨?_, ?_⟩
    · exact realLLe_trans (realLNeg_mem (realLOf_mem hw)) realLZero_mem
        (realLAdd_mem hzR (realLNeg_mem (realLOf_mem hsQ))) hnegw
        ((realLLe_sub_nonneg (realLOf_mem hsQ) hzR).mp hsz)
    · have h2 := realLLt_add_right hzR (realLOf_mem (ratAdd_mem_Rat hsQ hw))
        (realLNeg_mem (realLOf_mem hsQ)) hzsw
      rw [realLOf_add hsQ hw, realLAdd_comm (realLOf_mem hsQ) (realLOf_mem hw),
        realLAdd_assoc (realLOf_mem hw) (realLOf_mem hsQ)
          (realLNeg_mem (realLOf_mem hsQ)),
        realLAdd_neg (realLOf_mem hsQ), realLAdd_zero (realLOf_mem hw)] at h2
      exact realLLe_of_lt (realLAdd_mem hzR (realLNeg_mem (realLOf_mem hsQ)))
        (realLOf_mem hw) h2
  have hloq : ratLt lo q := (realLOf_lt_realLOf hloQ hq).mp
    (realLLt_of_lt_of_le (realLOf_mem hloQ) hzR (realLOf_mem hq) hlo hzq)
  have hceil : realLLe z (realLOf (ratAdd lo w)) :=
    realLLe_of_lt hzR (realLOf_mem (ratAdd_mem_Rat hloQ hw))
      (realLLt_of_lt_of_le hzR (realLOf_mem hhiQ)
        (realLOf_mem (ratAdd_mem_Rat hloQ hw)) hhi
        ((realLOf_le_realLOf hhiQ (ratAdd_mem_Rat hloQ hw)).mpr hwidth.left))
  rcases ratLt_trichotomy hloQ hp with hlt | heq | hgt
  · have hpq : ratLe p q := (realLOf_le_realLOf hp hq).mp
      (realLLe_trans (realLOf_mem hp) hzR (realLOf_mem hq) hpz hzq)
    refine ⟨p, hp, ratLe_refl hp, hpq, key p hp hpz ?_⟩
    refine realLLt_of_lt_of_le hzR (realLOf_mem hhiQ)
      (realLOf_mem (ratAdd_mem_Rat hp hw)) hhi ?_
    refine (realLOf_le_realLOf hhiQ (ratAdd_mem_Rat hp hw)).mpr ?_
    exact ratLe_trans hhiQ (ratAdd_mem_Rat hloQ hw) (ratAdd_mem_Rat hp hw)
      hwidth.left ((ratAdd_le_add_right_iff hw hloQ hp).mpr hlt.left)
  · subst heq
    refine ⟨lo, hloQ, ratLe_refl hloQ, hloq.left,
      key lo hloQ (realLLe_of_lt (realLOf_mem hloQ) hzR hlo) ?_⟩
    exact realLLt_of_lt_of_le hzR (realLOf_mem hhiQ)
      (realLOf_mem (ratAdd_mem_Rat hloQ hw)) hhi
      ((realLOf_le_realLOf hhiQ (ratAdd_mem_Rat hloQ hw)).mpr hwidth.left)
  · refine ⟨lo, hloQ, hgt.left, hloq.left,
      key lo hloQ (realLLe_of_lt (realLOf_mem hloQ) hzR hlo) ?_⟩
    exact realLLt_of_lt_of_le hzR (realLOf_mem hhiQ)
      (realLOf_mem (ratAdd_mem_Rat hloQ hw)) hhi
      ((realLOf_le_realLOf hhiQ (ratAdd_mem_Rat hloQ hw)).mpr hwidth.left)

/-! ### Uniform continuity along a Lipschitz reparameterisation

Hadamard's factorisation integrates `F'` along the segment from `a` to `x`, so
what has to be uniformly continuous is `F'` composed with an affine map. The
composition is the general fact and the affine case is an instance of it: a map
that moves points by at most `K` times the step turns a modulus for `H` into a
modulus for `H ∘ G`, by asking for the step `K` times smaller. -/

/-- A map that moves points by at most a fixed multiple of the step. -/
def LipschitzOn (G : ZFSet.{u} → ZFSet.{u}) (c d K : ZFSet.{u}) : Prop :=
  ∀ w s s', w ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} w → s ∈ realLIcc c d →
    s' ∈ realLIcc c d →
    Close s s' (realLOf w) → Close (G s) (G s') (realLOf (ratMul K w))

/-- The point a fraction `t` of the way from `a` to `x`. -/
def segment (a x t : ZFSet.{u}) : ZFSet.{u} :=
  realLAdd a (realLMul t (realLAdd x (realLNeg a)))

theorem segment_mem {a x t : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hx : x ∈ RealL.{u})
    (ht : t ∈ RealL.{u}) : segment a x t ∈ RealL.{u} :=
  realLAdd_mem ha (realLMul_mem ht (realLAdd_mem hx (realLNeg_mem ha)))

/-- A point of the segment is a convex combination of its endpoints. Written
this way the endpoints appear with non-negative coefficients summing to one, so
containment is proved without deciding the sign of the step, which the natural
argument must decide. -/
theorem segment_eq_convex {a x t : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hx : x ∈ RealL.{u})
    (ht : t ∈ RealL.{u}) :
    segment a x t
      = realLAdd (realLMul (realLAdd realLOne.{u} (realLNeg t)) a) (realLMul t x) := by
  have hta := realLMul_mem ht ha
  have htx := realLMul_mem ht hx
  rw [segment, realLMul_distrib ht hx (realLNeg_mem ha), realLMul_neg ht ha,
    ← realLSub_mul realLOne_mem ht ha, realLMul_comm realLOne_mem ha, realLMul_one ha,
    realLAdd_assoc ha (realLNeg_mem hta) htx,
    realLAdd_comm (realLNeg_mem hta) htx]

/-- An interval is convex. Both halves are the same argument: a bound that
holds at each endpoint holds at the convex combination, because the coefficients
are non-negative and sum to one.

The natural proof -- the segment lies above `a` if the step is positive and above
`x` otherwise -- decides the sign of the step and is therefore unavailable. This
one never compares anything. -/
theorem segment_mem_realLIcc {a x p q t : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u})
    (hq : q ∈ NumberTheory.Rat.{u}) (ha : a ∈ realLIcc p q) (hx : x ∈ realLIcc p q)
    (ht : t ∈ realLIcc ratZero.{u} ratOne.{u}) : segment a x t ∈ realLIcc p q := by
  obtain ⟨haR, hpa, haq⟩ := (mem_realLIcc_iff p q a).mp ha
  obtain ⟨hxR, hpx, hxq⟩ := (mem_realLIcc_iff p q x).mp hx
  obtain ⟨htR, ht0, ht1⟩ := (mem_realLIcc_iff ratZero.{u} ratOne.{u} t).mp ht
  have hs := realLAdd_mem realLOne_mem (realLNeg_mem htR)
  have hs0 : realLLe realLZero.{u} (realLAdd realLOne.{u} (realLNeg t)) :=
    (realLLe_sub_nonneg htR realLOne_mem).mp ht1
  -- the coefficients sum to one, so a common bound is reproduced exactly
  have hsum : ∀ P : ZFSet.{u}, P ∈ RealL.{u} →
      realLAdd (realLMul (realLAdd realLOne.{u} (realLNeg t)) P) (realLMul t P) = P := by
    intro P hP
    rw [← realLAdd_mul hs htR hP, realLSub_add_cancel realLOne_mem htR,
      realLMul_comm realLOne_mem hP, realLMul_one hP]
  refine (mem_realLIcc_iff p q _).mpr ⟨segment_mem haR hxR htR, ?_, ?_⟩
  · rw [segment_eq_convex haR hxR htR, ← hsum (realLOf p) (realLOf_mem hp)]
    refine realLLe_add (realLMul_mem hs (realLOf_mem hp)) (realLMul_mem hs haR)
      (realLMul_mem htR (realLOf_mem hp)) (realLMul_mem htR hxR) ?_ ?_
    · have h := realLMul_le_right (realLOf_mem hp) haR hs hpa hs0
      rwa [realLMul_comm (realLOf_mem hp) hs, realLMul_comm haR hs] at h
    · have h := realLMul_le_right (realLOf_mem hp) hxR htR hpx ht0
      rwa [realLMul_comm (realLOf_mem hp) htR, realLMul_comm hxR htR] at h
  · rw [segment_eq_convex haR hxR htR, ← hsum (realLOf q) (realLOf_mem hq)]
    refine realLLe_add (realLMul_mem hs haR) (realLMul_mem hs (realLOf_mem hq))
      (realLMul_mem htR hxR) (realLMul_mem htR (realLOf_mem hq)) ?_ ?_
    · have h := realLMul_le_right haR (realLOf_mem hq) hs haq hs0
      rwa [realLMul_comm haR hs, realLMul_comm (realLOf_mem hq) hs] at h
    · have h := realLMul_le_right hxR (realLOf_mem hq) htR hxq ht0
      rwa [realLMul_comm hxR htR, realLMul_comm (realLOf_mem hq) htR] at h

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

/-- At parameter zero the segment is at its base point. -/
theorem segment_ratZero {a x : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hx : x ∈ RealL.{u}) :
    segment a x (realLOf ratZero.{u}) = a := by
  have hs := realLAdd_mem hx (realLNeg_mem ha)
  show realLAdd a (realLMul realLZero.{u} (realLAdd x (realLNeg a))) = a
  rw [realLMul_comm realLZero_mem hs, realLMul_zero hs, realLAdd_zero ha]

/-- At parameter one the segment has arrived. -/
theorem segment_ratOne {a x : ZFSet.{u}} (ha : a ∈ RealL.{u}) (hx : x ∈ RealL.{u}) :
    segment a x (realLOf ratOne.{u}) = x := by
  have hs := realLAdd_mem hx (realLNeg_mem ha)
  show realLAdd a (realLMul realLOne.{u} (realLAdd x (realLNeg a))) = x
  rw [realLMul_comm realLOne_mem hs, realLMul_one hs, realLAdd_comm ha hs,
    realLSub_add_cancel hx ha]

/-- Minus one is below zero, as reals: the bracket bound every unit-interval
coefficient estimate opens with. -/
theorem realLNeg_one_le_zero :
    realLLe (realLNeg (realLOf ratOne.{u})) realLZero.{u} := by
  have hn10 : ratLe (ratNeg ratOne.{u}) ratZero.{u} := by
    have := (ratAdd_le_add_right_iff (ratNeg_mem_Rat ratOne_mem_Rat)
      ratZero_mem_Rat ratOne_mem_Rat).mpr ratZero_lt_one.left
    rwa [ratZero_add (ratNeg_mem_Rat ratOne_mem_Rat),
      ratAdd_neg ratOne_mem_Rat] at this
  rw [realLOf_neg ratOne_mem_Rat]
  exact (realLOf_le_realLOf (ratNeg_mem_Rat ratOne_mem_Rat)
    ratZero_mem_Rat).mpr hn10

/-- Minus one is strictly below zero, as reals. -/
theorem realLNeg_one_lt_zero :
    realLLt (realLNeg realLOne.{u}) realLZero.{u} := by
  have h01 : realLLt realLZero.{u} realLOne.{u} :=
    (realLOf_lt_realLOf ratZero_mem_Rat ratOne_mem_Rat).mpr ratZero_lt_one
  have := realLNeg_lt_neg realLZero_mem realLOne_mem h01
  rwa [realLNeg_zero] at this

/-- Clamp a real into `[-1, 1]`. The point is the two sign lemmas below: the
clamp's sign is the argument's sign, so a sign disjunction for clamped reals
is a sign disjunction outright. -/
def realLClamp (z : ZFSet.{u}) : ZFSet.{u} :=
  realLMax (realLNeg realLOne.{u}) (realLMin z realLOne.{u})

theorem realLClamp_mem {z : ZFSet.{u}} (hz : z ∈ RealL.{u}) :
    realLClamp z ∈ RealL.{u} :=
  realLMax_mem (realLNeg_mem realLOne_mem) (realLMin_mem hz realLOne_mem)

/-- `-1 ≤ clamp z ≤ 1`, whatever `z` is -- membership is not even needed,
because both bounds are facts about `-1` and `1` alone. -/
theorem realLClamp_bracket {z : ZFSet.{u}} :
    And (realLLe (realLNeg realLOne.{u}) (realLClamp z))
      (realLLe (realLClamp z) realLOne.{u}) := by
  refine ⟨realLLe_max_left (realLNeg_mem realLOne_mem), ?_⟩
  refine realLMax_le (fun h => ?_) (realLMin_le_right realLOne_mem)
  exact realLLt_irrefl realLOne_mem
    (realLLt_trans realLOne_mem (realLNeg_mem realLOne_mem) realLOne_mem h
      (realLLt_trans (realLNeg_mem realLOne_mem) realLZero_mem realLOne_mem
        realLNeg_one_lt_zero
        ((realLOf_lt_realLOf ratZero_mem_Rat ratOne_mem_Rat).mpr
          ratZero_lt_one)))

/-- The clamp is nonpositive exactly when the argument is. -/
theorem realLClamp_nonpos_iff {z : ZFSet.{u}} (hz : z ∈ RealL.{u}) :
    Iff (realLLe (realLClamp z) realLZero.{u}) (realLLe z realLZero.{u}) := by
  constructor
  · intro h hzpos
    exact h (realLLt_max_of_right (realLLt_min hz realLOne_mem hzpos
      ((realLOf_lt_realLOf ratZero_mem_Rat ratOne_mem_Rat).mpr
        ratZero_lt_one)))
  · intro hz0
    refine realLMax_le realLNeg_one_le_zero ?_
    exact realLLe_trans (realLMin_mem hz realLOne_mem) hz realLZero_mem
      (realLMin_le_left hz) hz0

/-- The clamp is nonnegative exactly when the argument is. -/
theorem realLClamp_nonneg_iff {z : ZFSet.{u}} (hz : z ∈ RealL.{u}) :
    Iff (realLLe realLZero.{u} (realLClamp z)) (realLLe realLZero.{u} z) := by
  constructor
  · intro h hneg
    exact h (realLMax_lt (realLNeg_mem realLOne_mem)
      (realLMin_mem hz realLOne_mem) realLNeg_one_lt_zero
      (realLMin_lt_of_left hneg))
  · intro h0z
    have h0m : realLLe realLZero.{u} (realLMin z realLOne.{u}) :=
      le_realLMin h0z (fun h => realLLt_irrefl realLZero_mem
        (realLLt_trans realLZero_mem realLOne_mem realLZero_mem
          ((realLOf_lt_realLOf ratZero_mem_Rat ratOne_mem_Rat).mpr
            ratZero_lt_one) h))
    exact realLLe_trans realLZero_mem (realLMin_mem hz realLOne_mem)
      (realLClamp_mem hz) h0m
      (realLLe_max_right (realLMin_mem hz realLOne_mem))




/-- Closeness survives `max`, case-free: both sides of the bracket are
least-upper-bound arguments, and no comparison between the reals is ever
decided. -/
theorem close_max {a b c d δ : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hc : c ∈ RealL.{u}) (hd : d ∈ RealL.{u})
    (hδ : δ ∈ RealL.{u}) (h₁ : Close a b δ) (h₂ : Close c d δ) :
    Close (realLMax a c) (realLMax b d) δ := by
  have hmac := realLMax_mem ha hc
  have hmbd := realLMax_mem hb hd
  refine ⟨?_, ?_⟩
  · refine (realLNeg_le_sub_iff hmac hmbd hδ).mpr ?_
    refine realLMax_le ?_ ?_
    · exact realLLe_trans hb (realLAdd_mem ha hδ) (realLAdd_mem hmac hδ)
        ((realLNeg_le_sub_iff ha hb hδ).mp h₁.left)
        (realLLe_add_right ha hmac hδ (realLLe_max_left ha))
    · exact realLLe_trans hd (realLAdd_mem hc hδ) (realLAdd_mem hmac hδ)
        ((realLNeg_le_sub_iff hc hd hδ).mp h₂.left)
        (realLLe_add_right hc hmac hδ (realLLe_max_right hc))
  · refine (realLSub_le_iff hmac hmbd hδ).mpr ?_
    refine realLMax_le ?_ ?_
    · exact realLLe_trans ha (realLAdd_mem hb hδ) (realLAdd_mem hmbd hδ)
        ((realLSub_le_iff ha hb hδ).mp h₁.right)
        (realLLe_add_right hb hmbd hδ (realLLe_max_left hb))
    · exact realLLe_trans hc (realLAdd_mem hd hδ) (realLAdd_mem hmbd hδ)
        ((realLSub_le_iff hc hd hδ).mp h₂.right)
        (realLLe_add_right hd hmbd hδ (realLLe_max_right hd))

/-- Closeness survives `min`: the mirror of `close_max`, through the
shifted-min inequality rather than a case split. -/
theorem close_min {a b c d δ : ZFSet.{u}} (ha : a ∈ RealL.{u})
    (hb : b ∈ RealL.{u}) (hc : c ∈ RealL.{u}) (hd : d ∈ RealL.{u})
    (hδ : δ ∈ RealL.{u}) (h₁ : Close a b δ) (h₂ : Close c d δ) :
    Close (realLMin a c) (realLMin b d) δ := by
  have hmac := realLMin_mem ha hc
  have hmbd := realLMin_mem hb hd
  refine ⟨?_, ?_⟩
  · refine (realLNeg_le_sub_iff hmac hmbd hδ).mpr ?_
    refine realLLe_trans hmbd
      (realLMin_mem (realLAdd_mem ha hδ) (realLAdd_mem hc hδ))
      (realLAdd_mem hmac hδ) ?_ (realLMin_add_le ha hc hδ)
    refine le_realLMin ?_ ?_
    · exact realLLe_trans hmbd hb (realLAdd_mem ha hδ)
        (realLMin_le_left hb) ((realLNeg_le_sub_iff ha hb hδ).mp h₁.left)
    · exact realLLe_trans hmbd hd (realLAdd_mem hc hδ)
        (realLMin_le_right hd) ((realLNeg_le_sub_iff hc hd hδ).mp h₂.left)
  · refine (realLSub_le_iff hmac hmbd hδ).mpr ?_
    refine realLLe_trans hmac
      (realLMin_mem (realLAdd_mem hb hδ) (realLAdd_mem hd hδ))
      (realLAdd_mem hmbd hδ) ?_ (realLMin_add_le hb hd hδ)
    refine le_realLMin ?_ ?_
    · exact realLLe_trans hmac ha (realLAdd_mem hb hδ)
        (realLMin_le_left ha) ((realLSub_le_iff ha hb hδ).mp h₁.right)
    · exact realLLe_trans hmac hc (realLAdd_mem hd hδ)
        (realLMin_le_right hc) ((realLSub_le_iff hc hd hδ).mp h₂.right)

/-- The positive part of a real: `max` against zero. -/
def posPart (z : ZFSet.{u}) : ZFSet.{u} := realLMax z realLZero.{u}

theorem posPart_mem {z : ZFSet.{u}} (hz : z ∈ RealL.{u}) :
    posPart z ∈ RealL.{u} := realLMax_mem hz realLZero_mem

theorem posPart_nonneg {z : ZFSet.{u}} :
    realLLe realLZero.{u} (posPart z) := realLLe_max_right realLZero_mem

theorem le_posPart {z : ZFSet.{u}} (hz : z ∈ RealL.{u}) :
    realLLe z (posPart z) := realLLe_max_left hz

/-- On the nonnegative side the positive part is the identity. -/
theorem posPart_of_nonneg {z : ZFSet.{u}} (hz : z ∈ RealL.{u})
    (h : realLLe realLZero.{u} z) : posPart z = z :=
  realLLe_antisymm (posPart_mem hz) hz
    (realLMax_le (realLLe_refl hz) h) (le_posPart hz)

/-- On the nonpositive side the positive part vanishes. -/
theorem posPart_of_nonpos {z : ZFSet.{u}} (hz : z ∈ RealL.{u})
    (h : realLLe z realLZero.{u}) : posPart z = realLZero.{u} :=
  realLLe_antisymm (posPart_mem hz) realLZero_mem
    (realLMax_le h (realLLe_refl realLZero_mem)) posPart_nonneg

/-- Subadditivity: `(u+v)⁺ ≤ u⁺ + v⁺`, with no case decided. -/
theorem posPart_add_le {v w : ZFSet.{u}} (hv : v ∈ RealL.{u})
    (hw : w ∈ RealL.{u}) :
    realLLe (posPart (realLAdd v w)) (realLAdd (posPart v) (posPart w)) := by
  have hpv := posPart_mem hv
  have hpw := posPart_mem hw
  refine realLMax_le ?_ ?_
  · have step2 : realLLe (realLAdd w (posPart v))
        (realLAdd (posPart w) (posPart v)) :=
      realLLe_add_right hw hpw hpv (le_posPart hw)
    rw [realLAdd_comm hw hpv, realLAdd_comm hpw hpv] at step2
    exact realLLe_trans (realLAdd_mem hv hw) (realLAdd_mem hpv hw)
      (realLAdd_mem hpv hpw)
      (realLLe_add_right hv hpv hw (le_posPart hv)) step2
  · have step : realLLe (realLAdd realLZero.{u} (posPart v))
        (realLAdd (posPart w) (posPart v)) :=
      realLLe_add_right realLZero_mem hpw hpv (posPart_nonneg (z := w))
    rw [realLAdd_comm realLZero_mem hpv, realLAdd_zero hpv,
      realLAdd_comm hpw hpv] at step
    exact realLLe_trans realLZero_mem hpv (realLAdd_mem hpv hpw)
      (posPart_nonneg (z := v)) step

/-- The negative part: the positive part of the negation. -/
def negPart (z : ZFSet.{u}) : ZFSet.{u} := posPart (realLNeg z)

theorem negPart_mem {z : ZFSet.{u}} (hz : z ∈ RealL.{u}) :
    negPart z ∈ RealL.{u} := posPart_mem (realLNeg_mem hz)

/-- The two parts annihilate: `z⁺ · z⁻ = 0`. Nothing decides the sign of
`z`. A rational witness `p` below the product fixes a scale; two
cotransitivity reads against `ε` and `-ε` for an `ε` with `ε² < p` leave
four quarters, and each is contradicted -- the outer two because one factor
is nonpositive, the middle because both are below `ε`, the crossing because
`0 < z < 0`. -/
theorem posPart_mul_negPart {z : ZFSet.{u}} (hz : z ∈ RealL.{u}) :
    realLMul (posPart z) (negPart z) = realLZero.{u} := by
  have hP := posPart_mem hz
  have hN := negPart_mem hz
  have hPN := realLMul_mem hP hN
  refine realLLe_antisymm hPN realLZero_mem (fun hlt => ?_)
    (realLMul_nonneg hP hN (posPart_nonneg (z := z))
      (posPart_nonneg (z := realLNeg z)))
  obtain ⟨p, hpU, hpL⟩ := id hlt
  rw [realLZero, realLOf, snd_opair] at hpU
  obtain ⟨hpQ, hp0⟩ := (mem_sep_iff _ _ _).mp hpU
  have hm : realLLt (realLOf p) (realLMul (posPart z) (negPart z)) :=
    (realLOf_lt_iff_mem_lower hPN hpQ).mpr hpL
  obtain ⟨N, hNw, hNp⟩ := exists_invWidth_lt hpQ hp0
  obtain ⟨j, rfl⟩ := (mem_omega_iff N).mp hNw
  have hεQ := invWidth_mem_Rat (ofNat_mem_omega.{u} j)
  have hε0 := invWidth_pos (ofNat_mem_omega.{u} j)
  have hεR := realLOf_mem hεQ
  have hε0R : realLLt realLZero.{u} (realLOf (invWidth (ofNat.{u} j))) :=
    (realLOf_lt_realLOf ratZero_mem_Rat hεQ).mpr hε0
  have hsq : ratLt (ratMul (invWidth (ofNat.{u} j)) (invWidth (ofNat.{u} j))) p := by
    have hone : ratLe (ratMul (invWidth (ofNat.{u} j)) (invWidth (ofNat.{u} j)))
        (ratMul ratOne.{u} (invWidth (ofNat.{u} j))) :=
      ratMul_le_mul_right hεQ ratOne_mem_Rat hεQ (invWidth_le_one j) hε0.left
    rw [ratOne_mul hεQ] at hone
    exact ratLt_of_le_of_lt (ratMul_mem_Rat hεQ hεQ) hεQ hpQ hone hNp
  have hnε0R : realLLt (realLOf (ratNeg (invWidth (ofNat.{u} j)))) realLZero.{u} := by
    refine (realLOf_lt_realLOf (ratNeg_mem_Rat hεQ) ratZero_mem_Rat).mpr ?_
    have := (ratNeg_lt_neg_iff hεQ ratZero_mem_Rat).mpr hε0
    rwa [ratNeg_zero] at this
  rcases realLLt_cotrans realLZero_mem hεR hz hε0R with h0z | hzε
  · -- `0 < z`: the negative part is nonpositive, so the product is.
    have hnzlt : realLLt (realLNeg z) realLZero.{u} := by
      have := realLNeg_lt_neg realLZero_mem hz h0z
      rwa [realLNeg_zero] at this
    have hNle : realLLe (negPart z) realLZero.{u} :=
      realLMax_le (realLLe_of_lt (realLNeg_mem hz) realLZero_mem hnzlt)
        (realLLe_refl realLZero_mem)
    have hstep : realLLe (realLMul (negPart z) (posPart z))
        (realLMul realLZero.{u} (posPart z)) :=
      realLMul_le_right hN realLZero_mem hP hNle (posPart_nonneg (z := z))
    rw [realLMul_comm hN hP, realLMul_comm realLZero_mem hP,
      realLMul_zero hP] at hstep
    exact hstep hlt
  · rcases realLLt_cotrans (realLOf_mem (ratNeg_mem_Rat hεQ)) realLZero_mem
      hz hnε0R with hnz | hz0
    · -- the middle strip: both parts are below `ε`, so the product is below
      -- `ε² < p`, against the witness.
      have hPle : realLLe (posPart z) (realLOf (invWidth (ofNat.{u} j))) :=
        realLMax_le (realLLe_of_lt hz hεR hzε)
          (realLLe_of_lt realLZero_mem hεR hε0R)
      have hnzε : realLLt (realLNeg z) (realLOf (invWidth (ofNat.{u} j))) := by
        have := realLNeg_lt_neg (realLOf_mem (ratNeg_mem_Rat hεQ)) hz hnz
        rwa [realLOf_neg (ratNeg_mem_Rat hεQ), ratNeg_ratNeg hεQ] at this
      have hNle : realLLe (negPart z) (realLOf (invWidth (ofNat.{u} j))) :=
        realLMax_le (realLLe_of_lt (realLNeg_mem hz) hεR hnzε)
          (realLLe_of_lt realLZero_mem hεR hε0R)
      have hone : realLLe (realLMul (posPart z) (negPart z))
          (realLMul (realLOf (invWidth (ofNat.{u} j))) (negPart z)) :=
        realLMul_le_right hP hεR hN hPle (posPart_nonneg (z := realLNeg z))
      have htwo : realLLe (realLMul (negPart z) (realLOf (invWidth (ofNat.{u} j))))
          (realLMul (realLOf (invWidth (ofNat.{u} j)))
            (realLOf (invWidth (ofNat.{u} j)))) :=
        realLMul_le_right hN hεR hεR hNle
          (realLLe_of_lt realLZero_mem hεR hε0R)
      rw [realLMul_comm hN hεR] at htwo
      have hchain := realLLe_trans hPN (realLMul_mem hεR hN)
        (realLMul_mem hεR hεR) hone htwo
      rw [← realLOf_mul hεQ hεQ] at hchain
      have hlast := realLLt_of_lt_of_le (realLOf_mem hpQ) hPN
        (realLOf_mem (ratMul_mem_Rat hεQ hεQ)) hm hchain
      exact ratLt_irrefl (ratLt_trans hpQ (ratMul_mem_Rat hεQ hεQ) hpQ
        ((realLOf_lt_realLOf hpQ (ratMul_mem_Rat hεQ hεQ)).mp hlast) hsq)
    · -- `z < 0`: the positive part is nonpositive, so the product is.
      have hPle : realLLe (posPart z) realLZero.{u} :=
        realLMax_le (realLLe_of_lt hz realLZero_mem hz0)
          (realLLe_refl realLZero_mem)
      have hstep : realLLe (realLMul (posPart z) (negPart z))
          (realLMul realLZero.{u} (negPart z)) :=
        realLMul_le_right hP realLZero_mem hN hPle
          (posPart_nonneg (z := realLNeg z))
      rw [realLMul_comm realLZero_mem hN, realLMul_zero hN] at hstep
      exact hstep hlt




/-- The decomposition `z⁺ = z + z⁻`: the two parts reassemble the real. -/
theorem posPart_eq_add_negPart {z : ZFSet.{u}} (hz : z ∈ RealL.{u}) :
    posPart z = realLAdd z (negPart z) := by
  have hnz := realLNeg_mem hz
  have hdist := realLMax_add_dist hnz realLZero_mem hz
  rw [realLAdd_comm hnz hz, realLAdd_neg hz,
    realLAdd_comm realLZero_mem hz, realLAdd_zero hz] at hdist
  calc posPart z = realLMax z realLZero.{u} := rfl
    _ = realLMax realLZero.{u} z := realLMax_comm _ _
    _ = realLAdd (realLMax (realLNeg z) realLZero.{u}) z := hdist
    _ = realLAdd z (realLMax (realLNeg z) realLZero.{u}) :=
        realLAdd_comm (realLMax_mem hnz realLZero_mem) hz
    _ = realLAdd z (negPart z) := rfl

/-- The positive part is monotone. -/
theorem posPart_mono {v w : ZFSet.{u}} (hv : v ∈ RealL.{u})
    (hw : w ∈ RealL.{u}) (h : realLLe v w) :
    realLLe (posPart v) (posPart w) :=
  realLMax_le (realLLe_trans hv hw (posPart_mem hw) h (le_posPart hw))
    (posPart_nonneg (z := w))

/-- The annihilation squeeze. If `x` and `y` are within `w ≥ 0` of each
other, then `x⁺ · y⁻ ≤ w²`: the cross term is at most `w · y⁻` (through
`y⁺y⁻ = 0`) and at most `x⁺ · w` (through `x⁺x⁻ = 0`), so its square is at most
`w²` times itself, and cancelling pins it under `w²`. Quadratic, with no sign
ever decided. -/
theorem posPart_mul_negPart_le_sq {x y w : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hw : w ∈ RealL.{u})
    (h0w : realLLe realLZero.{u} w) (hc : Close x y w) :
    realLLe (realLMul (posPart x) (negPart y)) (realLMul w w) := by
  have hPx := posPart_mem hx
  have hNy := negPart_mem hy
  have hPy := posPart_mem hy
  have hNx := negPart_mem hx
  have ht := realLMul_mem hPx hNy
  have h0t : realLLe realLZero.{u} (realLMul (posPart x) (negPart y)) :=
    realLMul_nonneg hPx hNy (posPart_nonneg (z := x))
      (posPart_nonneg (z := realLNeg y))
  have h0Ny : realLLe realLZero.{u} (negPart y) :=
    posPart_nonneg (z := realLNeg y)
  have h0Px : realLLe realLZero.{u} (posPart x) := posPart_nonneg (z := x)
  -- `x⁺ ≤ y⁺ + w`
  have hxle : realLLe x (realLAdd y w) := (realLSub_le_iff hx hy hw).mp hc.right
  have h1 : realLLe (posPart x) (realLAdd (posPart y) w) := by
    have ha := posPart_mono hx (realLAdd_mem hy hw) hxle
    have hb := posPart_add_le hy hw
    rw [posPart_of_nonneg hw h0w] at hb
    exact realLLe_trans hPx (posPart_mem (realLAdd_mem hy hw))
      (realLAdd_mem hPy hw) ha hb
  -- `y⁻ ≤ x⁻ + w`
  have h2 : realLLe (negPart y) (realLAdd (negPart x) w) := by
    have hneg := realLNeg_le_neg hx (realLAdd_mem hy hw) hxle
    rw [realLNeg_realLAdd hy hw] at hneg
    have hshift := (realLSub_le_iff (realLNeg_mem hy) hw (realLNeg_mem hx)).mp hneg
    rw [realLAdd_comm hw (realLNeg_mem hx)] at hshift
    have ha := posPart_mono (realLNeg_mem hy)
      (realLAdd_mem (realLNeg_mem hx) hw) hshift
    have hb := posPart_add_le (realLNeg_mem hx) hw
    rw [posPart_of_nonneg hw h0w] at hb
    exact realLLe_trans hNy (posPart_mem (realLAdd_mem (realLNeg_mem hx) hw))
      (realLAdd_mem hNx hw) ha hb
  -- `t ≤ w · y⁻`, through `y⁺y⁻ = 0`
  have step1 : realLLe (realLMul (posPart x) (negPart y))
      (realLMul w (negPart y)) := by
    have hm := realLMul_le_right hPx (realLAdd_mem hPy hw) hNy h1 h0Ny
    have hdist : realLMul (realLAdd (posPart y) w) (negPart y)
        = realLAdd (realLMul (posPart y) (negPart y))
          (realLMul w (negPart y)) := by
      rw [realLMul_comm (realLAdd_mem hPy hw) hNy,
        realLMul_distrib hNy hPy hw,
        realLMul_comm hNy hPy, realLMul_comm hNy hw]
    rw [hdist, posPart_mul_negPart hy,
      realLAdd_comm realLZero_mem (realLMul_mem hw hNy),
      realLAdd_zero (realLMul_mem hw hNy)] at hm
    exact hm
  -- `t ≤ w · x⁺`, through `x⁺x⁻ = 0`
  have step2 : realLLe (realLMul (posPart x) (negPart y))
      (realLMul w (posPart x)) := by
    have hm := realLMul_le_right hNy (realLAdd_mem hNx hw) hPx h2 h0Px
    have hdist : realLMul (realLAdd (negPart x) w) (posPart x)
        = realLAdd (realLMul (posPart x) (negPart x))
          (realLMul w (posPart x)) := by
      rw [realLMul_comm (realLAdd_mem hNx hw) hPx,
        realLMul_distrib hPx hNx hw, realLMul_comm hPx hw]
    rw [hdist, posPart_mul_negPart hx,
      realLAdd_comm realLZero_mem (realLMul_mem hw hPx),
      realLAdd_zero (realLMul_mem hw hPx),
      realLMul_comm hNy hPx] at hm
    exact hm
  -- square the two bounds
  have hwNy := realLMul_mem hw hNy
  have hwPx := realLMul_mem hw hPx
  have h0wNy : realLLe realLZero.{u} (realLMul w (negPart y)) :=
    realLMul_nonneg hw hNy h0w h0Ny
  have sqa : realLLe (realLMul (realLMul (posPart x) (negPart y))
        (realLMul (posPart x) (negPart y)))
      (realLMul (realLMul w (negPart y)) (realLMul (posPart x) (negPart y))) :=
    realLMul_le_right ht hwNy ht step1 h0t
  have sqb : realLLe (realLMul (realLMul w (negPart y))
        (realLMul (posPart x) (negPart y)))
      (realLMul (realLMul w (negPart y)) (realLMul w (posPart x))) := by
    have hm := realLMul_le_right ht hwPx hwNy step2 h0wNy
    rw [realLMul_comm ht hwNy, realLMul_comm hwPx hwNy] at hm
    exact hm
  have sq := realLLe_trans (realLMul_mem ht ht) (realLMul_mem hwNy ht)
    (realLMul_mem hwNy hwPx) sqa sqb
  -- rearrange `(w·y⁻)·(w·x⁺) = (w·w)·t`
  have rearr : realLMul (realLMul w (negPart y)) (realLMul w (posPart x))
      = realLMul (realLMul w w) (realLMul (posPart x) (negPart y)) := by
    rw [realLMul_assoc hw hNy (realLMul_mem hw hPx),
      realLMul_comm hNy (realLMul_mem hw hPx),
      realLMul_assoc hw hPx hNy,
      ← realLMul_assoc hw hw (realLMul_mem hPx hNy)]
  rw [rearr] at sq
  -- cancel: `t² ≤ w²·t` pins `t ≤ w²`
  intro hlt
  have h0sq : realLLe realLZero.{u} (realLMul w w) :=
    realLMul_nonneg hw hw h0w h0w
  have htpos : realLLt realLZero.{u} (realLMul (posPart x) (negPart y)) :=
    realLLt_of_le_of_lt realLZero_mem (realLMul_mem hw hw) ht h0sq hlt
  have hmul : realLLt (realLMul (realLMul w w)
        (realLMul (posPart x) (negPart y)))
      (realLMul (realLMul (posPart x) (negPart y))
        (realLMul (posPart x) (negPart y))) :=
    realLMul_lt_right (realLMul_mem hw hw) ht ht hlt htpos
  exact realLLt_irrefl (realLMul_mem (realLMul_mem hw hw) ht)
    (realLLt_of_lt_of_le (realLMul_mem (realLMul_mem hw hw) ht)
      (realLMul_mem ht ht) (realLMul_mem (realLMul_mem hw hw) ht) hmul sq)

/-- Closeness is symmetric: negate the difference. -/
theorem close_symm {x y c : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hc : c ∈ NumberTheory.Rat.{u}) (h : Close x y (realLOf c)) :
    Close y x (realLOf c) := by
  have hstep := withinOf_neg (realLAdd_mem hx (realLNeg_mem hy)) hc h
  rwa [realLNeg_sub hx hy] at hstep



/-- `max(x,y) = (x-y)⁺ + y`: the max through the positive part. -/
theorem realLMax_eq_posPart_add {x y : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) :
    realLMax x y = realLAdd (posPart (realLAdd x (realLNeg y))) y := by
  have h := realLMax_add_dist (realLAdd_mem hx (realLNeg_mem hy))
    realLZero_mem hy
  rw [realLSub_add_cancel hx hy, realLAdd_comm realLZero_mem hy,
    realLAdd_zero hy] at h
  show realLMax x y
    = realLAdd (realLMax (realLAdd x (realLNeg y)) realLZero.{u}) y
  exact h

/-- `min(x,y) = x - (x-y)⁺`: the min through the positive part, by two
lattice arguments rather than a case split. -/
theorem realLMin_eq_sub_posPart {x y : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) :
    realLMin x y = realLAdd x (realLNeg (posPart (realLAdd x (realLNeg y)))) := by
  have hn := posPart_mem (realLAdd_mem hx (realLNeg_mem hy))
  have hxn := realLAdd_mem hx (realLNeg_mem hn)
  have hmin := realLMin_mem hx hy
  refine realLLe_antisymm hmin hxn ?_ ?_
  · -- `min + (x-y)⁺ ≤ x`, then cancel
    have hkey : realLLe (realLAdd (realLMin x y)
        (posPart (realLAdd x (realLNeg y)))) x := by
      have hdist := realLMax_add_dist (realLAdd_mem hx (realLNeg_mem hy))
        realLZero_mem hmin
      rw [realLAdd_comm hmin hn]
      show realLLe (realLAdd (realLMax (realLAdd x (realLNeg y)) realLZero.{u})
        (realLMin x y)) x
      rw [← hdist]
      refine realLMax_le ?_ ?_
      · have hstep := realLLe_add_right hmin hy
          (realLAdd_mem hx (realLNeg_mem hy)) (realLMin_le_right hy)
        rw [realLAdd_comm hmin (realLAdd_mem hx (realLNeg_mem hy)),
          realLAdd_comm hy (realLAdd_mem hx (realLNeg_mem hy)),
          realLSub_add_cancel hx hy] at hstep
        exact hstep
      · rw [realLAdd_comm realLZero_mem hmin, realLAdd_zero hmin]
        exact realLMin_le_left hx
    have hstep := realLLe_add_right (realLAdd_mem hmin hn) hx
      (realLNeg_mem hn) hkey
    rwa [realLAdd_assoc hmin hn (realLNeg_mem hn), realLAdd_neg hn,
      realLAdd_zero hmin] at hstep
  · refine le_realLMin ?_ ?_
    · -- `x - (x-y)⁺ ≤ x`
      have hneg : realLLe (realLNeg (posPart (realLAdd x (realLNeg y))))
          realLZero.{u} := by
        have hstep := realLNeg_le_neg realLZero_mem hn
          (posPart_nonneg (z := realLAdd x (realLNeg y)))
        rwa [realLNeg_zero] at hstep
      have hstep := realLLe_add_right (realLNeg_mem hn) realLZero_mem hx hneg
      rwa [realLAdd_comm (realLNeg_mem hn) hx,
        realLAdd_comm realLZero_mem hx, realLAdd_zero hx] at hstep
    · -- `x - (x-y)⁺ ≤ y`, since `x ≤ max(x,y) = (x-y)⁺ + y`
      refine (realLSub_le_iff hx hn hy).mpr ?_
      rw [← realLMax_eq_posPart_add hx hy]
      exact realLLe_max_left hx

/-- Absorption: if `u + v ≤ 0`, then `(u + v⁺)⁺ = u⁺` -- the added
positive part is swallowed by `u`'s own negative part. -/
theorem posPart_absorb {v w : ZFSet.{u}} (hv : v ∈ RealL.{u})
    (hw : w ∈ RealL.{u}) (h : realLLe (realLAdd v w) realLZero.{u}) :
    posPart (realLAdd v (posPart w)) = posPart v := by
  have hpw := posPart_mem hw
  have hvw := realLAdd_mem hv hpw
  have hwle : realLLe w (realLNeg v) := by
    have hstep := realLLe_add_right (realLAdd_mem hv hw) realLZero_mem
      (realLNeg_mem hv) h
    rwa [realLAdd_comm hv hw, realLAdd_assoc hw hv (realLNeg_mem hv),
      realLAdd_neg hv, realLAdd_zero hw,
      realLAdd_comm realLZero_mem (realLNeg_mem hv),
      realLAdd_zero (realLNeg_mem hv)] at hstep
  refine realLLe_antisymm (posPart_mem hvw) (posPart_mem hv) ?_ ?_
  · refine realLMax_le ?_ (posPart_nonneg (z := v))
    have hmon : realLLe (posPart w) (negPart v) :=
      posPart_mono hw (realLNeg_mem hv) hwle
    have hadd := realLLe_add_right hpw (negPart_mem hv) hv hmon
    rw [realLAdd_comm hpw hv, realLAdd_comm (negPart_mem hv) hv,
      ← posPart_eq_add_negPart hv] at hadd
    exact hadd
  · refine posPart_mono hv hvw ?_
    have hstep := realLLe_add_right realLZero_mem hpw hv
      (posPart_nonneg (z := w))
    rwa [realLAdd_comm realLZero_mem hv, realLAdd_zero hv,
      realLAdd_comm hpw hv] at hstep

/-- The median through the ramps: for `A ≤ B`,
`max(A, min(L, B)) = L + (A-L)⁺ - (L-B)⁺`. Proved through `posPart_absorb`,
with no case split. -/
theorem median_eq_clamp {A B L : ZFSet.{u}} (hA : A ∈ RealL.{u})
    (hB : B ∈ RealL.{u}) (hL : L ∈ RealL.{u}) (hAB : realLLe A B) :
    realLMax A (realLMin L B)
      = realLAdd L (realLAdd (posPart (realLAdd A (realLNeg L)))
          (realLNeg (posPart (realLAdd L (realLNeg B))))) := by
  have hn := posPart_mem (realLAdd_mem hL (realLNeg_mem hB))
  have hM := realLAdd_mem hL (realLNeg_mem hn)
  have hp := posPart_mem (realLAdd_mem hA (realLNeg_mem hL))
  rw [realLMin_eq_sub_posPart hL hB, realLMax_eq_posPart_add hA hM]
  have h3 : realLAdd A (realLNeg (realLAdd L
      (realLNeg (posPart (realLAdd L (realLNeg B))))))
      = realLAdd (realLAdd A (realLNeg L))
        (posPart (realLAdd L (realLNeg B))) := by
    rw [realLNeg_realLAdd hL (realLNeg_mem hn), realLNeg_realLNeg hn,
      ← realLAdd_assoc hA (realLNeg_mem hL) hn]
  rw [h3]
  have habs : posPart (realLAdd (realLAdd A (realLNeg L))
      (posPart (realLAdd L (realLNeg B))))
      = posPart (realLAdd A (realLNeg L)) := by
    refine posPart_absorb (realLAdd_mem hA (realLNeg_mem hL))
      (realLAdd_mem hL (realLNeg_mem hB)) ?_
    rw [realLSub_add_sub hL hA hB]
    exact realLSub_nonpos_of_le hA hB hAB
  rw [habs, ← realLAdd_assoc hp hL (realLNeg_mem hn),
    realLAdd_comm hp hL, realLAdd_assoc hL hp (realLNeg_mem hn)]


/-- A nonnegative real below `c` is within `c`: the lower bracket rides
through zero. -/
theorem withinOf_of_nonneg_le {x c : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hc : c ∈ NumberTheory.Rat.{u}) (hc0 : ratLe ratZero.{u} c)
    (h0 : realLLe realLZero.{u} x) (hup : realLLe x (realLOf c)) :
    WithinOf x (realLOf c) := by
  refine ⟨?_, hup⟩
  rw [realLOf_neg hc]
  exact realLLe_trans (realLOf_mem (ratNeg_mem_Rat hc)) realLZero_mem hx
    ((realLOf_le_realLOf (ratNeg_mem_Rat hc) ratZero_mem_Rat).mpr
      (ratNeg_nonpos hc hc0)) h0

/-- The positive part is one-Lipschitz: closeness passes through it. -/
theorem posPart_close {x y δ : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) (hδ : δ ∈ RealL.{u}) (h : Close x y δ)
    (hδ0 : realLLe realLZero.{u} δ) : Close (posPart x) (posPart y) δ := by
  refine close_max hx hy realLZero_mem realLZero_mem hδ h ?_
  refine ⟨?_, ?_⟩
  · rw [realLAdd_neg realLZero_mem]
    intro hlt
    have hflip := realLNeg_lt_neg realLZero_mem (realLNeg_mem hδ) hlt
    rw [realLNeg_realLNeg hδ, realLNeg_zero] at hflip
    exact hδ0 hflip
  · rw [realLAdd_neg realLZero_mem]
    exact hδ0

/-- The positive part preserves uniform continuity: it is one-Lipschitz, so
the modulus passes through unchanged. -/
theorem uniformlyContinuousOn_posPart {H : ZFSet.{u} → ZFSet.{u}}
    {p q : ZFSet.{u}} (hHm : ∀ x, x ∈ realLIcc p q → H x ∈ RealL.{u})
    (h : UniformlyContinuousOn H p q) :
    UniformlyContinuousOn (fun x => posPart (H x)) p q := by
  intro n
  obtain ⟨m, hm⟩ := h n
  refine ⟨m, fun w x y hwQ hw0 hwle hx hy hc => ?_⟩
  exact posPart_close (hHm x hx) (hHm y hy)
    (realLOf_mem (invWidth_mem_Rat (ofNat_mem_omega.{u} n)))
    (hm w x y hwQ hw0 hwle hx hy hc)
    ((realLOf_le_realLOf ratZero_mem_Rat
      (invWidth_mem_Rat (ofNat_mem_omega.{u} n))).mpr
      (invWidth_pos (ofNat_mem_omega.{u} n)).left)

/-- The max of two uniformly continuous functions is uniformly continuous:
the coarser modulus serves both. -/
theorem uniformlyContinuousOn_max {H₁ H₂ : ZFSet.{u} → ZFSet.{u}}
    {p q : ZFSet.{u}}
    (h1m : ∀ x, x ∈ realLIcc p q → H₁ x ∈ RealL.{u})
    (h2m : ∀ x, x ∈ realLIcc p q → H₂ x ∈ RealL.{u})
    (h1 : UniformlyContinuousOn H₁ p q)
    (h2 : UniformlyContinuousOn H₂ p q) :
    UniformlyContinuousOn (fun t => realLMax (H₁ t) (H₂ t)) p q := by
  intro n
  obtain ⟨m₁, hm₁⟩ := h1 n
  obtain ⟨m₂, hm₂⟩ := h2 n
  refine ⟨Nat.max m₁ m₂, fun w x y hwQ hw0 hwle hx hy hc => ?_⟩
  exact close_max (h1m x hx) (h1m y hy) (h2m x hx) (h2m y hy)
    (realLOf_mem (invWidth_mem_Rat (ofNat_mem_omega.{u} n)))
    (hm₁ w x y hwQ hw0
      (ratLe_invWidth_of_le hwQ (Nat.le_max_left m₁ m₂) hwle) hx hy hc)
    (hm₂ w x y hwQ hw0
      (ratLe_invWidth_of_le hwQ (Nat.le_max_right m₁ m₂) hwle) hx hy hc)

/-- The median of two uniformly continuous functions against a constant is
uniformly continuous: `close_max` and `close_min` pass the coarser of the
two moduli straight through, and the constant costs nothing. -/
theorem uniformlyContinuousOn_median {H₁ H₂ : ZFSet.{u} → ZFSet.{u}}
    {L p q : ZFSet.{u}} (hL : L ∈ RealL.{u})
    (h1m : ∀ x, x ∈ realLIcc p q → H₁ x ∈ RealL.{u})
    (h2m : ∀ x, x ∈ realLIcc p q → H₂ x ∈ RealL.{u})
    (h1 : UniformlyContinuousOn H₁ p q)
    (h2 : UniformlyContinuousOn H₂ p q) :
    UniformlyContinuousOn (fun t => realLMax (H₁ t) (realLMin L (H₂ t))) p q := by
  intro n
  obtain ⟨m₁, hm₁⟩ := h1 n
  obtain ⟨m₂, hm₂⟩ := h2 n
  refine ⟨Nat.max m₁ m₂, fun w x y hwQ hw0 hwle hx hy hc => ?_⟩
  have hεQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
  have hε0 : ratLe ratZero.{u} (invWidth (ofNat.{u} n)) :=
    (invWidth_pos (ofNat_mem_omega.{u} n)).left
  have hwle₁ : ratLe w (invWidth (ofNat.{u} m₁)) :=
    ratLe_invWidth_of_le hwQ (Nat.le_max_left m₁ m₂) hwle
  have hwle₂ : ratLe w (invWidth (ofNat.{u} m₂)) :=
    ratLe_invWidth_of_le hwQ (Nat.le_max_right m₁ m₂) hwle
  exact close_max (h1m x hx) (h1m y hy)
    (realLMin_mem hL (h2m x hx)) (realLMin_mem hL (h2m y hy))
    (realLOf_mem hεQ)
    (hm₁ w x y hwQ hw0 hwle₁ hx hy hc)
    (close_min hL hL (h2m x hx) (h2m y hy) (realLOf_mem hεQ)
      (close_self hL hεQ hε0)
      (hm₂ w x y hwQ hw0 hwle₂ hx hy hc))


/-- The slack of the positive-part square against its linear approximation:
`(x⁺)² - ((y⁺)² + (y⁺+y⁺)(x-y)) = d² + (y⁺x⁻ + y⁺x⁻)` for `d = x⁺-y⁺`.
`posPart_mul_negPart` and `posPart_mul_negPart_le_sq` pin each right-hand term
under `w²`. -/
theorem posPart_sq_slack {x y : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) :
    realLAdd (realLMul (posPart x) (posPart x))
      (realLNeg (realLAdd (realLMul (posPart y) (posPart y))
        (realLMul (realLAdd (posPart y) (posPart y)) (realLAdd x (realLNeg y)))))
    = realLAdd
        (realLMul (realLAdd (posPart x) (realLNeg (posPart y)))
          (realLAdd (posPart x) (realLNeg (posPart y))))
        (realLAdd (realLMul (posPart y) (negPart x))
          (realLMul (posPart y) (negPart x))) := by
  have hP := posPart_mem hx
  have hQ := posPart_mem hy
  have hNx := negPart_mem hx
  have hNy := negPart_mem hy
  have hd := realLAdd_mem hP (realLNeg_mem hQ)
  have hQQ := realLAdd_mem hQ hQ
  have hxy := realLAdd_mem hx (realLNeg_mem hy)
  -- the difference `d - (x-y)` is `x⁻ - y⁻`
  have hE : realLAdd (realLAdd (posPart x) (realLNeg (posPart y)))
      (realLNeg (realLAdd x (realLNeg y)))
      = realLAdd (negPart x) (realLNeg (negPart y)) := by
    rw [realLNeg_sub hx hy,
      realLAdd_swap_inner hP (realLNeg_mem hQ) hy (realLNeg_mem hx)]
    have h1 : realLAdd (posPart x) (realLNeg x) = negPart x := by
      rw [posPart_eq_add_negPart hx, realLAdd_comm hx hNx,
        realLAdd_assoc hNx hx (realLNeg_mem hx), realLAdd_neg hx,
        realLAdd_zero hNx]
    have h2 : realLAdd y (realLNeg (posPart y)) = realLNeg (negPart y) := by
      rw [posPart_eq_add_negPart hy, realLNeg_realLAdd hy hNy,
        ← realLAdd_assoc hy (realLNeg_mem hy) (realLNeg_mem hNy),
        realLAdd_neg hy, realLAdd_comm realLZero_mem (realLNeg_mem hNy),
        realLAdd_zero (realLNeg_mem hNy)]
    rw [h1, h2]
  -- `y⁺ · (x⁻ - y⁻) = y⁺x⁻`, by annihilation
  have hQE : realLMul (posPart y) (realLAdd (negPart x) (realLNeg (negPart y)))
      = realLMul (posPart y) (negPart x) := by
    rw [realLMul_distrib hQ hNx (realLNeg_mem hNy),
      realLMul_neg hQ hNy, posPart_mul_negPart hy, realLNeg_zero,
      realLAdd_zero (realLMul_mem hQ hNx)]
  -- difference of squares: `P² - Q² = d · (P+Q)`
  have hdos := realLSub_sq hP hQ
  -- `P + Q = d + (Q+Q)`
  have hPQ : realLAdd (posPart x) (posPart y)
      = realLAdd (realLAdd (posPart x) (realLNeg (posPart y)))
        (realLAdd (posPart y) (posPart y)) := by
    rw [realLAdd_assoc hP (realLNeg_mem hQ) hQQ,
      ← realLAdd_assoc (realLNeg_mem hQ) hQ hQ,
      realLAdd_comm (realLNeg_mem hQ) hQ, realLAdd_neg hQ,
      realLAdd_comm realLZero_mem hQ, realLAdd_zero hQ]
  -- assemble: slack = d² + (Q+Q)·(d - (x-y)), then annihilate
  rw [realLNeg_realLAdd (realLMul_mem hQ hQ) (realLMul_mem hQQ hxy),
    ← realLAdd_assoc (realLMul_mem hP hP) (realLNeg_mem (realLMul_mem hQ hQ))
      (realLNeg_mem (realLMul_mem hQQ hxy)),
    hdos, hPQ,
    realLMul_distrib hd hd hQQ,
    realLAdd_assoc (realLMul_mem hd hd) (realLMul_mem hd hQQ)
      (realLNeg_mem (realLMul_mem hQQ hxy)),
    realLMul_comm hd hQQ,
    ← realLMul_neg hQQ hxy,
    ← realLMul_distrib hQQ hd (realLNeg_mem hxy),
    hE, realLAdd_mul hQ hQ (realLAdd_mem hNx (realLNeg_mem hNy)),
    hQE]

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
#print axioms withinOf_of_margins
#print axioms hasDerivOn_mvi
#print axioms eq_of_hasDerivOn_zero
#print axioms realLLe_of_margins
#print axioms close_shift
#print axioms hasDerivOn_mono
#print axioms hasDerivOn_linear
#print axioms hasDerivOn_const
#print axioms hasDerivOn_neg
#print axioms hasDerivOn_add
#print axioms hasDerivOn_le_of_slope_le
#print axioms PointwiseModulusW
#print axioms uniformlyContinuousOn_of_hasDerivOn
#print axioms gridPoint_succ_cases
#print axioms gridPoint_close_step
#print axioms realLOf_mem_realLIcc
#print axioms withinOf_of_withinOf_mul
#print axioms exists_rat_between
#print axioms segment_mem
#print axioms segment_eq_convex
#print axioms segment_mem_realLIcc
#print axioms hasDerivOn_comp
#print axioms segment_ratZero
#print axioms segment_ratOne
#print axioms withinOf_diam
#print axioms realLNeg_one_le_zero
#print axioms realLNeg_one_lt_zero
#print axioms realLClamp_mem
#print axioms realLClamp_bracket

#print axioms realLClamp_nonpos_iff
#print axioms realLClamp_nonneg_iff
#print axioms close_max
#print axioms close_min
#print axioms posPart_mem
#print axioms posPart_of_nonneg
#print axioms posPart_of_nonpos
#print axioms posPart_add_le
#print axioms posPart_close
#print axioms negPart_mem
#print axioms posPart_mul_negPart
#print axioms posPart_eq_add_negPart
#print axioms posPart_mono
#print axioms posPart_mul_negPart_le_sq
#print axioms close_symm
#print axioms posPart_sq_slack
#print axioms withinOf_of_nonneg_le
#print axioms uniformlyContinuousOn_max
#print axioms realLMax_eq_posPart_add
#print axioms realLMin_eq_sub_posPart
#print axioms posPart_absorb
#print axioms median_eq_clamp
#print axioms uniformlyContinuousOn_posPart
#print axioms uniformlyContinuousOn_median

#print axioms hasDerivOn_mul
#print axioms hasDerivOn_congr
#print axioms close_self
#print axioms uniformlyContinuousOn_const
#print axioms uniformlyContinuousOn_add
#print axioms exists_rat_near_in_Icc

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
#print axioms mvi_step
#print axioms mvi_grid
#print axioms mono_grid
#print axioms ratSub_add_sub
#print axioms posPart_nonneg
#print axioms le_posPart
end Analysis

#print axioms Analysis.continuousAtOn_of_pointwiseModulus
namespace ZFSet
export Analysis (ContinuousAtOn HasDerivAt HasDerivOn LipschitzOn PointwiseModulus PointwiseModulusW TaggedPartition UniformlyContinuousOn VanishReadout close_add_lin close_max close_min close_of_close_close close_realLOf_sub_self close_self close_shift close_symm continuousAtOn_of_pointwiseModulus eq_of_hasDerivOn_zero exists_invWidth_add_self_lt exists_invWidth_mul_lt exists_rat_between exists_rat_bound exists_rat_near_in_Icc gridPoint_close_step gridPoint_succ_cases hasDerivAt_comp hasDerivAt_mul hasDerivOn_add hasDerivOn_comp hasDerivOn_congr hasDerivOn_const hasDerivOn_le_of_slope_le hasDerivOn_linear hasDerivOn_mono hasDerivOn_mul hasDerivOn_mvi hasDerivOn_neg hasDerivOn_step invWidth_le_one le_posPart meanSlope median_eq_clamp negPart negPart_mem posPart posPart_absorb posPart_add_le posPart_close posPart_eq_add_negPart posPart_mem posPart_mono posPart_mul_negPart posPart_mul_negPart_le_sq posPart_nonneg posPart_of_nonneg posPart_of_nonpos posPart_sq_slack product_slack ratLe_invWidth_of_le ratSub_add_sub realLClamp realLClamp_bracket realLClamp_mem realLClamp_nonneg_iff realLClamp_nonpos_iff realLIcc_mono realLLe_of_margins realLMax_eq_posPart_add realLMin_eq_sub_posPart realLNeg_one_le_zero realLNeg_one_lt_zero realLOf_mem_realLIcc segment segment_eq_convex segment_mem segment_mem_realLIcc segment_ratOne segment_ratZero tilt uniformlyContinuousOn_add uniformlyContinuousOn_const uniformlyContinuousOn_max uniformlyContinuousOn_median uniformlyContinuousOn_of_hasDerivOn uniformlyContinuousOn_posPart withinOf_add withinOf_diam withinOf_increment withinOf_increment_sharp withinOf_mono withinOf_mul withinOf_neg withinOf_of_margins withinOf_of_nonneg_le withinOf_of_withinOf_mul withinOf_realLOf_iff withinOf_self withinOf_zero)
end ZFSet
