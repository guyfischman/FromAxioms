/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Square roots of located reals.

Geometry needs one thing the number tower does not yet supply: a square root of
an arbitrary non-negative real. `SqrtTwo.lean` names `√2` by a nested-interval
walk tailored to the digit sequence of that one number; here the root is read
off the located pair directly, as

    L' = { p : p < 0 ∨ p·p ∈ L }        U' = { r : 0 < r ∧ r·r ∈ U }

and every clause of `IsLocated` comes back from trichotomy on ℚ. Nothing is
decided about the real, so the construction is choice-free and serves as the
free half of a price measurement: a geometric theorem that reduces to a
square root costs nothing beyond the ambient axioms.

`realLSqrt_sq` is the identity `√x · √x = x`, proved through the order rather
than through the four-corner product sets: each direction refutes a strict
inequality by exhibiting a corner, and `realLLe_antisymm` closes it.
-/

import FromAxioms.Analysis.Located

universe u

open Analysis NumberTheory SetTheory
namespace Geometry

/-! ## Rational preliminaries

Squaring is monotone on the non-negatives and continuous, and both facts are
needed in the form "given a target, produce a rational". There is no `min`
function on ℚ -- defining one needs the decision as data -- so the bounded
step below reaches the same effect by a case split on the total order. -/

/-- `(a + b)² = a² + b·((a + a) + b)`, the shift identity the openness clauses
need; `b` is negative in one of them.

Written without numerals --- `a + a` rather than `2a` --- so it needs nothing
of the rationals but their ring structure. Public because a root construction
at any degree wants the same expansion at its own degree, and this is the
square's. -/
theorem sq_shift {a b : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u}) (hb : b ∈ NumberTheory.Rat.{u}) :
    ratMul (ratAdd a b) (ratAdd a b)
      = ratAdd (ratMul a a) (ratMul b (ratAdd (ratAdd a a) b)) := by
  have hab := ratAdd_mem_Rat ha hb
  have haa := ratMul_mem_Rat ha ha
  have hba := ratMul_mem_Rat hb ha
  have hbb := ratMul_mem_Rat hb hb
  rw [ratAdd_mul ha hb hab, ratMul_add ha ha hb, ratMul_add hb ha hb,
      ratMul_add hb (ratAdd_mem_Rat ha ha) hb, ratMul_add hb ha ha,
      ratAdd_assoc haa (ratMul_mem_Rat ha hb) (ratAdd_mem_Rat hba hbb),
      ratMul_comm ha hb,
      ← ratAdd_assoc hba hba hbb]

/-- A positive step, below a given bound, whose product with `c` stays under
`d`. The bound is what keeps the step's higher powers under control once it is
substituted --- `δ²` for the square, `δ²` and `δ³` for the cube.

Nothing here is square-specific: `c` and `d` are arbitrary, and the caller
supplies whatever constant its own expansion needs. Public for that reason ---
an openness clause at any degree picks its step the same way. -/
theorem exists_small_step {c d b : ZFSet.{u}} (hc : c ∈ NumberTheory.Rat.{u})
    (hd : d ∈ NumberTheory.Rat.{u}) (hbQ : b ∈ NumberTheory.Rat.{u}) (hc0 : ratLe ratZero.{u} c)
    (hd0 : ratLt ratZero.{u} d) (hb0 : ratLt ratZero.{u} b) :
    ∃ δ, δ ∈ NumberTheory.Rat.{u} ∧ ratLt ratZero.{u} δ ∧ ratLe δ b ∧ ratLt (ratMul c δ) d := by
  obtain ⟨D, hDQ, hD0, hDlt⟩ := exists_mul_lt hc hd hc0 hd0
  rcases ratLe_total hDQ hbQ with h | h
  · exact ⟨D, hDQ, hD0, h, hDlt⟩
  · refine ⟨b, hbQ, hb0, ratLe_refl hbQ, ?_⟩
    exact ratLt_of_le_of_lt (ratMul_mem_Rat hc hbQ) (ratMul_mem_Rat hc hDQ) hd
      (by
        have hm := ratMul_le_mul_right hbQ hDQ hc h hc0
        rwa [ratMul_comm hbQ hc, ratMul_comm hDQ hc] at hm)
      hDlt

/-- Squaring is strictly monotone on the non-negatives. -/
theorem ratSq_lt_sq {a b : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u}) (hb : b ∈ NumberTheory.Rat.{u})
    (h0 : ratLe ratZero.{u} a) (h : ratLt a b) :
    ratLt (ratMul a a) (ratMul b b) := by
  have hb0 : ratLt ratZero.{u} b := ratLt_of_le_of_lt ratZero_mem_Rat ha hb h0 h
  have hbne : b ≠ ratZero.{u} := ratNe_zero_of_pos hb0
  have s₁ : ratLe (ratMul a a) (ratMul b a) := ratMul_le_mul_right ha hb ha h.left h0
  have s₂ : ratLt (ratMul a b) (ratMul b b) :=
    ratMul_lt_mul_right ha hb hb hbne hb0.left h
  exact ratLt_of_le_of_lt (ratMul_mem_Rat ha ha) (ratMul_mem_Rat ha hb)
    (ratMul_mem_Rat hb hb) (by rwa [ratMul_comm hb ha] at s₁) s₂

theorem ratSq_le_sq {a b : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u}) (hb : b ∈ NumberTheory.Rat.{u})
    (h0 : ratLe ratZero.{u} a) (h : ratLe a b) :
    ratLe (ratMul a a) (ratMul b b) := by
  have s₁ : ratLe (ratMul a a) (ratMul b a) := ratMul_le_mul_right ha hb ha h h0
  have s₂ : ratLe (ratMul a b) (ratMul b b) :=
    ratMul_le_mul_right ha hb hb h (ratLe_trans ratZero_mem_Rat ha hb h0 h)
  exact ratLe_trans (ratMul_mem_Rat ha ha) (ratMul_mem_Rat ha hb)
    (ratMul_mem_Rat hb hb) (by rwa [ratMul_comm hb ha] at s₁) s₂

/-- The converse, by trichotomy: on the non-negatives the square reflects `<`. -/
theorem ratLt_of_sq_lt_sq {a b : ZFSet.{u}} (ha : a ∈ NumberTheory.Rat.{u}) (hb : b ∈ NumberTheory.Rat.{u})
    (hb0 : ratLe ratZero.{u} b)
    (h : ratLt (ratMul a a) (ratMul b b)) : ratLt a b := by
  rcases ratLt_trichotomy ha hb with hlt | rfl | hgt
  · exact hlt
  · exact absurd h ratLt_irrefl
  · exact absurd (ratSq_le_sq hb ha hb0 hgt.left)
      ((ratLt_iff_not_ratLe (ratMul_mem_Rat ha ha) (ratMul_mem_Rat hb hb)).mp h)

/-- Below a rational whose square is under `t`, there is a larger one with the
same property: squaring is continuous, and this is the form the lower set's
openness clause wants. -/
theorem exists_gt_sq_lt {p t : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (ht : t ∈ NumberTheory.Rat.{u})
    (hp0 : ratLe ratZero.{u} p) (h : ratLt (ratMul p p) t) :
    ∃ p', p' ∈ NumberTheory.Rat.{u} ∧ ratLt p p' ∧ ratLt (ratMul p' p') t := by
  have hpp := ratMul_mem_Rat hp hp
  have hc : ratAdd (ratAdd p p) ratOne.{u} ∈ NumberTheory.Rat.{u} :=
    ratAdd_mem_Rat (ratAdd_mem_Rat hp hp) ratOne_mem_Rat
  have hpp0 : ratLe ratZero.{u} (ratAdd p p) := by
    have h₁ : ratLe (ratAdd ratZero.{u} p) (ratAdd p p) :=
      (ratAdd_le_add_right_iff hp ratZero_mem_Rat hp).mpr hp0
    rw [ratZero_add hp] at h₁
    exact ratLe_trans ratZero_mem_Rat hp (ratAdd_mem_Rat hp hp) hp0 h₁
  have hc0 : ratLe ratZero.{u} (ratAdd (ratAdd p p) ratOne.{u}) := by
    refine ratLe_trans ratZero_mem_Rat (ratAdd_mem_Rat hp hp) hc hpp0 ?_
    have := (ratAdd_le_add_left_iff (ratAdd_mem_Rat hp hp) ratZero_mem_Rat
      ratOne_mem_Rat).mpr ratZero_lt_one.left
    rwa [ratAdd_zero (ratAdd_mem_Rat hp hp)] at this
  have hd : ratAdd t (ratNeg (ratMul p p)) ∈ NumberTheory.Rat.{u} :=
    ratAdd_mem_Rat ht (ratNeg_mem_Rat hpp)
  have hd0 : ratLt ratZero.{u} (ratAdd t (ratNeg (ratMul p p))) := by
    have := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat hpp) hpp ht).mpr h
    rwa [ratAdd_neg hpp] at this
  obtain ⟨δ, hδQ, hδ0, hδ1, hδc⟩ :=
    exists_small_step hc hd ratOne_mem_Rat hc0 hd0 ratZero_lt_one
  refine ⟨ratAdd p δ, ratAdd_mem_Rat hp hδQ, ?_, ?_⟩
  · have := (ratAdd_lt_add_left_iff hp ratZero_mem_Rat hδQ).mpr hδ0
    rwa [ratAdd_zero hp] at this
  · rw [sq_shift hp hδQ]
    have hstep : ratLe (ratMul δ (ratAdd (ratAdd p p) δ))
        (ratMul (ratAdd (ratAdd p p) ratOne.{u}) δ) := by
      have hmono : ratLe (ratAdd (ratAdd p p) δ) (ratAdd (ratAdd p p) ratOne.{u}) :=
        (ratAdd_le_add_left_iff (ratAdd_mem_Rat hp hp) hδQ ratOne_mem_Rat).mpr hδ1
      have := ratMul_le_mul_right (ratAdd_mem_Rat (ratAdd_mem_Rat hp hp) hδQ) hc hδQ
        hmono hδ0.left
      rwa [ratMul_comm (ratAdd_mem_Rat (ratAdd_mem_Rat hp hp) hδQ) hδQ] at this
    have hlt : ratLt (ratMul δ (ratAdd (ratAdd p p) δ))
        (ratAdd t (ratNeg (ratMul p p))) :=
      ratLt_of_le_of_lt (ratMul_mem_Rat hδQ (ratAdd_mem_Rat (ratAdd_mem_Rat hp hp) hδQ))
        (ratMul_mem_Rat hc hδQ) hd hstep hδc
    have := (ratAdd_lt_add_left_iff hpp
      (ratMul_mem_Rat hδQ (ratAdd_mem_Rat (ratAdd_mem_Rat hp hp) hδQ)) hd).mpr hlt
    rwa [← ratAdd_assoc hpp ht (ratNeg_mem_Rat hpp), ratAdd_comm hpp ht,
      ratAdd_assoc ht hpp (ratNeg_mem_Rat hpp), ratAdd_neg hpp, ratAdd_zero ht] at this

/-- The mirror image, for the upper set: below a positive rational whose square
is above `s`, there is a smaller positive one still above `s`. -/
theorem exists_lt_sq_gt {r s : ZFSet.{u}} (hr : r ∈ NumberTheory.Rat.{u}) (hs : s ∈ NumberTheory.Rat.{u})
    (hr0 : ratLt ratZero.{u} r) (h : ratLt s (ratMul r r)) :
    ∃ r', r' ∈ NumberTheory.Rat.{u} ∧ ratLt ratZero.{u} r' ∧ ratLt r' r ∧ ratLt s (ratMul r' r') := by
  have hrr := ratMul_mem_Rat hr hr
  have hc := ratAdd_mem_Rat hr hr
  have hc0 : ratLe ratZero.{u} (ratAdd r r) := by
    have h₁ : ratLe (ratAdd ratZero.{u} r) (ratAdd r r) :=
      (ratAdd_le_add_right_iff hr ratZero_mem_Rat hr).mpr hr0.left
    rw [ratZero_add hr] at h₁
    exact ratLe_trans ratZero_mem_Rat hr (ratAdd_mem_Rat hr hr) hr0.left h₁
  have hd : ratAdd (ratMul r r) (ratNeg s) ∈ NumberTheory.Rat.{u} :=
    ratAdd_mem_Rat hrr (ratNeg_mem_Rat hs)
  have hd0 : ratLt ratZero.{u} (ratAdd (ratMul r r) (ratNeg s)) := by
    have := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat hs) hs hrr).mpr h
    rwa [ratAdd_neg hs] at this
  obtain ⟨δ₀, hδ₀Q, hδ₀0, hδ₀r, hδ₀c⟩ := exists_small_step hc hd hr hc0 hd0 hr0
  obtain ⟨δ, hδQ, hδ0, hδlt⟩ := rat_dense ratZero_mem_Rat hδ₀Q hδ₀0
  have hδr : ratLt δ r := ratLt_of_lt_of_le hδQ hδ₀Q hr hδlt hδ₀r
  have hδc : ratLt (ratMul (ratAdd r r) δ) (ratAdd (ratMul r r) (ratNeg s)) := by
    rcases ratLt_trichotomy ratZero_mem_Rat hc with hcpos | hceq | hcneg
    · refine ratLt_trans (ratMul_mem_Rat hc hδQ) (ratMul_mem_Rat hc hδ₀Q) hd ?_ hδ₀c
      have := ratMul_lt_mul_right hδQ hδ₀Q hc (ratNe_zero_of_pos hcpos)
        hcpos.left hδlt
      rwa [ratMul_comm hδQ hc, ratMul_comm hδ₀Q hc] at this
    · rw [← hceq, ratZero_mul hδQ]; exact hd0
    · exact absurd hc0 ((ratLt_iff_not_ratLe hc ratZero_mem_Rat).mp hcneg)
  have hnegδ := ratNeg_mem_Rat hδQ
  have hnegδ0 : ratLt (ratNeg δ) ratZero.{u} := by
    have := (ratNeg_lt_neg_iff hδQ ratZero_mem_Rat).mpr hδ0
    rwa [ratNeg_zero] at this
  refine ⟨ratAdd r (ratNeg δ), ratAdd_mem_Rat hr hnegδ, ?_, ?_, ?_⟩
  · have := (ratAdd_lt_add_right_iff hnegδ hδQ hr).mpr hδr
    rwa [ratAdd_neg hδQ] at this
  · have := (ratAdd_lt_add_left_iff hr hnegδ ratZero_mem_Rat).mpr hnegδ0
    rwa [ratAdd_zero hr] at this
  · rw [sq_shift hr hnegδ]
    -- `(-δ)·((r+r) + (-δ)) = -(δ·((r+r) + (-δ)))`, and that is above `-(δ·(r+r))`
    have hinner := ratAdd_mem_Rat hc hnegδ
    have hkey : ratMul (ratNeg δ) (ratAdd (ratAdd r r) (ratNeg δ))
        = ratNeg (ratMul δ (ratAdd (ratAdd r r) (ratNeg δ))) := by
      rw [ratMul_comm hnegδ hinner, ratMul_neg hinner hδQ,
          ratMul_comm hinner hδQ]
    rw [hkey]
    have hbound : ratLe (ratMul δ (ratAdd (ratAdd r r) (ratNeg δ)))
        (ratMul (ratAdd r r) δ) := by
      have hmono : ratLe (ratAdd (ratAdd r r) (ratNeg δ)) (ratAdd r r) := by
        have := (ratAdd_le_add_left_iff hc hnegδ ratZero_mem_Rat).mpr
          (by
            have := (ratNeg_le_neg_iff hδQ ratZero_mem_Rat).mpr hδ0.left
            rwa [ratNeg_zero] at this)
        rwa [ratAdd_zero hc] at this
      have := ratMul_le_mul_right hinner hc hδQ hmono hδ0.left
      rwa [ratMul_comm hinner hδQ] at this
    have hlt : ratLt (ratMul δ (ratAdd (ratAdd r r) (ratNeg δ)))
        (ratAdd (ratMul r r) (ratNeg s)) :=
      ratLt_of_le_of_lt (ratMul_mem_Rat hδQ hinner) (ratMul_mem_Rat hc hδQ) hd
        hbound hδc
    -- negate and add `r²` back, which is how `s` is freed on the left
    have hneg : ratLt (ratAdd (ratNeg (ratMul r r)) s)
        (ratNeg (ratMul δ (ratAdd (ratAdd r r) (ratNeg δ)))) := by
      have h := (ratNeg_lt_neg_iff hd (ratMul_mem_Rat hδQ hinner)).mpr hlt
      rwa [ratNeg_add hrr (ratNeg_mem_Rat hs), ratNeg_ratNeg hs] at h
    have := (ratAdd_lt_add_left_iff hrr
      (ratAdd_mem_Rat (ratNeg_mem_Rat hrr) hs)
      (ratNeg_mem_Rat (ratMul_mem_Rat hδQ hinner))).mpr hneg
    rwa [← ratAdd_assoc hrr (ratNeg_mem_Rat hrr) hs, ratAdd_neg hrr,
      ratZero_add hs] at this

/-! ## The root of a located pair

The lower set of the root is the rationals whose square is below `x` -- with
every negative rational thrown in, since a negative rational is below the root
of a non-negative real for no reason to do with its square. The upper set takes
the positive rationals whose square is above `x`. -/

def sqrtLower (L : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun p => ratLt p ratZero.{u} ∨ ratMul p p ∈ L) NumberTheory.Rat.{u}

def sqrtUpper (U : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun r => ratLt ratZero.{u} r ∧ ratMul r r ∈ U) NumberTheory.Rat.{u}

theorem mem_sqrtLower_iff (L p : ZFSet.{u}) :
    p ∈ sqrtLower L ↔ p ∈ NumberTheory.Rat.{u} ∧ (ratLt p ratZero.{u} ∨ ratMul p p ∈ L) :=
  mem_sep_iff _ _ _

theorem mem_sqrtUpper_iff (U r : ZFSet.{u}) :
    r ∈ sqrtUpper U ↔ r ∈ NumberTheory.Rat.{u} ∧ (ratLt ratZero.{u} r ∧ ratMul r r ∈ U) :=
  mem_sep_iff _ _ _

/-- Trichotomy, folded into the two cases the root's clauses actually split
on: a rational is either non-negative or strictly negative. -/
private theorem nonneg_or_neg {p : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) :
    ratLe ratZero.{u} p ∨ ratLt p ratZero.{u} := by
  rcases ratLt_trichotomy hp ratZero_mem_Rat with h | h | h
  · exact Or.inr h
  · exact Or.inl (by rw [h]; exact ratLe_refl ratZero_mem_Rat)
  · exact Or.inl h.left

/-- A non-negative member of the root's lower set is there because of its
square, the other disjunct being refuted by its sign. -/
private theorem sq_mem_of_nonneg {L q : ZFSet.{u}} (hq : q ∈ sqrtLower L)
    (hqQ : q ∈ NumberTheory.Rat.{u}) (h0 : ratLe ratZero.{u} q) : ratMul q q ∈ L := by
  rcases ((mem_sqrtLower_iff L q).mp hq).right with hneg | hsq
  · exact absurd h0 ((ratLt_iff_not_ratLe hqQ ratZero_mem_Rat).mp hneg)
  · exact hsq

/-- Everything above a non-negative real is a positive rational: zero itself
cannot be in the upper set, because the upper set is open. -/
theorem upper_pos_of_nonneg {L U : ZFSet.{u}} (h : IsLocated L U)
    (hnn : realLLe realLZero.{u} (opair L U)) : ∀ r, r ∈ U → ratLt ratZero.{u} r := by
  intro r hr
  have hrQ := h.upper_subset r hr
  have hneg : ∀ s, s ∈ U → ¬ ratLt s ratZero.{u} := by
    intro s hs hs0
    exact hnn ⟨s, by rw [snd_opair]; exact hs, by
      rw [realLZero, realLOf, fst_opair]
      exact (mem_ratCut_iff _ s).mpr ⟨h.upper_subset s hs, hs0⟩⟩
  rcases ratLt_trichotomy hrQ ratZero_mem_Rat with hlt | heq | hgt
  · exact absurd hlt (hneg r hr)
  · obtain ⟨r', hr', hlt⟩ := h.upper_open r hr
    exact absurd (heq ▸ hlt) (hneg r' hr')
  · exact hgt

/-- The root of a non-negative located real is a located pair, and no clause
of it decides anything about the real: each is trichotomy on ℚ, or the
continuity of squaring in the two openness clauses. -/
theorem isLocated_sqrt {L U : ZFSet.{u}} (h : IsLocated L U)
    (hpos : ∀ r, r ∈ U → ratLt ratZero.{u} r) :
    IsLocated (sqrtLower L) (sqrtUpper U) where
  lower_subset p hp := ((mem_sqrtLower_iff L p).mp hp).left
  upper_subset r hr := ((mem_sqrtUpper_iff U r).mp hr).left
  lower_inhabited := by
    obtain ⟨t, htQ, hlt⟩ := rat_no_least ratZero_mem_Rat
    exact ⟨t, (mem_sqrtLower_iff L t).mpr ⟨htQ, Or.inl hlt⟩⟩
  upper_inhabited := by
    obtain ⟨r₀, hr₀⟩ := h.upper_inhabited
    have hr₀Q := h.upper_subset r₀ hr₀
    have hr₀0 := hpos r₀ hr₀
    have hsQ := ratAdd_mem_Rat hr₀Q ratOne_mem_Rat
    have hs1 : ratLt ratOne.{u} (ratAdd r₀ ratOne.{u}) := by
      have := (ratAdd_lt_add_right_iff ratOne_mem_Rat ratZero_mem_Rat hr₀Q).mpr hr₀0
      rwa [ratZero_add ratOne_mem_Rat] at this
    have hs0 : ratLt ratZero.{u} (ratAdd r₀ ratOne.{u}) :=
      ratLt_trans ratZero_mem_Rat ratOne_mem_Rat hsQ ratZero_lt_one hs1
    have hgrow : ratLt (ratAdd r₀ ratOne.{u})
        (ratMul (ratAdd r₀ ratOne.{u}) (ratAdd r₀ ratOne.{u})) := by
      have := ratMul_lt_mul_right ratOne_mem_Rat hsQ hsQ
        (ratNe_zero_of_pos hs0) hs0.left hs1
      rwa [ratOne_mul hsQ] at this
    refine ⟨ratAdd r₀ ratOne.{u}, (mem_sqrtUpper_iff U _).mpr ⟨hsQ, hs0, ?_⟩⟩
    refine h.upper_up r₀ hr₀ _ (ratMul_mem_Rat hsQ hsQ) ?_
    exact ratLt_trans hr₀Q hsQ (ratMul_mem_Rat hsQ hsQ)
      (by
        have := (ratAdd_lt_add_left_iff hr₀Q ratZero_mem_Rat ratOne_mem_Rat).mpr
          ratZero_lt_one
        rwa [ratAdd_zero hr₀Q] at this)
      hgrow
  ordered p hp r hr := by
    obtain ⟨hpQ, -⟩ := (mem_sqrtLower_iff L p).mp hp
    obtain ⟨hrQ, hr0, hrU⟩ := (mem_sqrtUpper_iff U r).mp hr
    rcases nonneg_or_neg hpQ with h0 | hneg
    · exact ratLt_of_sq_lt_sq hpQ hrQ hr0.left
        (h.ordered _ (sq_mem_of_nonneg hp hpQ h0) _ hrU)
    · exact ratLt_trans hpQ ratZero_mem_Rat hrQ hneg hr0
  lower_down q hq p hpQ hlt := by
    rcases nonneg_or_neg hpQ with h0 | hneg
    · have hqQ := ((mem_sqrtLower_iff L q).mp hq).left
      have hq0 : ratLe ratZero.{u} q :=
        ratLe_trans ratZero_mem_Rat hpQ hqQ h0 hlt.left
      exact (mem_sqrtLower_iff L p).mpr ⟨hpQ, Or.inr
        (h.lower_down _ (sq_mem_of_nonneg hq hqQ hq0) _ (ratMul_mem_Rat hpQ hpQ)
          (ratSq_lt_sq hpQ hqQ h0 hlt))⟩
    · exact (mem_sqrtLower_iff L p).mpr ⟨hpQ, Or.inl hneg⟩
  upper_up r hr p hpQ hlt := by
    obtain ⟨hrQ, hr0, hrU⟩ := (mem_sqrtUpper_iff U r).mp hr
    refine (mem_sqrtUpper_iff U p).mpr ⟨hpQ, ratLt_trans ratZero_mem_Rat hrQ hpQ hr0 hlt, ?_⟩
    exact h.upper_up _ hrU _ (ratMul_mem_Rat hpQ hpQ)
      (ratSq_lt_sq hrQ hpQ hr0.left hlt)
  lower_open p hp := by
    have hpQ := ((mem_sqrtLower_iff L p).mp hp).left
    rcases nonneg_or_neg hpQ with h0 | hneg
    · obtain ⟨t, htL, hlt⟩ := h.lower_open _ (sq_mem_of_nonneg hp hpQ h0)
      obtain ⟨p', hp'Q, hpp', hsq⟩ :=
        exists_gt_sq_lt hpQ (h.lower_subset t htL) h0 hlt
      exact ⟨p', (mem_sqrtLower_iff L p').mpr ⟨hp'Q, Or.inr
        (h.lower_down _ htL _ (ratMul_mem_Rat hp'Q hp'Q) hsq)⟩, hpp'⟩
    · obtain ⟨t, htQ, h₁, h₂⟩ := rat_dense hpQ ratZero_mem_Rat hneg
      exact ⟨t, (mem_sqrtLower_iff L t).mpr ⟨htQ, Or.inl h₂⟩, h₁⟩
  upper_open r hr := by
    obtain ⟨hrQ, hr0, hrU⟩ := (mem_sqrtUpper_iff U r).mp hr
    obtain ⟨s, hsU, hlt⟩ := h.upper_open _ hrU
    obtain ⟨r', hr'Q, hr'0, hr'r, hsq⟩ :=
      exists_lt_sq_gt hrQ (h.upper_subset s hsU) hr0 hlt
    exact ⟨r', (mem_sqrtUpper_iff U r').mpr ⟨hr'Q, hr'0,
      h.upper_up _ hsU _ (ratMul_mem_Rat hr'Q hr'Q) hsq⟩, hr'r⟩
  located p hpQ q hqQ hlt := by
    rcases nonneg_or_neg hpQ with h0 | hneg
    · have hq0 : ratLt ratZero.{u} q :=
        ratLt_of_le_of_lt ratZero_mem_Rat hpQ hqQ h0 hlt
      rcases h.located _ (ratMul_mem_Rat hpQ hpQ) _ (ratMul_mem_Rat hqQ hqQ)
        (ratSq_lt_sq hpQ hqQ h0 hlt) with hL | hU
      · exact Or.inl ((mem_sqrtLower_iff L p).mpr ⟨hpQ, Or.inr hL⟩)
      · exact Or.inr ((mem_sqrtUpper_iff U q).mpr ⟨hqQ, hq0, hU⟩)
    · exact Or.inl ((mem_sqrtLower_iff L p).mpr ⟨hpQ, Or.inl hneg⟩)

/-- The square root of a located real. -/
def realLSqrt (z : ZFSet.{u}) : ZFSet.{u} :=
  opair (sqrtLower (fst z)) (sqrtUpper (snd z))

theorem realLSqrt_mem {z : ZFSet.{u}} (hz : z ∈ RealL.{u})
    (hnn : realLLe realLZero.{u} z) : realLSqrt z ∈ RealL.{u} := by
  obtain ⟨L, U, rfl, hloc⟩ := (mem_RealL_iff z).mp hz
  refine (mem_RealL_iff _).mpr ⟨sqrtLower L, sqrtUpper U, ?_, ?_⟩
  · rw [realLSqrt, fst_opair, snd_opair]
  · exact isLocated_sqrt hloc (upper_pos_of_nonneg hloc hnn)

/-! ## The root squared

Neither direction unfolds the four-corner product. A strict inequality between
`√x · √x` and `x` would put one rational in both `L` and `U`, and the corner
that does it is picked by the total order on the two bracket endpoints. -/

private theorem not_lt_sq {L U : ZFSet.{u}} (h : IsLocated L U)
    (hpos : ∀ r, r ∈ U → ratLt ratZero.{u} r) :
    ¬ realLLt (opair L U)
        (realLMul (realLSqrt (opair L U)) (realLSqrt (opair L U))) := by
  rintro ⟨p, hpU, hpM⟩
  rw [snd_opair] at hpU
  rw [realLMul, fst_opair, realLSqrt, fst_opair, snd_opair, fst_opair, snd_opair] at hpM
  obtain ⟨hpQ, q, hq, q', hq', r, hr, r', hr', c₁, c₂, c₃, c₄⟩ :=
    (mem_mulLower_iff _ _ _ _ p).mp hpM
  have hqQ := ((mem_sqrtLower_iff L q).mp hq).left
  have hrQ := ((mem_sqrtLower_iff L r).mp hr).left
  obtain ⟨hq'Q, hq'0, -⟩ := (mem_sqrtUpper_iff U q').mp hq'
  obtain ⟨hr'Q, hr'0, -⟩ := (mem_sqrtUpper_iff U r').mp hr'
  have hp0 : ratLt ratZero.{u} p := hpos p hpU
  -- a rational in `L` above `p` contradicts `p ∈ U`
  have finish : ∀ c, c ∈ NumberTheory.Rat.{u} → ratLt p c → c ∈ L → False := fun c hcQ hpc hcL =>
    ratLt_irrefl (h.ordered p (h.lower_down c hcL p hpQ hpc) p hpU)
  -- a non-positive left endpoint makes a corner non-positive, and `p` is above it
  have hq0 : ratLe ratZero.{u} q := by
    rcases ratLe_total ratZero_mem_Rat hqQ with h0 | h0
    · exact h0
    · exfalso
      have hle : ratLe (ratMul q r') ratZero.{u} := by
        have := ratMul_le_mul_right hqQ ratZero_mem_Rat hr'Q h0 hr'0.left
        rwa [ratZero_mul hr'Q] at this
      exact ratLt_irrefl (ratLt_trans hpQ (ratMul_mem_Rat hqQ hr'Q) hpQ c₂
        (ratLt_of_le_of_lt (ratMul_mem_Rat hqQ hr'Q) ratZero_mem_Rat hpQ hle hp0))
  have hr0 : ratLe ratZero.{u} r := by
    rcases ratLe_total ratZero_mem_Rat hrQ with h0 | h0
    · exact h0
    · exfalso
      have hle : ratLe (ratMul q' r) ratZero.{u} := by
        have h₁ := ratMul_le_mul_right hrQ ratZero_mem_Rat hq'Q h0 hq'0.left
        rw [ratZero_mul hq'Q] at h₁
        rwa [ratMul_comm hq'Q hrQ]
      exact ratLt_irrefl (ratLt_trans hpQ (ratMul_mem_Rat hq'Q hrQ) hpQ c₃
        (ratLt_of_le_of_lt (ratMul_mem_Rat hq'Q hrQ) ratZero_mem_Rat hpQ hle hp0))
  have hqL := sq_mem_of_nonneg hq hqQ hq0
  have hrL := sq_mem_of_nonneg hr hrQ hr0
  have hqr := ratMul_mem_Rat hqQ hrQ
  rcases ratLe_total hqQ hrQ with hle | hle
  · exact finish (ratMul r r) (ratMul_mem_Rat hrQ hrQ)
      (ratLt_of_lt_of_le hpQ hqr (ratMul_mem_Rat hrQ hrQ) c₁
        (ratMul_le_mul_right hqQ hrQ hrQ hle hr0)) hrL
  · refine finish (ratMul q q) (ratMul_mem_Rat hqQ hqQ)
      (ratLt_of_lt_of_le hpQ hqr (ratMul_mem_Rat hqQ hqQ) c₁ ?_) hqL
    have := ratMul_le_mul_right hrQ hqQ hqQ hle hq0
    rwa [ratMul_comm hrQ hqQ] at this

end Geometry

#print axioms Geometry.isLocated_sqrt
#print axioms Geometry.realLSqrt_mem
#print axioms Geometry.exists_gt_sq_lt
#print axioms Geometry.exists_lt_sq_gt

namespace ZFSet
export Geometry (exists_gt_sq_lt exists_lt_sq_gt exists_small_step isLocated_sqrt mem_sqrtLower_iff mem_sqrtUpper_iff ratLt_of_sq_lt_sq ratSq_le_sq ratSq_lt_sq realLSqrt realLSqrt_mem sq_shift sqrtLower sqrtUpper upper_pos_of_nonneg)
end ZFSet
