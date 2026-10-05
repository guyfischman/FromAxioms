/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
Bridge, rung 4: `Real` to Lean's `ℝ`.

    1  omega  -> Nat      Comparator/Bridge/NatTransfer.lean
    2  Int    -> ℤ        Comparator/Bridge/IntTransfer.lean
    3  Rat    -> ℚ        Comparator/Bridge/RatTransfer.lean
    4  Real   -> ℝ        this file

`Analysis.toCut` with `toCut_add`, `toCut_mul`, `toCut_le` and
`toCut_injective` takes `RealL → Real` internally, so the comparator never sees
a located pair. What is left is `Real → ℝ`, and a Dedekind cut becomes a Lean
real by taking a supremum: no Cauchy sequence, no `invScale`, no completion.

So the floor is that the supremum exists, which is `IsCut.nonempty` and
`IsCut.proper` read through rung 3. Making `proper`'s outside rational into an
upper bound in `ℚ` is exactly `toRat_le`, so that lemma is the last rung below
this file.

This file carries both directions and the full ring structure:

    ofRL / ofRL_mem            R -> RealL, landing in the carrier
    toRL / toRL_ofRL           RealL -> R, and the round trip
    toRL_add, toRL_mul,        the ring laws
      toRL_neg, toRL_zero,
      toRL_one, toRL_realLPow
    toRL_le_iff, toRL_lt_iff,  the order, as an iff
      toRL_injective
    toRL_realLInv              and the inverse
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- `bernsteinPolynomial`, for `toRL_bernTerm` at the end of this file.
import Mathlib.RingTheory.Polynomial.Bernstein
import Comparator.Bridge.RatTransfer
import FromAxioms.Analysis.Real

namespace Comparator

open SetTheory

/-- The rationals of a cut, as a set of Lean reals. -/
def cutReals (c : ZFSet) : Set ℝ :=
  {x : ℝ | ∃ (q : ZFSet) (hq : q ∈ NumberTheory.Rat), q ∈ c ∧ x = (toRat q hq : ℝ)}

/-- A cut is nonempty below, which is `IsCut.nonempty` plus the fact that
its members are rationals. -/
theorem cutReals_nonempty {c : ZFSet} (h : Analysis.IsCut c) :
    (cutReals c).Nonempty := by
  obtain ⟨q, hq⟩ := h.nonempty
  exact ⟨(toRat q (h.subset _ hq) : ℝ), q, h.subset _ hq, hq, rfl⟩

/-- And it is bounded above, which is the whole floor of this rung.

`IsCut.proper` supplies a rational outside the cut. That it is an upper bound is
`IsCut.down` read contrapositively --- a rational strictly above a member would
be dragged in --- and turning not above into `≤` is `ratLe_of_not_lt`. The step
from the tower's `ratLe` to `≤` on `ℚ`, and hence on `ℝ`, is `toRat_le`. -/
theorem cutReals_bddAbove {c : ZFSet} (h : Analysis.IsCut c) :
    BddAbove (cutReals c) := by
  obtain ⟨r, hrQ, hrc⟩ := h.proper
  refine ⟨(toRat r hrQ : ℝ), ?_⟩
  rintro x ⟨q, hqQ, hqc, rfl⟩
  have hnlt : ¬ NumberTheory.ratLt r q := fun hlt => hrc (h.down q hqc r hrQ hlt)
  have hle : NumberTheory.ratLe q r := NumberTheory.ratLe_of_not_lt hqQ hrQ hnlt
  exact_mod_cast toRat_le hqQ hrQ hle

/-- A cut as a Lean real. -/
noncomputable def toR (c : ZFSet) : ℝ := sSup (cutReals c)

/-- The map is monotone, and on cuts the tower's order is `⊆`
(`Real.lean`'s `cutLe`), so this is the order half of the embedding. -/
theorem toR_mono {c d : ZFSet} (hc : Analysis.IsCut c) (hd : Analysis.IsCut d)
    (hsub : c ⊆ d) : toR c ≤ toR d :=
  csSup_le_csSup (cutReals_bddAbove hd) (cutReals_nonempty hc)
    (fun _ ⟨q, hqQ, hqc, hx⟩ => ⟨q, hqQ, hsub _ hqc, hx⟩)

/-- Every rational of the cut is below its real, the lower half of the
characterisation a caller needs. -/
theorem le_toR {c q : ZFSet} (h : Analysis.IsCut c) (hq : q ∈ c) :
    (toRat q (h.subset _ hq) : ℝ) ≤ toR c :=
  le_csSup (cutReals_bddAbove h) ⟨q, h.subset _ hq, hq, rfl⟩

/-- A rational outside the cut bounds the cut's real. The same argument that
made `cutReals_bddAbove` work, kept as a lemma because the order-reflection
below needs it at an arbitrary rational rather than at `proper`'s witness. -/
theorem toR_le_of_not_mem {c q : ZFSet} (h : Analysis.IsCut c)
    (hqQ : q ∈ NumberTheory.Rat) (hqc : q ∉ c) : toR c ≤ (toRat q hqQ : ℝ) := by
  refine csSup_le (cutReals_nonempty h) ?_
  rintro x ⟨p, hpQ, hpc, rfl⟩
  have hnlt : ¬ NumberTheory.ratLt q p := fun hlt => hqc (h.down p hpc q hqQ hlt)
  exact_mod_cast toRat_le hpQ hqQ (NumberTheory.ratLe_of_not_lt hpQ hqQ hnlt)

/-- A rational strictly below the cut's real is in the cut --- the previous
lemma contrapositively, and the step that turns `toR` from monotone into an
order embedding. -/
theorem mem_of_lt_toR {c q : ZFSet} (h : Analysis.IsCut c)
    (hqQ : q ∈ NumberTheory.Rat) (hlt : (toRat q hqQ : ℝ) < toR c) : q ∈ c := by
  by_contra hqc
  exact absurd (toR_le_of_not_mem h hqQ hqc) (not_le.mpr hlt)

/-- `toR` reflects the order, so together with `toR_mono` it is an embedding
of the tower's cuts into `ℝ`.

`IsCut.no_greatest` does the work, and needs `toRat_lt`: a member `q` of `c` is
strictly below some other member `p`, so `toRat q < toRat p ≤ toR c ≤ toR d`,
and `mem_of_lt_toR` puts `q` in `d`. With a non-strict bound the chain would
give `≤` and place nothing. -/
theorem subset_of_toR_le {c d : ZFSet} (hc : Analysis.IsCut c)
    (hd : Analysis.IsCut d) (hle : toR c ≤ toR d) : c ⊆ d := by
  intro q hq
  obtain ⟨p, hpc, hqp⟩ := hc.no_greatest q hq
  have hstrict : (toRat q (hc.subset _ hq) : ℝ) < (toRat p (hc.subset _ hpc) : ℝ) := by
    exact_mod_cast toRat_lt (hc.subset _ hq) (hc.subset _ hpc) hqp
  exact mem_of_lt_toR hd (hc.subset _ hq)
    (lt_of_lt_of_le hstrict (le_trans (le_toR hc hpc) hle))

/-- And the embedding is injective, by antisymmetry of `⊆` on cuts. -/
theorem toR_injective {c d : ZFSet} (hc : Analysis.IsCut c) (hd : Analysis.IsCut d)
    (h : toR c = toR d) : c = d :=
  SetTheory.ext _ _ fun _ =>
    ⟨fun hq => subset_of_toR_le hc hd h.le _ hq,
     fun hq => subset_of_toR_le hd hc h.ge _ hq⟩

/-! ### The other direction

`toR` alone is not enough for a comparator pair: a challenge quantifies over
`x : ℝ`, so the Solution has to produce a cut for an arbitrary Lean real. -/

/-- A Lean real as a cut: the tower rationals strictly below it.

Pinned to `ZFSet.{0}`. `ratOfLean` is level-0 (it is built from
`intOfLean.{0}`), while `toR` and `cutReals` above are universe-polymorphic, so
this is pinned with it. -/
noncomputable def ofR (x : ℝ) : ZFSet.{0} :=
  SetTheory.sep
    (fun q => ∃ hq : q ∈ NumberTheory.Rat.{0}, (toRat q hq : ℝ) < x)
    NumberTheory.Rat.{0}

theorem mem_ofR_iff (x : ℝ) (q : ZFSet.{0}) :
    q ∈ ofR x ↔ q ∈ NumberTheory.Rat.{0}
      ∧ ∃ hq : q ∈ NumberTheory.Rat.{0}, (toRat q hq : ℝ) < x :=
  SetTheory.mem_sep_iff _ _ _

/-- And it is a cut.

Each field is a fact about `ℝ` transported through rung 3. `nonempty` and
`proper` are `exists_rat_lt` and `exists_rat_gt`, which need `ratOfLean` to
name a tower rational --- which the round trip supplies. `down` is `toRat_lt`
plus transitivity, and `no_greatest` is the density of `ℚ` in `ℝ`. -/
theorem isCut_ofR (x : ℝ) : Analysis.IsCut (ofR x) := by
  refine ⟨fun q hq => ((mem_ofR_iff x q).mp hq).left, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := exists_rat_lt x
    refine ⟨ratOfLean p, (mem_ofR_iff x _).mpr ⟨ratOfLean_mem p, ratOfLean_mem p, ?_⟩⟩
    rw [toRat_ratOfLean]; exact hp
  · obtain ⟨p, hp⟩ := exists_rat_gt x
    refine ⟨ratOfLean p, ratOfLean_mem p, fun hmem => ?_⟩
    obtain ⟨-, hq, hlt⟩ := (mem_ofR_iff x _).mp hmem
    rw [show toRat (ratOfLean p) hq = p from toRat_ratOfLean p] at hlt
    exact absurd hlt (not_lt.mpr hp.le)
  · intro q hq p hpQ hlt
    obtain ⟨-, hqQ, hqx⟩ := (mem_ofR_iff x q).mp hq
    refine (mem_ofR_iff x p).mpr ⟨hpQ, hpQ, ?_⟩
    refine lt_trans ?_ hqx
    exact_mod_cast toRat_lt hpQ hqQ hlt
  · intro q hq
    obtain ⟨-, hqQ, hqx⟩ := (mem_ofR_iff x q).mp hq
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hqx
    refine ⟨ratOfLean p, (mem_ofR_iff x _).mpr ⟨ratOfLean_mem p, ratOfLean_mem p, ?_⟩, ?_⟩
    · rw [toRat_ratOfLean]; exact hp2
    · -- back across rung 3: the strict inequality in `ℚ` is the tower's `ratLt`
      by_contra hnlt
      have hle := NumberTheory.ratLe_of_not_lt (ratOfLean_mem p) hqQ hnlt
      have : (p : ℝ) ≤ (toRat q hqQ : ℝ) := by
        have := toRat_le (ratOfLean_mem p) hqQ hle
        rw [toRat_ratOfLean] at this
        exact_mod_cast this
      exact absurd hp1 (not_lt.mpr this)

/-- The round trip at rung 4: the cut of a real has that real as its
supremum. With `isCut_ofR` this makes `toR` surjective onto `ℝ`, so a challenge
quantifying over Lean reals can be answered with a tower cut. -/
theorem toR_ofR (x : ℝ) : toR (ofR x) = x := by
  refine le_antisymm (csSup_le (cutReals_nonempty (isCut_ofR x)) ?_) ?_
  · rintro y ⟨q, hqQ, hqc, rfl⟩
    obtain ⟨-, hq, hlt⟩ := (mem_ofR_iff x q).mp hqc
    exact le_of_lt hlt
  · refine le_of_forall_lt_imp_le_of_dense fun y hy => ?_
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hy
    have hmem : ratOfLean p ∈ ofR x :=
      (mem_ofR_iff x _).mpr ⟨ratOfLean_mem p, ratOfLean_mem p,
        by rw [toRat_ratOfLean]; exact hp2⟩
    refine le_trans (le_of_lt hp1) ?_
    have := le_toR (isCut_ofR x) hmem
    rw [show toRat (ratOfLean p) ((isCut_ofR x).subset _ hmem) = p from
      toRat_ratOfLean p] at this
    exact this

/-! ### Arithmetic

The order half above is enough for density; a row stating anything about `+`
across the bridge needs this. -/

/-- `toR` carries the tower's cut addition to `+` on `ℝ`.

`Analysis.realAdd` is the sumset --- the rationals of the form `q + r` with
`q` in one cut and `r` in the other --- so this is the statement that the
supremum of a sumset is the sum of the suprema, and each direction is a separate
argument.

`≤` is termwise: every member of the sumset is `toRat q + toRat r`, bounded by
`toR x + toR y` through `le_toR` twice, and `toRat_add` is what turns the tower's
`ratAdd` into `+` before the bound can be applied.

For `≥`, a real strictly below `toR x + toR y` is `u + v` for rationals
`u < toR x` and `v < toR y` --- obtained by pushing the slack into two halves
with `exists_rat_btwn` --- and `mem_of_lt_toR` puts each in its cut, so their
sum is in the sumset. Neither direction is the other. -/
theorem toR_realAdd {x y : ZFSet.{0}} (hx : Analysis.IsCut x) (hy : Analysis.IsCut y) :
    toR (Analysis.realAdd x y) = toR x + toR y := by
  have hxy : Analysis.IsCut (Analysis.realAdd x y) :=
    (Analysis.mem_Real_iff _).mp
      (Analysis.realAdd_mem_Real ((Analysis.mem_Real_iff x).mpr hx)
        ((Analysis.mem_Real_iff y).mpr hy))
  refine le_antisymm (csSup_le (cutReals_nonempty hxy) ?_) ?_
  · rintro z ⟨p, hpQ, hp, rfl⟩
    obtain ⟨-, q, hq, r, hr, rfl⟩ := (Analysis.mem_realAdd_iff x y p).mp hp
    have hqQ := hx.subset _ hq
    have hrQ := hy.subset _ hr
    rw [show toRat (NumberTheory.ratAdd q r) hpQ
        = toRat q hqQ + toRat r hrQ from toRat_add hqQ hrQ hpQ]
    push_cast
    exact add_le_add (le_toR hx hq) (le_toR hy hr)
  · refine le_of_forall_lt_imp_le_of_dense fun w hw => ?_
    -- split the slack: `w - toR y < toR x`, so a rational sits between.
    obtain ⟨u, hu1, hu2⟩ := exists_rat_btwn (show w - toR y < toR x by linarith)
    obtain ⟨v, hv1, hv2⟩ := exists_rat_btwn (show w - (u : ℝ) < toR y by linarith)
    have humem : ratOfLean u ∈ x :=
      mem_of_lt_toR hx (ratOfLean_mem u) (by rw [toRat_ratOfLean]; exact hu2)
    have hvmem : ratOfLean v ∈ y :=
      mem_of_lt_toR hy (ratOfLean_mem v) (by rw [toRat_ratOfLean]; exact hv2)
    have hsum : NumberTheory.ratAdd (ratOfLean u) (ratOfLean v)
        ∈ Analysis.realAdd x y :=
      (Analysis.mem_realAdd_iff x y _).mpr
        ⟨NumberTheory.ratAdd_mem_Rat (ratOfLean_mem u) (ratOfLean_mem v),
         ratOfLean u, humem, ratOfLean v, hvmem, rfl⟩
    have hle := le_toR hxy hsum
    rw [show toRat (NumberTheory.ratAdd (ratOfLean u) (ratOfLean v))
          (hxy.subset _ hsum)
        = toRat (ratOfLean u) (ratOfLean_mem u) + toRat (ratOfLean v) (ratOfLean_mem v)
        from toRat_add _ _ _, toRat_ratOfLean, toRat_ratOfLean] at hle
    push_cast at hle
    linarith

/-! ### The rational embedding, needed before multiplication

`Analysis.realLOf` puts a tower rational into `RealL` as `(ratCut q, …)`. The
cut-level half is stated here rather than with its `RealL` companion below,
because the non-negativity fact multiplication opens with is `toR_mono` against
this at zero. -/

/-- The cut of a rational has that rational as its supremum.

`≤` is `toRat_lt` at each member; `≥` is density, and the rational produced by
`exists_rat_btwn` has to be pushed back through `ratOfLean` to be a member. -/
theorem toR_ratCut {q : ZFSet.{0}} (hq : q ∈ NumberTheory.Rat.{0}) :
    toR (Analysis.ratCut q) = (toRat q hq : ℝ) := by
  have hc : Analysis.IsCut (Analysis.ratCut q) :=
    Analysis.isCut_lower (Analysis.isLocated_ratCut hq)
  refine le_antisymm (csSup_le (cutReals_nonempty hc) ?_) ?_
  · rintro y ⟨p, hpQ, hp, rfl⟩
    have hlt := ((Analysis.mem_ratCut_iff q p).mp hp).right
    exact_mod_cast le_of_lt (toRat_lt hpQ hq hlt)
  · refine le_of_forall_lt_imp_le_of_dense fun w hw => ?_
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hw
    have hmem : ratOfLean p ∈ Analysis.ratCut q :=
      (Analysis.mem_ratCut_iff q _).mpr ⟨ratOfLean_mem p, by
        refine ratOfLean_toRat hq ▸ ratOfLean_lt ?_
        exact_mod_cast hp2⟩
    have hle := le_toR hc hmem
    rw [show toRat (ratOfLean p) (hc.subset _ hmem) = p from toRat_ratOfLean p] at hle
    exact le_trans (le_of_lt hp1) hle

/-! ### Multiplication

The sumset argument does not transfer. `Analysis.realMulNonneg` is not the
productset: it is the rationals below a product of non-negative members, together
with every negative rational. Both features are forced --- without the sign
restriction the productset is unbounded above (two large negatives multiply up),
and without the negative rationals the set would not be downward closed. So the
proof splits where the definition splits. -/

/-- A non-negative cut has a non-negative real, which the product needs at
both ends. `realNonneg` is `realZero ⊆ x`, so this is `toR_mono` against
`toR_ratCut` at zero. -/
theorem toR_nonneg {x : ZFSet.{0}} (hx : Analysis.IsCut x)
    (hx0 : Analysis.realNonneg x) : 0 ≤ toR x := by
  have hz : Analysis.IsCut (Analysis.ratCut NumberTheory.ratZero.{0}) :=
    Analysis.isCut_lower (Analysis.isLocated_ratCut NumberTheory.ratZero_mem_Rat)
  have := toR_mono hz hx hx0
  rwa [toR_ratCut NumberTheory.ratZero_mem_Rat, toRat_zero, Rat.cast_zero] at this

/-- The product crosses, for non-negative cuts.

`≤` splits on the definition's own disjunction: a negative rational is below the
product because both factors are non-negative, and a rational below `q * r` is
below `toR x * toR y` by monotonicity of `*` on non-negatives, with `toRat_mul`
turning the tower's `ratMul` into `*`.

`≥` splits on the sign of the target. Below zero, the negative disjunct alone
supplies a member. At or above zero, both factors must be strictly positive
(otherwise the product is `0`), and then `w / toR y < toR x` picks a rational `q`
in `x`, and `w / q < toR y` picks `r` in `y`, with `q * r > w` by construction. -/
theorem toR_realMulNonneg {x y : ZFSet.{0}} (hx : Analysis.IsCut x)
    (hy : Analysis.IsCut y) (hx0 : Analysis.realNonneg x)
    (hy0 : Analysis.realNonneg y) :
    toR (Analysis.realMulNonneg x y) = toR x * toR y := by
  have hxn := toR_nonneg hx hx0
  have hyn := toR_nonneg hy hy0
  have hxy : Analysis.IsCut (Analysis.realMulNonneg x y) :=
    (Analysis.mem_Real_iff _).mp
      (Analysis.realMulNonneg_mem_Real ((Analysis.mem_Real_iff x).mpr hx)
        ((Analysis.mem_Real_iff y).mpr hy) hx0 hy0)
  refine le_antisymm (csSup_le (cutReals_nonempty hxy) ?_) ?_
  · rintro z ⟨p, hpQ, hp, rfl⟩
    obtain ⟨-, hcase⟩ := (Analysis.mem_realMulNonneg_iff x y p).mp hp
    rcases hcase with hneg | ⟨q, hq, r, hr, hq0, hr0, hlt⟩
    · have : (toRat p hpQ : ℝ) < 0 := by
        have := toRat_lt hpQ NumberTheory.ratZero_mem_Rat hneg
        rw [toRat_zero] at this
        exact_mod_cast this
      -- the product of two non-negatives is non-negative
      nlinarith [mul_nonneg hxn hyn]
    · have hqQ := hx.subset _ hq
      have hrQ := hy.subset _ hr
      have hq0' : (0 : ℚ) ≤ toRat q hqQ := by
        have := toRat_le NumberTheory.ratZero_mem_Rat hqQ hq0
        rwa [toRat_zero] at this
      have hr0' : (0 : ℚ) ≤ toRat r hrQ := by
        have := toRat_le NumberTheory.ratZero_mem_Rat hrQ hr0
        rwa [toRat_zero] at this
      have hprod : (toRat p hpQ : ℝ) < (toRat q hqQ : ℝ) * (toRat r hrQ : ℝ) := by
        have := toRat_lt hpQ (NumberTheory.ratMul_mem_Rat hqQ hrQ) hlt
        rw [toRat_mul hqQ hrQ] at this
        exact_mod_cast this
      have hqle := le_toR hx hq
      have hrle := le_toR hy hr
      -- the monotone step is `mul_le_mul`
      have hstep : (toRat q hqQ : ℝ) * (toRat r hrQ : ℝ) ≤ toR x * toR y :=
        mul_le_mul hqle hrle (by exact_mod_cast hr0') hxn
      linarith
  · refine le_of_forall_lt_imp_le_of_dense fun w hw => ?_
    rcases lt_or_ge w 0 with hwneg | hwpos
    · -- a negative rational is already a member
      obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hwneg
      have hmem : ratOfLean p ∈ Analysis.realMulNonneg x y :=
        (Analysis.mem_realMulNonneg_iff x y _).mpr ⟨ratOfLean_mem p, Or.inl (by
          refine ratOfLean_zero ▸ ratOfLean_lt ?_
          exact_mod_cast hp2)⟩
      have hle := le_toR hxy hmem
      rw [show toRat (ratOfLean p) (hxy.subset _ hmem) = p from toRat_ratOfLean p] at hle
      exact le_trans (le_of_lt hp1) hle
    · -- both factors are strictly positive, or the product could not exceed `w`
      -- a zero factor would make the product `0`, which `w ≥ 0` already exceeds
      have hxpos : 0 < toR x := by
        rcases hxn.lt_or_eq with h | h
        · exact h
        · exfalso; rw [← h, zero_mul] at hw; linarith
      have hypos : 0 < toR y := by
        rcases hyn.lt_or_eq with h | h
        · exact h
        · exfalso; rw [← h, mul_zero] at hw; linarith
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show w / toR y < toR x by
        rw [div_lt_iff₀ hypos]; exact hw)
      have hqpos : (0 : ℝ) < (q : ℝ) :=
        lt_of_le_of_lt (div_nonneg hwpos (le_of_lt hypos)) hq1
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show w / (q : ℝ) < toR y by
        rw [div_lt_iff₀ hqpos, mul_comm]
        exact (div_lt_iff₀ hypos).mp hq1)
      have hrpos : (0 : ℝ) < (r : ℝ) :=
        lt_of_le_of_lt (div_nonneg hwpos (le_of_lt hqpos)) hr1
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := le_of_lt hqpos
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := le_of_lt hrpos
      have hqmem : ratOfLean q ∈ x :=
        mem_of_lt_toR hx (ratOfLean_mem q) (by rw [toRat_ratOfLean]; exact hq2)
      have hrmem : ratOfLean r ∈ y :=
        mem_of_lt_toR hy (ratOfLean_mem r) (by rw [toRat_ratOfLean]; exact hr2)
      have hwqr : w < (q : ℝ) * (r : ℝ) := by
        rw [mul_comm]
        exact (div_lt_iff₀ hqpos).mp hr1
      obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hwqr
      have hmem : ratOfLean p ∈ Analysis.realMulNonneg x y :=
        (Analysis.mem_realMulNonneg_iff x y _).mpr ⟨ratOfLean_mem p, Or.inr
          ⟨ratOfLean q, hqmem, ratOfLean r, hrmem,
           ratOfLean_zero ▸ ratOfLean_le (by exact_mod_cast hq0),
           ratOfLean_zero ▸ ratOfLean_le (by exact_mod_cast hr0),
           by rw [ratOfLean_mul]; exact ratOfLean_lt (by exact_mod_cast hp2)⟩⟩
      have hle := le_toR hxy hmem
      rw [show toRat (ratOfLean p) (hxy.subset _ hmem) = p from toRat_ratOfLean p] at hle
      exact le_trans (le_of_lt hp1) hle

/-! ### `RealL`, the analysis layer's carrier

`Real` is the cut layer. Every theorem the analysis rows are stated over ---
`Analysis.RealL` --- lives one level up, on located pairs, and `Analysis.toCut`
is the tower's own map down. Composing gives the transfer those rows name. -/

/-- A located real as a Lean real. -/
noncomputable def toRL (z : ZFSet.{0}) : ℝ := toR (Analysis.toCut z)

theorem isCut_toCut {z : ZFSet.{0}} (hz : z ∈ Analysis.RealL) :
    Analysis.IsCut (Analysis.toCut z) :=
  (Analysis.mem_Real_iff _).mp (Analysis.toCut_mem hz)

/-- Addition crosses, by `toCut_add` and `toR_realAdd`. -/
theorem toRL_add {x y : ZFSet.{0}} (hx : x ∈ Analysis.RealL) (hy : y ∈ Analysis.RealL) :
    toRL (Analysis.realLAdd x y) = toRL x + toRL y := by
  rw [toRL, Analysis.toCut_add hx hy]
  exact toR_realAdd (isCut_toCut hx) (isCut_toCut hy)

/-- Zero goes to zero --- without computing a supremum.

The cut of `realLZero` is the negative rationals, and evaluating `sSup` on it
directly would be an argument. It is not needed: `realLAdd_zero` at `realLZero`
makes `toRL realLZero` its own double, and the only such real is `0`. The
algebra decides it. -/
theorem toRL_zero : toRL Analysis.realLZero.{0} = 0 := by
  have h := toRL_add Analysis.realLZero_mem Analysis.realLZero_mem
  rw [Analysis.realLAdd_zero Analysis.realLZero_mem] at h
  linarith

/-- Negation crosses, and there is no cut-level negation behind it.

A Dedekind cut has no negation constructively --- `Analysis.realAdd_neg_of_located`
needs locatedness, which is exactly the data `RealL` carries and `Real` does not.
So this cannot be proved the way `toRL_add` was. It comes from the group law
instead: `realLAdd_neg` says `x + (-x) = 0`, `toRL_add` carries that to `ℝ`, and
`toRL_zero` finishes it. -/
theorem toRL_neg {x : ZFSet.{0}} (hx : x ∈ Analysis.RealL) :
    toRL (Analysis.realLNeg x) = -toRL x := by
  have h := toRL_add hx (Analysis.realLNeg_mem hx)
  rw [Analysis.realLAdd_neg hx, toRL_zero] at h
  linarith

/-- The order crosses, by `toCut_le` and `toR_mono`. -/
theorem toRL_mono {x y : ZFSet.{0}} (hx : x ∈ Analysis.RealL) (hy : y ∈ Analysis.RealL)
    (h : Analysis.realLLe x y) : toRL x ≤ toRL y :=
  toR_mono (isCut_toCut hx) (isCut_toCut hy) (Analysis.toCut_le hx hy h)

/-- And the transfer is injective, by `toR_injective` then `toCut_injective`. -/
theorem toRL_injective {x y : ZFSet.{0}} (hx : x ∈ Analysis.RealL)
    (hy : y ∈ Analysis.RealL) (h : toRL x = toRL y) : x = y :=
  Analysis.toCut_injective hx hy
    (toR_injective (isCut_toCut hx) (isCut_toCut hy) h)

/-- The order is reflected at the located layer too.

`realLLe` is `¬ realLLt y x`, not a subset relation, so this is not the same
statement as `subset_of_toR_le`; the tower supplies both halves of the
translation (`realLLe_lower_subset` and `realLLe_of_lower_subset`) and this is
the second one composed with the cut-level reflection. -/
theorem realLLe_of_toRL_le {x y : ZFSet.{0}} (hx : x ∈ Analysis.RealL)
    (hy : y ∈ Analysis.RealL) (h : toRL x ≤ toRL y) : Analysis.realLLe x y := by
  have hsub := subset_of_toR_le (isCut_toCut hx) (isCut_toCut hy) h
  obtain ⟨L₁, U₁, hx1, h₁⟩ := (Analysis.mem_RealL_iff x).mp hx
  obtain ⟨L₂, U₂, hy2, h₂⟩ := (Analysis.mem_RealL_iff y).mp hy
  subst hx1; subst hy2
  refine Analysis.realLLe_of_lower_subset h₂ ?_
  simpa [Analysis.toCut, SetTheory.fst_opair] using hsub

/-- The maximum crosses.

Both directions are order-theoretic rather than set-theoretic: `≥` is
`realLLe_max_left`/`_right` under `toRL_mono`, and `≤` splits on which of the
two Lean reals is larger, uses `realLLe_of_toRL_le` to get the tower inequality
back, and closes with `realLMax_le`. The case split is classical, so it is made
here and not in the tower. -/
theorem toRL_max {x y : ZFSet.{0}} (hx : x ∈ Analysis.RealL) (hy : y ∈ Analysis.RealL) :
    toRL (Analysis.realLMax x y) = max (toRL x) (toRL y) := by
  have hmem := Analysis.realLMax_mem hx hy
  refine le_antisymm ?_ ?_
  · rcases le_total (toRL x) (toRL y) with h | h
    · have hle := Analysis.realLMax_le (realLLe_of_toRL_le hx hy h)
        (Analysis.realLLe_refl hy)
      exact le_trans (toRL_mono hmem hy hle) (le_max_right _ _)
    · have hle := Analysis.realLMax_le (Analysis.realLLe_refl hx)
        (realLLe_of_toRL_le hy hx h)
      exact le_trans (toRL_mono hmem hx hle) (le_max_left _ _)
  · exact max_le (toRL_mono hx hmem (Analysis.realLLe_max_left hx))
      (toRL_mono hy hmem (Analysis.realLLe_max_right hy))

/-- And so does the absolute value, since `Analysis.realLAbs` is literally
`realLMax x (realLNeg x)` and `|r|` is `max r (-r)`. -/
theorem toRL_abs {x : ZFSet.{0}} (hx : x ∈ Analysis.RealL) :
    toRL (Analysis.realLAbs x) = |toRL x| := by
  rw [Analysis.realLAbs, toRL_max hx (Analysis.realLNeg_mem hx), toRL_neg hx,
    abs_eq_max_neg]

/-! ### Surjectivity at the located layer

`ofR` gives a cut, and not every cut is located --- locatedness is exactly the
constructive extra that makes `RealL` a separate layer from `Real`. Classically
it holds of the cut of a Lean real, and the argument is made here. -/

/-- The rationals strictly above a Lean real. -/
noncomputable def upperR (x : ℝ) : ZFSet.{0} :=
  SetTheory.sep
    (fun q => ∃ hq : q ∈ NumberTheory.Rat.{0}, x < (toRat q hq : ℝ))
    NumberTheory.Rat.{0}

theorem mem_upperR_iff (x : ℝ) (q : ZFSet.{0}) :
    q ∈ upperR x ↔ q ∈ NumberTheory.Rat.{0}
      ∧ ∃ hq : q ∈ NumberTheory.Rat.{0}, x < (toRat q hq : ℝ) :=
  SetTheory.mem_sep_iff _ _ _

/-- A Lean real as a located pair. -/
noncomputable def ofRL (x : ℝ) : ZFSet.{0} := SetTheory.opair (ofR x) (upperR x)

/-- And the pair really is located.

Nine of the ten fields are the cut argument again, run on both halves. The
tenth, `located`, is the classical step: given `p < q` in `ℚ`, it must place
`p` below `x` or `q` above it, and `lt_or_le` in `ℝ` decides that. The tower
can never do this for an arbitrary real --- deciding the order on located reals
is what `DecidableRealLLt` costs --- so a comparator that could not spend
excluded middle here would have no `ofRL` at all. It is spent in `comparator/`,
and nothing under `FromAxioms/` sees it. -/
theorem isLocated_ofRL (x : ℝ) : Analysis.IsLocated (ofR x) (upperR x) where
  lower_subset q hq := ((mem_ofR_iff x q).mp hq).left
  upper_subset q hq := ((mem_upperR_iff x q).mp hq).left
  lower_inhabited := (isCut_ofR x).nonempty
  upper_inhabited := by
    obtain ⟨p, hp⟩ := exists_rat_gt x
    exact ⟨ratOfLean p, (mem_upperR_iff x _).mpr ⟨ratOfLean_mem p, ratOfLean_mem p,
      by rw [toRat_ratOfLean]; exact hp⟩⟩
  ordered q hq r hr := by
    obtain ⟨-, hqQ, hqx⟩ := (mem_ofR_iff x q).mp hq
    obtain ⟨-, hrQ, hxr⟩ := (mem_upperR_iff x r).mp hr
    by_contra hnlt
    have hle := NumberTheory.ratLe_of_not_lt hrQ hqQ hnlt
    have : (toRat r hrQ : ℝ) ≤ (toRat q hqQ : ℝ) := by
      exact_mod_cast toRat_le hrQ hqQ hle
    linarith
  lower_down q hq p hpQ hlt := (isCut_ofR x).down q hq p hpQ hlt
  upper_up r hr p hpQ hlt := by
    obtain ⟨-, hrQ, hxr⟩ := (mem_upperR_iff x r).mp hr
    refine (mem_upperR_iff x p).mpr ⟨hpQ, hpQ, ?_⟩
    have : (toRat r hrQ : ℝ) < (toRat p hpQ : ℝ) := by
      exact_mod_cast toRat_lt hrQ hpQ hlt
    linarith
  lower_open q hq := (isCut_ofR x).no_greatest q hq
  upper_open r hr := by
    obtain ⟨-, hrQ, hxr⟩ := (mem_upperR_iff x r).mp hr
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hxr
    refine ⟨ratOfLean p, (mem_upperR_iff x _).mpr ⟨ratOfLean_mem p, ratOfLean_mem p,
      by rw [toRat_ratOfLean]; exact hp1⟩, ?_⟩
    by_contra hnlt
    have hle := NumberTheory.ratLe_of_not_lt hrQ (ratOfLean_mem p) hnlt
    have : (toRat r hrQ : ℝ) ≤ (p : ℝ) := by
      have := toRat_le hrQ (ratOfLean_mem p) hle
      rw [toRat_ratOfLean] at this
      exact_mod_cast this
    linarith
  located p hp q hq _ := by
    -- The classical step, and the only one.
    rcases lt_or_le (toRat p hp : ℝ) x with h | h
    · exact Or.inl ((mem_ofR_iff x p).mpr ⟨hp, hp, h⟩)
    · exact Or.inr ((mem_upperR_iff x q).mpr ⟨hq, hq, by
        have : (toRat p hp : ℝ) < (toRat q hq : ℝ) := by
          exact_mod_cast toRat_lt hp hq ‹NumberTheory.ratLt p q›
        linarith⟩)

theorem ofRL_mem (x : ℝ) : ofRL x ∈ Analysis.RealL.{0} :=
  (Analysis.mem_RealL_iff _).mpr ⟨ofR x, upperR x, rfl, isLocated_ofRL x⟩

/-- The round trip at the located layer. With `ofRL_mem` this makes `toRL`
surjective onto `ℝ`, so a challenge quantifying over Lean reals can be answered
with a located real --- which is what the analysis rows are stated over. -/
theorem toRL_ofRL (x : ℝ) : toRL (ofRL x) = x := by
  rw [toRL, ofRL, Analysis.toCut, SetTheory.fst_opair]
  exact toR_ofR x

/-- And so `toRL` agrees with `toRat` on the embedded rationals. -/
theorem toRL_realLOf {q : ZFSet.{0}} (hq : q ∈ NumberTheory.Rat.{0}) :
    toRL (Analysis.realLOf q) = (toRat q hq : ℝ) := by
  rw [toRL, Analysis.realLOf, Analysis.toCut, SetTheory.fst_opair]
  exact toR_ratCut hq

/-! ### The metric vocabulary

Everything above moves points. The analysis rows --- the intermediate value
theorem, the extreme value theorem, the mean value theorem --- are all stated
with a modulus: the tower's `UniformlyContinuousOn` quantifies over rational
widths `w` and asks for `Close (H x) (H y) (realLOf (1/n))`. So the piece
between `toRL` and any of those rows is `Close`, and it is `toRL_abs` and
`toRL_add` read together.

`Close x y e` unfolds to `WithinOf (realLAdd x (realLNeg y)) e`, which is a
conjunction of two `realLLe`s --- so `rintro ⟨_, _⟩` and `exact ⟨_, _⟩` cross it
without unfolding a `def`, and mathlib's `abs_le` is the same conjunction on the
other side. -/

/-- The tower's order and mathlib's are the same order, both ways. `toRL_mono` and
`realLLe_of_toRL_le` as one `Iff`. -/
theorem toRL_le_iff {x y : ZFSet.{0}} (hx : x ∈ Analysis.RealL) (hy : y ∈ Analysis.RealL) :
    Analysis.realLLe x y ↔ toRL x ≤ toRL y :=
  ⟨toRL_mono hx hy, realLLe_of_toRL_le hx hy⟩

/-- `Close` is `|x - y| ≤ e`. The bridge every modulus argument crosses. -/
theorem toRL_close_iff {x y e : ZFSet.{0}} (hx : x ∈ Analysis.RealL)
    (hy : y ∈ Analysis.RealL) (he : e ∈ Analysis.RealL) :
    Analysis.Close x y e ↔ |toRL x - toRL y| ≤ toRL e := by
  have hny := Analysis.realLNeg_mem hy
  have hd := Analysis.realLAdd_mem hx hny
  have hxy : toRL (Analysis.realLAdd x (Analysis.realLNeg y)) = toRL x - toRL y := by
    rw [toRL_add hx hny, toRL_neg hy]
    ring
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := (toRL_le_iff (Analysis.realLNeg_mem he) hd).mp h1
      rw [toRL_neg he, hxy] at this
      exact this
    · have := (toRL_le_iff hd he).mp h2
      rw [hxy] at this
      exact this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · refine (toRL_le_iff (Analysis.realLNeg_mem he) hd).mpr ?_
      rw [toRL_neg he, hxy]
      exact h1
    · refine (toRL_le_iff hd he).mpr ?_
      rw [hxy]
      exact h2

/-- The tower's closed interval is mathlib's, on the image of `toRL`.

Stated with the endpoints as rationals, because `realLIcc p q` takes them that
way --- `realLOf p` is the embedded rational and `toRL_realLOf` reads it as a
`ℚ`-valued real. Both directions: the forward one is what a hypothesis about a
mathlib point needs to enter the tower, the backward one is what the tower's
conclusion needs to leave it. -/
theorem toRL_mem_realLIcc_iff {p q x : ZFSet.{0}} (hp : p ∈ NumberTheory.Rat.{0})
    (hq : q ∈ NumberTheory.Rat.{0}) (hx : x ∈ Analysis.RealL) :
    x ∈ Analysis.realLIcc p q
      ↔ toRL x ∈ Set.Icc ((toRat p hp : ℝ)) ((toRat q hq : ℝ)) := by
  rw [Analysis.mem_realLIcc_iff, Set.mem_Icc,
    toRL_le_iff (Analysis.realLOf_mem hp) hx,
    toRL_le_iff hx (Analysis.realLOf_mem hq),
    toRL_realLOf hp, toRL_realLOf hq]
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

/-- The tower's width `1/(m+1)`, as a rational.

`UniformlyContinuousOn` states both its modulus and its target width as
`invWidth (ofNat _)`, so nothing about a continuity argument can cross the
bridge until this does. `invWidth n` is `ratOf intOne (intOf (succ n) empty)`,
literally `1 / (n+1)`, and reading that off is: `toRat_ratOf` for the quotient,
`toInt_intOf` for the numerator and denominator, `toNat_ofNat` for the index.
`succ (ofNat m) = ofNat (m+1)` is `ofNat_succ`, which is `rfl`. -/
theorem toRat_invWidth (m : Nat) (h : NumberTheory.invWidth (NumberTheory.ofNat.{0} m)
      ∈ NumberTheory.Rat.{0}) :
    toRat (NumberTheory.invWidth (NumberTheory.ofNat.{0} m)) h = 1 / ((m : ℚ) + 1) := by
  -- Both the numerator and the denominator are `intOf _ empty`, so `toInt_intOf`
  -- serves both: `intOne` is `intOf (ofNat 1) empty`.
  have hemp : SetTheory.empty.{0} ∈ SetTheory.omega.{0} := by
    rw [← NumberTheory.ofNat_zero]
    exact NumberTheory.ofNat_mem_omega 0
  have hs : SetTheory.succ (NumberTheory.ofNat.{0} m) ∈ SetTheory.omega.{0} := by
    rw [← NumberTheory.ofNat_succ]
    exact NumberTheory.ofNat_mem_omega (m + 1)
  -- `toRat`, `toInt` and `toNat` each take a membership proof about the set
  -- being rewritten, so every step is a `have` between `ℤ`s and `ℕ`s rather
  -- than a rewrite. `intOne` is `intOf (ofNat 1) empty`, `empty` is `ofNat 0`,
  -- and `succ (ofNat m)` is `ofNat (m+1)`, all three by `rfl`.
  have hpos := NumberTheory.intOf_succ_pos (NumberTheory.ofNat_mem_omega m)
  have hemp0 : toNat SetTheory.empty.{0} hemp = 0 := toNat_ofNat 0 hemp
  have hs1 : toNat (SetTheory.succ (NumberTheory.ofNat.{0} m)) hs = m + 1 :=
    toNat_ofNat (m + 1) hs
  have h1 : toInt NumberTheory.intOne.{0} NumberTheory.intOne_mem_Int = 1 := by
    have e := toInt_intOf (NumberTheory.ofNat_mem_omega 1) hemp
      NumberTheory.intOne_mem_Int
    rw [toNat_ofNat 1, hemp0] at e
    exact e.trans (by norm_num)
  have h2 : toInt (NumberTheory.intOf (SetTheory.succ (NumberTheory.ofNat.{0} m))
      SetTheory.empty.{0}) (NumberTheory.intPositive_subset _ hpos) = (m : ℤ) + 1 := by
    have e := toInt_intOf hs hemp (NumberTheory.intPositive_subset _ hpos)
    rw [hs1, hemp0] at e
    rw [e]
    push_cast
    ring
  rw [toRat_congr h (NumberTheory.ratOf_mem_Rat NumberTheory.intOne_mem_Int hpos) rfl,
    toRat_ratOf NumberTheory.intOne_mem_Int hpos, h1, h2]
  push_cast
  ring

/-- A mathlib function on `ℝ`, read as a tower function on `RealL`.

`ofRL ∘ f ∘ toRL`. It is not a section of anything --- `ofRL (toRL z)` is the
canonical located real with the same value as `z`, not `z` --- and that is
harmless, because every consumer reads the value back through `toRL` and
`toRL_ofRL` says the value survives. -/
noncomputable def liftFun (f : ℝ → ℝ) (z : ZFSet.{0}) : ZFSet.{0} := ofRL (f (toRL z))

theorem liftFun_mem (f : ℝ → ℝ) (z : ZFSet.{0}) : liftFun f z ∈ Analysis.RealL.{0} :=
  ofRL_mem _

@[simp] theorem toRL_liftFun (f : ℝ → ℝ) (z : ZFSet.{0}) : toRL (liftFun f z) = f (toRL z) :=
  toRL_ofRL _

/-- The modulus crosses. A mathlib ε-δ uniform-continuity statement on
`[p, q]` becomes the tower's `UniformlyContinuousOn`.

The tower states continuity with a modulus over rational widths
(`invWidth (ofNat m)` = `1/(m+1)`) and mathlib states it with a real `δ`, so
the two are separated by one Archimedean step, `exists_nat_one_div_lt`, and by
`toRat_invWidth` reading the tower's width as a rational.

The hypothesis is the ε-δ form and not `UniformContinuousOn`. Mathlib's
uniformity-filter definition is the harder thing to consume and the easier
thing to produce --- a caller with `ContinuousOn f (Icc a b)` reaches this form
through compactness --- so taking the ε-δ statement keeps the two libraries'
definitional choices out of the bridge. -/
theorem uniformlyContinuousOn_liftFun (f : ℝ → ℝ) {p q : ZFSet.{0}}
    (hp : p ∈ NumberTheory.Rat.{0}) (hq : q ∈ NumberTheory.Rat.{0})
    (hf : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ Set.Icc ((toRat p hp : ℝ)) ((toRat q hq : ℝ)),
      ∀ y ∈ Set.Icc ((toRat p hp : ℝ)) ((toRat q hq : ℝ)),
        |x - y| ≤ δ → |f x - f y| ≤ ε) :
    Analysis.UniformlyContinuousOn (liftFun f) p q := by
  intro n
  have hnpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨δ, hδ, hfδ⟩ := hf _ hnpos
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m, ?_⟩
  intro w x y hw hw0 hwm hx hy hclose
  have hxR := (Analysis.mem_realLIcc_iff p q x).mp hx |>.1
  have hyR := (Analysis.mem_realLIcc_iff p q y).mp hy |>.1
  have hwR := Analysis.realLOf_mem hw
  have hnQ : NumberTheory.invWidth (NumberTheory.ofNat.{0} n) ∈ NumberTheory.Rat.{0} :=
    NumberTheory.invWidth_mem_Rat (NumberTheory.ofNat_mem_omega n)
  have hmQ : NumberTheory.invWidth (NumberTheory.ofNat.{0} m) ∈ NumberTheory.Rat.{0} :=
    NumberTheory.invWidth_mem_Rat (NumberTheory.ofNat_mem_omega m)
  -- the two points, in mathlib's interval
  have hxI := (toRL_mem_realLIcc_iff hp hq hxR).mp hx
  have hyI := (toRL_mem_realLIcc_iff hp hq hyR).mp hy
  -- the hypothesis width, as a real: `|x - y| ≤ w ≤ 1/(m+1) < δ`
  have hdist : |toRL x - toRL y| ≤ δ := by
    have h1 := (toRL_close_iff hxR hyR hwR).mp hclose
    rw [toRL_realLOf hw] at h1
    have h2 : ((toRat w hw : ℝ)) ≤ 1 / ((m : ℝ) + 1) := by
      have hq := toRat_le hw hmQ hwm
      rw [toRat_invWidth m hmQ] at hq
      have hr : ((toRat w hw : ℝ)) ≤ ((1 / ((m : ℚ) + 1) : ℚ) : ℝ) := Rat.cast_le.mpr hq
      push_cast at hr
      exact hr
    have h3 : (1 : ℝ) / ((m : ℝ) + 1) ≤ δ := le_of_lt hm
    linarith [h1, h2, h3]
  -- the conclusion, back across the bridge
  refine (toRL_close_iff (liftFun_mem f x) (liftFun_mem f y)
    (Analysis.realLOf_mem hnQ)).mpr ?_
  rw [toRL_liftFun, toRL_liftFun, toRL_realLOf hnQ, toRat_invWidth n hnQ]
  have := hfδ _ hxI _ hyI hdist
  push_cast
  exact this

/-- The strict order crosses too, and this half is classical.

`realLLe a b` is `¬ realLLt b a` by definition, so `realLLt x y` and
`¬ realLLe y x` differ by a double negation --- which is free in one direction
and costs excluded middle in the other. That is a fact about the tower's order,
not about this bridge: `realLLt` is an existential over rationals and nothing
decides it. Mathlib is classical, so `not_not` is available here; the tower's own
theorems that need this carry `EM` in a binder, which is the honest form. -/
theorem toRL_lt_iff {x y : ZFSet.{0}} (hx : x ∈ Analysis.RealL) (hy : y ∈ Analysis.RealL) :
    Analysis.realLLt x y ↔ toRL x < toRL y := by
  constructor
  · intro h
    rw [← not_le, ← toRL_le_iff hy hx]
    exact fun hle => hle h
  · intro h
    rw [← not_le, ← toRL_le_iff hy hx] at h
    exact not_not.mp h

/-- `toRat` of the tower's `1`. `ratOne` is `ratOf intOne intOne`, so this is
the same three-step reading as `toRat_invWidth` with the numerator repeated. -/
theorem toRat_ratOne (h : NumberTheory.ratOne.{0} ∈ NumberTheory.Rat.{0}) :
    toRat NumberTheory.ratOne.{0} h = 1 := by
  have hemp : SetTheory.empty.{0} ∈ SetTheory.omega.{0} := by
    rw [← NumberTheory.ofNat_zero]
    exact NumberTheory.ofNat_mem_omega 0
  have hemp0 : toNat SetTheory.empty.{0} hemp = 0 := toNat_ofNat 0 hemp
  have hone : toInt NumberTheory.intOne.{0} NumberTheory.intOne_mem_Int = 1 := by
    have e := toInt_intOf (NumberTheory.ofNat_mem_omega 1) hemp
      NumberTheory.intOne_mem_Int
    rw [toNat_ofNat 1, hemp0] at e
    exact e.trans (by norm_num)
  have honeP := NumberTheory.one_mem_intPositive.{0}
  rw [toRat_congr h (NumberTheory.ratOf_mem_Rat NumberTheory.intOne_mem_Int honeP) rfl,
    toRat_ratOf NumberTheory.intOne_mem_Int honeP, hone]
  norm_num

/-- The unit interval's endpoints, as reals. -/
theorem toRL_realLZero : toRL Analysis.realLZero.{0} = 0 := toRL_zero

theorem toRL_realLOne :
    toRL (Analysis.realLOf NumberTheory.ratOne.{0}) = 1 := by
  rw [toRL_realLOf NumberTheory.ratOne_mem_Rat, toRat_ratOne]
  norm_num

/-- The tower's exact IVT, delivered in Mathlib's vocabulary.

Every hypothesis is mathlib's and the conclusion is mathlib's; the tower's
`Metamath.ExactIVT01` is the only thing in between. The three obligations it
states are exactly the three bridges above:

    maps into `RealL`        `liftFun_mem`
    a rational modulus       `uniformlyContinuousOn_liftFun`
    a strict straddle        `toRL_lt_iff`, at `realLZero` and `realLOf ratOne`

and its conclusion comes back through `toRL_mem_realLIcc_iff` and `toRL_liftFun`,
with `f x = 0` read off `toRL (liftFun f c) = toRL realLZero`.

`ExactIVT01` is supplied without a binder here. The tower proves
`exactIVT01Top_of_em` --- the exact IVT costs excluded middle, and
`llpo_of_exact_ivt` shows the price is real --- so a comparator against a
classical library supplies `Classical.em` and the row's
`principle: SignDisjunction` is what the print then records. -/
theorem exists_root_of_lt (f : ℝ → ℝ)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |x - y| ≤ δ → |f x - f y| ≤ ε)
    (h0 : f 0 < 0) (h1 : 0 < f 1) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, f x = 0 := by
  have hivt : Metamath.ExactIVT01.{0} :=
    Metamath.exactIVT01_of_top (Analysis.exactIVT01Top_of_em (fun p => Classical.em p))
  have hz := NumberTheory.ratZero_mem_Rat.{0}
  have ho := NumberTheory.ratOne_mem_Rat.{0}
  have hz0 : (toRat NumberTheory.ratZero.{0} hz : ℝ) = 0 := by
    rw [toRat_congr hz NumberTheory.ratZero_mem_Rat rfl, toRat_zero]
    norm_num
  have ho1 : (toRat NumberTheory.ratOne.{0} ho : ℝ) = 1 := by
    rw [toRat_ratOne ho]
    norm_num
  -- the modulus, restated on the tower's interval
  have huc : Analysis.UniformlyContinuousOn (liftFun f)
      NumberTheory.ratZero.{0} NumberTheory.ratOne.{0} := by
    refine uniformlyContinuousOn_liftFun f hz ho (fun ε hε => ?_)
    obtain ⟨δ, hδ, hd⟩ := hf ε hε
    exact ⟨δ, hδ, by rw [hz0, ho1]; exact hd⟩
  -- the two strict straddles
  have hlo : Analysis.realLLt (liftFun f (Analysis.realLOf NumberTheory.ratZero.{0}))
      Analysis.realLZero.{0} := by
    refine (toRL_lt_iff (liftFun_mem f _) Analysis.realLZero_mem).mpr ?_
    rw [toRL_liftFun, toRL_realLZero, toRL_realLOf hz, hz0]
    exact h0
  have hhi : Analysis.realLLt Analysis.realLZero.{0}
      (liftFun f (Analysis.realLOf NumberTheory.ratOne.{0})) := by
    refine (toRL_lt_iff Analysis.realLZero_mem (liftFun_mem f _)).mpr ?_
    rw [toRL_liftFun, toRL_realLZero, toRL_realLOf ho, ho1]
    exact h1
  obtain ⟨c, hc, hcz⟩ := hivt (liftFun f) (fun x _ => liftFun_mem f x) huc hlo hhi
  refine ⟨toRL c, ?_, ?_⟩
  · have hcR := (Analysis.mem_realLIcc_iff _ _ c).mp hc |>.1
    have := (toRL_mem_realLIcc_iff hz ho hcR).mp hc
    rwa [hz0, ho1] at this
  · have := congrArg toRL hcz
    rwa [toRL_liftFun, toRL_realLZero] at this

/-- Non-negativity crosses both ways, which the sign split needs.

`toR_nonneg` is the forward half. The backward half is `subset_of_toR_le`:
`realNonneg x` unfolds to `realZero ⊆ x`, i.e. `ratCut ratZero ⊆ x`, so an
inclusion of cuts is exactly what a `≤` of their suprema gives. -/
theorem toRL_nonneg_iff {x : ZFSet.{0}} (hx : x ∈ Analysis.RealL) :
    0 ≤ toRL x ↔ Analysis.realNonneg (Analysis.toCut x) := by
  -- Stated at `realZero`, not at `ratCut ratZero`: they are the same term, and
  -- `rw` matches syntactically.
  have hz : Analysis.IsCut Analysis.realZero.{0} :=
    Analysis.isCut_lower (Analysis.isLocated_ratCut NumberTheory.ratZero_mem_Rat)
  have hzR : toR Analysis.realZero.{0} = 0 := by
    show toR (Analysis.ratCut NumberTheory.ratZero.{0}) = 0
    rw [toR_ratCut NumberTheory.ratZero_mem_Rat, toRat_zero]
    norm_num
  constructor
  · intro h
    refine subset_of_toR_le hz (isCut_toCut hx) ?_
    rw [hzR]
    exact h
  · intro h
    have := toR_nonneg (isCut_toCut hx) h
    exact this

/-- The product crosses, for non-negative arguments. `toCut_mul` moves the
tower's `realLMul` to the cut level and `toR_realMulNonneg` finishes. -/
theorem toRL_mulNonneg {x y : ZFSet.{0}} (hx : x ∈ Analysis.RealL)
    (hy : y ∈ Analysis.RealL) (hx0 : 0 ≤ toRL x) (hy0 : 0 ≤ toRL y) :
    toRL (Analysis.realLMul x y) = toRL x * toRL y := by
  have hcx := (toRL_nonneg_iff hx).mp hx0
  have hcy := (toRL_nonneg_iff hy).mp hy0
  rw [toRL, Analysis.toCut_mul hx hy hcx hcy,
    toR_realMulNonneg (isCut_toCut hx) (isCut_toCut hy) hcx hcy]
  rfl

/-- The product crosses at every sign.

Four cases, and the tower supplies each sign identity: `realLNeg_realLMul`
(`(-x)·y = -(x·y)`), `realLMul_neg` (`x·(-y) = -(x·y)`) and `realLMul_neg_neg`.
Each branch rewrites the negative factors away, applies `toRL_mulNonneg`, and
`toRL_neg` puts the sign back.

The split is decided in `ℝ`, not in the tower, so this lemma can exist here.
`realLLt` is an existential over rationals and nothing in `RealL` decides a
sign; `le_or_lt` in mathlib's classical `ℝ` does, and `toRL_nonneg_iff` carries
the answer back. So the comparator can have the unrestricted product while the
tower keeps only the non-negative one, which is the difference the comparison
measures. -/
theorem toRL_mul {x y : ZFSet.{0}} (hx : x ∈ Analysis.RealL)
    (hy : y ∈ Analysis.RealL) :
    toRL (Analysis.realLMul x y) = toRL x * toRL y := by
  have hnx := Analysis.realLNeg_mem hx
  have hny := Analysis.realLNeg_mem hy
  rcases le_or_gt 0 (toRL x) with hx0 | hx0
  · rcases le_or_gt 0 (toRL y) with hy0 | hy0
    · exact toRL_mulNonneg hx hy hx0 hy0
    · have hny0 : 0 ≤ toRL (Analysis.realLNeg y) := by
        rw [toRL_neg hy]; linarith
      have h := toRL_mulNonneg hx hny hx0 hny0
      rw [Analysis.realLMul_neg hx hy, toRL_neg (Analysis.realLMul_mem hx hy),
        toRL_neg hy] at h
      linarith
  · rcases le_or_gt 0 (toRL y) with hy0 | hy0
    · have hnx0 : 0 ≤ toRL (Analysis.realLNeg x) := by
        rw [toRL_neg hx]; linarith
      have h := toRL_mulNonneg hnx hy hnx0 hy0
      rw [Analysis.realLNeg_realLMul hx hy, toRL_neg (Analysis.realLMul_mem hx hy),
        toRL_neg hx] at h
      linarith
    · have hnx0 : 0 ≤ toRL (Analysis.realLNeg x) := by
        rw [toRL_neg hx]; linarith
      have hny0 : 0 ≤ toRL (Analysis.realLNeg y) := by
        rw [toRL_neg hy]; linarith
      have h := toRL_mulNonneg hnx hny hnx0 hny0
      rw [Analysis.realLMul_neg_neg hx hy, toRL_neg hx, toRL_neg hy] at h
      linarith

/-- A finite sum crosses `toRL`.

`Analysis.realLSum` recurses as `realLSum G (k+1) = realLAdd (realLSum G k) (G k)`,
which is `Finset.sum_range_succ` on the other side, so the induction is one line
per case with `toRL_add` and `toRL_zero`.

Membership is a hypothesis on the whole family, not on the summands used ---
`toRL_add` needs both arguments in `RealL`, and at step `k+1` the left argument
is the partial sum, whose membership is itself the induction. `realLSum_mem`
supplies that from the same hypothesis, so the statement asks for `G`
everywhere rather than below `m`. -/
theorem toRL_realLSum {G : Nat → ZFSet.{0}} (hG : ∀ k, G k ∈ Analysis.RealL) :
    ∀ m : Nat, toRL (Analysis.realLSum G m) = ∑ k ∈ Finset.range m, toRL (G k)
  | 0 => by
    rw [Finset.sum_range_zero]
    exact toRL_realLZero
  | m + 1 => by
    rw [Finset.sum_range_succ, ← toRL_realLSum hG m,
      show Analysis.realLSum G (m + 1)
        = Analysis.realLAdd (Analysis.realLSum G m) (G m) from rfl,
      toRL_add (Analysis.realLSum_mem (fun k => hG k) m) (hG m)]

#print axioms toRL_le_iff
#print axioms toRL_close_iff
#print axioms toRL_mem_realLIcc_iff
#print axioms toRat_invWidth
#print axioms toRL_liftFun
#print axioms uniformlyContinuousOn_liftFun
#print axioms toRL_lt_iff
#print axioms toRat_ratOne
/-! ### The Bernstein basis

The two definitions line up term for term, so this is a transport and not a
theorem:

    tower     `bernPair n k x y = C(n,k) * (x^k * y^(n-k))`
              `bernTerm n k x   = bernPair n k x (1 - x)`
    mathlib   `bernsteinPolynomial R n v = (C(n,v) : R[X]) * X^v * (1-X)^(n-v)`

so what has to cross is a product, a power, a difference and a natural-number
coefficient --- and nothing about approximation. -/

/-- `realLOne` is `realLOf ratOne` by definition; `rw` needs it at the name the
goals carry. -/
theorem toRL_one : toRL Analysis.realLOne.{0} = 1 := toRL_realLOne

/-- Powers cross. The induction is `toRL_mul` at every step, so it
needs the unrestricted product: `realLPow x k` has no sign. -/
theorem toRL_realLPow {x : ZFSet.{0}} (hx : x ∈ Analysis.RealL) :
    ∀ k : Nat, toRL (Analysis.realLPow x k) = toRL x ^ k
  | 0 => by
    rw [pow_zero]
    exact toRL_one
  | k + 1 => by
    show toRL (Analysis.realLMul x (Analysis.realLPow x k)) = _
    rw [toRL_mul hx (Analysis.realLPow_mem hx k), toRL_realLPow hx k, pow_succ]
    ring

/-- `1 - x` crosses, in the spelling the tower writes it: `realLAdd realLOne
(realLNeg x)`. -/
theorem toRL_one_sub {x : ZFSet.{0}} (hx : x ∈ Analysis.RealL) :
    toRL (Analysis.realLAdd Analysis.realLOne.{0} (Analysis.realLNeg x))
      = 1 - toRL x := by
  rw [toRL_add Analysis.realLOne_mem (Analysis.realLNeg_mem hx), toRL_neg hx,
    toRL_one]
  ring

/-- `toInt` of a natural, which both halves of `ratNat` need. `intOfNat n` is
`intOf (ofNat n) empty`, so this is `toInt_intOf` with the second `toNat` at
zero. -/
theorem toInt_intOfNat (c : Nat) (h : NumberTheory.intOfNat.{0} c ∈ NumberTheory.Int.{0}) :
    toInt (NumberTheory.intOfNat.{0} c) h = (c : ℤ) := by
  have hemp : SetTheory.empty.{0} ∈ SetTheory.omega.{0} := by
    rw [← NumberTheory.ofNat_zero]
    exact NumberTheory.ofNat_mem_omega 0
  have hemp0 : toNat SetTheory.empty.{0} hemp = 0 := toNat_ofNat 0 hemp
  have e := toInt_intOf (NumberTheory.ofNat_mem_omega c) hemp h
  rw [toNat_ofNat c, hemp0] at e
  exact e.trans (by push_cast; ring)

/-- A rational `p/q` crosses, for natural `p` and positive natural `q`.

Stated at a general denominator because the Bernstein sum samples at `k/N`. -/
theorem toRat_ratNat (p q : Nat) (hq : 0 < q)
    (h : NumberTheory.ratNat.{0} p q ∈ NumberTheory.Rat.{0}) :
    toRat (NumberTheory.ratNat.{0} p q) h = (p : ℚ) / (q : ℚ) := by
  have hpos := NumberTheory.intOfNat_mem_intPositive (n := q) hq
  rw [toRat_congr h
      (NumberTheory.ratOf_mem_Rat (NumberTheory.intOfNat_mem_Int p) hpos) rfl,
    toRat_ratOf (NumberTheory.intOfNat_mem_Int p) hpos,
    toInt_intOfNat p, toInt_intOfNat q]
  push_cast
  ring

/-- The tower's binomial coefficient is `Nat.choose`.

`NumberTheory.choose` is Pascal's recursion written out --- `_ 0 => 1`,
`0 (k+1) => 0`, `(n+1) (k+1) => choose n k + choose n (k+1)` --- and those are
exactly `Nat.choose`'s three equations. -/
theorem choose_eq_natChoose : ∀ n k : Nat, NumberTheory.choose n k = Nat.choose n k
  | _, 0 => by rw [NumberTheory.choose_zero, Nat.choose_zero_right]
  | 0, _ + 1 => rfl
  | n + 1, k + 1 => by
    show NumberTheory.choose n k + NumberTheory.choose n (k + 1) = _
    rw [choose_eq_natChoose n k, choose_eq_natChoose n (k + 1), Nat.choose_succ_succ]

/-- The bernstein basis term crosses. The two definitions are the same
expression. -/
theorem toRL_bernTerm {x : ZFSet.{0}} (hx : x ∈ Analysis.RealL) (n k : Nat) :
    toRL (Analysis.bernTerm n k x)
      = (bernsteinPolynomial ℝ n k).eval (toRL x) := by
  have hone := Analysis.realLOne_mem.{0}
  have hsub := Analysis.realLAdd_mem hone (Analysis.realLNeg_mem hx)
  have hc := NumberTheory.ratNat_mem_Rat (p := NumberTheory.choose n k) Nat.one_pos
  show toRL (Analysis.realLMul
      (Analysis.realLOf (NumberTheory.ratNat.{0} (NumberTheory.choose n k) 1))
      (Analysis.realLMul (Analysis.realLPow x k)
        (Analysis.realLPow (Analysis.realLAdd Analysis.realLOne.{0}
          (Analysis.realLNeg x)) (n - k)))) = _
  rw [toRL_mul (Analysis.realLOf_mem hc)
      (Analysis.realLMul_mem (Analysis.realLPow_mem hx k)
        (Analysis.realLPow_mem hsub (n - k))),
    toRL_mul (Analysis.realLPow_mem hx k) (Analysis.realLPow_mem hsub (n - k)),
    toRL_realLPow hx k, toRL_realLPow hsub (n - k), toRL_one_sub hx,
    toRL_realLOf hc, toRat_ratNat _ 1 Nat.one_pos, choose_eq_natChoose]
  rw [bernsteinPolynomial]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_natCast, Polynomial.eval_sub, Polynomial.eval_one]
  push_cast
  ring

/-- The bernstein operator crosses, by `toRL_realLSum`, `toRL_mul`
and `toRL_bernTerm`.

The right-hand side is the evaluation of a mathlib polynomial ---
`∑ k, C (coefficient) * bernsteinPolynomial ℝ n k` --- written out, so the
Solution can name that polynomial and get its `eval` for free. -/
theorem toRL_bernOp {F : ZFSet.{0} → ZFSet.{0}} {x : ZFSet.{0}}
    (hx : x ∈ Analysis.RealL) (hF : ∀ z, F z ∈ Analysis.RealL) (n : Nat) :
    toRL (Analysis.bernOp n F x)
      = ∑ k ∈ Finset.range (n + 1),
          toRL (F (Analysis.realLOf (NumberTheory.ratNat.{0} k n)))
            * (bernsteinPolynomial ℝ n k).eval (toRL x) := by
  show toRL (Analysis.realLSum (fun k => Analysis.realLMul
      (F (Analysis.realLOf (NumberTheory.ratNat.{0} k n)))
      (Analysis.bernTerm n k x)) (n + 1)) = _
  rw [toRL_realLSum (fun k => Analysis.realLMul_mem (hF _)
    (Analysis.bernTerm_mem hx n k)) (n + 1)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [toRL_mul (hF _) (Analysis.bernTerm_mem hx n k), toRL_bernTerm hx n k]

/-- The inverse crosses, at a positive argument.

The hypothesis is positivity, not apartness. `Analysis.realLInv_mem` and
`Analysis.realLMul_inv` are both keyed to `realLLt realLZero z`, and the caller
that needs this --- the reparameterisation of `[p,q]` onto `[0,1]` --- has
`p < q`, from which `Analysis.sub_pos_of_lt` gives `0 < q - p`. So the
hypothesis is one the consumer already holds.

The proof is `toRL_mul`. `realLMul_inv` says `z * z⁻¹ = 1` in the tower;
`toRL_mul` reads that as `toRL z * toRL z⁻¹ = 1` over `ℝ`, and
`eq_one_div_of_mul_eq_one_left` turns it into the inverse once `toRL z ≠ 0`,
which `toRL_lt_iff` gets from the positivity. Nothing about cuts is reopened.
-/
theorem toRL_realLInv {x : ZFSet.{0}} (hx : x ∈ Analysis.RealL)
    (hpos : Analysis.realLLt Analysis.realLZero.{0} x) :
    toRL (Analysis.realLInv x) = (toRL x)⁻¹ := by
  have hinv := Analysis.realLInv_mem hx hpos
  have hne : toRL x ≠ 0 := by
    have := (toRL_lt_iff Analysis.realLZero_mem hx).mp hpos
    rw [toRL_zero] at this
    exact ne_of_gt this
  have hprod : toRL x * toRL (Analysis.realLInv x) = 1 := by
    rw [← toRL_mul hx hinv, Analysis.realLMul_inv hx hpos, toRL_one]
  field_simp at hprod ⊢
  linarith [hprod]

/-- And the quotient, which is the shape `unitOf`'s real-endpoint sibling
`Analysis.unitOfR` is written in: `(x - p) * (q - p)⁻¹`. -/
theorem toRL_realLMul_realLInv {x y : ZFSet.{0}} (hx : x ∈ Analysis.RealL)
    (hy : y ∈ Analysis.RealL)
    (hpos : Analysis.realLLt Analysis.realLZero.{0} y) :
    toRL (Analysis.realLMul x (Analysis.realLInv y)) = toRL x / toRL y := by
  rw [toRL_mul hx (Analysis.realLInv_mem hy hpos), toRL_realLInv hy hpos,
    div_eq_mul_inv]

/-- The real-ended interval crosses. `Analysis.realLIccR` is `realLIcc`'s
widening to real endpoints; this is `toRL_mem_realLIcc_iff` over it, and it is
simpler than that one because there is no `toRat` step --- the endpoints are
already reals on both sides. -/
theorem toRL_mem_realLIccR_iff {p q x : ZFSet.{0}} (hp : p ∈ Analysis.RealL)
    (hq : q ∈ Analysis.RealL) (hx : x ∈ Analysis.RealL) :
    x ∈ Analysis.realLIccR p q ↔ toRL x ∈ Set.Icc (toRL p) (toRL q) := by
  rw [Analysis.mem_realLIccR_iff, Set.mem_Icc]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨(toRL_le_iff hp hx).mp h1, (toRL_le_iff hx hq).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hx, (toRL_le_iff hp hx).mpr h1, (toRL_le_iff hx hq).mpr h2⟩

/-- `Analysis.segUnitR` crosses --- the forward half of the real-endpoint
reparameterisation, read as mathlib's affine map. -/
theorem toRL_segUnitR {p q t : ZFSet.{0}} (hp : p ∈ Analysis.RealL)
    (hq : q ∈ Analysis.RealL) (ht : t ∈ Analysis.RealL) :
    toRL (Analysis.segUnitR p q t) = (toRL q - toRL p) * toRL t + toRL p := by
  have hnp := Analysis.realLNeg_mem hp
  have hw := Analysis.realLAdd_mem hq hnp
  rw [Analysis.segUnitR, toRL_add (Analysis.realLMul_mem hw ht) hp,
    toRL_mul hw ht, toRL_add hq hnp, toRL_neg hp]
  -- `toRL_neg` leaves `q + -p`; the statement says `q - p`. One `ring`.
  ring

/-- And `Analysis.unitOfR`, which is where `toRL_realLInv` is spent. -/
theorem toRL_unitOfR {p q x : ZFSet.{0}} (hp : p ∈ Analysis.RealL)
    (hq : q ∈ Analysis.RealL) (hx : x ∈ Analysis.RealL)
    (hpq : Analysis.realLLt p q) :
    toRL (Analysis.unitOfR p q x) = (toRL x - toRL p) / (toRL q - toRL p) := by
  have hnp := Analysis.realLNeg_mem hp
  have hw := Analysis.realLAdd_mem hq hnp
  have hwpos := Analysis.sub_pos_of_lt hp hq hpq
  rw [Analysis.unitOfR,
    toRL_realLMul_realLInv (Analysis.realLAdd_mem hx hnp) hw hwpos,
    toRL_add hx hnp, toRL_add hq hnp, toRL_neg hp]
  ring

/-- The modulus crosses at real endpoints too.

`uniformlyContinuousOn_liftFun` above with `realLIcc` replaced by
`Analysis.realLIccR` and the `toRat` reading of the endpoints replaced by
`toRL`. The modulus is untouched and still rational: a rational modulus is what
makes the tower's definition constructive, while a rational endpoint is what
made it narrow.

The proof is the same proof. Nothing in it looked at the endpoints except to
place the two points in mathlib's interval, which is the one line that changes.
-/
theorem uniformlyContinuousOnR_liftFun (f : ℝ → ℝ) {p q : ZFSet.{0}}
    (hp : p ∈ Analysis.RealL) (hq : q ∈ Analysis.RealL)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ Set.Icc (toRL p) (toRL q), ∀ y ∈ Set.Icc (toRL p) (toRL q),
        |x - y| ≤ δ → |f x - f y| ≤ ε) :
    Analysis.UniformlyContinuousOnR (liftFun f) p q := by
  intro n
  have hnpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  obtain ⟨δ, hδ, hfδ⟩ := hf _ hnpos
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m, ?_⟩
  intro w x y hw hw0 hwm hx hy hclose
  have hxR := ((Analysis.mem_realLIccR_iff p q x).mp hx).1
  have hyR := ((Analysis.mem_realLIccR_iff p q y).mp hy).1
  have hwR := Analysis.realLOf_mem hw
  have hnQ : NumberTheory.invWidth (NumberTheory.ofNat.{0} n) ∈ NumberTheory.Rat.{0} :=
    NumberTheory.invWidth_mem_Rat (NumberTheory.ofNat_mem_omega n)
  have hmQ : NumberTheory.invWidth (NumberTheory.ofNat.{0} m) ∈ NumberTheory.Rat.{0} :=
    NumberTheory.invWidth_mem_Rat (NumberTheory.ofNat_mem_omega m)
  have hxI := (toRL_mem_realLIccR_iff hp hq hxR).mp hx
  have hyI := (toRL_mem_realLIccR_iff hp hq hyR).mp hy
  have hdist : |toRL x - toRL y| ≤ δ := by
    have h1 := (toRL_close_iff hxR hyR hwR).mp hclose
    rw [toRL_realLOf hw] at h1
    have h2 : ((toRat w hw : ℝ)) ≤ 1 / ((m : ℝ) + 1) := by
      have hq' := toRat_le hw hmQ hwm
      rw [toRat_invWidth m hmQ] at hq'
      have hr : ((toRat w hw : ℝ)) ≤ ((1 / ((m : ℚ) + 1) : ℚ) : ℝ) := Rat.cast_le.mpr hq'
      push_cast at hr
      exact hr
    have h3 : (1 : ℝ) / ((m : ℝ) + 1) ≤ δ := le_of_lt hm
    linarith [h1, h2, h3]
  refine (toRL_close_iff (liftFun_mem f x) (liftFun_mem f y)
    (Analysis.realLOf_mem hnQ)).mpr ?_
  rw [toRL_liftFun, toRL_liftFun, toRL_realLOf hnQ, toRat_invWidth n hnQ]
  have := hfδ _ hxI _ hyI hdist
  push_cast
  exact this

#print axioms toRL_realLInv
#print axioms toRL_realLMul_realLInv
#print axioms toRL_mem_realLIccR_iff
#print axioms toRL_segUnitR
#print axioms toRL_unitOfR
#print axioms uniformlyContinuousOnR_liftFun

#print axioms exists_root_of_lt
#print axioms toRL_realLSum
#print axioms toRL_nonneg_iff
#print axioms toRL_mulNonneg
#print axioms toRL_mul
#print axioms toRL_realLPow
#print axioms toInt_intOfNat
#print axioms toRat_ratNat
#print axioms toRL_bernTerm
#print axioms toRL_bernOp

#print axioms toR
#print axioms cutReals_bddAbove
#print axioms isCut_ofR
#print axioms toR_ofR
#print axioms toR_realAdd
#print axioms toRL_add
#print axioms toRL_neg
#print axioms toRL_mono
#print axioms toRL_max
#print axioms toRL_abs
#print axioms isLocated_ofRL
#print axioms toRL_ofRL
#print axioms toRL_realLOf
#print axioms toR_mono
#print axioms le_toR
#print axioms subset_of_toR_le
#print axioms toR_injective

end Comparator
