/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
Bridge, rung 3: `Rat` to Lean's `ℚ`.

    1  omega  -> Nat      Comparator/Bridge/NatTransfer.lean
    2  Int    -> ℤ        Comparator/Bridge/IntTransfer.lean
    3  Rat    -> ℚ        this file
    4  RealL  -> ℝ        preserving order and limits

The three rungs have the same shape. Each level of the tower is a quotient of
pairs from the level below, each carries a `mem_..._iff` giving surjectivity
onto representatives, and each carries an equality law saying when two
representatives agree:

    mem_omega_iff       x ∈ omega ↔ ∃ n : Nat, x = ofNat n
    mem_Int_iff         z ∈ Int   ↔ ∃ a b ∈ omega, z = intOf a b
                        intOf a b = intOf c d ↔ a + d = c + b
    mem_Rat_iff         r ∈ Rat   ↔ ∃ a ∈ Int, ∃ b ∈ intPositive, r = ratOf a b
                        ratOf a b = ratOf c d ↔ a * d = c * b

So the transfer at each level is: choose a representative, transfer its
components, and combine them with the operation the quotient was taken over ---
a subtraction at rung 2, a division at rung 3. The equality law is what makes
the result independent of the representative, and it is the only content.

Rung 4 is not this shape. `RealL` is not a quotient of pairs of rationals;
`mem_RealL_iff` gives `z = opair L U` with `IsLocated L U`, a located cut.
There is no representative to transfer componentwise.

`Analysis.toCut` with `toCut_add`, `toCut_mul`, `toCut_le` and
`toCut_injective`, takes `RealL → Real` internally, so the comparator never
sees a located pair. What is left is `Real → ℝ`, and a Dedekind cut becomes a
Lean real by taking a supremum: no Cauchy sequence, no `invScale`, no
completion. `Comparator/Bridge/RealTransfer.lean` is that, and its floor is
that the supremum exists --- `IsCut.nonempty` and `IsCut.proper` read through
this file, so `toRat_le` below is the last rung under it.
-/
import Mathlib.Data.Rat.Defs
-- `div_eq_div_iff` is in `Rat.Defs`; `div_le_div_iff` is not.
import Mathlib.Algebra.Order.Field.Basic
-- The order instances for `ℚ` are a separate import from the lemma that uses
-- them, and the module is `Algebra/Order/Field/Rat`.
import Mathlib.Algebra.Order.Field.Rat
-- `linarith` is its own module.
import Mathlib.Tactic.Linarith
import Comparator.Bridge.IntTransfer

namespace Comparator

open SetTheory

/-- A member of `Rat` as a Lean rational, through a representative pair.

The denominator lies in `intPositive`, so it is nonzero and the division is the
honest one; `ratOf_eq_ratOf_iff` --- `a * d = c * b` --- is what makes the
value independent of the representative chosen. -/
noncomputable def toRat (r : ZFSet) (hr : r ∈ NumberTheory.Rat) : ℚ :=
  let h := (NumberTheory.mem_Rat_iff r).mp hr
  let hb := h.choose_spec.right
  (toInt h.choose h.choose_spec.left : ℚ) /
    (toInt hb.choose (NumberTheory.intPositive_subset _ hb.choose_spec.left) : ℚ)

/-- The representative `toRat` picks reconstructs `r`. -/
theorem ratOf_toRat (r : ZFSet) (hr : r ∈ NumberTheory.Rat) :
    ∃ a b, a ∈ NumberTheory.Int ∧ b ∈ NumberTheory.intPositive ∧ r = NumberTheory.ratOf a b := by
  refine ⟨((NumberTheory.mem_Rat_iff r).mp hr).choose,
    ((NumberTheory.mem_Rat_iff r).mp hr).choose_spec.right.choose,
    ((NumberTheory.mem_Rat_iff r).mp hr).choose_spec.left,
    ((NumberTheory.mem_Rat_iff r).mp hr).choose_spec.right.choose_spec.left, ?_⟩
  exact ((NumberTheory.mem_Rat_iff r).mp hr).choose_spec.right.choose_spec.right

/-- The representative `toRat` picks, with the value it produces there.

The rung-3 counterpart of `intOf_toInt`: the pair together with the value
equation, which destructuring `ratOf_toRat` loses. -/
theorem toRat_val (r : ZFSet) (hr : r ∈ NumberTheory.Rat) :
    ∃ (a b : ZFSet) (ha : a ∈ NumberTheory.Int) (hb : b ∈ NumberTheory.intPositive),
      r = NumberTheory.ratOf a b ∧
      toRat r hr
        = (toInt a ha : ℚ) / (toInt b (NumberTheory.intPositive_subset _ hb) : ℚ) :=
  ⟨((NumberTheory.mem_Rat_iff r).mp hr).choose,
   ((NumberTheory.mem_Rat_iff r).mp hr).choose_spec.right.choose,
   ((NumberTheory.mem_Rat_iff r).mp hr).choose_spec.left,
   ((NumberTheory.mem_Rat_iff r).mp hr).choose_spec.right.choose_spec.left,
   ((NumberTheory.mem_Rat_iff r).mp hr).choose_spec.right.choose_spec.right,
   rfl⟩

/-- `toRat` is representative-independent, the rung-3 counterpart of
`toInt_intOf`.

`ratOf_toRat` names the pair `toRat` happened to choose; this computes `toRat`
at any representative, which every lemma below needs because `ratLe_ratOf`
hands back a specific pair. `ratOf_eq_ratOf_iff` turns the equality of the two
`ratOf`s into the cross-multiplication `a * d = c * b`, `toInt_mul` carries
that to `ℤ`, and the two denominators are nonzero by `toInt_pos`, so the
division is honest and `field_simp` finishes. -/
theorem toRat_ratOf {a b : ZFSet} (ha : a ∈ NumberTheory.Int)
    (hb : b ∈ NumberTheory.intPositive)
    (h : NumberTheory.ratOf a b ∈ NumberTheory.Rat) :
    toRat (NumberTheory.ratOf a b) h
      = (toInt a ha : ℚ) / (toInt b (NumberTheory.intPositive_subset _ hb) : ℚ) := by
  obtain ⟨c, d, hc, hd, heq, hval⟩ := toRat_val (NumberTheory.ratOf a b) h
  have hbI := NumberTheory.intPositive_subset _ hb
  have hdI := NumberTheory.intPositive_subset _ hd
  have hcross : NumberTheory.intMul a d = NumberTheory.intMul c b :=
    (NumberTheory.ratOf_eq_ratOf_iff ha hb hc hd).mp heq
  have hZ : (toInt a ha : ℤ) * toInt d hdI = toInt c hc * toInt b hbI := by
    have h1 := toInt_mul ha hdI (NumberTheory.intMul_mem_Int ha hdI)
    have h2 := toInt_mul hc hbI (NumberTheory.intMul_mem_Int hc hbI)
    rw [← h1, ← h2]
    congr 1
  have hbne : (toInt b hbI : ℚ) ≠ 0 := by
    exact_mod_cast (toInt_pos hb).ne'
  have hdne : (toInt d hdI : ℚ) ≠ 0 := by
    exact_mod_cast (toInt_pos hd).ne'
  rw [hval, div_eq_div_iff hdne hbne]
  exact_mod_cast hZ.symm

/-- `toRat` carries the tower's order to `≤` on `ℚ`.

This is the last rung below `Real → ℝ`. A Dedekind cut is a set of tower
rationals, and turning it into a Lean real means taking a supremum of
`{toRat q | q ∈ c}`; that set is bounded above exactly because `IsCut.proper`
supplies a rational outside the cut, and reading outside as *an upper bound
in `ℚ`* is this lemma.

`ratLe_ratOf` says the tower's order on representatives is the
cross-multiplication `intLe (a*d) (c*b)`; `toInt_le` carries that to `ℤ`,
`toInt_mul` expands both products, and `div_le_div_iff` turns it back into an
inequality of quotients. Positivity of the two denominators is `toInt_pos`, and
it is needed twice: once for the direction of `div_le_div_iff` and once for the
divisions to be honest at all. -/
theorem toRat_le {r s : ZFSet} (hr : r ∈ NumberTheory.Rat)
    (hs : s ∈ NumberTheory.Rat) (h : NumberTheory.ratLe r s) :
    toRat r hr ≤ toRat s hs := by
  obtain ⟨a, b, ha, hb, hrab, hvalr⟩ := toRat_val r hr
  obtain ⟨c, d, hc, hd, hscd, hvals⟩ := toRat_val s hs
  have hbI := NumberTheory.intPositive_subset _ hb
  have hdI := NumberTheory.intPositive_subset _ hd
  have hcross : NumberTheory.intLe (NumberTheory.intMul a d) (NumberTheory.intMul c b) := by
    refine (NumberTheory.ratLe_ratOf ha hb hc hd).mp ?_
    rw [← hrab, ← hscd]
    exact h
  have hZ : (toInt a ha : ℤ) * toInt d hdI ≤ toInt c hc * toInt b hbI := by
    have h1 := toInt_mul ha hdI (NumberTheory.intMul_mem_Int ha hdI)
    have h2 := toInt_mul hc hbI (NumberTheory.intMul_mem_Int hc hbI)
    rw [← h1, ← h2]
    exact toInt_le _ _ hcross
  have hbpos : (0 : ℚ) < (toInt b hbI : ℚ) := by exact_mod_cast toInt_pos hb
  have hdpos : (0 : ℚ) < (toInt d hdI : ℚ) := by exact_mod_cast toInt_pos hd
  -- At this pin the name is `div_le_div_iff₀`.
  rw [hvalr, hvals, div_le_div_iff₀ hbpos hdpos]
  exact_mod_cast hZ

/-- `toRat` is injective, the rung-3 counterpart of `toInt_injective`.

Cross-multiplying the two quotients gives `toInt a * toInt d = toInt c * toInt b`
in `ℤ`; `toInt_mul` folds each side back into a single `toInt`, `toInt_injective`
lifts the equation to the tower, and `ratOf_eq_ratOf_iff` reads it as equality of
the two `ratOf`s. -/
theorem toRat_injective {r s : ZFSet} (hr : r ∈ NumberTheory.Rat)
    (hs : s ∈ NumberTheory.Rat) (h : toRat r hr = toRat s hs) : r = s := by
  obtain ⟨a, b, ha, hb, hrab, hvalr⟩ := toRat_val r hr
  obtain ⟨c, d, hc, hd, hscd, hvals⟩ := toRat_val s hs
  have hbI := NumberTheory.intPositive_subset _ hb
  have hdI := NumberTheory.intPositive_subset _ hd
  have hbne : (toInt b hbI : ℚ) ≠ 0 := by exact_mod_cast (toInt_pos hb).ne'
  have hdne : (toInt d hdI : ℚ) ≠ 0 := by exact_mod_cast (toInt_pos hd).ne'
  rw [hvalr, hvals, div_eq_div_iff hbne hdne] at h
  have hZ : (toInt a ha : ℤ) * toInt d hdI = toInt c hc * toInt b hbI := by
    exact_mod_cast h
  have hcross : NumberTheory.intMul a d = NumberTheory.intMul c b := by
    refine toInt_injective (NumberTheory.intMul_mem_Int ha hdI)
      (NumberTheory.intMul_mem_Int hc hbI) ?_
    rw [toInt_mul ha hdI, toInt_mul hc hbI]
    exact hZ
  rw [hrab, hscd]
  exact (NumberTheory.ratOf_eq_ratOf_iff ha hb hc hd).mpr hcross

/-- `toRat` carries the tower's strict order to `<`.

`ratLe_of_lt` gives `≤` through `toRat_le`; the two values differ because
`toRat` is injective and `ratLt_irrefl` forbids `r = s`. Stated because the cut
lemmas above `Real → ℝ` need strictness: `IsCut.no_greatest` produces a member
strictly above, and a non-strict bound there would not place the smaller
rational below the supremum. -/
theorem toRat_lt {r s : ZFSet} (hr : r ∈ NumberTheory.Rat)
    (hs : s ∈ NumberTheory.Rat) (h : NumberTheory.ratLt r s) :
    toRat r hr < toRat s hs := by
  refine lt_of_le_of_ne (toRat_le hr hs (NumberTheory.ratLe_of_lt hr hs h)) ?_
  intro heq
  exact NumberTheory.ratLt_irrefl (toRat_injective hr hs heq ▸ h)

/-- `toRat` carries `ratAdd` to `+`.

`ratAdd_ratOf` is `ratOf a b + ratOf c d = ratOf (a*d + c*b) (b*d)`, so the
numerator crosses by `toInt_add` and `toInt_mul` and the denominator by
`toInt_mul` --- both integer operations, so `toInt_add` comes first.

`div_add_div` needs both denominators nonzero, and `toInt_pos` supplies that at
`b`, `d` and their product. -/
theorem toRat_add {r s : ZFSet} (hr : r ∈ NumberTheory.Rat)
    (hs : s ∈ NumberTheory.Rat)
    (hrs : NumberTheory.ratAdd r s ∈ NumberTheory.Rat) :
    toRat (NumberTheory.ratAdd r s) hrs = toRat r hr + toRat s hs := by
  obtain ⟨a, b, ha, hb, hrab, hvalr⟩ := toRat_val r hr
  obtain ⟨c, d, hc, hd, hscd, hvals⟩ := toRat_val s hs
  have hbI := NumberTheory.intPositive_subset _ hb
  have hdI := NumberTheory.intPositive_subset _ hd
  have hbd : NumberTheory.intMul b d ∈ NumberTheory.intPositive :=
    NumberTheory.intMul_mem_intPositive hb hd
  have hbdI := NumberTheory.intPositive_subset _ hbd
  have hnum : NumberTheory.intAdd (NumberTheory.intMul a d) (NumberTheory.intMul c b)
      ∈ NumberTheory.Int :=
    NumberTheory.intAdd_mem_Int (NumberTheory.intMul_mem_Int ha hdI)
      (NumberTheory.intMul_mem_Int hc hbI)
  have hsum : NumberTheory.ratAdd r s
      = NumberTheory.ratOf
          (NumberTheory.intAdd (NumberTheory.intMul a d) (NumberTheory.intMul c b))
          (NumberTheory.intMul b d) := by
    rw [hrab, hscd, NumberTheory.ratAdd_ratOf ha hb hc hd]
  have hval : toRat (NumberTheory.ratAdd r s) hrs
      = (toInt _ hnum : ℚ) / (toInt _ hbdI : ℚ) := by
    rw [show toRat (NumberTheory.ratAdd r s) hrs
        = toRat (NumberTheory.ratOf
            (NumberTheory.intAdd (NumberTheory.intMul a d) (NumberTheory.intMul c b))
            (NumberTheory.intMul b d)) (hsum ▸ hrs) from by congr 1]
    exact toRat_ratOf hnum hbd _
  rw [hval, hvalr, hvals,
    toInt_add (NumberTheory.intMul_mem_Int ha hdI) (NumberTheory.intMul_mem_Int hc hbI),
    toInt_mul ha hdI, toInt_mul hc hbI, toInt_mul hbI hdI]
  have hbne : (toInt b hbI : ℚ) ≠ 0 := by exact_mod_cast (toInt_pos hb).ne'
  have hdne : (toInt d hdI : ℚ) ≠ 0 := by exact_mod_cast (toInt_pos hd).ne'
  push_cast
  rw [div_add_div _ _ hbne hdne]
  ring_nf

/-- `toRat` carries `ratMul` to `*`.

`ratMul_ratOf` is `ratOf a b * ratOf c d = ratOf (a*c) (b*d)`
--- numerator and denominator each a single `intMul`, so this needs only
`toInt_mul` where `toRat_add` needed `toInt_add` as well.

The rung below cut multiplication. `Analysis.realMulNonneg` is a separation whose
members are the rationals below a product of non-negative members, together with
every negative rational; reading that set through `toRat` needs the product of
two rationals to cross, which is this. -/
theorem toRat_mul {r s : ZFSet} (hr : r ∈ NumberTheory.Rat)
    (hs : s ∈ NumberTheory.Rat)
    (hrs : NumberTheory.ratMul r s ∈ NumberTheory.Rat) :
    toRat (NumberTheory.ratMul r s) hrs = toRat r hr * toRat s hs := by
  obtain ⟨a, b, ha, hb, hrab, hvalr⟩ := toRat_val r hr
  obtain ⟨c, d, hc, hd, hscd, hvals⟩ := toRat_val s hs
  have hbI := NumberTheory.intPositive_subset _ hb
  have hdI := NumberTheory.intPositive_subset _ hd
  have hbd : NumberTheory.intMul b d ∈ NumberTheory.intPositive :=
    NumberTheory.intMul_mem_intPositive hb hd
  have hbdI := NumberTheory.intPositive_subset _ hbd
  have hac : NumberTheory.intMul a c ∈ NumberTheory.Int :=
    NumberTheory.intMul_mem_Int ha hc
  have hprod : NumberTheory.ratMul r s
      = NumberTheory.ratOf (NumberTheory.intMul a c) (NumberTheory.intMul b d) := by
    rw [hrab, hscd, NumberTheory.ratMul_ratOf ha hb hc hd]
  have hval : toRat (NumberTheory.ratMul r s) hrs
      = (toInt _ hac : ℚ) / (toInt _ hbdI : ℚ) := by
    rw [show toRat (NumberTheory.ratMul r s) hrs
        = toRat (NumberTheory.ratOf (NumberTheory.intMul a c) (NumberTheory.intMul b d))
          (hprod ▸ hrs) from by congr 1]
    exact toRat_ratOf hac hbd _
  rw [hval, hvalr, hvals, toInt_mul ha hc, toInt_mul hbI hdI]
  push_cast
  rw [div_mul_div_comm]

/-! ### The other direction

Everything above pushes the tower's rationals into `ℚ`. Rung 4's surjectivity
needs the reverse --- a cut is carved out by the Lean rationals below a real, and
each of those has to name a member of the tower's `Rat`. -/

/-- A Lean rational as a member of `Rat`, through its numerator and
denominator.

`q.den` is positive by construction (`q.pos`), so the denominator lies in
`intPositive` and `ratOf` applies. -/
noncomputable def ratOfLean (q : ℚ) : ZFSet.{0} :=
  NumberTheory.ratOf (NumberTheory.intOfLean q.num) (NumberTheory.intOfLean (q.den : ℤ))

/-- The denominator lands in `intPositive`, which `ratOf` requires and which
`toRat`'s division needs to be honest. -/
theorem intOfLean_den_mem (q : ℚ) :
    NumberTheory.intOfLean.{0} (q.den : ℤ) ∈ NumberTheory.intPositive.{0} := by
  rw [NumberTheory.intOfLean_eq_intOf (m := q.den) (n := 0) (by simp)]
  exact NumberTheory.ofNat_mem_intPositive q.pos

theorem ratOfLean_mem (q : ℚ) : ratOfLean q ∈ NumberTheory.Rat.{0} :=
  NumberTheory.ratOf_mem_Rat (NumberTheory.intOfLean_mem_Int _) (intOfLean_den_mem q)

/-- `toInt` inverts `intOfLean`, which the round trip below needs at both the
numerator and the denominator. -/
theorem toInt_intOfLean (k : ℤ) :
    toInt (NumberTheory.intOfLean.{0} k) (NumberTheory.intOfLean_mem_Int k) = k := by
  -- `intOfLean` is a plain `def`, so the unfolding is by `have` rather than `rw`.
  have h : toInt (NumberTheory.intOfLean.{0} k) (NumberTheory.intOfLean_mem_Int k)
      = (toNat (NumberTheory.ofNat k.toNat) (NumberTheory.ofNat_mem_omega _) : ℤ)
        - (toNat (NumberTheory.ofNat (-k).toNat) (NumberTheory.ofNat_mem_omega _) : ℤ) :=
    toInt_intOf (NumberTheory.ofNat_mem_omega _) (NumberTheory.ofNat_mem_omega _)
      (NumberTheory.intOfLean_mem_Int k)
  rw [h, toNat_ofNat, toNat_ofNat]
  omega

/-- The round trip. `toRat` inverts `ratOfLean`, so every Lean rational is
the value of a tower rational --- which is what rung 4's surjectivity needs to
carve a cut out of the rationals below a real. -/
theorem toRat_ratOfLean (q : ℚ) : toRat (ratOfLean q) (ratOfLean_mem q) = q := by
  have hval : toRat (ratOfLean q) (ratOfLean_mem q)
      = (toInt (NumberTheory.intOfLean q.num) (NumberTheory.intOfLean_mem_Int _) : ℚ)
        / (toInt (NumberTheory.intOfLean (q.den : ℤ))
            (NumberTheory.intPositive_subset _ (intOfLean_den_mem q)) : ℚ) :=
    toRat_ratOf (NumberTheory.intOfLean_mem_Int _) (intOfLean_den_mem q) (ratOfLean_mem q)
  rw [hval, toInt_intOfLean, toInt_intOfLean]
  rw [show ((q.den : ℤ) : ℚ) = (q.den : ℚ) from by push_cast; ring]
  exact_mod_cast Rat.num_div_den q

/-- `toRat` carries its membership proof as an argument, so rewriting the set inside
it is a dependent rewrite: `rw [h]` cannot retype the proof.

`subst` plus proof irrelevance closes it in one line, and the membership
arguments then never have to match syntactically. -/
theorem toRat_congr {r s : ZFSet} (hr : r ∈ NumberTheory.Rat)
    (hs : s ∈ NumberTheory.Rat) (h : r = s) : toRat r hr = toRat s hs := by
  subst h; rfl

/-- The round trip the other way. By injectivity rather than by computation:
`toRat (ratOfLean (toRat r)) = toRat r`, so the two sets agree. -/
theorem ratOfLean_toRat {r : ZFSet} (hr : r ∈ NumberTheory.Rat) :
    ratOfLean (toRat r hr) = r :=
  toRat_injective (ratOfLean_mem _) hr (toRat_ratOfLean _)

/-- `toRat` sends the tower's zero to `0` --- without computing it, by the same
doubling argument `toRL_zero` uses one layer up. -/
theorem toRat_zero : toRat NumberTheory.ratZero.{0} NumberTheory.ratZero_mem_Rat = 0 := by
  have hz : NumberTheory.ratZero.{0} ∈ NumberTheory.Rat.{0} := NumberTheory.ratZero_mem_Rat
  have h := toRat_add hz hz (NumberTheory.ratAdd_mem_Rat hz hz)
  rw [toRat_congr (NumberTheory.ratAdd_mem_Rat hz hz) hz
    (NumberTheory.ratZero_add hz)] at h
  linarith

/-- Negation crosses, from the group law rather than from a formula. -/
theorem toRat_neg {r : ZFSet.{0}} (hr : r ∈ NumberTheory.Rat.{0}) :
    toRat (NumberTheory.ratNeg r) (NumberTheory.ratNeg_mem_Rat hr) = -toRat r hr := by
  have hz : NumberTheory.ratZero.{0} ∈ NumberTheory.Rat.{0} := NumberTheory.ratZero_mem_Rat
  have h := toRat_add hr (NumberTheory.ratNeg_mem_Rat hr)
    (NumberTheory.ratAdd_mem_Rat hr (NumberTheory.ratNeg_mem_Rat hr))
  rw [toRat_congr (NumberTheory.ratAdd_mem_Rat hr (NumberTheory.ratNeg_mem_Rat hr)) hz
    (NumberTheory.ratAdd_neg hr), toRat_zero] at h
  linarith

/-! ### Order and arithmetic pushed the other way

`toRat_le` and `toRat_lt` read the tower's order in `ℚ`. Building a tower object
from Lean data --- a `ratSeqs` member out of a `Nat → ℚ`, say --- needs the
converses, and each is the forward lemma plus trichotomy. -/

/-- `ratOfLean 0` is the tower's zero --- by injectivity, since both send to `0`.
Needed wherever a sign condition stated in the tower (`ratLe ratZero q`) has to be
produced from `0 ≤ q` in `ℚ`. -/
theorem ratOfLean_zero : ratOfLean 0 = NumberTheory.ratZero.{0} :=
  toRat_injective (ratOfLean_mem 0) NumberTheory.ratZero_mem_Rat
    (by rw [toRat_ratOfLean, toRat_zero])

theorem ratOfLean_lt {p q : ℚ} (h : p < q) :
    NumberTheory.ratLt (ratOfLean p) (ratOfLean q) := by
  by_contra hn
  have hle := NumberTheory.ratLe_of_not_lt (ratOfLean_mem q) (ratOfLean_mem p) hn
  have := toRat_le (ratOfLean_mem q) (ratOfLean_mem p) hle
  rw [toRat_ratOfLean, toRat_ratOfLean] at this
  linarith

theorem ratOfLean_le {p q : ℚ} (h : p ≤ q) :
    NumberTheory.ratLe (ratOfLean p) (ratOfLean q) := by
  refine NumberTheory.ratLe_of_not_lt (ratOfLean_mem p) (ratOfLean_mem q) ?_
  intro hlt
  have := toRat_lt (ratOfLean_mem q) (ratOfLean_mem p) hlt
  rw [toRat_ratOfLean, toRat_ratOfLean] at this
  linarith

theorem ratOfLean_add (p q : ℚ) :
    NumberTheory.ratAdd (ratOfLean p) (ratOfLean q) = ratOfLean (p + q) := by
  refine toRat_injective
    (NumberTheory.ratAdd_mem_Rat (ratOfLean_mem p) (ratOfLean_mem q))
    (ratOfLean_mem _) ?_
  rw [toRat_add (ratOfLean_mem p) (ratOfLean_mem q), toRat_ratOfLean,
    toRat_ratOfLean, toRat_ratOfLean]

theorem ratOfLean_mul (p q : ℚ) :
    NumberTheory.ratMul (ratOfLean p) (ratOfLean q) = ratOfLean (p * q) := by
  refine toRat_injective
    (NumberTheory.ratMul_mem_Rat (ratOfLean_mem p) (ratOfLean_mem q))
    (ratOfLean_mem _) ?_
  rw [toRat_mul (ratOfLean_mem p) (ratOfLean_mem q), toRat_ratOfLean,
    toRat_ratOfLean, toRat_ratOfLean]

theorem ratOfLean_neg (p : ℚ) :
    NumberTheory.ratNeg (ratOfLean p) = ratOfLean (-p) := by
  refine toRat_injective (NumberTheory.ratNeg_mem_Rat (ratOfLean_mem p))
    (ratOfLean_mem _) ?_
  rw [toRat_neg (ratOfLean_mem p), toRat_ratOfLean, toRat_ratOfLean]

/-- The width, as the tower spells it. `IsNested.shrink` states the interval
width as `ratAdd (b N) (ratNeg (a N))`, so a Lean subtraction has to be
assembled from the two lemmas above rather than transported by one. -/
theorem ratOfLean_sub (p q : ℚ) :
    NumberTheory.ratAdd (ratOfLean p) (NumberTheory.ratNeg (ratOfLean q))
      = ratOfLean (p - q) := by
  rw [ratOfLean_neg, ratOfLean_add]
  congr 1
  ring

end Comparator
