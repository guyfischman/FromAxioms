/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
Bridge, rung 2: `Int` to Lean's `ℤ`.

    1  omega  -> Nat      Comparator/Bridge/NatTransfer.lean
    2  Int    -> ℤ        this file
    3  Rat    -> ℚ
    4  RealL  -> ℝ        preserving order and limits

The tower supplies the surjectivity again. `NumberTheory.mem_Int_iff` is

    z ∈ Int ↔ ∃ a ∈ omega, ∃ b ∈ omega, z = intOf a b

--- an integer is a difference of two naturals, as a class of the pair. So rung
2 is rung 1 twice and a subtraction, and the choice is again spent only in
extracting the witnesses.

Why the definition goes through `intOf` and not through `intOfNat`.
`intOfNat` embeds a natural and is injective (`intOfNat_injective`), but it
does not reach the negative integers, so it cannot be inverted on all of `Int`.
`mem_Int_iff` covers everything.

The well-definedness is the content. `intOf a b` is a class of the pair
`(a, b)`, and many pairs give the same integer --- `intOf 3 1` and `intOf 5 3`
are equal. So `toInt` as written picks a representative and the subtraction
`toNat a - toNat b` over `ℤ` is what makes the answer independent of it:
`intOf_eq_iff` in the tower says `intOf a b = intOf c d ↔ a + d = c + b`, which
is exactly `a - b = c - d` after transfer. That equivalence is what
`toInt_spec` below would need, and it is the one thing on this rung that is not
bookkeeping.
-/
-- `Mathlib.Data.Int.Defs` does not exist at the pinned v4.24.0; `Basic` does.
import Mathlib.Data.Int.Basic
-- `Mathlib.Data.Int.Basic` does not bring `ring`.
import Mathlib.Tactic.Ring
import Comparator.Bridge.NatTransfer

namespace Comparator

-- `NumberTheory` is not opened here. It exports `Int`, which then clashes with
-- Lean's own `Int` and every mention becomes `Ambiguous term: ℤ or
-- NumberTheory.Int`. A transfer file names both sides by construction, so it is
-- the one place where opening the tower's namespace cannot work.
open SetTheory

/-- A member of `Int` as a Lean integer, through a representative pair.

`Classical.choose` twice: once for the pair, once inside each `toNat`. The
choice is spent in the comparator, not in the tower. -/
noncomputable def toInt (z : ZFSet) (hz : z ∈ NumberTheory.Int) : ℤ :=
  let h := (NumberTheory.mem_Int_iff z).mp hz
  let a := h.choose
  let hb := h.choose_spec.right
  (toNat a h.choose_spec.left : ℤ) - (toNat hb.choose hb.choose_spec.left : ℤ)

/-- The representative `toInt` picks reconstructs `z`. -/
theorem intOf_toInt (z : ZFSet) (hz : z ∈ NumberTheory.Int) :
    ∃ a ha b hb, z = NumberTheory.intOf a b ∧
      toInt z hz = (toNat a ha : ℤ) - (toNat b hb : ℤ) := by
  refine ⟨((NumberTheory.mem_Int_iff z).mp hz).choose,
    ((NumberTheory.mem_Int_iff z).mp hz).choose_spec.left,
    ((NumberTheory.mem_Int_iff z).mp hz).choose_spec.right.choose,
    ((NumberTheory.mem_Int_iff z).mp hz).choose_spec.right.choose_spec.left, ?_, rfl⟩
  exact ((NumberTheory.mem_Int_iff z).mp hz).choose_spec.right.choose_spec.right

/-- `toInt` carries the tower's order to `≤` on `ℤ`, on representatives.

`intLe_intOf` says the tower's order is subset on the representative sums ---
`intLe (intOf a b) (intOf c d) ↔ add a d ⊆ add c b` --- and
`toInt (intOf a b) = toNat a - toNat b`. So the whole content is that `toNat`
carries `add` to `+` and `⊆` to `≤`, which `NatTransfer` proves; the
rearrangement is `omega`. -/
theorem toInt_le_of_intLe {a b c d : ZFSet}
    (ha : a ∈ SetTheory.omega) (hb : b ∈ SetTheory.omega)
    (hc : c ∈ SetTheory.omega) (hd : d ∈ SetTheory.omega)
    (had : NumberTheory.add a d ∈ SetTheory.omega)
    (hcb : NumberTheory.add c b ∈ SetTheory.omega)
    (h : NumberTheory.intLe (NumberTheory.intOf a b) (NumberTheory.intOf c d)) :
    (toNat a ha : ℤ) - (toNat b hb : ℤ) ≤ (toNat c hc : ℤ) - (toNat d hd : ℤ) := by
  have hle := toNat_le_of_subset _ _ had hcb
    ((NumberTheory.intLe_intOf ha hb hc hd).mp h)
  rw [toNat_add a d ha hd had, toNat_add c b hc hb hcb] at hle
  omega

/-- `toInt` is representative-independent.

`intOf_toInt` names the representative `toInt` happened to choose; this says the
value is the same for any representative, which is what every algebraic lemma
above needs --- `intMul_intOf` hands back a specific pair, and without this there
is no way to compute `toInt` at it.

`intOf_eq_intOf_iff` turns the equality of the two `intOf`s into
`add a d = add c b`, and `toNat_add` carries that to `ℕ`. -/
theorem toInt_intOf {a b : ZFSet} (ha : a ∈ SetTheory.omega)
    (hb : b ∈ SetTheory.omega) (h : NumberTheory.intOf a b ∈ NumberTheory.Int) :
    toInt (NumberTheory.intOf a b) h = (toNat a ha : ℤ) - (toNat b hb : ℤ) := by
  obtain ⟨c, hc, d, hd, heq, hval⟩ := intOf_toInt (NumberTheory.intOf a b) h
  rw [hval]
  -- the two representatives agree: `a + d = c + b`
  have hadd := (NumberTheory.intOf_eq_intOf_iff ha hb hc hd).mp heq
  -- through `ofNat_injective` again: `toNat`'s proof argument depends on the
  -- set, so neither `congrArg` nor a rewrite can move between the two sides
  have hn : toNat (NumberTheory.add a d) (NumberTheory.add_mem_omega ha hd)
      = toNat (NumberTheory.add c b) (NumberTheory.add_mem_omega hc hb) := by
    -- `NumberTheory` is not opened in this file (its `Int` clashes
    -- with Lean's), so every tower name here is qualified
    apply NumberTheory.ofNat_injective
    rw [ofNat_toNat, ofNat_toNat]
    exact hadd
  rw [toNat_add a d ha hd, toNat_add c b hc hb] at hn
  omega

/-- `toInt` carries `intMul` to `*`, on representatives.

`intMul_intOf` is the representative formula
`(a - b)(c - d) = (ac + bd) - (ad + bc)`, and `toNat_mul`/`toNat_add` carry
each side; the rearrangement over `ℤ` is `ring`. -/
theorem toInt_mul_intOf {a b c d : ZFSet}
    (ha : a ∈ SetTheory.omega) (hb : b ∈ SetTheory.omega)
    (hc : c ∈ SetTheory.omega) (hd : d ∈ SetTheory.omega)
    (hac : NumberTheory.mul a c ∈ SetTheory.omega)
    (hbd : NumberTheory.mul b d ∈ SetTheory.omega)
    (had : NumberTheory.mul a d ∈ SetTheory.omega)
    (hbc : NumberTheory.mul b c ∈ SetTheory.omega)
    (h1 : NumberTheory.add (NumberTheory.mul a c) (NumberTheory.mul b d)
      ∈ SetTheory.omega)
    (h2 : NumberTheory.add (NumberTheory.mul a d) (NumberTheory.mul b c)
      ∈ SetTheory.omega) :
    ((toNat _ h1 : ℤ) - (toNat _ h2 : ℤ))
      = ((toNat a ha : ℤ) - (toNat b hb : ℤ))
        * ((toNat c hc : ℤ) - (toNat d hd : ℤ)) := by
  rw [toNat_add _ _ hac hbd h1, toNat_add _ _ had hbc h2,
    toNat_mul a c ha hc hac, toNat_mul b d hb hd hbd,
    toNat_mul a d ha hd had, toNat_mul b c hb hc hbc]
  push_cast
  ring

/-- `toInt` carries the tower's order to `≤`, at arbitrary members of `Int`.

The general form of `toInt_le_of_intLe`. `intOf_toInt` names each side's chosen
representative and its value, and `add_mem_omega` supplies the two closure
facts. -/
theorem toInt_le {z w : ZFSet} (hz : z ∈ NumberTheory.Int)
    (hw : w ∈ NumberTheory.Int) (h : NumberTheory.intLe z w) :
    toInt z hz ≤ toInt w hw := by
  obtain ⟨a, ha, b, hb, hzab, hval⟩ := intOf_toInt z hz
  obtain ⟨c, hc, d, hd, hwcd, hval'⟩ := intOf_toInt w hw
  rw [hval, hval']
  refine toInt_le_of_intLe ha hb hc hd
    (NumberTheory.add_mem_omega ha hd) (NumberTheory.add_mem_omega hc hb) ?_
  rw [← hzab, ← hwcd]
  exact h

/-- `toInt` carries `intMul` to `*`, at arbitrary members of `Int`.

The general form of `toInt_mul_intOf`, standing to it exactly as `toInt_le`
stands to `toInt_le_of_intLe`: `intOf_toInt` names each side's representative,
`intMul_intOf` computes the product at those representatives,
and `toInt_intOf` evaluates `toInt` there --- which is the step that needs
representative-independence, since the product's own representative is not the
one `toInt` would have chosen.

`toRat_le` needs `toInt` to commute with `intMul`, to read `ratLe_ratOf`'s
cross-multiplication `intLe (a*d) (c*b)` as an inequality between Lean
rationals. -/
theorem toInt_mul {z w : ZFSet} (hz : z ∈ NumberTheory.Int)
    (hw : w ∈ NumberTheory.Int)
    (hzw : NumberTheory.intMul z w ∈ NumberTheory.Int) :
    toInt (NumberTheory.intMul z w) hzw = toInt z hz * toInt w hw := by
  obtain ⟨a, ha, b, hb, hzab, hval⟩ := intOf_toInt z hz
  obtain ⟨c, hc, d, hd, hwcd, hval'⟩ := intOf_toInt w hw
  have hac := NumberTheory.mul_mem_omega ha hc
  have hbd := NumberTheory.mul_mem_omega hb hd
  have had := NumberTheory.mul_mem_omega ha hd
  have hbc := NumberTheory.mul_mem_omega hb hc
  have h1 := NumberTheory.add_mem_omega hac hbd
  have h2 := NumberTheory.add_mem_omega had hbc
  have hprod : NumberTheory.intMul z w
      = NumberTheory.intOf (NumberTheory.add (NumberTheory.mul a c)
          (NumberTheory.mul b d))
        (NumberTheory.add (NumberTheory.mul a d) (NumberTheory.mul b c)) := by
    rw [hzab, hwcd, NumberTheory.intMul_intOf ha hb hc hd]
  rw [hval, hval']
  -- `toInt` at the product's representative, which is not the one it chose.
  have := toInt_intOf h1 h2 (hprod ▸ hzw)
  rw [show toInt (NumberTheory.intMul z w) hzw
      = toInt (NumberTheory.intOf (NumberTheory.add (NumberTheory.mul a c)
          (NumberTheory.mul b d))
        (NumberTheory.add (NumberTheory.mul a d) (NumberTheory.mul b c)))
        (hprod ▸ hzw) from by congr 1, this]
  exact toInt_mul_intOf ha hb hc hd hac hbd had hbc h1 h2

/-- `toInt` carries `intAdd` to `+`, at arbitrary members of `Int`.

The additive twin of `toInt_mul`, and simpler: `intAdd_intOf` is
`intOf a b + intOf c d = intOf (a+c) (b+d)`, so once `toInt_intOf` evaluates at
that representative the rearrangement is `omega`.

`toRat_add` needs this: `ratAdd_ratOf` expresses the rational sum through
`intAdd` and `intMul` at the numerators, so both integer operations have to
cross before the rational one can. -/
theorem toInt_add {z w : ZFSet} (hz : z ∈ NumberTheory.Int)
    (hw : w ∈ NumberTheory.Int)
    (hzw : NumberTheory.intAdd z w ∈ NumberTheory.Int) :
    toInt (NumberTheory.intAdd z w) hzw = toInt z hz + toInt w hw := by
  obtain ⟨a, ha, b, hb, hzab, hval⟩ := intOf_toInt z hz
  obtain ⟨c, hc, d, hd, hwcd, hval'⟩ := intOf_toInt w hw
  have hac := NumberTheory.add_mem_omega ha hc
  have hbd := NumberTheory.add_mem_omega hb hd
  have hsum : NumberTheory.intAdd z w
      = NumberTheory.intOf (NumberTheory.add a c) (NumberTheory.add b d) := by
    rw [hzab, hwcd, NumberTheory.intAdd_intOf ha hb hc hd]
  rw [hval, hval']
  have h := toInt_intOf hac hbd (hsum ▸ hzw)
  rw [show toInt (NumberTheory.intAdd z w) hzw
      = toInt (NumberTheory.intOf (NumberTheory.add a c) (NumberTheory.add b d))
        (hsum ▸ hzw) from by congr 1, h,
    toNat_add a c ha hc hac, toNat_add b d hb hd hbd]
  omega

/-- `toInt` is injective. Two members with the same Lean value are the same
set --- the representative sums agree, so `intOf_eq_intOf_iff` closes it. -/
theorem toInt_injective {z w : ZFSet} (hz : z ∈ NumberTheory.Int)
    (hw : w ∈ NumberTheory.Int) (h : toInt z hz = toInt w hw) : z = w := by
  obtain ⟨a, ha, b, hb, hzab, hval⟩ := intOf_toInt z hz
  obtain ⟨c, hc, d, hd, hwcd, hval'⟩ := intOf_toInt w hw
  rw [hval, hval'] at h
  have had := NumberTheory.add_mem_omega ha hd
  have hcb := NumberTheory.add_mem_omega hc hb
  have hn : NumberTheory.add a d = NumberTheory.add c b := by
    refine toNat_injective had hcb ?_
    rw [toNat_add a d ha hd had, toNat_add c b hc hb hcb]
    omega
  rw [hzab, hwcd]
  exact (NumberTheory.intOf_eq_intOf_iff ha hb hc hd).mpr hn

/-- `toInt` sends the tower's zero to `0`. -/
theorem toInt_zero (h : NumberTheory.intZero ∈ NumberTheory.Int) :
    toInt NumberTheory.intZero h = 0 := by
  have hz : NumberTheory.intZero
      = NumberTheory.intOf (NumberTheory.ofNat 0) (NumberTheory.ofNat 0) := rfl
  rw [show toInt NumberTheory.intZero h
      = toInt (NumberTheory.intOf (NumberTheory.ofNat 0) (NumberTheory.ofNat 0))
        (hz ▸ h) from by congr 1,
    toInt_intOf (NumberTheory.ofNat_mem_omega 0) (NumberTheory.ofNat_mem_omega 0),
    toNat_ofNat 0]
  simp

/-- A positive member has a positive value, so the division in `toRat` is by a
nonzero denominator.

`intPositive` is `intNonneg` and `≠ intZero`; the first gives `0 ≤` through
`toInt_le` against `toInt_zero`, and the second gives `≠ 0` through
`toInt_injective`. -/
theorem toInt_pos {b : ZFSet} (hb : b ∈ NumberTheory.intPositive) :
    0 < toInt b (NumberTheory.intPositive_subset _ hb) := by
  obtain ⟨-, -, hne⟩ := (NumberTheory.mem_intPositive_iff b).mp hb
  have hz : NumberTheory.intZero ∈ NumberTheory.Int := NumberTheory.intZero_mem_Int
  have hle : toInt NumberTheory.intZero hz
      ≤ toInt b (NumberTheory.intPositive_subset _ hb) :=
    toInt_le hz _ (NumberTheory.intZero_le_of_intPositive hb)
  rw [toInt_zero] at hle
  refine lt_of_le_of_ne hle (fun heq => hne ?_)
  exact (toInt_injective (NumberTheory.intPositive_subset _ hb) hz
    (by rw [toInt_zero, ← heq]))

end Comparator
