/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# ℝ is uncountable.

The diagonal is geometric rather than digitwise: walk down the thirds of `[0,1]`
so that stage `n` steps clear of the `n`-th real. The digit sequence of
`Ternary.lean` is exactly the record of which way each step went, and the real
it names is inside every interval, hence outside every `L n`.

The split this development keeps finding shows up here in its
sharpest form. Which third to take is a genuine decision, and locatedness
supplies it only as a disjunction:

    p < q  →  p ∈ L n  ∨  q ∈ U n

Reading that disjunction as a digit is defining data by cases, so it costs
`Classical.choice`. Everything else -- the walk, the interval, the proof that
the limit misses every `L n` -- is choice-free, and is stated here against a
locator: a digit sequence together with the promise that each digit steps
clear. `exists_missed` then buys the locator classically, once, and nothing
downstream pays again.

So the honest statement of the result is two-part: the diagonal is constructive
given the decisions, and the decisions are what excluded middle is for.
-/

import FromAxioms.Constructive.Omniscience

universe u

open Analysis NumberTheory
namespace SetTheory

/-- The right end of the left third at stage `n`, and the left end of the right
third. They are `1/3ⁿ⁺¹` apart, and stepping clear of a real means landing on
the correct side of one of them. -/
def leftEnd (c : Nat → Nat) (n : Nat) : ZFSet.{u} :=
  ratNat (3 * tnum c n + 1) (pow3 (n + 1))

def rightEnd (c : Nat → Nat) (n : Nat) : ZFSet.{u} :=
  ratNat (3 * tnum c n + 2) (pow3 (n + 1))

/-- A digit sequence that steps clear of the family `(L, U)`: digit `0` keeps
the left third, and certifies that the `n`-th real is above it; digit `1` keeps
the right third and certifies that the real is below it. -/
def Locates (L U : Nat → ZFSet.{u}) (c : Nat → Nat) : Prop :=
  ∀ n, (c n = 0 ∧ leftEnd c n ∈ L n) ∨ (c n = 1 ∧ rightEnd c n ∈ U n)

/-! ## What the decisions are worth

The locator is a dependent binary choice: the disjunction at stage `n` is
about the interval reached by the digits already taken. Naming that as a
principle turns the whole diagonal choice-free -- `exists_missed_of_binaryDC`
uses no axiom -- and leaves the classical content in one theorem, `binaryDC`,
which is a single `if`.

`em` alone does not prove `binaryDC`, for the familiar reason: `p ∨ ¬p` is a
`Prop`, and building a digit sequence from it is elimination into data.
`Decidable` is what is needed, and only choice supplies it for an arbitrary
proposition. -/

/-- The dyadic sum over a finite bit pattern.

`dyadicOf s` is the sum of `2 ^ -n` over those `n` with `s[n] = true`. The
recursion carries the scale instead of an exponent, so no `ratPow` appears.

`List Bool` is this tree's idiom for a finite bit pattern --- `dyadicHi` and
`dyadicLo` already take one --- and it stands in for the Bishop-finite subsets
of the order-completeness uncountability argument, which this tree does not
have. -/
def dyadicOf : List Bool → ZFSet.{u}
  | [] => ratZero.{u}
  | true :: s => ratAdd ratOne.{u} (ratMul (ratNat.{u} 1 2) (dyadicOf s))
  | false :: s => ratMul (ratNat.{u} 1 2) (dyadicOf s)

/-- A dyadic sum is rational. -/
theorem dyadicOf_mem_Rat (s : List Bool) :
    dyadicOf.{u} s ∈ NumberTheory.Rat.{u} := by
  induction s with
  | nil => exact ratZero_mem_Rat
  | cons b t ih =>
    cases b with
    | true =>
      exact ratAdd_mem_Rat ratOne_mem_Rat
        (ratMul_mem_Rat (ratNat_mem_Rat (by omega)) ih)
    | false => exact ratMul_mem_Rat (ratNat_mem_Rat (by omega)) ih

/-- A dyadic sum is nonnegative, which is one of the two side conditions
`lub_of_familyLocated` will want of the family the route sums over. -/
theorem dyadicOf_nonneg (s : List Bool) :
    ratLe ratZero.{u} (dyadicOf.{u} s) := by
  have hhalf : ratLe ratZero.{u} (ratNat.{u} 1 2) :=
    ratLe_of_lt ratZero_mem_Rat (ratNat_mem_Rat (by omega))
      (ratNat_one_pos (by omega))
  induction s with
  | nil => exact ratLe_refl ratZero_mem_Rat
  | cons b t ih =>
    have hscaled : ratLe ratZero.{u} (ratMul (ratNat.{u} 1 2) (dyadicOf.{u} t)) :=
      ratZero_le_mul (ratNat_mem_Rat (by omega)) (dyadicOf_mem_Rat t) hhalf ih
    cases b with
    | true =>
      -- the type is ASCRIBED rather than inferred: `ratNat_mem_Rat` has no
      -- named `u` binder (universes are not named arguments), so pinning the
      -- universe has to be done on the `have` itself
      have hmul : ratMul (ratNat.{u} 1 2) (dyadicOf.{u} t)
          ∈ NumberTheory.Rat.{u} :=
        ratMul_mem_Rat (ratNat_mem_Rat (by omega)) (dyadicOf_mem_Rat t)
      -- `1 + 0 <= 1 + (1/2) * d` from `0 <= (1/2) * d`, then the left side
      -- collapses; there is no `_add_left_of_nonneg` in this tree and the
      -- `_iff` form is what it has
      have h1 : ratLe (ratAdd ratOne.{u} ratZero.{u})
          (ratAdd ratOne.{u} (ratMul (ratNat.{u} 1 2) (dyadicOf.{u} t))) :=
        (ratAdd_le_add_left_iff ratOne_mem_Rat ratZero_mem_Rat hmul).mpr hscaled
      rw [ratAdd_zero ratOne_mem_Rat] at h1
      exact ratLe_trans ratZero_mem_Rat ratOne_mem_Rat
        (ratAdd_mem_Rat ratOne_mem_Rat hmul)
        (ratLe_of_lt ratZero_mem_Rat ratOne_mem_Rat ratZero_lt_one) h1
    | false => exact hscaled

/-- Two halves make one, in the `ratNat` vocabulary and inside the reach of
this module.

`half_mul_two_le_one` (`Analysis.Caratheodory`) states the corresponding
inequality, but that module is downstream of this one. -/
theorem ratNat_two_mul_half : ratMul (ratNat.{u} 2 1) (ratNat.{u} 1 2)
    = ratOne.{u} := by
  rw [ratNat_mul (by omega) (by omega)]
  rw [(ratNat_eq_iff (p := 2 * 1) (q := 1 * 2) (r := 1) (s := 1)
    (by omega) (by omega)).mpr (by omega)]
  exact ratNat_one_one

/-- A dyadic sum is at most two, the remaining side condition
`lub_of_familyLocated` wants of the family the order route sums over. -/
theorem dyadicOf_le_two (s : List Bool) :
    ratLe (dyadicOf.{u} s) (ratNat.{u} 2 1) := by
  have h2 : ratNat.{u} 2 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have hh : ratNat.{u} 1 2 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have hh0 : ratLe ratZero.{u} (ratNat.{u} 1 2) :=
    ratLe_of_lt ratZero_mem_Rat hh (ratNat_one_pos (by omega))
  induction s with
  | nil =>
    exact ratLe_of_lt ratZero_mem_Rat h2 (ratNat_pos (by omega))
  | cons b t ih =>
    have hd : dyadicOf.{u} t ∈ NumberTheory.Rat.{u} := dyadicOf_mem_Rat t
    have hmul : ratMul (ratNat.{u} 1 2) (dyadicOf.{u} t)
        ∈ NumberTheory.Rat.{u} := ratMul_mem_Rat hh hd
    -- `ratMul_le_mul_right` scales on the RIGHT and `dyadicOf` puts the half
    -- on the LEFT, so the commutation is needed
    have hstep : ratLe (ratMul (ratNat.{u} 1 2) (dyadicOf.{u} t)) ratOne.{u} := by
      have := ratMul_le_mul_right hd h2 hh ih hh0
      rw [ratMul_comm hd hh, ratMul_comm h2 hh] at this
      rw [ratMul_comm hh h2] at this
      rw [ratNat_two_mul_half] at this
      exact this
    cases b with
    | true =>
      have h1 : ratLe (ratAdd ratOne.{u} (ratMul (ratNat.{u} 1 2) (dyadicOf.{u} t)))
          (ratAdd ratOne.{u} ratOne.{u}) :=
        (ratAdd_le_add_left_iff ratOne_mem_Rat hmul ratOne_mem_Rat).mpr hstep
      rw [ratOne_add_ratOne] at h1
      exact h1
    | false =>
      -- `1 <= 2` the same way, from `1 + 0 <= 1 + 1`; reaching for a
      -- `ratNat_lt_ratNat_of_lt` would have been an invented name
      have hone_le_two : ratLe ratOne.{u} (ratNat.{u} 2 1) := by
        have h := (ratAdd_le_add_left_iff ratOne_mem_Rat ratZero_mem_Rat
          ratOne_mem_Rat).mpr
          (ratLe_of_lt ratZero_mem_Rat ratOne_mem_Rat ratZero_lt_one)
        rw [ratAdd_zero ratOne_mem_Rat, ratOne_add_ratOne] at h
        exact h
      exact ratLe_trans hmul ratOne_mem_Rat h2 hstep hone_le_two

/-- A dyadic sum splits at any cut-off.

`dyadicOf s = dyadicOf (s.take k) + (1/2)^k * dyadicOf (s.drop k)`, exactly.
Rung 3's induction controls patterns up to length `k` and needs to know what
the rest contributes; with `dyadicOf_nonneg` and `dyadicOf_le_two` this pins
the tail into `[0, 2 * (1/2)^k]` without any inequality reasoning here. -/
theorem dyadicOf_split (k : Nat) : ∀ s : List Bool,
    dyadicOf.{u} s = ratAdd (dyadicOf.{u} (s.take k))
      (ratMul (ratPow (ratNat.{u} 1 2) k) (dyadicOf.{u} (s.drop k))) := by
  induction k with
  | zero =>
    intro s
    show dyadicOf.{u} s = ratAdd (dyadicOf.{u} []) (ratMul ratOne.{u} (dyadicOf.{u} s))
    rw [ratOne_mul (dyadicOf_mem_Rat s)]
    show dyadicOf.{u} s = ratAdd ratZero.{u} (dyadicOf.{u} s)
    rw [ratZero_add (dyadicOf_mem_Rat s)]
  | succ k ih =>
    intro s
    have hhalf : ratNat.{u} 1 2 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
    have hpow : ratPow (ratNat.{u} 1 2) k ∈ NumberTheory.Rat.{u} := ratPow_mem hhalf k
    cases s with
    | nil =>
      show dyadicOf.{u} ([] : List Bool)
        = ratAdd (dyadicOf.{u} []) (ratMul _ (dyadicOf.{u} []))
      show ratZero.{u} = ratAdd ratZero.{u} (ratMul _ ratZero.{u})
      rw [ratMul_zero (ratPow_mem hhalf (k + 1)), ratZero_add ratZero_mem_Rat]
    | cons b t =>
      have hd := dyadicOf_mem_Rat (t.take k)
      have hr := dyadicOf_mem_Rat (t.drop k)
      -- `(1/2)^(k+1) * y` regrouped as `(1/2) * ((1/2)^k * y)`
      have hpowstep : ratMul (ratPow (ratNat.{u} 1 2) (k + 1)) (dyadicOf.{u} (t.drop k))
          = ratMul (ratNat.{u} 1 2) (ratMul (ratPow (ratNat.{u} 1 2) k)
              (dyadicOf.{u} (t.drop k))) := by
        rw [ratPow_succ, ratMul_comm hpow hhalf, ratMul_assoc hhalf hpow hr]
      cases b with
      | true =>
        show ratAdd ratOne.{u} (ratMul (ratNat.{u} 1 2) (dyadicOf.{u} t))
          = ratAdd (ratAdd ratOne.{u} (ratMul (ratNat.{u} 1 2)
              (dyadicOf.{u} (t.take k))))
            (ratMul (ratPow (ratNat.{u} 1 2) (k + 1)) (dyadicOf.{u} (t.drop k)))
        rw [ih t, ratMul_add hhalf hd (ratMul_mem_Rat hpow hr), hpowstep,
          ratAdd_assoc ratOne_mem_Rat (ratMul_mem_Rat hhalf hd)
            (ratMul_mem_Rat hhalf (ratMul_mem_Rat hpow hr))]
      | false =>
        show ratMul (ratNat.{u} 1 2) (dyadicOf.{u} t)
          = ratAdd (ratMul (ratNat.{u} 1 2) (dyadicOf.{u} (t.take k)))
            (ratMul (ratPow (ratNat.{u} 1 2) (k + 1)) (dyadicOf.{u} (t.drop k)))
        rw [ih t, ratMul_add hhalf hd (ratMul_mem_Rat hpow hr), hpowstep]

/-- Binary dependent choice: at each stage, a decision that may depend on the
digits already taken. -/
def BinaryDC : Prop := ∀ A B : Nat → Nat → Prop, (∀ k n, A k n ∨ B k n) →
  ∃ c : Nat → Nat, (∀ n, c n ≤ 1) ∧
    ∀ n, (c n = 0 ∧ A (tnum c n) n) ∨ (c n = 1 ∧ B (tnum c n) n)

/-! ## The set-function form

`exists_missed` quantifies over Lean-level families, which is the stronger
statement for a negative result: every set function induces one.
This is the version that lives inside the theory. -/

/-- Dependent choice restricted to located pairs.

`BinaryDC` chooses a path through a binary tree over ARBITRARY predicates. The
uncountability argument uses it at exactly one instance: the left and right
halves of a located pair. This is that instance, named as a Prop so the cost
the landmark actually pays can be recorded rather than approximated by the
general principle it was first proved from. -/
def LocatorDC : Prop :=
  ∀ L U : Nat → ZFSet.{u}, (∀ n, IsLocated (L n) (U n)) →
    ∃ c : Nat → Nat, Locates L U c

/-! ## Audit

The diagonal is constructive. Every declaration here takes the digits resolving
each stage as a hypothesis and stays at `[propext, Quot.sound]`. -/

#print axioms dyadicOf
#print axioms dyadicOf_mem_Rat
#print axioms dyadicOf_nonneg
#print axioms ratNat_two_mul_half
#print axioms dyadicOf_le_two
#print axioms dyadicOf_split
#print axioms LocatorDC
/-- The sharp upper bound on a dyadic sum, which `dyadicOf_le_two` is the
slack form of.

    dyadicOf s <= 2 - 2 * (1/2)^|s|

At length 0 both sides are 0; at length 1 both are 1; at length 2 both are 3/2.
The bound is ATTAINED by the all-true string at every length, which is exactly
why the slack version cannot replace it: separation needs to know that a finite
string never reaches 2, and by how much it misses.

WHY IT IS THE MISSING INGREDIENT. Two same-length strings differing in the head
have values in `[1, 2)` and `[0, 1]`; both can approach 1, and only a bound that
says HOW FAR a finite tail stays below 2 keeps them apart. With this,
`dyadicOf (true :: u)` is at least 1 and `dyadicOf (false :: v)` is at most
`1 - (1/2)^|v|`, so the gap is at least `(1/2)^|v|`. -/
theorem dyadicOf_le_sharp : ∀ s : List Bool,
    ratLe (dyadicOf.{u} s)
      (ratAdd (ratNat.{u} 2 1)
        (ratNeg (ratMul (ratNat.{u} 2 1) (ratPow (ratNat.{u} 1 2) s.length))))
  | [] => by
      have h2 : ratNat.{u} 2 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
      show ratLe (dyadicOf.{u} ([] : List Bool)) _
      rw [show (([] : List Bool)).length = 0 from rfl, ratPow, ratMul_one h2,
        ratAdd_neg h2]
      exact ratLe_refl ratZero_mem_Rat
  | b :: t => by
      have ih := dyadicOf_le_sharp t
      have hh : ratNat.{u} 1 2 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
      have h2 : ratNat.{u} 2 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
      have hp : ratPow (ratNat.{u} 1 2) t.length ∈ NumberTheory.Rat.{u} := ratPow_mem hh _
      have hd := dyadicOf_mem_Rat.{u} t
      have hh0 : ratLe ratZero.{u} (ratNat.{u} 1 2) :=
        ratLe_of_lt ratZero_mem_Rat hh (ratNat_one_pos (by omega))
      have hrhs : ratMul (ratNat.{u} 2 1) (ratPow (ratNat.{u} 1 2) (t.length + 1))
          = ratPow (ratNat.{u} 1 2) t.length := by
        rw [ratPow_succ, ← ratMul_assoc h2 hp hh, ratMul_comm h2 hp,
          ratMul_assoc hp h2 hh, ratNat_two_mul_half, ratMul_one hp]
      have hscaled : ratLe (ratMul (ratNat.{u} 1 2) (dyadicOf.{u} t))
          (ratAdd ratOne.{u} (ratNeg (ratPow (ratNat.{u} 1 2) t.length))) := by
        have hstep := ratMul_le_mul_right hd
          (ratAdd_mem_Rat h2 (ratNeg_mem_Rat (ratMul_mem_Rat h2 hp))) hh ih hh0
        rw [ratMul_comm hd hh,
          ratMul_comm (ratAdd_mem_Rat h2 (ratNeg_mem_Rat (ratMul_mem_Rat h2 hp))) hh,
          ratMul_add hh h2 (ratNeg_mem_Rat (ratMul_mem_Rat h2 hp)),
          ratMul_comm hh h2, ratNat_two_mul_half,
          ratMul_neg hh (ratMul_mem_Rat h2 hp), ← ratMul_assoc hh h2 hp,
          ratMul_comm hh h2, ratNat_two_mul_half, ratOne_mul hp] at hstep
        exact hstep
      have hone_one : ratAdd ratOne.{u} ratOne.{u} = ratNat.{u} 2 1 := by
        rw [← ratNat_one_one, ratNat_add_same_denom (by omega : (0:Nat) < 1)]
      cases b
      · -- `false :: t` is the half, and `1 - p <= 2 - p`
        show ratLe (ratMul (ratNat.{u} 1 2) (dyadicOf.{u} t)) _
        rw [show (false :: t).length = t.length + 1 from rfl, hrhs]
        refine ratLe_trans (ratMul_mem_Rat hh hd)
          (ratAdd_mem_Rat ratOne_mem_Rat (ratNeg_mem_Rat hp))
          (ratAdd_mem_Rat h2 (ratNeg_mem_Rat hp)) hscaled ?_
        refine (ratAdd_le_add_right_iff (ratNeg_mem_Rat hp) ratOne_mem_Rat h2).mpr ?_
        rw [← hone_one]
        have := (ratAdd_le_add_left_iff ratOne_mem_Rat ratZero_mem_Rat ratOne_mem_Rat).mpr
          (ratLe_of_lt ratZero_mem_Rat ratOne_mem_Rat ratZero_lt_one)
        rwa [ratAdd_zero ratOne_mem_Rat] at this
      · -- `true :: t` adds one, and `1 + (1 - p) = 2 - p`
        show ratLe (ratAdd ratOne.{u} (ratMul (ratNat.{u} 1 2) (dyadicOf.{u} t))) _
        rw [show (true :: t).length = t.length + 1 from rfl, hrhs]
        have hsum := (ratAdd_le_add_left_iff ratOne_mem_Rat (ratMul_mem_Rat hh hd)
          (ratAdd_mem_Rat ratOne_mem_Rat (ratNeg_mem_Rat hp))).mpr hscaled
        rwa [← ratAdd_assoc ratOne_mem_Rat ratOne_mem_Rat (ratNeg_mem_Rat hp),
          hone_one] at hsum

#print axioms SetTheory.dyadicOf_le_sharp


-- NO EQUAL-DEPTH HYPOTHESIS, though separation reads as a claim about nodes at
-- the same DEPTH. None is needed: `dyadicOf (false :: v) + (1/2)^|v| <= 1` and
-- `1 <= dyadicOf (true :: u)` for ANY tails, so the gap is measured by v's
-- length alone and u is unconstrained.
--
-- THE SHARP BOUND IS SPENT ON THE `false` SIDE and only there.
-- `dyadicOf_le_two` would give `dyadicOf (false :: v) <= 1`, which leaves NO
-- gap against `1 <= dyadicOf (true :: u)`, so the sharp version is proved
-- first.

/-- Half a dyadic sum stays a half-power below one. The sharp bound scaled,
and the form the head comparison needs. -/
theorem dyadicOf_half_le (s : List Bool) :
    ratLe (ratMul (ratNat.{u} 1 2) (dyadicOf.{u} s))
      (ratAdd ratOne.{u} (ratNeg (ratPow (ratNat.{u} 1 2) s.length))) := by
  have hh : ratNat.{u} 1 2 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have h2 : ratNat.{u} 2 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have hp : ratPow (ratNat.{u} 1 2) s.length ∈ NumberTheory.Rat.{u} := ratPow_mem hh _
  have hd := dyadicOf_mem_Rat.{u} s
  have hh0 : ratLe ratZero.{u} (ratNat.{u} 1 2) :=
    ratLe_of_lt ratZero_mem_Rat hh (ratNat_one_pos (by omega))
  have hstep := ratMul_le_mul_right hd
    (ratAdd_mem_Rat h2 (ratNeg_mem_Rat (ratMul_mem_Rat h2 hp))) hh
    (dyadicOf_le_sharp s) hh0
  rw [ratMul_comm hd hh,
    ratMul_comm (ratAdd_mem_Rat h2 (ratNeg_mem_Rat (ratMul_mem_Rat h2 hp))) hh,
    ratMul_add hh h2 (ratNeg_mem_Rat (ratMul_mem_Rat h2 hp)),
    ratMul_comm hh h2, ratNat_two_mul_half,
    ratMul_neg hh (ratMul_mem_Rat h2 hp), ← ratMul_assoc hh h2 hp,
    ratMul_comm hh h2, ratNat_two_mul_half, ratOne_mul hp] at hstep
  exact hstep

/-- Nodes that differ in the head are a half-power apart.

The separation, at the only place it has to be proved: a `true` head puts the
value at least 1, a `false` head puts it at most one minus a half-power, and the
gap is that half-power. Everything about deeper disagreement reduces to this
through `dyadicOf_split`.

The sharp bound is spent on the `false` side: `dyadicOf_le_two` would give at
most one, which leaves no gap at all. -/
theorem dyadicOf_head_separation (u v : List Bool) :
    ratLe (ratAdd (dyadicOf.{u} (false :: v)) (ratPow (ratNat.{u} 1 2) v.length))
      (dyadicOf.{u} (true :: u)) := by
  have hh : ratNat.{u} 1 2 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have hpv : ratPow (ratNat.{u} 1 2) v.length ∈ NumberTheory.Rat.{u} := ratPow_mem hh _
  have hdu := dyadicOf_mem_Rat.{u} u
  have hdv := dyadicOf_mem_Rat.{u} v
  have hh0 : ratLe ratZero.{u} (ratNat.{u} 1 2) :=
    ratLe_of_lt ratZero_mem_Rat hh (ratNat_one_pos (by omega))
  -- the `false` side, plus the gap, is at most one
  have hlow : ratLe (ratAdd (ratMul (ratNat.{u} 1 2) (dyadicOf.{u} v)) 
      (ratPow (ratNat.{u} 1 2) v.length)) ratOne.{u} := by
    have := (ratAdd_le_add_right_iff hpv (ratMul_mem_Rat hh hdv)
      (ratAdd_mem_Rat ratOne_mem_Rat (ratNeg_mem_Rat hpv))).mpr (dyadicOf_half_le v)
    rwa [ratAdd_assoc ratOne_mem_Rat (ratNeg_mem_Rat hpv) hpv,
      ratAdd_comm (ratNeg_mem_Rat hpv) hpv, ratAdd_neg hpv,
      ratAdd_zero ratOne_mem_Rat] at this
  -- the `true` side is at least one
  have hhigh : ratLe ratOne.{u} (ratAdd ratOne.{u} (ratMul (ratNat.{u} 1 2) (dyadicOf.{u} u))) := by
    have := (ratAdd_le_add_left_iff ratOne_mem_Rat ratZero_mem_Rat
      (ratMul_mem_Rat hh hdu)).mpr (ratZero_le_mul hh hdu hh0 (dyadicOf_nonneg u))
    rwa [ratAdd_zero ratOne_mem_Rat] at this
  show ratLe (ratAdd (ratMul (ratNat.{u} 1 2) (dyadicOf.{u} v)) _) _
  exact ratLe_trans (ratAdd_mem_Rat (ratMul_mem_Rat hh hdv) hpv) ratOne_mem_Rat
    (ratAdd_mem_Rat ratOne_mem_Rat (ratMul_mem_Rat hh hdu)) hlow hhigh

#print axioms SetTheory.dyadicOf_half_le
#print axioms SetTheory.dyadicOf_head_separation


-- `dyadicOf_split` DOES THE WORK AN INTEGRALITY ARGUMENT WOULD HAVE DONE. It
-- says the shared prefix contributes a common summand and the tail is scaled by
-- a fixed half-power --- exactly the decomposition separation needs. That is why
-- the subtower I priced does not exist: the recursion was already there, and
-- only the SHARP tail bound was missing.
--
-- ONE REWRITE ORDER MATTERS: the two `dyadicOf_split` rewrites are separated by
-- `hpre`. After folding s back up, the right side still names
-- `List.take k s`, and `dyadicOf_split k t` cannot fire until that is rewritten
-- to `List.take k t`. Folding both at once fails with a pattern-not-found that
-- names the t-shaped term while the goal holds the s-shaped one.

/-- Two nodes agreeing to depth k and differing there are separated.

The general form, reduced to the head case by `dyadicOf_split`: both values
share the prefix contribution exactly, so the difference is the scaled
difference of the tails, and the tails differ in their heads.

`dyadicOf_split` is doing the work that an integrality argument would otherwise
have to do --- it says the prefix contributes a common summand and the tail is
scaled by a fixed half-power, which is precisely the decomposition the
separation needs. -/
theorem dyadicOf_split_separation (s t : List Bool) (k : Nat)
    (hpre : List.take k s = List.take k t)
    (hs : List.drop k s = false :: (List.drop k s).tail)
    (ht : List.drop k t = true :: (List.drop k t).tail) :
    ratLe
      (ratAdd (dyadicOf.{u} s)
        (ratMul (ratPow (ratNat.{u} 1 2) k)
          (ratPow (ratNat.{u} 1 2) (List.drop k s).tail.length)))
      (dyadicOf.{u} t) := by
  have hh : ratNat.{u} 1 2 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have hh0 : ratLe ratZero.{u} (ratNat.{u} 1 2) :=
    ratLe_of_lt ratZero_mem_Rat hh (ratNat_one_pos (by omega))
  have hk : ratPow (ratNat.{u} 1 2) k ∈ NumberTheory.Rat.{u} := ratPow_mem hh k
  have hk0 : ratLe ratZero.{u} (ratPow (ratNat.{u} 1 2) k) := ratPow_nonneg hh hh0 k
  have hpre' := dyadicOf_mem_Rat.{u} (List.take k s)
  have hds := dyadicOf_mem_Rat.{u} (List.drop k s)
  have hdt := dyadicOf_mem_Rat.{u} (List.drop k t)
  have hgap : ratPow (ratNat.{u} 1 2) (List.drop k s).tail.length ∈ NumberTheory.Rat.{u} :=
    ratPow_mem hh _
  -- the tails differ in the head, so they are separated
  have hsep : ratLe
      (ratAdd (dyadicOf.{u} (List.drop k s))
        (ratPow (ratNat.{u} 1 2) (List.drop k s).tail.length))
      (dyadicOf.{u} (List.drop k t)) := by
    rw [hs, ht]
    exact dyadicOf_head_separation (List.drop k t).tail (List.drop k s).tail
  -- scale by the shared prefix factor, then add the shared prefix value
  have hscaled := ratMul_le_mul_right (ratAdd_mem_Rat hds hgap) hdt hk hsep hk0
  rw [ratMul_comm (ratAdd_mem_Rat hds hgap) hk, ratMul_comm hdt hk,
    ratMul_add hk hds hgap] at hscaled
  have hadd := (ratAdd_le_add_left_iff hpre'
    (ratAdd_mem_Rat (ratMul_mem_Rat hk hds) (ratMul_mem_Rat hk hgap))
    (ratMul_mem_Rat hk hdt)).mpr hscaled
  rw [← ratAdd_assoc hpre' (ratMul_mem_Rat hk hds) (ratMul_mem_Rat hk hgap),
    ← dyadicOf_split k s, hpre, ← dyadicOf_split k t] at hadd
  exact hadd

#print axioms SetTheory.dyadicOf_split_separation


/-- Distinct nodes of the same length have separated points.

The separation in the form a positivity argument uses: no absolute value, no
comparison of located reals, just the two directions as a disjunction with an
explicit gap.

The gap is `(1/2)^k * (1/2)^m` where k is the first differing index and m the
length of what follows it --- so `k + m + 1` is the common length, and the gap
is `(1/2)^(n-1)` however the difference is placed. Stating it with k and m
separately avoids an arithmetic identity that the caller may not need. -/
theorem dyadicOf_distinct_separated (s t : List Bool)
    (hlen : s.length = t.length) (hne : s ≠ t) :
    ∃ k m : Nat,
      ratLe (ratAdd (dyadicOf.{u} s)
          (ratMul (ratPow (ratNat.{u} 1 2) k) (ratPow (ratNat.{u} 1 2) m)))
        (dyadicOf.{u} t)
      ∨ ratLe (ratAdd (dyadicOf.{u} t)
          (ratMul (ratPow (ratNat.{u} 1 2) k) (ratPow (ratNat.{u} 1 2) m)))
        (dyadicOf.{u} s) := by
  obtain ⟨k, hpre, hcase⟩ := Constructive.exists_first_diff s t hlen hne
  rcases hcase with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact ⟨k, (List.drop k s).tail.length,
      Or.inl (dyadicOf_split_separation s t k hpre hs ht)⟩
  · exact ⟨k, (List.drop k t).tail.length,
      Or.inr (dyadicOf_split_separation t s k hpre.symm ht hs)⟩

#print axioms SetTheory.dyadicOf_distinct_separated


/-- The base-three embedding of a bit pattern.

`dyadicOf`'s shape with `1/3` for `1/2`, and the change is quantitative rather
than stylistic. For base b the depth-k nodes are `b^-(k-1)` apart while a
point sits within `(b/(b-1)) * b^-k` of its own node, so the slack is

    b - b/(b-1)   times   b^-k

which is zero at `b = 2` and positive for `b > 2`. Base three is the smallest
with any slack, so Julian and Richman chose it.

WHAT THE SLACK IS AND IS NOT FOR. It does NOT mean base two fails to separate:
`dyadicOf_distinct_separated`, thirty lines above, separates finite strings in
base two with the positive gap `(1/2)^k * (1/2)^m`. Both bases separate finite
strings, and an earlier version of this note wrongly said otherwise.

The slack governs the LIMITS. Extending a prefix by a set bit contributes
`(1/2)^k` in base two against a depth-`k+1` window of `(1/2)^k` --- equal, so the
nested intervals meet and no STRICT inequality is available --- and `2*(1/3)^k`
in base three against a window of `(1/3)^k`, twice it, leaving one window of
margin. `takeBits_strict_sep` spends exactly that margin, and `realLLt` needs a
strict inequality. -/
def triadicOf : List Bool → ZFSet.{u}
  | [] => ratZero.{u}
  | true :: s => ratAdd ratOne.{u} (ratMul (ratNat.{u} 1 3) (triadicOf s))
  | false :: s => ratMul (ratNat.{u} 1 3) (triadicOf s)

theorem triadicOf_mem_Rat : ∀ s : List Bool,
    triadicOf.{u} s ∈ NumberTheory.Rat.{u}
  | [] => ratZero_mem_Rat
  | true :: s => ratAdd_mem_Rat ratOne_mem_Rat
      (ratMul_mem_Rat (ratNat_mem_Rat (by omega)) (triadicOf_mem_Rat s))
  | false :: s => ratMul_mem_Rat (ratNat_mem_Rat (by omega))
      (triadicOf_mem_Rat s)

theorem triadicOf_nonneg : ∀ s : List Bool,
    ratLe ratZero.{u} (triadicOf.{u} s)
  | [] => ratLe_refl ratZero_mem_Rat
  | true :: s => by
      have h3 : ratNat.{u} 1 3 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
      have h30 : ratLe ratZero.{u} (ratNat.{u} 1 3) :=
        ratLe_of_lt ratZero_mem_Rat h3 (ratNat_one_pos (by omega))
      have hm := ratZero_le_mul h3 (triadicOf_mem_Rat s) h30
        (triadicOf_nonneg s)
      have := ratAdd_le_add ratZero_mem_Rat ratOne_mem_Rat ratZero_mem_Rat
        (ratMul_mem_Rat h3 (triadicOf_mem_Rat s))
        (ratLe_of_lt ratZero_mem_Rat ratOne_mem_Rat ratZero_lt_one) hm
      rwa [ratAdd_zero ratZero_mem_Rat] at this
  | false :: s => by
      have h3 : ratNat.{u} 1 3 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
      exact ratZero_le_mul h3 (triadicOf_mem_Rat s)
        (ratLe_of_lt ratZero_mem_Rat h3 (ratNat_one_pos (by omega)))
        (triadicOf_nonneg s)

#print axioms SetTheory.triadicOf
#print axioms SetTheory.triadicOf_mem_Rat
#print axioms SetTheory.triadicOf_nonneg


-- INTEGER COEFFICIENTS ON PURPOSE. The natural form is
-- `triadicOf s <= 3/2 - (3/2)(1/3)^|s|`, and every step of that needs
-- `ratNat 3 6 = ratNat 1 2` --- a numeral normalisation this tree has no lemma
-- for. Clearing denominators to `2*t + 3*(1/3)^|s| <= 3` removes all of them
-- except `3 * (1/3) = 1`, which is one `ratNat_eq_iff`. Same trick as writing
-- the telescoping bound `c n + c n` instead of `6 * (1/2)^n`.
--
-- ATTAINED at every length by the all-true string: 0+3, then 2*1+3*(1/3), then
-- 2*(4/3)+3*(1/9), all exactly 3. A slack bound is useless here --- that is
-- precisely how the base-two version failed.

/-- The sharp bound, in integer coefficients.

    2 * triadicOf s  +  3 * (1/3)^|s|   <=   3

which is `triadicOf s <= 3/2 - (3/2)(1/3)^|s|` cleared of denominators. Stated
this way ON PURPOSE: the fractional form needs `ratNat 3 6 = ratNat 1 2` at
every step, and this tree has no numeral-normalisation lemma --- the same reason
the telescoping bound is written `c n + c n` rather than `6 * (1/2)^n`.

ATTAINED by the all-true string at every length: 0 + 3 = 3, then 2*1 + 3*(1/3)
= 3, then 2*(4/3) + 3*(1/9) = 3. A slack bound would leave the gap unprovable,
as the base-two version did. -/
theorem triadicOf_sharp : ∀ s : List Bool,
    ratLe (ratAdd (ratMul (ratNat.{u} 2 1) (triadicOf.{u} s))
        (ratMul (ratNat.{u} 3 1) (ratPow (ratNat.{u} 1 3) s.length)))
      (ratNat.{u} 3 1)
  | [] => by
      have h3 : ratNat.{u} 3 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
      have h2 : ratNat.{u} 2 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
      show ratLe (ratAdd (ratMul (ratNat.{u} 2 1) (triadicOf.{u} ([] : List Bool))) _) _
      rw [show (([] : List Bool)).length = 0 from rfl, ratPow, ratMul_one h3,
        show triadicOf.{u} ([] : List Bool) = ratZero.{u} from rfl,
        ratMul_zero h2, ratZero_add h3]
      exact ratLe_refl h3
  | b :: t => by
      have hth : ratNat.{u} 1 3 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
      have h2 : ratNat.{u} 2 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
      have h3 : ratNat.{u} 3 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
      have hp : ratPow (ratNat.{u} 1 3) t.length ∈ NumberTheory.Rat.{u} := ratPow_mem hth _
      have hT := triadicOf_mem_Rat.{u} t
      have hth0 : ratLe ratZero.{u} (ratNat.{u} 1 3) :=
        ratLe_of_lt ratZero_mem_Rat hth (ratNat_one_pos (by omega))
      -- `3 * (1/3) = 1`, cleared through the numeral equality
      have hthree_third : ratMul (ratNat.{u} 3 1) (ratNat.{u} 1 3) = ratOne.{u} := by
        rw [ratNat_mul (by omega) (by omega),
          show ratNat.{u} (3*1) (1*3) = ratNat.{u} 1 1 from
            (ratNat_eq_iff (by omega) (by omega)).mpr (by omega),
          ratNat_one_one]
      -- the tail power collapses: `3 * (1/3)^(n+1) = (1/3)^n`
      have hcollapse : ratMul (ratNat.{u} 3 1) (ratPow (ratNat.{u} 1 3) (t.length + 1))
          = ratPow (ratNat.{u} 1 3) t.length := by
        rw [ratPow_succ, ← ratMul_assoc h3 hp hth, ratMul_comm h3 hp,
          ratMul_assoc hp h3 hth, hthree_third, ratMul_one hp]
      -- the inductive bound, scaled by a third
      have hscaled : ratLe
          (ratAdd (ratMul (ratNat.{u} 2 1) (ratMul (ratNat.{u} 1 3) (triadicOf.{u} t)))
            (ratPow (ratNat.{u} 1 3) t.length)) ratOne.{u} := by
        have hstep := ratMul_le_mul_right
          (ratAdd_mem_Rat (ratMul_mem_Rat h2 hT) (ratMul_mem_Rat h3 hp)) h3 hth
          (triadicOf_sharp t) hth0
        rw [ratAdd_mul (ratMul_mem_Rat h2 hT) (ratMul_mem_Rat h3 hp) hth,
          ratMul_assoc h2 hT hth, ratMul_comm hT hth, ← ratMul_assoc h2 hth hT,
          ratMul_comm h2 hth, ratMul_assoc hth h2 hT,
          ratMul_assoc h3 hp hth, ratMul_comm hp hth, ← ratMul_assoc h3 hth hp,
          hthree_third, ratOne_mul hp] at hstep
        rw [← ratMul_assoc hth h2 hT, ratMul_comm hth h2,
          ratMul_assoc h2 hth hT] at hstep
        exact hstep
      cases b
      · show ratLe (ratAdd (ratMul (ratNat.{u} 2 1)
            (ratMul (ratNat.{u} 1 3) (triadicOf.{u} t))) _) _
        rw [show (false :: t).length = t.length + 1 from rfl, hcollapse]
        refine ratLe_trans
          (ratAdd_mem_Rat (ratMul_mem_Rat h2 (ratMul_mem_Rat hth hT)) hp)
          ratOne_mem_Rat h3 hscaled ?_
        rw [← ratNat_one_one]
        exact (ratNat_le_iff (by omega) (by omega)).mpr (by omega)
      · show ratLe (ratAdd (ratMul (ratNat.{u} 2 1)
            (ratAdd ratOne.{u} (ratMul (ratNat.{u} 1 3) (triadicOf.{u} t)))) _) _
        rw [show (true :: t).length = t.length + 1 from rfl, hcollapse,
          ratMul_add h2 ratOne_mem_Rat (ratMul_mem_Rat hth hT), ratMul_one h2,
          ratAdd_assoc h2 (ratMul_mem_Rat h2 (ratMul_mem_Rat hth hT)) hp]
        have := (ratAdd_le_add_left_iff h2
          (ratAdd_mem_Rat (ratMul_mem_Rat h2 (ratMul_mem_Rat hth hT)) hp)
          ratOne_mem_Rat).mpr hscaled
        refine ratLe_trans (ratAdd_mem_Rat h2
            (ratAdd_mem_Rat (ratMul_mem_Rat h2 (ratMul_mem_Rat hth hT)) hp))
          (ratAdd_mem_Rat h2 ratOne_mem_Rat) h3 this ?_
        rw [← ratNat_one_one, ratNat_add_same_denom (by omega : (0:Nat) < 1)]
        exact ratLe_refl h3

#print axioms SetTheory.triadicOf_sharp


/-- The base-three split, `dyadicOf_split`'s proof with a third for a half.

Transferred verbatim apart from the constant: the decomposition does not care
about the base. Only the sharp bound had to be re-derived, since the base
enters quantitatively there. -/
theorem triadicOf_split (k : Nat) : ∀ s : List Bool,
    triadicOf.{u} s = ratAdd (triadicOf.{u} (s.take k))
      (ratMul (ratPow (ratNat.{u} 1 3) k) (triadicOf.{u} (s.drop k))) := by
  induction k with
  | zero =>
    intro s
    show triadicOf.{u} s = ratAdd (triadicOf.{u} []) (ratMul ratOne.{u} (triadicOf.{u} s))
    rw [ratOne_mul (triadicOf_mem_Rat s)]
    show triadicOf.{u} s = ratAdd ratZero.{u} (triadicOf.{u} s)
    rw [ratZero_add (triadicOf_mem_Rat s)]
  | succ k ih =>
    intro s
    have hth : ratNat.{u} 1 3 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
    have hpow : ratPow (ratNat.{u} 1 3) k ∈ NumberTheory.Rat.{u} := ratPow_mem hth k
    cases s with
    | nil =>
      show triadicOf.{u} ([] : List Bool)
        = ratAdd (triadicOf.{u} []) (ratMul _ (triadicOf.{u} []))
      show ratZero.{u} = ratAdd ratZero.{u} (ratMul _ ratZero.{u})
      rw [ratMul_zero (ratPow_mem hth (k + 1)), ratZero_add ratZero_mem_Rat]
    | cons b t =>
      have hd := triadicOf_mem_Rat (t.take k)
      have hr := triadicOf_mem_Rat (t.drop k)
      have hpowstep : ratMul (ratPow (ratNat.{u} 1 3) (k + 1)) (triadicOf.{u} (t.drop k))
          = ratMul (ratNat.{u} 1 3) (ratMul (ratPow (ratNat.{u} 1 3) k)
              (triadicOf.{u} (t.drop k))) := by
        rw [ratPow_succ, ratMul_comm hpow hth, ratMul_assoc hth hpow hr]
      cases b with
      | true =>
        show ratAdd ratOne.{u} (ratMul (ratNat.{u} 1 3) (triadicOf.{u} t))
          = ratAdd (ratAdd ratOne.{u} (ratMul (ratNat.{u} 1 3)
              (triadicOf.{u} (t.take k))))
            (ratMul (ratPow (ratNat.{u} 1 3) (k + 1)) (triadicOf.{u} (t.drop k)))
        rw [ih t, ratMul_add hth hd (ratMul_mem_Rat hpow hr), hpowstep,
          ratAdd_assoc ratOne_mem_Rat (ratMul_mem_Rat hth hd)
            (ratMul_mem_Rat hth (ratMul_mem_Rat hpow hr))]
      | false =>
        show ratMul (ratNat.{u} 1 3) (triadicOf.{u} t)
          = ratAdd (ratMul (ratNat.{u} 1 3) (triadicOf.{u} (t.take k)))
            (ratMul (ratPow (ratNat.{u} 1 3) (k + 1)) (triadicOf.{u} (t.drop k)))
        rw [ih t, ratMul_add hth hd (ratMul_mem_Rat hpow hr), hpowstep]

#print axioms SetTheory.triadicOf_split


-- What the base buys, in constants:
--
--     base 2:  spacing 2 * (1/2)^k   tail 2 * (1/2)^k     slack 0
--     base 3:  spacing 3 * (1/3)^k   tail (3/2) * (1/3)^k  slack (3/2) * (1/3)^k
--
-- Half the spacing survives, at every depth, so the positivity argument closes
-- in base three and does not in base two, whose separation lemmas are correct
-- and sharp and still cannot carry this half of the reversal.
--
-- `triadicOf_le_three` is the sharp bound with its power term dropped. Stated
-- separately because the tail estimate wants the WEAKEST consequence, and
-- passing the sharp form would carry an irrelevant `(1/3)^|s|` through the
-- multiplication.

/-- Doubled, a triadic sum is at most three. The sharp bound with its power
term dropped --- the weakest consequence, and the one the tail estimate uses. -/
theorem triadicOf_le_three (s : List Bool) :
    ratLe (ratMul (ratNat.{u} 2 1) (triadicOf.{u} s)) (ratNat.{u} 3 1) := by
  have hth : ratNat.{u} 1 3 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have h2 : ratNat.{u} 2 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have h3 : ratNat.{u} 3 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have hp := ratPow_mem hth s.length
  have hT := triadicOf_mem_Rat.{u} s
  have hnn : ratLe ratZero.{u} (ratMul (ratNat.{u} 3 1) (ratPow (ratNat.{u} 1 3) s.length)) :=
    ratZero_le_mul h3 hp (ratLe_of_lt ratZero_mem_Rat h3 (ratNat_pos (by omega)))
      (ratPow_nonneg hth (ratLe_of_lt ratZero_mem_Rat hth (ratNat_one_pos (by omega))) _)
  have hle := (ratAdd_le_add_left_iff (ratMul_mem_Rat h2 hT) ratZero_mem_Rat
    (ratMul_mem_Rat h3 hp)).mpr hnn
  rw [ratAdd_zero (ratMul_mem_Rat h2 hT)] at hle
  exact ratLe_trans (ratMul_mem_Rat h2 hT)
    (ratAdd_mem_Rat (ratMul_mem_Rat h2 hT) (ratMul_mem_Rat h3 hp)) h3
    hle (triadicOf_sharp s)

#print axioms SetTheory.triadicOf_le_three
/-- The first `n` bits of an infinite bit sequence, as a list. -/
def takeBits (b : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => b 0 :: takeBits (fun i => b (i + 1)) n

/-- A longer prefix restricts to the shorter one.

`n + 1 + m` is NOT definitionally `(n + m) + 1` in the form the recursion needs:
`Nat.add` recurses on its second argument, so `n + 1 + m` is `m` successors of
`n + 1`, while `takeBits` splits on the outermost successor of its own index.
The `omega` step supplies the reassociation the `show` cannot do by itself. -/
theorem takeBits_take : ∀ (n m : Nat) (b : Nat → Bool),
    List.take n (takeBits b (n + m)) = takeBits b n
  | 0, _, _ => rfl
  | n + 1, m, b => by
      have e : n + 1 + m = (n + m) + 1 := by omega
      rw [e]
      show b 0 :: List.take n (takeBits (fun i => b (i + 1)) (n + m))
        = b 0 :: takeBits (fun i => b (i + 1)) n
      rw [takeBits_take n m (fun i => b (i + 1))]

/-- Extending a prefix moves the value up, by less than `3 * (1/3)^n`.

The bracket that would make an infinite bit sequence Cauchy, and the place the
base pays off in the direction it was chosen for. `triadicOf_split` says the
extension contributes `(1/3)^n` times the value of the tail added, and
`triadicOf_le_three` caps that tail --- so the whole remainder of the expansion
is confined to a window of width `3 * (1/3)^n` above the prefix, shrinking
geometrically.

MONOTONE is the other half and is free: the added term is a product of
non-negatives, so a longer prefix never decreases the value. Together they say
the prefixes climb and are trapped, which is the shape a limit argument wants.

Everything is DOUBLED, as throughout the base-three family, to keep the
coefficients integral. -/
theorem takeBits_bracket (b : Nat → Bool) (n m : Nat) :
    ratLe (ratMul (ratNat.{u} 2 1) (triadicOf.{u} (takeBits b n)))
        (ratMul (ratNat.{u} 2 1) (triadicOf.{u} (takeBits b (n + m))))
    ∧ ratLe (ratMul (ratNat.{u} 2 1) (triadicOf.{u} (takeBits b (n + m))))
        (ratAdd (ratMul (ratNat.{u} 2 1) (triadicOf.{u} (takeBits b n)))
          (ratMul (ratPow (ratNat.{u} 1 3) n) (ratNat.{u} 3 1))) := by
  have hth : ratNat.{u} 1 3 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have h2 : ratNat.{u} 2 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have h3 : ratNat.{u} 3 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have hk : ratPow (ratNat.{u} 1 3) n ∈ NumberTheory.Rat.{u} := ratPow_mem hth n
  have hk0 : ratLe ratZero.{u} (ratPow (ratNat.{u} 1 3) n) :=
    ratPow_nonneg hth (ratLe_of_lt ratZero_mem_Rat hth (ratNat_one_pos (by omega))) n
  have hpre := takeBits_take n m b
  have hta := triadicOf_mem_Rat.{u} (takeBits b n)
  have htd := triadicOf_mem_Rat.{u} (List.drop n (takeBits b (n + m)))
  have htail : ratMul (ratPow (ratNat.{u} 1 3) n)
      (ratMul (ratNat.{u} 2 1) (triadicOf.{u} (List.drop n (takeBits b (n + m)))))
      ∈ NumberTheory.Rat.{u} := ratMul_mem_Rat hk (ratMul_mem_Rat h2 htd)
  have hsplit : ratMul (ratNat.{u} 2 1) (triadicOf.{u} (takeBits b (n + m)))
      = ratAdd (ratMul (ratNat.{u} 2 1) (triadicOf.{u} (takeBits b n)))
        (ratMul (ratPow (ratNat.{u} 1 3) n)
          (ratMul (ratNat.{u} 2 1)
            (triadicOf.{u} (List.drop n (takeBits b (n + m)))))) := by
    rw [triadicOf_split n (takeBits b (n + m)), hpre,
      ratMul_add h2 hta (ratMul_mem_Rat hk htd),
      ← ratMul_assoc h2 hk htd, ratMul_comm h2 hk, ratMul_assoc hk h2 htd]
  have htail0 : ratLe ratZero.{u}
      (ratMul (ratPow (ratNat.{u} 1 3) n)
        (ratMul (ratNat.{u} 2 1)
          (triadicOf.{u} (List.drop n (takeBits b (n + m)))))) := by
    refine ratZero_le_mul hk (ratMul_mem_Rat h2 htd) hk0 ?_
    exact ratZero_le_mul h2 htd
      (ratLe_of_lt ratZero_mem_Rat h2 (ratNat_pos (by omega)))
      (triadicOf_nonneg (List.drop n (takeBits b (n + m))))
  have htail3 : ratLe
      (ratMul (ratPow (ratNat.{u} 1 3) n)
        (ratMul (ratNat.{u} 2 1)
          (triadicOf.{u} (List.drop n (takeBits b (n + m))))))
      (ratMul (ratPow (ratNat.{u} 1 3) n) (ratNat.{u} 3 1)) := by
    have hstep := ratMul_le_mul_right (ratMul_mem_Rat h2 htd) h3 hk
      (triadicOf_le_three (List.drop n (takeBits b (n + m)))) hk0
    rwa [ratMul_comm (ratMul_mem_Rat h2 htd) hk, ratMul_comm h3 hk] at hstep
  refine ⟨?_, ?_⟩
  · rw [hsplit]
    have hz := (ratAdd_le_add_left_iff (ratMul_mem_Rat h2 hta)
      ratZero_mem_Rat htail).mpr htail0
    rwa [ratAdd_zero (ratMul_mem_Rat h2 hta)] at hz
  · rw [hsplit]
    exact (ratAdd_le_add_left_iff (ratMul_mem_Rat h2 hta) htail
      (ratMul_mem_Rat hk h3)).mpr htail3

#print axioms SetTheory.takeBits
#print axioms SetTheory.takeBits_take
#print axioms SetTheory.takeBits_bracket

--

/-- A prefix has the length asked for. -/
theorem takeBits_length : ∀ (n : Nat) (b : Nat → Bool),
    (takeBits b n).length = n
  | 0, _ => rfl
  | n + 1, b => by
      show (takeBits (fun i => b (i + 1)) n).length + 1 = n + 1
      rw [takeBits_length n (fun i => b (i + 1))]

#print axioms SetTheory.takeBits_length
/-- The prefix values as a `ratSeqs` element. -/
def triLowSeq (b : Nat → Bool) : ZFSet.{u} :=
  natSeq NumberTheory.Rat.{u}
    (fun n => ratMul (ratNat.{u} 2 1) (triadicOf.{u} (takeBits b n)))

/-- The upper ends as a `ratSeqs` element. -/
def triHighSeq (b : Nat → Bool) : ZFSet.{u} :=
  natSeq NumberTheory.Rat.{u}
    (fun n => ratAdd (ratMul (ratNat.{u} 2 1) (triadicOf.{u} (takeBits b n)))
      (ratMul (ratPow (ratNat.{u} 1 3) n) (ratNat.{u} 3 1)))

theorem triLow_mem (b : Nat → Bool) (n : Nat) :
    ratMul (ratNat.{u} 2 1) (triadicOf.{u} (takeBits b n)) ∈ NumberTheory.Rat.{u} :=
  ratMul_mem_Rat (ratNat_mem_Rat (by omega)) (triadicOf_mem_Rat _)

#print axioms SetTheory.triLowSeq
#print axioms SetTheory.triHighSeq
#print axioms SetTheory.triLow_mem
/-- The real named by an infinite bit sequence, base three.

The embedding `(Nat -> Bool) -> RealL`, built from the nested prefix intervals.
Every ingredient is choice-free, so the map itself is: `#print axioms` reports
`[propext, Quot.sound]` and no locator, no countable choice and no `EM` appears
anywhere in its construction.

WHAT IT DOES AND DOES NOT SETTLE FOR THE ROW. It settles the EASY DIRECTION:
Cantor space embeds in the located reals, constructively. It does NOT give
uncountability of `RealL`, because that needs the INVERSE --- from an arbitrary
real, read off a bit --- and reading a bit is a locatedness decision. The row's
price `LocatorDC` is entirely on that side, and this construction, by costing
nothing, is what makes the asymmetry visible rather than asserted. -/
def triadicReal (b : Nat → Bool) : ZFSet.{u} :=
  opair (nestLower (triLowSeq.{u} b)) (nestUpper (triHighSeq.{u} b))

#print axioms SetTheory.triadicReal
/-- A prefix is the previous prefix with the next bit appended.

`takeBits` is built from the FRONT --- `takeBits b (n+1) = b 0 :: takeBits (shift
b) n` --- so the last bit is not syntactically available, and every argument
about what one more level CONTRIBUTES needs this snoc form instead. -/
theorem takeBits_succ : ∀ (n : Nat) (b : Nat → Bool),
    takeBits b (n + 1) = takeBits b n ++ [b n]
  | 0, _ => rfl
  | n + 1, b => by
      show b 0 :: takeBits (fun i => b (i + 1)) (n + 1)
        = (b 0 :: takeBits (fun i => b (i + 1)) n) ++ [b (n + 1)]
      rw [takeBits_succ n (fun i => b (i + 1))]
      rfl

#print axioms SetTheory.takeBits_succ

/-- A one-bit string is worth its bit, as TWO lemmas rather than an `if`.

An `if` on a `Bool` needs a `Decidable` instance, and an inline one elaborates
before unification and can pick `Classical`. Two lemmas cost nothing and cannot. -/
theorem triadicOf_true : triadicOf.{u} [true] = ratOne.{u} := by
  show ratAdd ratOne.{u} (ratMul (ratNat.{u} 1 3) ratZero.{u}) = ratOne.{u}
  rw [ratMul_zero (ratNat_mem_Rat (by omega)), ratAdd_zero ratOne_mem_Rat]

theorem triadicOf_false : triadicOf.{u} [false] = ratZero.{u} := by
  show ratMul (ratNat.{u} 1 3) ratZero.{u} = ratZero.{u}
  exact ratMul_zero (ratNat_mem_Rat (by omega))

/-- The dropped tail of a one-longer prefix is exactly the new bit. -/
theorem drop_takeBits_succ (b : Nat → Bool) (k : Nat) :
    List.drop k (takeBits b (k + 1)) = [b k] := by
  rw [takeBits_succ k b]
  -- `rw [<- takeBits_length]` LOOPS: `k` also occurs inside `takeBits b k`, so
  -- rewriting it to that list's own length rewrites the list too. A `calc`
  -- pins which side moves.
  calc List.drop k (takeBits b k ++ [b k])
      = List.drop (takeBits b k).length (takeBits b k ++ [b k]) := by
        rw [takeBits_length k b]
    _ = [b k] := List.drop_left

/-- What one more bit contributes, exactly.

    v(k+1)  =  v k  +  (1/3)^k * (2 if the bit is true, else 0)

The exact step, where `takeBits_bracket` gives only an inequality. Strict
separation needs it: for two sequences agreeing before `k` and differing at
`k`, the doubled values differ by exactly `2 * (1/3)^k`, which is TWICE the
interval window `3 * (1/3)^(k+1) = (1/3)^k`. The general separation bound gives
exactly the window and so cannot be strict; this gives twice it, with the
difference to spare. -/
theorem takeBits_step (b : Nat → Bool) (k : Nat) :
    ratMul (ratNat.{u} 2 1) (triadicOf.{u} (takeBits b (k + 1)))
      = ratAdd (ratMul (ratNat.{u} 2 1) (triadicOf.{u} (takeBits b k)))
        (ratMul (ratPow (ratNat.{u} 1 3) k)
          (ratMul (ratNat.{u} 2 1) (triadicOf.{u} [b k]))) := by
  have hth : ratNat.{u} 1 3 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have h2 : ratNat.{u} 2 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have hk : ratPow (ratNat.{u} 1 3) k ∈ NumberTheory.Rat.{u} := ratPow_mem hth k
  have hta := triadicOf_mem_Rat.{u} (takeBits b k)
  have htd := triadicOf_mem_Rat.{u} [b k]
  have hpre : List.take k (takeBits b (k + 1)) = takeBits b k :=
    takeBits_take k 1 b
  rw [triadicOf_split k (takeBits b (k + 1)), hpre,
    drop_takeBits_succ b k,
    ratMul_add h2 hta (ratMul_mem_Rat hk htd),
    ← ratMul_assoc h2 hk htd, ratMul_comm h2 hk, ratMul_assoc hk h2 htd]

#print axioms SetTheory.triadicOf_true
#print axioms SetTheory.triadicOf_false
#print axioms SetTheory.drop_takeBits_succ
#print axioms SetTheory.takeBits_step


/-- The window at depth `k+1` is `(1/3)^k`.

    3 * (1/3)^(k+1)  =  (1/3)^k

The interval width one level down is exactly the scale of the level above. It is
also why the general separation bound cannot be strict: that bound IS this
quantity. -/
theorem window_succ (k : Nat) :
    ratMul (ratPow (ratNat.{u} 1 3) (k + 1)) (ratNat.{u} 3 1)
      = ratPow (ratNat.{u} 1 3) k := by
  have hth : ratNat.{u} 1 3 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have h3 : ratNat.{u} 3 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have hk : ratPow (ratNat.{u} 1 3) k ∈ NumberTheory.Rat.{u} := ratPow_mem hth k
  have h31 : ratMul (ratNat.{u} 1 3) (ratNat.{u} 3 1) = ratOne.{u} := by
    rw [ratNat_mul (by omega) (by omega), ← ratNat_one_one]
    exact (ratNat_eq_iff (by omega) (by omega)).mpr (by omega)
  rw [ratPow_succ, ratMul_assoc hk hth h3, h31, ratMul_one hk]

/-- Sequences agreeing before `k` and differing there are STRICTLY separated
at depth `k+1`.

    v_b(k+1) + 3*(1/3)^(k+1)   <   v_c(k+1)

`b`'s upper end is strictly below `c`'s lower end, so the two nested families
come apart rather than touching. The margin is `(1/3)^k`: the differing bit
contributes `2*(1/3)^k` by `takeBits_step`, and the window is only `(1/3)^k`.

THE GENERAL SEPARATION LEMMA CANNOT DO THIS. Its gap at this depth equals the
window exactly, giving `<=` and never `<`. Only the exact step, which knows the
bit is worth twice the window, leaves room. -/
theorem takeBits_strict_sep (b c : Nat → Bool) (k : Nat)
    (hpre : takeBits b k = takeBits c k) (hb : b k = false) (hc : c k = true) :
    ratLt (ratAdd (ratMul (ratNat.{u} 2 1) (triadicOf.{u} (takeBits b (k + 1))))
        (ratMul (ratPow (ratNat.{u} 1 3) (k + 1)) (ratNat.{u} 3 1)))
      (ratMul (ratNat.{u} 2 1) (triadicOf.{u} (takeBits c (k + 1)))) := by
  have hth : ratNat.{u} 1 3 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have h2 : ratNat.{u} 2 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have hk : ratPow (ratNat.{u} 1 3) k ∈ NumberTheory.Rat.{u} := ratPow_mem hth k
  have hk0 : ratLt ratZero.{u} (ratPow (ratNat.{u} 1 3) k) :=
    ratPow_pos hth (ratNat_one_pos (by omega)) k
  have hone_one : ratAdd ratOne.{u} ratOne.{u} = ratNat.{u} 2 1 := by
    rw [← ratNat_one_one, ratNat_add_same_denom (by omega : (0:Nat) < 1)]
  have hstepb := takeBits_step b k
  have hstepc := takeBits_step c k
  rw [hb, triadicOf_false, ratMul_zero h2, ratMul_zero hk,
    ratAdd_zero (triLow_mem b k)] at hstepb
  rw [hc, triadicOf_true, ratMul_one h2] at hstepc
  -- `rw [<- hone_one]` on the GOAL would rewrite EVERY `ratNat 2 1`, including
  -- the coefficient of `v` itself. Prove the doubling as its own equation, where
  -- only one occurrence exists, and rewrite with that.
  have hdouble : ratMul (ratPow (ratNat.{u} 1 3) k) (ratNat.{u} 2 1)
      = ratAdd (ratPow (ratNat.{u} 1 3) k) (ratPow (ratNat.{u} 1 3) k) := by
    rw [← hone_one, ratMul_add hk ratOne_mem_Rat ratOne_mem_Rat, ratMul_one hk]
  rw [window_succ k, hstepb, hstepc, hpre, hdouble]
  exact (ratAdd_lt_add_left_iff (triLow_mem c k) hk
    (ratAdd_mem_Rat hk hk)).mpr (ratLt_add_pos hk hk hk0)

#print axioms SetTheory.window_succ
#print axioms SetTheory.takeBits_strict_sep


--
--
--
--

/-- The dyadic readout, as APPROXIMATION rather than naming.

The expensive direction of `set, uncountability`, stated over the base where it
can be true. At every depth a real in range is bracketed by some bit string's
value and that value plus the window.

WHY BASE TWO AND NOT BASE THREE. A first attempt named this over `triadicOf` as
an exact naming --- every real in range IS `triadicReal` of some sequence --- and
`triadicOf_gap` refutes it: the base-three image is a Cantor set with a hole,
so most reals are named by nothing. Base two has no hole: `dyadicOf`'s two
branches meet, which is exactly the property that makes its SEPARATION fail and
its SURJECTION work. The two bases are for different halves of this row.

WHY APPROXIMATION AND NOT NAMING, even here. Asking for an `s` with
`realLOf (dyadicOf s) = x` demands the real be a dyadic rational. Asking for a
BRACKET at every depth is what a constructive readout can deliver and what a
locator supplies, and it is the shape `IsCauchyReal` and `IsNested` both take.

NOT PROVED. Naming it is the first half; deriving it from a locator, or the
landmark from it, is the second and is not done. Stated so a future attempt has
a TRUE target --- which the withdrawn `TriadicReadout` was not. -/
def DyadicApprox : Prop :=
  ∀ x : ZFSet.{u}, x ∈ RealL.{u} →
    realLLe (realLOf ratZero.{u}) x →
    realLLe x (realLOf (ratNat.{u} 2 1)) →
    ∀ n : Nat, ∃ s : List Bool, s.length = n ∧
      realLLe (realLOf (dyadicOf.{u} s)) x ∧
      realLLe x (realLOf (ratAdd (dyadicOf.{u} s)
        (ratMul (ratNat.{u} 2 1) (ratPow (ratNat.{u} 1 2) n))))

#print axioms SetTheory.DyadicApprox
/-- A one-bit dyadic string is worth its bit, as two lemmas rather than an
`if` --- an inline `if` on a `Bool` needs a `Decidable` instance that can fall
back to `Classical`. -/
theorem dyadicOf_true : dyadicOf.{u} [true] = ratOne.{u} := by
  show ratAdd ratOne.{u} (ratMul (ratNat.{u} 1 2) ratZero.{u}) = ratOne.{u}
  rw [ratMul_zero (ratNat_mem_Rat (by omega)), ratAdd_zero ratOne_mem_Rat]

theorem dyadicOf_false : dyadicOf.{u} [false] = ratZero.{u} := by
  show ratMul (ratNat.{u} 1 2) ratZero.{u} = ratZero.{u}
  exact ratMul_zero (ratNat_mem_Rat (by omega))

#print axioms SetTheory.dyadicOf_true
#print axioms SetTheory.dyadicOf_false

--
--

/-! ## The hole in the image, from `probe-nodegap.lean` -/

/-- Every node's doubled point misses the open interval `(1,2)`. -/
theorem triadicOf_gap (s : List Bool) :
    ratLe (ratMul (ratNat.{u} 2 1) (triadicOf.{u} s)) ratOne.{u}
    ∨ ratLe (ratNat.{u} 2 1) (ratMul (ratNat.{u} 2 1) (triadicOf.{u} s)) := by
  have h2 : ratNat.{u} 2 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have h3 : ratNat.{u} 3 1 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have hth : ratNat.{u} 1 3 ∈ NumberTheory.Rat.{u} := ratNat_mem_Rat (by omega)
  have hth0 : ratLe ratZero.{u} (ratNat.{u} 1 3) :=
    ratLe_of_lt ratZero_mem_Rat hth (ratNat_one_pos (by omega))
  have h20 : ratLe ratZero.{u} (ratNat.{u} 2 1) :=
    ratLe_of_lt ratZero_mem_Rat h2 (ratNat_pos (by omega))
  cases s with
  | nil =>
      left
      show ratLe (ratMul (ratNat.{u} 2 1) ratZero.{u}) ratOne.{u}
      rw [ratMul_zero h2]
      exact ratLe_of_lt ratZero_mem_Rat ratOne_mem_Rat ratZero_lt_one
  | cons b t =>
      have hT := triadicOf_mem_Rat.{u} t
      have hle3 := triadicOf_le_three.{u} t
      cases b with
      | false =>
          left
          -- `2 * tri (false :: t) = (1/3) * (2 * tri t) <= (1/3) * 3 = 1`
          show ratLe (ratMul (ratNat.{u} 2 1)
            (ratMul (ratNat.{u} 1 3) (triadicOf.{u} t))) ratOne.{u}
          have hre : ratMul (ratNat.{u} 2 1) (ratMul (ratNat.{u} 1 3) (triadicOf.{u} t))
              = ratMul (ratNat.{u} 1 3) (ratMul (ratNat.{u} 2 1) (triadicOf.{u} t)) := by
            rw [← ratMul_assoc h2 hth hT, ratMul_comm h2 hth, ratMul_assoc hth h2 hT]
          rw [hre]
          have hstep := ratMul_le_mul_of_le hth hth (ratMul_mem_Rat h2 hT) h3
            hth0 (ratZero_le_mul h2 hT h20 (triadicOf_nonneg t))
            (ratLe_refl hth) hle3
          have hone : ratMul (ratNat.{u} 1 3) (ratNat.{u} 3 1) = ratOne.{u} := by
            rw [ratNat_mul (by omega) (by omega), ← ratNat_one_one,
              ratNat_eq_iff (by omega) (by omega)]
          rwa [hone] at hstep
      | true =>
          right
          -- `2 * tri (true :: t) = 2 + (1/3)(2 * tri t) >= 2`
          show ratLe (ratNat.{u} 2 1) (ratMul (ratNat.{u} 2 1)
            (ratAdd ratOne.{u} (ratMul (ratNat.{u} 1 3) (triadicOf.{u} t))))
          rw [ratMul_add h2 ratOne_mem_Rat (ratMul_mem_Rat hth hT), ratMul_one h2]
          exact ratLe_self_add h2 (ratMul_mem_Rat h2 (ratMul_mem_Rat hth hT))
            (ratZero_le_mul h2 (ratMul_mem_Rat hth hT) h20
              (ratZero_le_mul hth hT hth0 (triadicOf_nonneg t)))

#print axioms SetTheory.triadicOf_gap

end SetTheory

namespace ZFSet
export SetTheory (BinaryDC Locates LocatorDC dyadicOf dyadicOf_half_le dyadicOf_head_separation dyadicOf_le_sharp dyadicOf_le_two dyadicOf_mem_Rat dyadicOf_nonneg dyadicOf_split dyadicOf_split_separation leftEnd ratNat_two_mul_half rightEnd)
end ZFSet
