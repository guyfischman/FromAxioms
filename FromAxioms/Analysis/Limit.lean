/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Limits of sequences of reals.

Convergence in the rational-`ε` form, over the witnessed strict order of
`Topology.lean`. The point of interest is that limits are unique without
excluded middle: two limits that differed would be separated by a rational, and
that rational contradicts both convergence statements at once.
-/

import FromAxioms.Constructive.Omniscience
import FromAxioms.Topology.Topology

universe u

open Algebra Constructive NumberTheory SetTheory Topology
namespace Analysis

def realSeqs : ZFSet.{u} :=
  sep (fun f => IsFunction f ∧ domain f = omega.{u}) (powerset (prod omega.{u} Real.{u}))

theorem mem_realSeqs_iff (f : ZFSet.{u}) :
    f ∈ realSeqs.{u} ↔ f ⊆ prod omega.{u} Real.{u} ∧ IsFunction f ∧ domain f = omega.{u} :=
  Iff.trans (mem_sep_iff _ _ _)
    ⟨fun h => ⟨(mem_powerset_iff _ _).mp h.left, h.right⟩,
     fun h => ⟨(mem_powerset_iff _ _).mpr h.left, h.right⟩⟩

theorem app_mem_Real {f : ZFSet.{u}} (hf : f ∈ realSeqs.{u}) {n : ZFSet.{u}}
    (hn : n ∈ omega.{u}) : app f n ∈ Real.{u} := by
  obtain ⟨hsub, hfun, hdom⟩ := (mem_realSeqs_iff f).mp hf
  exact mem_prod_right (hsub _ (opair_app_mem hfun (hdom ▸ hn)))


/-- `f n` is eventually within `ε` of `L`, for every positive rational `ε`. The
bounds are stated with the witnessed `realLt`, so a proof of convergence carries
the rationals that make it true. -/
def TendsTo (f L : ZFSet.{u}) : Prop :=
  ∀ ε, ε ∈ NumberTheory.Rat.{u} → ratLt ratZero.{u} ε → ∃ N, N ∈ omega.{u} ∧
    ∀ n, n ∈ omega.{u} → N ⊆ n →
      realLt (app f n) (realAdd L (ratCut ε)) ∧
        realLt (realAdd L (ratCut (ratNeg ε))) (app f n)

/-- If `q` is in one limit then it is in the other: pick `s` above `q` inside the
first cut, note the sequence is eventually above `s`, and the second limit's
upper bound then puts `q` inside it. -/
theorem tendsTo_subset {f x y : ZFSet.{u}} (hf : f ∈ realSeqs.{u}) (hx : x ∈ Real.{u})
    (hy : y ∈ Real.{u}) (hxt : TendsTo f x) (hyt : TendsTo f y) :
    ∀ q, q ∈ x → q ∈ y := by
  intro q hqx
  have hxc := (mem_Real_iff x).mp hx
  have hqR := hxc.subset _ hqx
  obtain ⟨s, hsx, hqs⟩ := hxc.no_greatest q hqx
  have hsR := hxc.subset _ hsx
  obtain ⟨t, htx, hst⟩ := hxc.no_greatest s hsx
  have htR := hxc.subset _ htx
  obtain ⟨t', ht'x, htt'⟩ := hxc.no_greatest t htx
  have ht'R := hxc.subset _ ht'x
  -- the two margins
  have hposdiff : ∀ a b : ZFSet.{u}, a ∈ NumberTheory.Rat.{u} → b ∈ NumberTheory.Rat.{u} → ratLt a b →
      ratLt ratZero.{u} (ratAdd b (ratNeg a)) := by
    intro a b haR hbR hab
    have := (ratAdd_lt_add_left_iff (ratNeg_mem_Rat haR) haR hbR).mpr hab
    rw [ratAdd_comm (ratNeg_mem_Rat haR) haR, ratAdd_neg haR,
      ratAdd_comm (ratNeg_mem_Rat haR) hbR] at this
    exact this
  obtain ⟨N₁, hN₁, hlow⟩ := hxt (ratAdd t (ratNeg s)) (ratAdd_mem_Rat htR (ratNeg_mem_Rat hsR))
    (hposdiff s t hsR htR hst)
  obtain ⟨N₂, hN₂, hhigh⟩ := hyt (ratAdd s (ratNeg q)) (ratAdd_mem_Rat hsR (ratNeg_mem_Rat hqR))
    (hposdiff q s hqR hsR hqs)
  obtain ⟨n, hn, hn₁, hn₂⟩ := exists_upper_omega hN₁ hN₂
  have hfn : app f n ∈ Real.{u} := app_mem_Real hf hn
  have hfnc := (mem_Real_iff _).mp hfn
  -- `s` is in the sequence value at `n`
  have hsfn : s ∈ app f n := by
    obtain ⟨a, hafn, hano⟩ := (hlow n hn hn₁).right
    have hsmem : s ∈ realAdd x (ratCut (ratNeg (ratAdd t (ratNeg s)))) := by
      refine (mem_realAdd_iff _ _ s).mpr ⟨hsR, t', ht'x,
        ratAdd s (ratNeg t'), (mem_ratCut_iff _ _).mpr
          ⟨ratAdd_mem_Rat hsR (ratNeg_mem_Rat ht'R), ?_⟩, ?_⟩
      · -- `s - t' < s - t = -(t - s)`
        have hlt : ratLt (ratAdd s (ratNeg t')) (ratAdd s (ratNeg t)) :=
          (ratAdd_lt_add_left_iff hsR (ratNeg_mem_Rat ht'R) (ratNeg_mem_Rat htR)).mpr
            ((ratNeg_lt_neg_iff ht'R htR).mpr htt')
        have heq : ratAdd s (ratNeg t) = ratNeg (ratAdd t (ratNeg s)) := by
          refine ratNeg_injective (ratAdd_mem_Rat hsR (ratNeg_mem_Rat htR))
            (ratNeg_mem_Rat (ratAdd_mem_Rat htR (ratNeg_mem_Rat hsR))) ?_
          rw [ratNeg_ratNeg (ratAdd_mem_Rat htR (ratNeg_mem_Rat hsR))]
          refine ratAdd_left_cancel (ratAdd_mem_Rat hsR (ratNeg_mem_Rat htR))
            (ratNeg_mem_Rat (ratAdd_mem_Rat hsR (ratNeg_mem_Rat htR)))
            (ratAdd_mem_Rat htR (ratNeg_mem_Rat hsR)) ?_
          rw [ratAdd_neg (ratAdd_mem_Rat hsR (ratNeg_mem_Rat htR)),
            ratAdd_assoc hsR (ratNeg_mem_Rat htR) (ratAdd_mem_Rat htR (ratNeg_mem_Rat hsR)),
            ← ratAdd_assoc (ratNeg_mem_Rat htR) htR (ratNeg_mem_Rat hsR),
            ratAdd_comm (ratNeg_mem_Rat htR) htR, ratAdd_neg htR,
            ratZero_add (ratNeg_mem_Rat hsR), ratAdd_neg hsR]
        rw [← heq]
        exact hlt
      · rw [← ratAdd_assoc ht'R hsR (ratNeg_mem_Rat ht'R), ratAdd_comm ht'R hsR,
          ratAdd_assoc hsR ht'R (ratNeg_mem_Rat ht'R), ratAdd_neg ht'R, ratAdd_zero hsR]
    exact hfnc.down _ hafn _ hsR
      (ratLt_of_mem_of_not_mem ((mem_Real_iff _).mp
        (realAdd_mem_Real hx (ratCut_mem_Real (ratNeg_mem_Rat
          (ratAdd_mem_Rat htR (ratNeg_mem_Rat hsR)))))) hsmem (hfnc.subset _ hafn) hano)
  -- and the upper bound at `n` puts `s` inside `y + (s - q)`
  obtain ⟨b, hbmem, hbfn⟩ := (hhigh n hn hn₂).left
  have hsy : s ∈ realAdd y (ratCut (ratAdd s (ratNeg q))) :=
    ((mem_Real_iff _).mp (realAdd_mem_Real hy (ratCut_mem_Real
      (ratAdd_mem_Rat hsR (ratNeg_mem_Rat hqR))))).down _ hbmem _ hsR
      (ratLt_of_mem_of_not_mem hfnc hsfn
        (((mem_Real_iff _).mp (realAdd_mem_Real hy (ratCut_mem_Real
          (ratAdd_mem_Rat hsR (ratNeg_mem_Rat hqR))))).subset _ hbmem) hbfn)
  obtain ⟨-, p, hpy, r, hrcut, hspr⟩ := (mem_realAdd_iff _ _ s).mp hsy
  obtain ⟨hrR, hrlt⟩ := (mem_ratCut_iff _ _).mp hrcut
  have hpR := ((mem_Real_iff y).mp hy).subset _ hpy
  -- `q < p`, because `r < s - q`
  refine ((mem_Real_iff y).mp hy).down _ hpy _ hqR ?_
  have hqr : ratLt (ratAdd q r) s := by
    have := (ratAdd_lt_add_left_iff hqR hrR (ratAdd_mem_Rat hsR (ratNeg_mem_Rat hqR))).mpr hrlt
    rw [← ratAdd_assoc hqR hsR (ratNeg_mem_Rat hqR), ratAdd_comm hqR hsR,
      ratAdd_assoc hsR hqR (ratNeg_mem_Rat hqR), ratAdd_neg hqR, ratAdd_zero hsR] at this
    exact this
  rw [hspr] at hqr
  exact (ratAdd_lt_add_right_iff hrR hqR hpR).mp hqr

/-- Limits are unique, and constructively: a rational separating two limits
contradicts both convergence statements at once. -/
theorem tendsTo_unique {f L L' : ZFSet.{u}} (hf : f ∈ realSeqs.{u}) (hL : L ∈ Real.{u})
    (hL' : L' ∈ Real.{u}) (h : TendsTo f L) (h' : TendsTo f L') : L = L' :=
  ext _ _ (fun q => ⟨fun hq => tendsTo_subset hf hL hL' h h' q hq,
    fun hq => tendsTo_subset hf hL' hL h' h q hq⟩)

/-! ## Series

Partial sums are a Lean-level recursion turned into a set function by `natSeq`,
exactly as `Cauchy.lean` builds rational sequences. A series has a sum when its
partial sums converge, and the sum is unique because limits are. -/

def realPartial (f : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => realZero.{u}
  | n + 1 => realAdd (realPartial f n) (app f (ofNat.{u} n))

theorem realPartial_mem_Real {f : ZFSet.{u}} (hf : f ∈ realSeqs.{u}) :
    ∀ n : Nat, realPartial f n ∈ Real.{u}
  | 0 => realZero_mem_Real
  | n + 1 => realAdd_mem_Real (realPartial_mem_Real hf n) (app_mem_Real hf (ofNat_mem_omega n))

def seriesSeq (f : ZFSet.{u}) : ZFSet.{u} := natSeq Real.{u} (realPartial f)

theorem seriesSeq_mem_realSeqs {f : ZFSet.{u}} (hf : f ∈ realSeqs.{u}) :
    seriesSeq f ∈ realSeqs.{u} := by
  refine (mem_realSeqs_iff _).mpr ⟨?_, ?_, ?_⟩
  · show graphOn omega.{u} Real.{u} (natFun Real.{u} (realPartial f)) ⊆ _
    exact graphOn_subset _ _ _
  · show IsFunction (graphOn omega.{u} Real.{u} (natFun Real.{u} (realPartial f)))
    exact graphOn_isFunction _ _ _
  · show domain (graphOn omega.{u} Real.{u} (natFun Real.{u} (realPartial f))) = _
    exact graphOn_domain (natFun_mem (realPartial_mem_Real hf))

/-- A series sums to `S` when its partial sums converge to `S`. -/
def HasSum (f S : ZFSet.{u}) : Prop := TendsTo (seriesSeq f) S

/-- A series has at most one sum. -/
theorem hasSum_unique {f S S' : ZFSet.{u}} (hf : f ∈ realSeqs.{u}) (hS : S ∈ Real.{u})
    (hS' : S' ∈ Real.{u}) (h : HasSum f S) (h' : HasSum f S') : S = S' :=
  tendsTo_unique (seriesSeq_mem_realSeqs hf) hS hS' h h'

/-! ## Sequences of sets, and countable additivity

The shape a measure has to satisfy. Nothing is proved about it here beyond what
the definition forces: constructing a non-trivial measure needs the sum of a
series of lengths, and that is the next thing to build. -/

def setSeqs (A : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun E => IsFunction E ∧ domain E = omega.{u}) (powerset (prod omega.{u} A))

theorem mem_setSeqs_iff (A E : ZFSet.{u}) :
    E ∈ setSeqs A ↔ E ⊆ prod omega.{u} A ∧ IsFunction E ∧ domain E = omega.{u} :=
  Iff.trans (mem_sep_iff _ _ _)
    ⟨fun h => ⟨(mem_powerset_iff _ _).mp h.left, h.right⟩,
     fun h => ⟨(mem_powerset_iff _ _).mpr h.left, h.right⟩⟩

theorem app_setSeq_mem {A E : ZFSet.{u}} (hE : E ∈ setSeqs A) {n : ZFSet.{u}}
    (hn : n ∈ omega.{u}) : app E n ∈ A := by
  obtain ⟨hsub, hfun, hdom⟩ := (mem_setSeqs_iff A E).mp hE
  exact mem_prod_right (hsub _ (opair_app_mem hfun (hdom ▸ hn)))

/-- The sets of a sequence are pairwise disjoint. -/
def PairwiseDisjoint (E : ZFSet.{u}) : Prop :=
  ∀ m, m ∈ omega.{u} → ∀ n, n ∈ omega.{u} → m ≠ n → inter (app E m) (app E n) = empty.{u}

/-- The union of a sequence of sets.

For `E` a function on `omega` the members of `range E` are exactly the terms,
so a point lies in `sUnion (range E)` exactly when it lies in some term; that
is `mem_seqUnion_iff`, and `IsCountablyAdditive` below needs exactly that of
this definition.

Do not interpose an `imageIn` layer. `imageIn f S y` SEPARATES `y`, so
`sUnion (imageIn E omega (sUnion (range E)))` keeps only those points of the
union that are themselves a term of the sequence. For a sequence of sets of
points there are none unless one term is an ELEMENT of another, so that
expression is `empty` for every sequence a content is asked about, and
`IsCountablyAdditive` built on it constrains the series alone. -/
def seqUnion (E : ZFSet.{u}) : ZFSet.{u} := sUnion (range E)

/-- A point is in the union exactly when it is in some term.

Both directions need only that `E` is a function on `omega`: forward, a member
of `range E` is `app E a` for an `a` in the domain; backward, each `app E n` is
in the range by `app_mem_range`. -/
theorem mem_seqUnion_iff {A E : ZFSet.{u}} (hE : E ∈ setSeqs A) (z : ZFSet.{u}) :
    z ∈ seqUnion E ↔ ∃ n, n ∈ omega.{u} ∧ z ∈ app E n := by
  obtain ⟨-, hfun, hdom⟩ := (mem_setSeqs_iff A E).mp hE
  refine Iff.trans (mem_sUnion_iff _ _) ⟨?_, ?_⟩
  · rintro ⟨y, hy, hzy⟩
    obtain ⟨a, hae⟩ := (mem_range_iff y E).mp hy
    have ha : a ∈ domain E := (mem_domain_iff a E).mpr ⟨y, hae⟩
    rw [← app_eq hfun hae] at hzy
    exact ⟨a, hdom ▸ ha, hzy⟩
  · rintro ⟨n, hn, hzn⟩
    exact ⟨app E n, app_mem_range hfun (hdom ▸ hn), hzn⟩

#print axioms mem_seqUnion_iff

/-- A content is countably additive when the values on a disjoint sequence sum to
the value on the union. -/
def IsCountablyAdditive (m A : ZFSet.{u}) : Prop :=
  ∀ E, E ∈ setSeqs A → PairwiseDisjoint E → seqUnion E ∈ A →
    HasSum (compOn m E omega.{u} Real.{u}) (app m (seqUnion E))

/-! ## Monotone convergence is not constructive

A non-decreasing bounded sequence of reals need not converge: from the limit of
the sequence that steps from `0` to `1` as soon as a bit is set, one reads off
whether any bit is set. So the monotone convergence theorem implies `LPO`, and
this file states it as a hypothesis rather than proving it. -/

def MonotoneSeq (f : ZFSet.{u}) : Prop :=
  ∀ m, m ∈ omega.{u} → ∀ n, n ∈ omega.{u} → m ⊆ n → realLe (app f m) (app f n)

def BoundedAbove (f B : ZFSet.{u}) : Prop :=
  ∀ n, n ∈ omega.{u} → realLe (app f n) B

def MonotoneConvergence : Prop :=
  ∀ f B : ZFSet.{u}, f ∈ realSeqs.{u} → B ∈ Real.{u} → MonotoneSeq f → BoundedAbove f B →
    ∃ L, L ∈ Real.{u} ∧ TendsTo f L

/-- Has a bit been set below `n`? -/
def hitBy (α : Nat → Bool) (n : Nat) : Bool := (List.range n).any α

theorem hitBy_true_iff {α : Nat → Bool} {n : Nat} :
    hitBy α n = true ↔ ∃ i, i < n ∧ α i = true := by
  rw [hitBy, List.any_eq_true]
  exact ⟨fun ⟨i, hi, hα⟩ => ⟨i, List.mem_range.mp hi, hα⟩,
    fun ⟨i, hi, hα⟩ => ⟨i, List.mem_range.mpr hi, hα⟩⟩

theorem hitBy_mono {α : Nat → Bool} {m n : Nat} (hmn : m ≤ n) (h : hitBy α m = true) :
    hitBy α n = true := by
  obtain ⟨i, hi, hα⟩ := hitBy_true_iff.mp h
  exact hitBy_true_iff.mpr ⟨i, by omega, hα⟩

/-- The staircase: `0` until a bit is set, `1` afterwards. -/
def stairSeq (α : Nat → Bool) : ZFSet.{u} :=
  natSeq Real.{u} (fun n => ratCut (if hitBy α n then ratOne.{u} else ratZero.{u}))

theorem stair_mem_Real (α : Nat → Bool) (n : Nat) :
    ratCut (if hitBy α n then ratOne.{u} else ratZero.{u}) ∈ Real.{u} := by
  cases h : hitBy α n
  · rw [if_neg Bool.noConfusion]
    exact ratCut_mem_Real ratZero_mem_Rat
  · rw [if_pos rfl]
    exact ratCut_mem_Real ratOne_mem_Rat

theorem stairSeq_mem_realSeqs (α : Nat → Bool) : stairSeq.{u} α ∈ realSeqs.{u} := by
  refine (mem_realSeqs_iff _).mpr ⟨?_, ?_, ?_⟩
  · show graphOn omega.{u} Real.{u} (natFun Real.{u} _) ⊆ _
    exact graphOn_subset _ _ _
  · show IsFunction (graphOn omega.{u} Real.{u} (natFun Real.{u} _))
    exact graphOn_isFunction _ _ _
  · show domain (graphOn omega.{u} Real.{u} (natFun Real.{u} _)) = _
    exact graphOn_domain (natFun_mem (stair_mem_Real α))

theorem app_stairSeq (α : Nat → Bool) (n : Nat) :
    app (stairSeq.{u} α) (ofNat.{u} n)
      = ratCut (if hitBy α n then ratOne.{u} else ratZero.{u}) :=
  app_natSeq (stair_mem_Real α) n

/-! ### Where the cost of monotone convergence sits -/

/-- Monotone convergence implies `LPO`. -/
theorem lpo_of_monotoneConvergence (h : MonotoneConvergence.{u}) : LPO := by
  intro α
  -- the staircase is non-decreasing and bounded by `1`
  have hmono : MonotoneSeq (stairSeq.{u} α) := by
    intro m hm n hn hmn
    obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
    obtain ⟨j, rfl⟩ := (mem_omega_iff n).mp hn
    rw [app_stairSeq, app_stairSeq]
    cases hi : hitBy α i
    · rw [if_neg Bool.noConfusion]
      intro q hq
      obtain ⟨hqR, hq0⟩ := (mem_ratCut_iff _ q).mp hq
      cases hj : hitBy α j
      · rw [if_neg Bool.noConfusion]
        exact (mem_ratCut_iff _ q).mpr ⟨hqR, hq0⟩
      · rw [if_pos rfl]
        exact (mem_ratCut_iff _ q).mpr ⟨hqR, ratLt_trans hqR ratZero_mem_Rat ratOne_mem_Rat
          hq0 ratZero_lt_one⟩
    · have hj : hitBy α j = true := hitBy_mono ((ofNat_subset_iff i j).mp hmn) hi
      rw [if_pos rfl, if_pos hj]
      exact fun q hq => hq
  have hbound : BoundedAbove (stairSeq.{u} α) (ratCut ratOne.{u}) := by
    intro n hn
    obtain ⟨i, rfl⟩ := (mem_omega_iff n).mp hn
    rw [app_stairSeq]
    cases hi : hitBy α i
    · rw [if_neg Bool.noConfusion]
      intro q hq
      obtain ⟨hqR, hq0⟩ := (mem_ratCut_iff _ q).mp hq
      exact (mem_ratCut_iff _ q).mpr ⟨hqR, ratLt_trans hqR ratZero_mem_Rat ratOne_mem_Rat
        hq0 ratZero_lt_one⟩
    · rw [if_pos rfl]
      exact fun q hq => hq
  obtain ⟨L, hL, hlim⟩ := h _ _ (stairSeq_mem_realSeqs α) (ratCut_mem_Real ratOne_mem_Rat)
    hmono hbound
  -- a margin with room on both sides of `1`
  obtain ⟨t, htQ, ht0, htlt⟩ := exists_add_self_lt ratOne_mem_Rat ratZero_lt_one
  obtain ⟨N, hN, hbnd⟩ := hlim t htQ ht0
  obtain ⟨k, rfl⟩ := (mem_omega_iff N).mp hN
  cases hk : hitBy α k
  · -- no bit below `k`; a later bit would force the sequence to `1`
    refine Or.inr (fun n => ?_)
    cases hn : α n
    · rfl
    · exfalso
      obtain ⟨m, hm₁, hm₂⟩ : ∃ m : Nat, k ≤ m ∧ hitBy α m = true :=
        ⟨n + 1 + k, by omega, hitBy_true_iff.mpr ⟨n, by omega, hn⟩⟩
      obtain ⟨hup, hlo⟩ := hbnd (ofNat.{u} m) (ofNat_mem_omega m) ((ofNat_subset_iff k m).mpr hm₁)
      rw [app_stairSeq, if_pos hm₂] at hup
      -- `1 < L + t` puts `t` inside `L`
      obtain ⟨q, hqmem, hq1⟩ := hup
      obtain ⟨hqR, l, hl, d, hd, hqld⟩ := (mem_realAdd_iff L _ q).mp hqmem
      obtain ⟨hdR, hdt⟩ := (mem_ratCut_iff t d).mp hd
      have hlR := ((mem_Real_iff L).mp hL).subset _ hl
      have h1q : ratLe ratOne.{u} q := by
        rcases ratLt_trichotomy hqR ratOne_mem_Rat with hlt | heq | hgt
        · exact absurd ((mem_ratCut_iff ratOne.{u} q).mpr ⟨hqR, hlt⟩) hq1
        · exact heq ▸ ratLe_refl hqR
        · exact hgt.left
      have htl : ratLt t l := by
        -- `l = q - d > 1 - t > t`
        have hstep : ratLt (ratAdd t d) q :=
          ratLt_of_lt_of_le (ratAdd_mem_Rat htQ hdR) ratOne_mem_Rat hqR
            (ratLt_trans (ratAdd_mem_Rat htQ hdR) (ratAdd_mem_Rat htQ htQ) ratOne_mem_Rat
              ((ratAdd_lt_add_left_iff htQ hdR htQ).mpr hdt) htlt) h1q
        rw [hqld] at hstep
        exact (ratAdd_lt_add_right_iff hdR htQ hlR).mp hstep
      have htL : t ∈ L := ((mem_Real_iff L).mp hL).down _ hl _ htQ htl
      -- but the sequence is still `0` at `k`, so `L - t` has nothing below it
      obtain ⟨hup', hlo'⟩ := hbnd (ofNat.{u} k) (ofNat_mem_omega k) (fun w hw => hw)
      rw [app_stairSeq, if_neg (by rw [hk]; exact Bool.noConfusion)] at hlo'
      obtain ⟨r, hr0, hrno⟩ := hlo'
      obtain ⟨hrR, hrlt⟩ := (mem_ratCut_iff _ r).mp hr0
      refine hrno ((mem_realAdd_iff L _ r).mpr ⟨hrR, t, htL, ratAdd r (ratNeg t),
        (mem_ratCut_iff _ _).mpr ⟨ratAdd_mem_Rat hrR (ratNeg_mem_Rat htQ), ?_⟩, ?_⟩)
      · -- `r - t < -t` because `r < 0`
        have := (ratAdd_lt_add_right_iff (ratNeg_mem_Rat htQ) hrR ratZero_mem_Rat).mpr hrlt
        rwa [ratZero_add (ratNeg_mem_Rat htQ)] at this
      · rw [← ratAdd_assoc htQ hrR (ratNeg_mem_Rat htQ), ratAdd_comm htQ hrR,
          ratAdd_assoc hrR htQ (ratNeg_mem_Rat htQ), ratAdd_neg htQ, ratAdd_zero hrR]
  · obtain ⟨i, hi, hα⟩ := hitBy_true_iff.mp (by rw [hk] : hitBy α k = true)
    exact Or.inl ⟨i, hα⟩

/-! ## Audit -/

#print axioms tendsTo_unique
#print axioms hasSum_unique
#print axioms lpo_of_monotoneConvergence
/-- Every partial sum of a vanishing sequence vanishes. The induction is on
the recursion `realPartial` is defined by, so nothing is decided. -/
theorem realPartial_of_zero {f : ZFSet.{u}} (h : ∀ n : Nat, app f (ofNat.{u} n) = realZero.{u}) :
    ∀ n : Nat, realPartial f n = realZero.{u}
  | 0 => rfl
  | n + 1 => by
    rw [realPartial, realPartial_of_zero h n, h n]
    exact realAdd_zero realZero_mem_Real

/-- A vanishing series sums to zero. `N` is `0`: the bound holds at every
index at once, so no modulus is computed. -/
theorem hasSum_zero_of_vanishing {f : ZFSet.{u}} (hf : f ∈ realSeqs.{u})
    (h : ∀ n : Nat, app f (ofNat.{u} n) = realZero.{u}) :
    HasSum f realZero.{u} := by
  intro ε hε hε0
  refine ⟨ofNat.{u} 0, ofNat_mem_omega 0, fun n hn _ => ?_⟩
  obtain ⟨k, rfl⟩ := (mem_omega_iff n).mp hn
  rw [seriesSeq, app_natSeq (fun m => realPartial_mem_Real hf m) k,
    realPartial_of_zero h k,
    realAdd_comm realZero_mem_Real (ratCut_mem_Real hε),
    realAdd_zero (ratCut_mem_Real hε)]
  refine ⟨?_, ?_⟩
  · -- `0 < ε`: the rational `0` is below `ε` and not below `0`
    exact ⟨ratZero.{u}, (mem_ratCut_iff _ _).mpr ⟨ratZero_mem_Rat, hε0⟩,
      fun hm => ratLt_irrefl ((mem_ratCut_iff _ _).mp hm).right⟩
  · -- `-ε < 0`: the rational `-ε` is below `0` and not below itself
    rw [realAdd_comm realZero_mem_Real (ratCut_mem_Real (ratNeg_mem_Rat hε)),
      realAdd_zero (ratCut_mem_Real (ratNeg_mem_Rat hε))]
    have hneg : ratLt (ratNeg ε) ratZero.{u} := by
      have := (ratNeg_lt_neg_iff hε ratZero_mem_Rat).mpr hε0
      rwa [ratNeg_zero] at this
    have hneg : ratLt (ratNeg ε) ratZero.{u} := by
      have := (ratNeg_lt_neg_iff hε ratZero_mem_Rat).mpr hε0
      rwa [ratNeg_zero] at this
    exact ⟨ratNeg ε, (mem_ratCut_iff _ _).mpr ⟨ratNeg_mem_Rat hε, hneg⟩,
      fun hm => ratLt_irrefl ((mem_ratCut_iff _ _).mp hm).right⟩

#print axioms mem_realSeqs_iff
#print axioms app_mem_Real
#print axioms tendsTo_subset
#print axioms realPartial_mem_Real
#print axioms seriesSeq_mem_realSeqs
#print axioms mem_setSeqs_iff
#print axioms app_setSeq_mem
#print axioms hitBy_true_iff
#print axioms hitBy_mono
#print axioms stair_mem_Real
#print axioms stairSeq_mem_realSeqs
#print axioms app_stairSeq
#print axioms realPartial_of_zero
end Analysis
#print axioms Analysis.hasSum_zero_of_vanishing
namespace ZFSet
export Analysis (BoundedAbove HasSum IsCountablyAdditive MonotoneConvergence MonotoneSeq PairwiseDisjoint TendsTo app_mem_Real app_setSeq_mem app_stairSeq hasSum_unique hasSum_zero_of_vanishing hitBy hitBy_mono hitBy_true_iff lpo_of_monotoneConvergence mem_realSeqs_iff mem_seqUnion_iff mem_setSeqs_iff realPartial realPartial_mem_Real realPartial_of_zero realSeqs seqUnion seriesSeq seriesSeq_mem_realSeqs setSeqs stairSeq stairSeq_mem_realSeqs stair_mem_Real tendsTo_subset tendsTo_unique)
end ZFSet
