/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Contents on an algebra of sets.

An algebra of subsets of `X`, and a finitely additive non-negative function on
it. Complements are in the algebra by assumption and intersections are too:
deriving one from the other is De Morgan, which for sets is
`sdiff_sdiff_cancel` -- a classical theorem in this development. Assuming both
keeps the algebra constructive.

Countable additivity is not here. It needs sums of series of reals, which needs
limits, and that is the next thing to build rather than something to assume.
-/

import FromAxioms.Analysis.Limit

universe u

open Algebra Constructive NumberTheory SetTheory Topology
namespace Analysis

/-! ## Algebras of sets -/

structure IsAlgebra (A X : ZFSet.{u}) : Prop where
  sub : ∀ U, U ∈ A → U ⊆ X
  mem_empty : empty.{u} ∈ A
  mem_univ : X ∈ A
  union_closed : ∀ U, U ∈ A → ∀ V, V ∈ A → U ∪ V ∈ A
  inter_closed : ∀ U, U ∈ A → ∀ V, V ∈ A → inter U V ∈ A
  sdiff_closed : ∀ U, U ∈ A → ∀ V, V ∈ A → sdiff U V ∈ A

/-! ## Contents

A content is non-negative, vanishes on the empty set, and adds over disjoint
pairs. -/

structure IsContent (m A : ZFSet.{u}) : Prop where
  isFun : IsFunction m
  dom : domain m = A
  ran : range m ⊆ Real.{u}
  nonneg : ∀ U, U ∈ A → realNonneg (app m U)
  map_empty : app m empty.{u} = realZero.{u}
  additive : ∀ U, U ∈ A → ∀ V, V ∈ A → inter U V = empty.{u} →
    app m (U ∪ V) = realAdd (app m U) (app m V)

theorem content_app_mem {m A U : ZFSet.{u}} (hm : IsContent m A) (hU : U ∈ A) :
    app m U ∈ Real.{u} :=
  hm.ran _ (app_mem_range hm.isFun (by rw [hm.dom]; exact hU))


/-- A finitely additive content, over an arbitrary carrier.

`IsContent` names the CUT reals in three of its clauses, so the located content
-- which is what this development actually has -- cannot instantiate it. This is
the same structure with the value ring, its addition, its zero and its
NON-NEGATIVES taken as parameters, exactly as `MeasuredCoverP` takes its
parameter type.

Positivity is a `nonneg` SET and there is no totality clause, following
`IsInnerProduct`: `IsPosCone`'s `total` is priced at `NeApartZero`, and a
content never decides a sign, so inheriting it would charge this theory for a
definition rather than for its mathematics. -/
structure IsContentOn (R add zero nonneg m A : ZFSet.{u}) : Prop where
  isFun : IsFunction m
  dom : domain m = A
  ran : range m ⊆ R
  nonneg_mem : ∀ U, U ∈ A → app m U ∈ nonneg
  map_empty : app m empty.{u} = zero
  additive : ∀ U, U ∈ A → ∀ V, V ∈ A → inter U V = empty.{u} →
    app m (U ∪ V) = opAt add (app m U) (app m V)

/-- The value of a content lies in its carrier. -/
theorem contentOn_app_mem {R add zero nonneg m A U : ZFSet.{u}}
    (hm : IsContentOn R add zero nonneg m A) (hU : U ∈ A) : app m U ∈ R :=
  hm.ran _ (app_mem_range hm.isFun (by rw [hm.dom]; exact hU))

/-- The Dirac content at a point: mass one on the sets containing `x0`,
zero on the rest.

THE NON-DEGENERATE WITNESS the generalised interface was missing. `zeroContentOn`
below is the only other one and its own docstring calls it knowingly degenerate
--- it satisfies every clause vacuously, so a theorem over `IsContentOn` could
demand anything and nothing would notice.

Why Dirac and not the counting measure: `|U|` as a FUNCTION of `U` needs
detachable membership at every point of the space, while this needs it at ONE.
`condP` (LeastSearch.lean) builds the value with no decidability at all; only
its EQUATIONS need the split, and only `additive` uses them. -/
def diracContent (A R zero one x0 : ZFSet.{u}) : ZFSet.{u} :=
  graphOn A R (fun U => condP (x0 ∈ U) one zero)

theorem app_diracContent {A R zero one x0 U : ZFSet.{u}}
    (hzero : zero ∈ R) (hone : one ∈ R)
    (hdet : ∀ V, V ∈ A → x0 ∈ V ∨ ¬ x0 ∈ V) (hU : U ∈ A) :
    app (diracContent A R zero one x0) U = condP (x0 ∈ U) one zero := by
  rw [diracContent, app_graphOn (fun V hV => ?_) hU]
  -- `rcases` on the SUPPLIED decision, not `by_cases`: deciding `x0 ∈ V`
  -- classically would put `Classical.choice` in every consumer, and
  -- `LeastSearch` says outright that a construction needing to know its branch
  -- must be handed the decision rather than recover it from the term.
  rcases hdet V hV with h | h
  · rw [condP_pos h]; exact hone
  · rw [condP_neg h]; exact hzero

/-- The Dirac content IS a content, over any carrier with a zero and a one
in its non-negative part.

The detachability hypothesis is the whole cost, and it is used ONCE --- in
`additive`, to split on whether `x0` lies in `U`. Everything else goes through
`condP`'s two equations. Disjointness is what makes the split total: `x0` cannot
be in both, so the sum has exactly one non-zero term. -/
theorem isContentOn_dirac {R add zero one nonneg A X x0 : ZFSet.{u}}
    (hA : IsAlgebra A X) (hzero : zero ∈ R) (hone : one ∈ R)
    (hz : zero ∈ nonneg) (ho : one ∈ nonneg)
    (hdet : ∀ U, U ∈ A → x0 ∈ U ∨ ¬ x0 ∈ U)
    (hx0 : ¬ x0 ∈ empty.{u})
    (hzl : opAt add zero zero = zero) (hzr : opAt add one zero = one)
    (hlz : opAt add zero one = one) :
    IsContentOn R add zero nonneg (diracContent A R zero one x0) A where
  isFun := graphOn_isFunction _ _ _
  dom := graphOn_domain (fun U hU => by
    rcases hdet U hU with h | h
    · rw [condP_pos h]; exact hone
    · rw [condP_neg h]; exact hzero)
  ran := graphOn_range
  nonneg_mem := fun U hU => by
    rw [app_diracContent hzero hone hdet hU]
    rcases hdet U hU with h | h
    · rw [condP_pos h]; exact ho
    · rw [condP_neg h]; exact hz
  map_empty := by
    rw [app_diracContent hzero hone hdet hA.mem_empty, condP_neg hx0]
  additive := fun U hU V hV hdisj => by
    rw [app_diracContent hzero hone hdet (hA.union_closed U hU V hV),
      app_diracContent hzero hone hdet hU, app_diracContent hzero hone hdet hV]
    rcases hdet U hU with hu | hu
    · -- `x0 ∈ U`, so it is in the union and NOT in `V` by disjointness
      have hnv : ¬ x0 ∈ V := by
        intro hv
        -- the ascription is what lets `hdisj` rewrite: `∩` elaborates through
        -- an instance that is not syntactically `inter`
        have hmem : x0 ∈ inter U V := (mem_inter_iff x0 U V).mpr ⟨hu, hv⟩
        rw [hdisj] at hmem
        exact hx0 hmem
      rw [condP_pos ((mem_union_iff x0 U V).mpr (Or.inl hu)), condP_pos hu,
        condP_neg hnv, hzr]
    · rcases hdet V hV with hv | hv
      · rw [condP_pos ((mem_union_iff x0 U V).mpr (Or.inr hv)), condP_neg hu,
          condP_pos hv, hlz]
      · rw [condP_neg (fun h => (mem_union_iff x0 U V).mp h |>.elim hu hv),
          condP_neg hu, condP_neg hv, hzl]

/-- The zero content over an ARBITRARY carrier -- `zeroContent` generalised
alongside the interface. -/
def zeroContentOn (A R zero : ZFSet.{u}) : ZFSet.{u} :=
  graphOn A R (fun _ => zero)

/-- A witness for the generalised interface. Knowingly the DEGENERATE one:
it is the same instance `IsContent` already had, and by the finding above it is
exactly the instance that fails to exercise the interface's existence demand. It
is exhibited because a structure nobody instantiates makes every theorem over it
possibly vacuous -- which the tower's `witness` check enforces -- and the
non-degenerate located instance is its own item. -/
theorem isContentOn_zeroContentOn {A R add zero nonneg X : ZFSet.{u}}
    (hzR : zero ∈ R) (hzN : zero ∈ nonneg)
    (hadd : opAt add zero zero = zero) (hA : IsAlgebra A X) :
    IsContentOn R add zero nonneg (zeroContentOn A R zero) A where
  isFun := graphOn_isFunction _ _ _
  dom := graphOn_domain (fun _ _ => hzR)
  ran := graphOn_range
  nonneg_mem := fun U hU => by
    rw [zeroContentOn, app_graphOn (fun _ _ => hzR) hU]; exact hzN
  map_empty := by
    rw [zeroContentOn, app_graphOn (fun _ _ => hzR) hA.mem_empty]
  additive := fun U hU V hV _ => by
    rw [zeroContentOn, app_graphOn (fun _ _ => hzR) (hA.union_closed U hU V hV),
      app_graphOn (fun _ _ => hzR) hU, app_graphOn (fun _ _ => hzR) hV, hadd]
/-! ## Series over the cuts

`realLSum` and its lemmas are over `RealL`; `IsContent` is over `Real`, so
countable additivity needs partial sums here. They are built rather than
transported: `real_lub` gives a supremum on the cuts CHOICE-FREE, where the
same statement for located reals reverses to `EM` (`em_of_sup_located`).

Placed in this file rather than in `Real.lean` because every consumer is here and
`realLe_realAdd_of_nonneg` below is what the monotonicity step needs. -/

/-- Partial sums of a family of cuts. -/
def realSum (G : Nat → ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => realZero.{u}
  | k + 1 => realAdd (realSum G k) (G k)

#print axioms Analysis.realSum
/-- Adding a non-negative real can only move a cut up. -/
theorem realLe_realAdd_of_nonneg {x y : ZFSet.{u}} (hx : x ∈ Real.{u})
    (hy0 : realNonneg y) : realLe x (realAdd x y) := by
  intro p hp
  have hxc := (mem_Real_iff x).mp hx
  have hpR := hxc.subset _ hp
  obtain ⟨p', hp', hlt⟩ := hxc.no_greatest p hp
  have hp'R := hxc.subset _ hp'
  -- `p - p'` is negative, hence in any non-negative cut
  have hneg : ratLt (ratAdd p (ratNeg p')) ratZero.{u} := by
    have := (ratAdd_lt_add_left_iff (ratNeg_mem_Rat hp'R) hpR hp'R).mpr hlt
    rw [ratAdd_comm (ratNeg_mem_Rat hp'R) hp'R, ratAdd_neg hp'R,
      ratAdd_comm (ratNeg_mem_Rat hp'R) hpR] at this
    exact this
  refine (mem_realAdd_iff x y p).mpr ⟨hpR, p', hp', ratAdd p (ratNeg p'), ?_, ?_⟩
  · exact hy0 _ ((mem_ratCut_iff ratZero.{u} _).mpr
      ⟨ratAdd_mem_Rat hpR (ratNeg_mem_Rat hp'R), hneg⟩)
  · rw [← ratAdd_assoc hp'R hpR (ratNeg_mem_Rat hp'R),
      ratAdd_comm hp'R hpR, ratAdd_assoc hpR hp'R (ratNeg_mem_Rat hp'R),
      ratAdd_neg hp'R, ratAdd_zero hpR]

/-- A content is monotone, on a detachable subset. The decomposition
`V = U ∪ (V \ U)` is what monotonicity rests on, and knowing that every point of
`V` is inside or outside `U` is exactly what that decomposition needs. -/
theorem content_mono {m A X U V : ZFSet.{u}} (hA : IsAlgebra A X) (hm : IsContent m A)
    (hU : U ∈ A) (hV : V ∈ A) (hsub : U ⊆ V) (hdet : ∀ w, w ∈ V → w ∈ U ∨ w ∉ U) :
    realLe (app m U) (app m V) := by
  have hdiff : sdiff V U ∈ A := hA.sdiff_closed V hV U hU
  -- `union_sdiff_self` IS this, at `V` and `U`, and its two hypotheses are the ones
  -- this lemma already takes. The ascribed type is what crosses `\` to `sdiff`:
  -- those are defeq through the `SDiff` instance and not syntactically equal.
  have hsplit : U ∪ sdiff V U = V := (union_sdiff_self hsub hdet).symm
  have hdisj : inter U (sdiff V U) = empty.{u} := by
    refine ext _ _ (fun w => ⟨fun hw => ?_, fun hw => absurd hw (not_mem_empty w)⟩)
    obtain ⟨hwU, hwD⟩ := (mem_inter_iff w U _).mp hw
    exact absurd hwU ((mem_sdiff_iff w V U).mp hwD).right
  have hadd := hm.additive U hU (sdiff V U) hdiff hdisj
  rw [hsplit] at hadd
  rw [hadd]
  exact realLe_realAdd_of_nonneg (content_app_mem hm hU) (hm.nonneg _ hdiff)

/-- The zero content, on any algebra. -/
def zeroContent (A : ZFSet.{u}) : ZFSet.{u} := graphOn A Real.{u} (fun _ => realZero.{u})

theorem isContent_zeroContent {A X : ZFSet.{u}} (hA : IsAlgebra A X) :
    IsContent (zeroContent A) A := by
  have happ : ∀ U, U ∈ A → app (zeroContent A) U = realZero.{u} :=
    fun U hU => app_graphOn (fun _ _ => realZero_mem_Real) hU
  refine ⟨graphOn_isFunction _ _ _, graphOn_domain (fun _ _ => realZero_mem_Real),
    graphOn_range, fun U hU => ?_, happ _ hA.mem_empty, fun U hU V hV _ => ?_⟩
  · rw [happ U hU]
    exact realLe_refl _
  · rw [happ _ (hA.union_closed U hU V hV), happ U hU, happ V hV,
      realAdd_zero realZero_mem_Real]

/-! ## Half-open intervals

The family Lebesgue's construction starts from. Adjacent intervals are disjoint
constructively; that they cover the union needs to compare each point with the
splitting endpoint, which is a decision -- the same detachability
`content_mono` asks for, in the place where it first bites. -/

/-- Even for a real built by a convergent walk with an explicit modulus,
comparing it with a rational is `LPO`: the ternary real of a bit sequence is
above `0` exactly when some bit fires. -/
theorem lpo_of_realLt_or_realLe
    (h : ∀ x, x ∈ Real.{u} → ∀ q, q ∈ NumberTheory.Rat.{u} →
      realLt (ratCut q) x ∨ realLe x (ratCut q)) : LPO := by
  refine lpo_of_ternary_decidable (fun α => ?_)
  have hx : nestLower (tlowSeq.{u} (boolDigit α)) ∈ Real.{u} :=
    lower_mem_Real (isLocated_nest (isNested_ternary (boolDigit_le_one α)))
  have hxc := (mem_Real_iff _).mp hx
  rcases h _ hx _ ratZero_mem_Rat with hlt | hle
  · -- a rational at or above `0` inside the cut puts `0` inside it
    obtain ⟨q, hqx, hq0⟩ := hlt
    have hqR := hxc.subset _ hqx
    refine Or.inl ?_
    rcases ratLt_trichotomy ratZero_mem_Rat hqR with h0q | heq | hq0'
    · exact hxc.down _ hqx _ ratZero_mem_Rat h0q
    · exact heq ▸ hqx
    · exact absurd ((mem_ratCut_iff ratZero.{u} q).mpr ⟨hqR, hq0'⟩) hq0
  · refine Or.inr (fun hmem => ?_)
    exact ratLt_irrefl ((mem_ratCut_iff ratZero.{u} ratZero.{u}).mp (hle _ hmem)).right

/-! ## Audit -/

/-- The zero content is countably additive, so `IsCountablyAdditive` has an
object that meets it.

What this does NOT do. The zero content is additive because every term is
`0`, so it EXHIBITS the predicate without testing it -- a definition with one
satisfying object is not thereby a definition anything interesting satisfies.
The theorem that would test it is the Lebesgue outer measure being countably
additive on measured sets, which needs the REVERSE Caratheodory inequality that
`lebesgueOuter_le_split` does not supply. -/
theorem isCountablyAdditive_zeroContent {A : ZFSet.{u}} :
    IsCountablyAdditive (zeroContent A) A := by
  intro E hE _ hu
  have happ : ∀ U, U ∈ A → app (zeroContent A) U = realZero.{u} :=
    fun _ hU => app_graphOn (fun _ _ => realZero_mem_Real) hU
  have hF : ∀ m, m ∈ omega.{u} → app (zeroContent A) (app E m) ∈ Real.{u} := by
    intro m hm
    rw [happ _ (app_setSeq_mem hE hm)]
    exact realZero_mem_Real
  have hterm : ∀ n : Nat,
      app (compOn (zeroContent A) E omega.{u} Real.{u}) (ofNat.{u} n) = realZero.{u} := by
    intro n
    rw [compOn, app_graphOn hF (ofNat_mem_omega n)]
    exact happ _ (app_setSeq_mem hE (ofNat_mem_omega n))
  have hseq : compOn (zeroContent A) E omega.{u} Real.{u} ∈ realSeqs.{u} :=
    (mem_realSeqs_iff _).mpr
      ⟨graphOn_subset _ _ _, graphOn_isFunction _ _ _, graphOn_domain hF⟩
  rw [happ _ hu]
  exact hasSum_zero_of_vanishing hseq hterm


#print axioms realLe_realAdd_of_nonneg

/-- Every partial union of members of an algebra is a member -- `mem_empty` and
`union_closed`, by induction. Finite closure only; a countable union is NOT
claimed, and a sigma-algebra would add one. -/
theorem unionUpto_mem_algebra {A X : ZFSet.{u}} (hA : IsAlgebra A X)
    {U : Nat → ZFSet.{u}} (hU : ∀ i : Nat, U i ∈ A) :
    ∀ k : Nat, unionUpto U k ∈ A
  | 0 => hA.mem_empty
  | k + 1 => hA.union_closed _ (unionUpto_mem_algebra hA hU k) _ (hU k)

/-- The content of a partial union IS the partial sum of the contents, at NO
COST.

The algebra supplies membership, pairwise disjointness supplies exactly what
`IsContent.additive` demands, and `unionUpto`'s recursion matches `realSum`'s -- so
the induction is one rewrite per step. No detachability and no principle: finite
additivity iterated is free, and every charge in countable additivity lies elsewhere.

Where the charges actually are. Bounding these sums by the content of a
containing member is `content_mono`, which takes detachability; and the
converse inequality -- that the whole is at most the least upper bound -- is
countable SUBadditivity, which is not proved here. This lemma is the half that
costs nothing, and stating it separately says so. -/
theorem content_unionUpto {m A X : ZFSet.{u}} (hA : IsAlgebra A X)
    (hm : IsContent m A) {U : Nat → ZFSet.{u}} (hU : ∀ i : Nat, U i ∈ A)
    (hdisj : ∀ i j : Nat, i ≠ j → inter (U i) (U j) = empty.{u}) :
    ∀ k : Nat, app m (unionUpto U k) = realSum (fun i => app m (U i)) k
  | 0 => hm.map_empty
  | k + 1 => by
      show app m (unionUpto U k ∪ U k)
        = realAdd (realSum (fun i => app m (U i)) k) (app m (U k))
      rw [hm.additive _ (unionUpto_mem_algebra hA hU k) _ (hU k)
        (unionUpto_inter_eq_empty hdisj k),
        content_unionUpto hA hm hU hdisj k]

#print axioms Analysis.unionUpto_mem_algebra
#print axioms Analysis.content_unionUpto
#print axioms content_mono
#print axioms lpo_of_realLt_or_realLe
#print axioms isContent_zeroContent
#print axioms Analysis.isCountablyAdditive_zeroContent


/-- The weighted count of the atoms `ofNat 0 … ofNat (n-1)` lying in `U`.

`realSum`'s shape with an indicator: each atom contributes its weight when it is
in `U` and nothing when it is not. -/
def natWeightSum (w : Nat → ZFSet.{u}) (U : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => realLZero.{u}
  | k + 1 =>
    realLAdd (natWeightSum w U k) (condP (ofNat.{u} k ∈ U) (w k) realLZero.{u})

#print axioms natWeightSum

/-- The atom's contribution is a real, given the decision at that atom. -/
theorem condP_weight_mem {w : Nat → ZFSet.{u}} {U : ZFSet.{u}} {k : Nat}
    (hw : ∀ j, w j ∈ RealL.{u})
    (hdet : ofNat.{u} k ∈ U ∨ ¬ ofNat.{u} k ∈ U) :
    condP (ofNat.{u} k ∈ U) (w k) realLZero.{u} ∈ RealL.{u} := by
  rcases hdet with h | h
  · rw [condP_pos h]; exact hw k
  · rw [condP_neg h]; exact realLZero_mem

#print axioms condP_weight_mem

theorem natWeightSum_mem {w : Nat → ZFSet.{u}} {U : ZFSet.{u}}
    (hw : ∀ j, w j ∈ RealL.{u})
    (hdet : ∀ j : Nat, ofNat.{u} j ∈ U ∨ ¬ ofNat.{u} j ∈ U) :
    ∀ n : Nat, natWeightSum w U n ∈ RealL.{u}
  | 0 => realLZero_mem
  | k + 1 => realLAdd_mem (natWeightSum_mem hw hdet k) (condP_weight_mem hw (hdet k))

#print axioms natWeightSum_mem


/-- Disjointness splits the weighted count, which is finite additivity
before it is dressed as a content.

The atom case is where disjointness is spent: `ofNat k` cannot be in both, so of
the two indicator terms at most one is a weight and the other is zero. -/
theorem natWeightSum_union {w : Nat → ZFSet.{u}} {U V : ZFSet.{u}}
    (hw : ∀ j, w j ∈ RealL.{u})
    (hU : ∀ j : Nat, ofNat.{u} j ∈ U ∨ ¬ ofNat.{u} j ∈ U)
    (hV : ∀ j : Nat, ofNat.{u} j ∈ V ∨ ¬ ofNat.{u} j ∈ V)
    (hdisj : inter U V = empty.{u}) :
    ∀ n : Nat, natWeightSum w (U ∪ V) n
      = realLAdd (natWeightSum w U n) (natWeightSum w V n)
  | 0 => (realLAdd_zero realLZero_mem).symm
  | k + 1 => by
    have hIH := natWeightSum_union hw hU hV hdisj k
    have hatom : condP (ofNat.{u} k ∈ U ∪ V) (w k) realLZero.{u}
        = realLAdd (condP (ofNat.{u} k ∈ U) (w k) realLZero.{u})
            (condP (ofNat.{u} k ∈ V) (w k) realLZero.{u}) := by
      rcases hU k with hu | hu
      · rcases hV k with hv | hv
        · -- disjointness is spent HERE and nowhere else
          have hboth : ofNat.{u} k ∈ inter U V :=
            (mem_inter_iff (ofNat.{u} k) U V).mpr ⟨hu, hv⟩
          rw [hdisj] at hboth
          exact absurd hboth (not_mem_empty _)
        · rw [condP_pos ((mem_union_iff (ofNat.{u} k) U V).mpr (Or.inl hu)),
            condP_pos hu, condP_neg hv, realLAdd_zero (hw k)]
      · rcases hV k with hv | hv
        · rw [condP_pos ((mem_union_iff (ofNat.{u} k) U V).mpr (Or.inr hv)),
            condP_neg hu, condP_pos hv,
            realLAdd_comm realLZero_mem (hw k), realLAdd_zero (hw k)]
        · rw [condP_neg (fun h => by
              rcases (mem_union_iff (ofNat.{u} k) U V).mp h with h1 | h1
              · exact hu h1
              · exact hv h1),
            condP_neg hu, condP_neg hv, realLAdd_zero realLZero_mem]
    show realLAdd (natWeightSum w (U ∪ V) k)
        (condP (ofNat.{u} k ∈ U ∪ V) (w k) realLZero.{u}) = _
    rw [hIH, hatom]
    -- `.symm`: the shuffle reads (S+c)+(S+c) = (S+S)+(c+c) and the goal is
    -- that equation the other way round.
    exact (realLAdd_interchange (natWeightSum_mem hw hU k) (condP_weight_mem hw (hU k))
      (natWeightSum_mem hw hV k) (condP_weight_mem hw (hV k))).symm

#print axioms natWeightSum_union

theorem natWeightSum_empty (w : Nat → ZFSet.{u}) :
    ∀ n : Nat, natWeightSum w empty.{u} n = realLZero.{u}
  | 0 => rfl
  | k + 1 => by
    show realLAdd (natWeightSum w empty.{u} k)
      (condP (ofNat.{u} k ∈ empty.{u}) (w k) realLZero.{u}) = _
    rw [natWeightSum_empty w k, condP_neg (not_mem_empty _),
      realLAdd_zero realLZero_mem]

#print axioms natWeightSum_empty

theorem natWeightSum_nonneg {w : Nat → ZFSet.{u}} {U : ZFSet.{u}}
    (hw : ∀ j, w j ∈ RealL.{u})
    (hnn : ∀ j, realLLe realLZero.{u} (w j))
    (hdet : ∀ j : Nat, ofNat.{u} j ∈ U ∨ ¬ ofNat.{u} j ∈ U) :
    ∀ n : Nat, realLLe realLZero.{u} (natWeightSum w U n)
  | 0 => realLLe_refl realLZero_mem
  | k + 1 => by
    refine realLAdd_nonneg (natWeightSum_mem hw hdet k) (condP_weight_mem hw (hdet k))
      (natWeightSum_nonneg hw hnn hdet k) ?_
    rcases hdet k with h | h
    · rw [condP_pos h]; exact hnn k
    · rw [condP_neg h]; exact realLLe_refl realLZero_mem

#print axioms natWeightSum_nonneg

/-- A finite weighted content, as a set function on the algebra. -/
def natWeightedContent (A R : ZFSet.{u}) (w : Nat → ZFSet.{u}) (n : Nat) : ZFSet.{u} :=
  graphOn A R (fun U => natWeightSum w U n)

#print axioms natWeightedContent

theorem app_natWeightedContent {A U : ZFSet.{u}} {n : Nat}
    {w : Nat → ZFSet.{u}} (hw : ∀ j, w j ∈ RealL.{u})
    (hdet : ∀ V, V ∈ A → ∀ j : Nat, ofNat.{u} j ∈ V ∨ ¬ ofNat.{u} j ∈ V)
    (hU : U ∈ A) :
    app (natWeightedContent A RealL.{u} w n) U = natWeightSum w U n :=
  app_graphOn (fun V hV => natWeightSum_mem hw (hdet V hV) n) hU

#print axioms app_natWeightedContent

#print axioms content_app_mem
end Analysis
#print axioms Analysis.IsContentOn
#print axioms Analysis.contentOn_app_mem
#print axioms Analysis.zeroContentOn
#print axioms Analysis.isContentOn_zeroContentOn

#print axioms Analysis.app_diracContent
#print axioms Analysis.isContentOn_dirac
namespace ZFSet
export Analysis (IsAlgebra IsContent IsContentOn app_diracContent app_natWeightedContent condP_weight_mem contentOn_app_mem content_app_mem content_mono content_unionUpto diracContent isContentOn_dirac isContentOn_zeroContentOn isContent_zeroContent isCountablyAdditive_zeroContent lpo_of_realLt_or_realLe natWeightSum natWeightSum_empty natWeightSum_mem natWeightSum_nonneg natWeightSum_union natWeightedContent realLe_realAdd_of_nonneg realSum unionUpto_mem_algebra zeroContent zeroContentOn)
end ZFSet
