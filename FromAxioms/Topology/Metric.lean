/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Balls, open sets and density on the located reals

The layer Baire needs, and which `Located.lean` stops just short of: it builds
`RealL` with an order, an apartness, arithmetic and located suprema, and nothing
above that.

Built over `RealL` distances rather than over an abstract metric space. The
point is a theorem about the reals this development actually has, not a general
topology -- and an abstract metric would need a distance into `RealL` anyway,
so the abstraction would buy nothing here and cost a layer.

A ball is written as a two-sided inequality, `c - r < x < c + r`, rather than
through an absolute value. When this file was written no `realLAbs` existed
and a case split on the sign seemed the price of one; `Deriv.lean` has since
defined it case-free as `max(x, -x)`. The two-sided form remains -- it is
the same set, and rewriting a working vocabulary buys nothing.

Density is stated as "meets every ball", not through a closure operator: a
closure needs limit points, and limit points on located reals need the located
suprema machinery for no gain. Meeting every ball is what the Baire argument
uses.
-/

import FromAxioms.SetTheory.Search
import FromAxioms.Topology.Topology

universe u

open Algebra Analysis NumberTheory SetTheory
namespace Topology

/-! ## Balls -/

/-- The open ball, as the two-sided inequality. -/
def realLBall (c r : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun x => realLLt (realLAdd c (realLNeg r)) x ∧ realLLt x (realLAdd c r))
    RealL.{u}

/-! ## Open and dense

Both are stated over `RealL` subsets, with membership as the only primitive.
-/

/-- Every point of `S` has a ball around it inside `S`. -/
def IsOpenL (S : ZFSet.{u}) : Prop :=
  S ⊆ RealL.{u} ∧
    ∀ x, x ∈ S → ∃ r, r ∈ RealL.{u} ∧ realLLt realLZero.{u} r ∧
      realLBall x r ⊆ S

/-! ## Dense and open, with their witnesses

Stated with the witnesses as data, the walk's step is a function and no
choice is needed anywhere. This is the locator pattern, and the same trade
`SideReadout` makes: the disjunction -- here the existential -- is available
already, and what is missing is the function that picks.
-/

/-- Openness and density, with the two witnesses supplied rather than
asserted. `centre` gives the point density promises; `radius` gives the ball
openness promises around it. -/
structure DenseOpenWitness (S : ZFSet.{u}) : Type (u + 1) where
  subset : S ⊆ RealL.{u}
  centre : ZFSet.{u} → ZFSet.{u} → ZFSet.{u}
  radius : ZFSet.{u} → ZFSet.{u}
  centre_mem : ∀ c r, c ∈ RealL.{u} → r ∈ RealL.{u} →
    realLLt realLZero.{u} r → centre c r ∈ S
  centre_ball : ∀ c r, c ∈ RealL.{u} → r ∈ RealL.{u} →
    realLLt realLZero.{u} r → centre c r ∈ realLBall c r
  radius_mem : ∀ x, x ∈ S → radius x ∈ RealL.{u}
  radius_pos : ∀ x, x ∈ S → realLLt realLZero.{u} (radius x)
  radius_sub : ∀ x, x ∈ S → realLBall x (radius x) ⊆ S

/-! ## Rational intervals

`IsNested` in `Nested.lean` is stated over rational sequences, so a recursion
that produces balls with real centres and radii cannot feed it directly. Every
point of an open set sits in a rational interval inside it, and the witnesses
come straight from the order bridge -- `realLLt (x - r) x` is a rational
strictly between them.
-/

/-- The open interval with rational endpoints. -/
def realLIoo (p q : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun x => realLLt (realLOf p) x ∧ realLLt x (realLOf q)) RealL.{u}

theorem mem_realLIoo_iff (p q x : ZFSet.{u}) :
    x ∈ realLIoo p q ↔ x ∈ RealL.{u} ∧
      realLLt (realLOf p) x ∧ realLLt x (realLOf q) :=
  mem_sep_iff _ _ _

/-! ## Shrinking

The step a Baire argument repeats: inside a ball, and inside a dense open set,
find a smaller ball contained in both and no wider than a prescribed bound.

The bound is a rational, and stays cheap for that reason. Radii shrinking
like `1/(n+2)` need no multiplication on `RealL` at all -- only `realLOf` of a
rational and `realLMin`. Halving would have needed `realLMul` by `1/2` and the
order lemmas that go with it.
-/

/-- A positive rational is a positive real. -/
theorem realLOf_pos {c : ZFSet.{u}} (hc : c ∈ NumberTheory.Rat.{u})
    (hc0 : ratLt ratZero.{u} c) : realLLt realLZero.{u} (realLOf c) := by
  obtain ⟨t, htQ, h0t, htc⟩ := rat_dense ratZero_mem_Rat hc hc0
  refine ⟨t, ?_, ?_⟩
  · rw [realLZero, realLOf, snd_opair]
    exact (mem_sep_iff _ _ _).mpr ⟨htQ, h0t⟩
  · rw [realLOf, fst_opair]
    exact (mem_ratCut_iff _ _).mpr ⟨htQ, htc⟩

/-! ## Width
-/

/-- A rational interval grows with its endpoints, and the proof is the order
bridge rather than a comparison of reals: `p ≤ p'` and `p' ∈ fst y` give
`p ∈ fst y` by `lower_down`. -/
theorem realLIoo_mono {p q p' q' : ZFSet.{u}} (hp : p ∈ NumberTheory.Rat.{u}) (hq : q ∈ NumberTheory.Rat.{u})
    (hp' : p' ∈ NumberTheory.Rat.{u}) (hq' : q' ∈ NumberTheory.Rat.{u})
    (h1 : ratLe p p') (h2 : ratLe q' q) : realLIoo p' q' ⊆ realLIoo p q := by
  intro y hy
  obtain ⟨hym, hlo, hhi⟩ := (mem_realLIoo_iff p' q' y).mp hy
  have hplo := (realLOf_lt_iff_mem_lower hym hp').mp hlo
  have hqhi := (lt_realLOf_iff_mem_upper hym hq').mp hhi
  obtain ⟨L, U, he, hloc⟩ := (mem_RealL_iff y).mp hym
  rw [he, fst_opair] at hplo
  rw [he, snd_opair] at hqhi
  refine (mem_realLIoo_iff p q y).mpr ⟨hym, ?_, ?_⟩
  · refine (realLOf_lt_iff_mem_lower hym hp).mpr ?_
    rw [he, fst_opair]
    rcases ratLt_trichotomy hp hp' with hlt | rfl | hgt
    · exact hloc.lower_down p' hplo p hp hlt
    · exact hplo
    · exact absurd hgt (fun hc => not_ratLt_of_ratLe hp hp' h1 hc)
  · refine (lt_realLOf_iff_mem_upper hym hq).mpr ?_
    rw [he, snd_opair]
    rcases ratLt_trichotomy hq' hq with hlt | rfl | hgt
    · exact hloc.upper_up q' hqhi q hq hlt
    · exact hqhi
    · exact absurd hgt (fun hc => not_ratLt_of_ratLe hq' hq h2 hc)

/-! ## A concrete dense open family

The sets Baire is usually applied to on the line: the reals apart from a given
point. Both openness and density are constructive here, and neither needs the
selector, so this family is where to look for one.

Openness reads the apartness as a radius: `x < c` gives the ball of radius
`c - x`, and casing on the disjunction is allowed because the goal is an
existential, hence a `Prop`. Density is cotransitivity: two rationals strictly
inside the interval, and `c` cannot be above the upper one and below the lower.
-/

/-- The order topology on the located reals, with RATIONAL endpoints.

`Topology.lean`'s `realOpens` is the same construction over `Real`, the Dedekind
cuts, and cannot be reused: the analysis in this tree is over `RealL`, and the
bridge `toCut` runs only one way --- a cut need not be located. So this is the
same argument over a different carrier, so `isTopology_realOpens` is a
TEMPLATE here rather than a component.

Rational endpoints rather than located ones, and that is a strengthening, not a
convenience: every located real is bracketed by rationals at every scale, so the
rational-endpoint intervals are already a basis, and a basis whose endpoints are
decidable objects keeps the opens from inheriting the reals' undecidable order.
`realLIoo` is stated the same way for the same reason. -/
def realLOpens : ZFSet.{u} :=
  sep (fun U => ∀ x, x ∈ U → ∃ p, p ∈ NumberTheory.Rat.{u} ∧ ∃ q, q ∈ NumberTheory.Rat.{u} ∧
    realLLt (realLOf p) x ∧ realLLt x (realLOf q) ∧ realLIoo p q ⊆ U)
    (powerset RealL.{u})

theorem mem_realLOpens_iff (U : ZFSet.{u}) :
    U ∈ realLOpens.{u} ↔ U ⊆ RealL.{u} ∧
      ∀ x, x ∈ U → ∃ p, p ∈ NumberTheory.Rat.{u} ∧ ∃ q, q ∈ NumberTheory.Rat.{u} ∧
        realLLt (realLOf p) x ∧ realLLt x (realLOf q) ∧ realLIoo p q ⊆ U :=
  Iff.trans (mem_sep_iff _ _ _)
    ⟨fun h => ⟨(mem_powerset_iff _ _).mp h.left, h.right⟩,
     fun h => ⟨(mem_powerset_iff _ _).mpr h.left, h.right⟩⟩

/-- The located order as a SET of pairs.

`IsOrderTopology` and `IsConditionallyComplete` take their order as a ZFSet
relation, because a general carrier has no `realLLt` to call. `RealL` has one,
so the coincidence theorem needs the two spellings joined, and this is the
join: the graph of `realLLt` cut out of `RealL × RealL`.

Reifying the order rather than quantifying over a predicate is the same move
`IsCompact` makes with its cover indices --- carry the DATA. It also keeps the
order's undecidability where it belongs: membership in this set is exactly
`realLLt`, so nothing is decided by forming it. -/
def realLLtRel : ZFSet.{u} :=
  sep (fun z => ∃ x, ∃ y, z = opair x y ∧ realLLt x y)
    (prod RealL.{u} RealL.{u})

/-- Membership in the reified order is the order. -/
theorem opair_mem_realLLtRel_iff {x y : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (hy : y ∈ RealL.{u}) :
    opair x y ∈ realLLtRel.{u} ↔ realLLt x y := by
  refine Iff.trans (mem_sep_iff _ _ _) ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨a, b, heq, hab⟩ := h.right
    obtain ⟨rfl, rfl⟩ := opair_injective heq
    exact hab
  · exact ⟨opair_mem_prod hx hy, ⟨x, y, rfl, h⟩⟩

/-- A rational interval is open in the order topology.

Nearly definitional, and why `realLOpens` was given rational endpoints: the
bracket witnessing `x` is the interval itself, so nothing has to be constructed
and no decision about a real is made. -/
theorem realLIoo_mem_realLOpens {c e : ZFSet.{u}} (hc : c ∈ NumberTheory.Rat.{u})
    (he : e ∈ NumberTheory.Rat.{u}) : realLIoo c e ∈ realLOpens.{u} :=
  (mem_realLOpens_iff _).mpr
    ⟨fun w hw => ((mem_realLIoo_iff c e w).mp hw).left,
     fun x hx =>
       let ⟨_, hcx, hxe⟩ := (mem_realLIoo_iff c e x).mp hx
       ⟨c, hc, e, he, hcx, hxe, fun w hw => hw⟩⟩

/-- The order topology on `RealL` is a topology, constructively.

PROBE: the statement elaborates; the five fields are the next session's work.
`mem_univ` wants rationals bracketing an arbitrary located real, which is
`IsLocated`'s two non-empty cuts; `inter_closed` wants the rational max and min
of the two brackets, decidable because the endpoints are rational. -/
theorem isTopology_realLOpens : IsTopology realLOpens.{u} RealL.{u} where
  opens_sub U hU := ((mem_realLOpens_iff U).mp hU).left
  mem_empty := (mem_realLOpens_iff _).mpr
    ⟨empty_subset _, fun x hx => absurd hx (not_mem_empty x)⟩
  mem_univ := (mem_realLOpens_iff _).mpr ⟨fun w hw => hw, fun x hx => by
    -- any width will do; the bracket is what `IsLocated` guarantees on both
    -- sides, and `exists_rat_bracket` is that fact with a width attached.
    obtain ⟨p, r, hp, hr, hpx, hxr, _⟩ :=
      exists_rat_bracket hx ratOne_mem_Rat ratZero_lt_one
    exact ⟨p, hp, r, hr, hpx, hxr,
      fun w hw => ((mem_realLIoo_iff p r w).mp hw).left⟩⟩
  inter_closed U hU V hV := by
    refine (mem_realLOpens_iff _).mpr ⟨fun w hw => ?_, fun x hx => ?_⟩
    · exact ((mem_realLOpens_iff U).mp hU).left w ((mem_inter_iff w U V).mp hw).left
    · obtain ⟨hxU, hxV⟩ := (mem_inter_iff x U V).mp hx
      obtain ⟨p₁, hp₁, q₁, hq₁, hp₁x, hxq₁, hsub₁⟩ :=
        ((mem_realLOpens_iff U).mp hU).right x hxU
      obtain ⟨p₂, hp₂, q₂, hq₂, hp₂x, hxq₂, hsub₂⟩ :=
        ((mem_realLOpens_iff V).mp hV).right x hxV
      -- The tighter bracket on each side. Rational endpoints are exactly what
      -- makes this a decidable comparison rather than a decision about reals.
      -- `realLIoo_mono` already exists here and takes the OUTER interval first.
      rcases ratLe_total hp₁ hp₂ with hlo | hlo <;>
        rcases ratLe_total hq₁ hq₂ with hhi | hhi
      · exact ⟨p₂, hp₂, q₁, hq₁, hp₂x, hxq₁, fun w hw =>
          (mem_inter_iff w U V).mpr
            ⟨hsub₁ w (realLIoo_mono hp₁ hq₁ hp₂ hq₁ hlo (ratLe_refl hq₁) w hw),
             hsub₂ w (realLIoo_mono hp₂ hq₂ hp₂ hq₁ (ratLe_refl hp₂) hhi w hw)⟩⟩
      · exact ⟨p₂, hp₂, q₂, hq₂, hp₂x, hxq₂, fun w hw =>
          (mem_inter_iff w U V).mpr
            ⟨hsub₁ w (realLIoo_mono hp₁ hq₁ hp₂ hq₂ hlo hhi w hw),
             hsub₂ w (realLIoo_mono hp₂ hq₂ hp₂ hq₂ (ratLe_refl hp₂) (ratLe_refl hq₂) w hw)⟩⟩
      · exact ⟨p₁, hp₁, q₁, hq₁, hp₁x, hxq₁, fun w hw =>
          (mem_inter_iff w U V).mpr
            ⟨hsub₁ w (realLIoo_mono hp₁ hq₁ hp₁ hq₁ (ratLe_refl hp₁) (ratLe_refl hq₁) w hw),
             hsub₂ w (realLIoo_mono hp₂ hq₂ hp₁ hq₁ hlo hhi w hw)⟩⟩
      · exact ⟨p₁, hp₁, q₂, hq₂, hp₁x, hxq₂, fun w hw =>
          (mem_inter_iff w U V).mpr
            ⟨hsub₁ w (realLIoo_mono hp₁ hq₁ hp₁ hq₂ (ratLe_refl hp₁) hhi w hw),
             hsub₂ w (realLIoo_mono hp₂ hq₂ hp₁ hq₂ hlo (ratLe_refl hq₂) w hw)⟩⟩
  union_closed F hF := by
    refine (mem_realLOpens_iff _).mpr ⟨fun w hw => ?_, fun x hx => ?_⟩
    · obtain ⟨U, hUF, hwU⟩ := (mem_sUnion_iff w F).mp hw
      exact ((mem_realLOpens_iff U).mp (hF U hUF)).left w hwU
    · -- an open cover member supplies the bracket, and its interval is inside
      -- the union because it is inside that member.
      obtain ⟨U, hUF, hxU⟩ := (mem_sUnion_iff x F).mp hx
      obtain ⟨p, hp, q, hq, hpx, hxq, hsub⟩ :=
        ((mem_realLOpens_iff U).mp (hF U hUF)).right x hxU
      exact ⟨p, hp, q, hq, hpx, hxq,
        fun w hw => (mem_sUnion_iff w F).mpr ⟨U, hUF, hsub w hw⟩⟩

def IsMetric (d X : ZFSet.{u}) : Prop :=
  IsFunction d ∧ domain d = prod X X ∧ range d ⊆ RealL.{u}
    ∧ (∀ x, x ∈ X → ∀ y, y ∈ X →
        realLLe realLZero.{u} (app d (opair x y)))
    ∧ (∀ x, x ∈ X → app d (opair x x) = realLZero.{u})
    ∧ (∀ x, x ∈ X → ∀ y, y ∈ X →
        app d (opair x y) = app d (opair y x))
    ∧ (∀ x, x ∈ X → ∀ y, y ∈ X → ∀ z, z ∈ X →
        realLLe (app d (opair x z))
          (realLAdd (app d (opair x y)) (app d (opair y z))))

/-- The triangle inequality, over any `Topology.IsMetric` -- this tree's
carrier-free spelling of a metric space, so the statement is at the generality
the definition already has.

A PROJECTION rather than new mathematics: the inequality is the last clause of
`IsMetric`, and every metric in this tree has satisfied it all along. What was
missing was a name. `Analysis.close_of_close_close` is the `RealL` special
case, and nothing stated the general form.

Named rather than reached positionally, since `IsMetric` has seven clauses and
`hd.right` six times is unreadable and breaks SILENTLY if a clause is ever
inserted. The three companions below name the other substantive clauses for the
same reason. -/
theorem isMetric_triangle {d X : ZFSet.{u}} (hd : IsMetric d X)
    {x y z : ZFSet.{u}} (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X) :
    realLLe (app d (opair x z))
      (realLAdd (app d (opair x y)) (app d (opair y z))) := by
  obtain ⟨-, -, -, -, -, -, htri⟩ := hd
  exact htri x hx y hy z hz

/-- Symmetry. -/
theorem isMetric_symm {d X : ZFSet.{u}} (hd : IsMetric d X)
    {x y : ZFSet.{u}} (hx : x ∈ X) (hy : y ∈ X) :
    app d (opair x y) = app d (opair y x) := by
  obtain ⟨-, -, -, -, -, hsym, -⟩ := hd
  exact hsym x hx y hy

#print axioms Topology.isMetric_triangle
#print axioms Topology.isMetric_symm
/-- The ball of RATIONAL radius. Rational for the same reason `realLOpens` uses
rational endpoints: a located real cannot be compared to a general real, and
`ratMin` is what makes two balls intersect. -/
def metricBall (d X c r : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun y => realLLt (app d (opair c y)) (realLOf r)) X

theorem mem_metricBall_iff (d X c r y : ZFSet.{u}) :
    y ∈ metricBall d X c r ↔
      y ∈ X ∧ realLLt (app d (opair c y)) (realLOf r) := mem_sep_iff _ _ _

/-- The topology a metric induces. -/
def metricOpens (d X : ZFSet.{u}) : ZFSet.{u} :=
  sep (fun U => ∀ x, x ∈ U → ∃ r, r ∈ NumberTheory.Rat.{u} ∧ ratLt ratZero.{u} r ∧
    metricBall d X x r ⊆ U) (powerset X)

theorem mem_metricOpens_iff (d X U : ZFSet.{u}) :
    U ∈ metricOpens d X ↔ U ⊆ X ∧
      ∀ x, x ∈ U → ∃ r, r ∈ NumberTheory.Rat.{u} ∧ ratLt ratZero.{u} r ∧
        metricBall d X x r ⊆ U := by
  rw [metricOpens, mem_sep_iff, mem_powerset_iff]

/-- The distance between two points of the space is a real. Named for the
reason the other four accessors are: `IsMetric` is a seven-way conjunction, so
every consumer would otherwise destructure it and consume the hypothesis. This
one was missing while `triangle`, `nonneg`, `symm` and `self` were not --- the
first proof that needs `realLLt_add` needs it, and none had. -/
theorem isMetric_app_mem {d X : ZFSet.{u}} (hd : IsMetric d X)
    {x y : ZFSet.{u}} (hx : x ∈ X) (hy : y ∈ X) :
    app d (opair x y) ∈ RealL.{u} := by
  obtain ⟨hfun, hdom, hran, -, -, -, -⟩ := hd
  exact hran _ (app_mem_range hfun (by rw [hdom]; exact opair_mem_prod hx hy))

/-- Total boundedness, constructively: the net is DATA. -/
structure TotallyBoundedOn (d X : ZFSet.{u}) : Type (u + 1) where
  count : Nat → Nat
  net : Nat → Nat → ZFSet.{u}
  net_mem : ∀ n i, i < count n → net n i ∈ X
  covers : ∀ n, ∀ x, x ∈ X → ∃ i, i < count n ∧
    realLLt (app d (opair (net n i) x)) (realLOf (invWidth (ofNat.{u} n)))

/-- A sequence is Cauchy for the metric. A `Prop` rather than a bundle: the
index per scale is used only inside proofs, which is the same reading
`IsCauchyReal` takes of its own modulus. -/
def IsCauchyOn (d : ZFSet.{u}) (s : Nat → ZFSet.{u}) : Prop :=
  ∀ n : Nat, ∃ N : Nat, ∀ j k : Nat, N ≤ j → N ≤ k →
    realLLt (app d (opair (s j) (s k))) (realLOf (invWidth (ofNat.{u} n)))

/-- Completeness, constructively: the limit is DATA.

Same decision as `TotallyBoundedOn`'s net, for the same reason. A limit
recovered from an existential is a choice, and every use of a complete space
here needs the limit as a term rather than as a proposition about one. -/
structure CompleteOn (d X : ZFSet.{u}) : Type (u + 1) where
  lim : (Nat → ZFSet.{u}) → ZFSet.{u}
  lim_mem : ∀ s : Nat → ZFSet.{u}, (∀ k, s k ∈ X) → IsCauchyOn d s → lim s ∈ X
  tendsTo : ∀ s : Nat → ZFSet.{u}, (∀ k, s k ∈ X) → IsCauchyOn d s →
    ∀ n : Nat, ∃ N : Nat, ∀ k : Nat, N ≤ k →
      realLLt (app d (opair (s k) (lim s)))
        (realLOf (invWidth (ofNat.{u} n)))

/-- A real below every scale is at most zero.

The Archimedean step, in the direction a limit argument needs: `exists_pos_lower`
turns a strict positivity into a positive rational inside the cut, and
`exists_invWidth_lt` finds a scale below it. Constructive throughout --- the
positivity is refuted, not decided. -/
theorem realLLe_zero_of_forall_lt_invWidth {x : ZFSet.{u}} (hx : x ∈ RealL.{u})
    (h : ∀ n : Nat, realLLt x (realLOf (invWidth (ofNat.{u} n)))) :
    realLLe x realLZero.{u} := by
  intro hpos
  obtain ⟨q, hqL, hq0⟩ := exists_pos_lower hpos
  have hqQ : q ∈ NumberTheory.Rat.{u} := ((mem_Real_iff _).mp (toCut_mem hx)).subset q hqL
  obtain ⟨N, hN, hlt⟩ := exists_invWidth_lt hqQ hq0
  obtain ⟨n, rfl⟩ := (mem_omega_iff N).mp hN
  have hxq : realLLt (realLOf q) x := (realLOf_lt_iff_mem_lower hx hqQ).mpr hqL
  have hchain : realLLt (realLOf q) (realLOf (invWidth (ofNat.{u} n))) :=
    realLLt_trans (realLOf_mem hqQ) hx
      (realLOf_mem (invWidth_mem_Rat.{u} (ofNat_mem_omega n))) hxq (h n)
  exact ratLt_irrefl (ratLt_trans hqQ
    (invWidth_mem_Rat.{u} (ofNat_mem_omega n)) hqQ
    ((realLOf_lt_realLOf hqQ (invWidth_mem_Rat.{u} (ofNat_mem_omega n))).mp hchain)
    hlt)

#print axioms Topology.realLLe_zero_of_forall_lt_invWidth

/-- Uniform continuity of a real-valued map over a metric carrier: the
distance in the source is the metric, the distance in the target is `Close`.
A `Prop` with the scale quantified, exactly as `UniformlyContinuousOn` is --
so that a proof written against the interval's modulus can produce it. -/
def UniformlyContinuousMetric (d X : ZFSet.{u})
    (F : ZFSet.{u} → ZFSet.{u}) : Prop :=
  ∀ n : Nat, ∃ m : Nat, ∀ x y, x ∈ X → y ∈ X →
    realLLt (app d (opair x y)) (realLOf (invWidth (ofNat.{u} m))) →
    Close (F x) (F y) (realLOf (invWidth (ofNat.{u} n)))

#print axioms mem_realLIoo_iff
#print axioms realLOf_pos
#print axioms mem_realLOpens_iff
#print axioms realLIoo_mem_realLOpens
#print axioms isTopology_realLOpens
#print axioms mem_metricBall_iff
end Topology

#print axioms Topology.realLIoo_mono
#print axioms Topology.DenseOpenWitness
#print axioms Topology.IsMetric
#print axioms Topology.metricBall
#print axioms Topology.metricOpens
#print axioms Topology.mem_metricOpens_iff
#print axioms Topology.isMetric_app_mem
#print axioms Topology.TotallyBoundedOn
#print axioms Topology.IsCauchyOn
#print axioms Topology.CompleteOn
#print axioms Topology.UniformlyContinuousMetric
#print axioms Topology.realLLtRel
#print axioms Topology.opair_mem_realLLtRel_iff
namespace ZFSet
export Topology (CompleteOn DenseOpenWitness IsCauchyOn IsMetric IsOpenL TotallyBoundedOn UniformlyContinuousMetric isMetric_app_mem isMetric_symm isMetric_triangle isTopology_realLOpens mem_metricBall_iff mem_metricOpens_iff mem_realLIoo_iff mem_realLOpens_iff metricBall metricOpens opair_mem_realLLtRel_iff realLBall realLIoo realLIoo_mem_realLOpens realLIoo_mono realLLe_zero_of_forall_lt_invWidth realLLtRel realLOf_pos realLOpens)
end ZFSet
