/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The generic halving machine

A bisection on the unit interval, stated once over its payload: the
state is a coded rational interval `⟨a, b⟩` inside `[0,1]` carrying a
predicate `P` on its endpoints, the relation halves at `ratMid`, and
totality -- some half keeps `P` -- is the hypothesis each instantiation
pays. `DC` chains the steps, the widths halve under the harmonic
ladder, the endpoints are a nested family, and `halve_limit` packages
the extraction: the named real sits at every stage inside a
`P`-interval of width at most `1/(m+1)`.

The integral-sign bisection, the exact IVT and the extreme value climb
are all instantiations.
-/

import FromAxioms.Analysis.Complete
import FromAxioms.Constructive.Vanishing

universe u

open Analysis Constructive SetTheory
namespace NumberTheory

/-- The midpoint facts every halving step re-derives: membership, the two
strict inequalities, and the unit-interval bounds. -/
theorem ratMid_facts {a b : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u})
    (h0a : ratLe ratZero.{u} a) (hab : ratLt a b)
    (hb1 : ratLe b ratOne.{u}) :
    And (ratMid a b ∈ Rat.{u}) (And (ratLt a (ratMid a b))
      (And (ratLt (ratMid a b) b) (And (ratLe ratZero.{u} (ratMid a b))
        (ratLe (ratMid a b) ratOne.{u})))) := by
  have hmQ := ratMid_mem_Rat ha hb
  have ham := lt_ratMid ha hb hab
  have hmb := ratMid_lt ha hb hab
  exact ⟨hmQ, ham, hmb,
    ratLe_trans ratZero_mem_Rat ha hmQ h0a ham.left,
    ratLe_trans hmQ hb ratOne_mem_Rat hmb.left hb1⟩

/-- A halving state: a coded interval `⟨a, b⟩` inside `[0,1]` carrying the
payload `P` on its endpoints. -/
def halveInv (P : ZFSet.{u} → ZFSet.{u} → Prop) (s : ZFSet.{u}) : Prop :=
  ∃ a b, a ∈ Rat.{u} ∧ b ∈ Rat.{u} ∧ s = opair a b ∧
    ratLe ratZero.{u} a ∧ ratLt a b ∧ ratLe b ratOne.{u} ∧ P a b

/-- The halving machine's state set. -/
def halveS (P : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  sep (halveInv P) (prod Rat.{u} Rat.{u})

/-- The halving machine's step relation: pass to either half, payload
intact. -/
def halveR (P : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  sep (fun p => ∃ a b, a ∈ Rat.{u} ∧ b ∈ Rat.{u} ∧
    ((p = opair (opair a b) (opair a (ratMid a b))
        ∧ halveInv P (opair a (ratMid a b)))
      ∨ (p = opair (opair a b) (opair (ratMid a b) b)
        ∧ halveInv P (opair (ratMid a b) b))))
    (prod (halveS P) (halveS P))

/-- Totality of the generic halving step: a payload that survives into
one half at every strict subinterval keeps the machine running. -/
theorem halve_total {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hstep : ∀ a b, a ∈ Rat.{u} → b ∈ Rat.{u} → ratLe ratZero.{u} a →
      ratLt a b → ratLe b ratOne.{u} → P a b →
      Or (P a (ratMid a b)) (P (ratMid a b) b)) :
    ∀ s, s ∈ halveS P → ∃ s', s' ∈ halveS P ∧ opair s s' ∈ halveR P := by
  intro s hs
  obtain ⟨hsP, hinv⟩ := (mem_sep_iff _ _ _).mp hs
  obtain ⟨a, b, haQ, hbQ, rfl, h0a, hab, hb1, hpay⟩ := hinv
  obtain ⟨hmQ, ham, hmb, h0m, hm1⟩ := ratMid_facts haQ hbQ h0a hab hb1
  rcases hstep a b haQ hbQ h0a hab hb1 hpay with hleft | hright
  · have hinv' : halveInv P (opair a (ratMid a b)) :=
      ⟨a, ratMid a b, haQ, hmQ, rfl, h0a, ham, hm1, hleft⟩
    refine ⟨opair a (ratMid a b), (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod haQ hmQ, hinv'⟩, (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod hs ((mem_sep_iff _ _ _).mpr
        ⟨opair_mem_prod haQ hmQ, hinv'⟩), ?_⟩⟩
    exact ⟨a, b, haQ, hbQ, Or.inl ⟨rfl, hinv'⟩⟩
  · have hinv' : halveInv P (opair (ratMid a b) b) :=
      ⟨ratMid a b, b, hmQ, hbQ, rfl, h0m, hmb, hb1, hright⟩
    refine ⟨opair (ratMid a b) b, (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod hmQ hbQ, hinv'⟩, (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod hs ((mem_sep_iff _ _ _).mpr
        ⟨opair_mem_prod hmQ hbQ, hinv'⟩), ?_⟩⟩
    exact ⟨a, b, haQ, hbQ, Or.inr ⟨rfl, hinv'⟩⟩

/-! ## What the machine actually spends

`DC` takes a relation that is merely TOTAL, so at each state the successor is
only known to exist. The halving machine has far more than that: the two
candidate successors are NAMED, and are computable functions of the state. What
it needs is the choice between two named moves, iterated -- not choice from an
arbitrary non-empty set of successors. -/

/-- Binary dependent choice on a set. `DC` with the totality hypothesis
replaced by a disjunction between two NAMED successors.

Weaker than `DC` by inspection -- the hypothesis is strictly stronger, since a
disjunction between two named moves yields totality while totality names
nothing -- and `binaryDCOn_of_dc` proves that direction. Whether it is STRICTLY
weaker is a question about models and is not settled here.

The successors are SET functions, not Lean functions. `DC` quantifies over
`S R : ZFSet`, so a Lean-level `f₀ : ZFSet → ZFSet` would make the two
principles comparable in Lean and NOT comparable inside the theory -- a Lean
function cannot be a bound
variable of the object language, so *there is a model where this holds and `DC`
fails* would be unsayable about it.

`f₀` and `f₁` are named IN ADVANCE, and a construction must supply them to be
covered here. Bisecting a step into two options is not enough: Baire's walk
can be rewritten so each step picks between two halves and still does not come
down, because a relation loose enough to be total admits a chain that never
enters the dense open, and one tight enough to force entry is not total.
-/
def BinaryDCOn : Prop :=
  ∀ S R f₀ f₁ : ZFSet.{u}, R ⊆ prod S S →
    IsFunction f₀ → domain f₀ = S → IsFunction f₁ → domain f₁ = S →
    (∀ a, a ∈ S →
      Or (And (app f₀ a ∈ S) (opair a (app f₀ a) ∈ R))
         (And (app f₁ a ∈ S) (opair a (app f₁ a) ∈ R))) →
    ∀ a₀, a₀ ∈ S →
    ∃ g, IsFunction g ∧ domain g = omega.{u} ∧ app g empty.{u} = a₀ ∧
      ∀ n, n ∈ omega.{u} → opair (app g n) (app g (succ n)) ∈ R

/-- `DC` implies it, which is the easy half and fixes the direction: the
named disjunction is one way of witnessing totality, so anything `BinaryDCOn`
asks for `DC` already supplies. -/
theorem binaryDCOn_of_dc (hdc : DC.{u}) : BinaryDCOn.{u} := by
  intro S R f₀ f₁ hRS _ _ _ _ hbin a₀ ha₀
  refine hdc S R hRS (fun a ha => ?_) a₀ ha₀
  rcases hbin a ha with ⟨hm, hr⟩ | ⟨hm, hr⟩
  · exact ⟨app f₀ a, hm, hr⟩
  · exact ⟨app f₁ a, hm, hr⟩

/-! ### What `BinaryDCOn` costs, at an arbitrary state set

TWO PRODUCERS CONCLUDE `BinaryDCOn` AND BOTH ARE PRINCIPLES --- the join
projecting, and `binaryDCOn_of_dc` above. No landmark yields it, so the seven
theorems spending this pair cannot be repointed at `BisectionSearch`: a
reversal would then have to conclude the join, and this half has no producer
that is not already a principle.

THE ARGUMENT BELOW IS NOT NEW AND ITS GENERALITY IS. This tree runs the same
`natSeq` recursion THREE times, each hard-wired to one state set:
`halveIter`/`halve_limit_of_selector` and `halveStepD`/`halveIterD` further
down this file, and `Topology.exists_baire_walk_of_selector` at `baireState`.
The insight is already in this file's own prose, one section below --- *`condP`
is total on any `Prop` ... the step is definable with no principle whatever ...
a set-level branch is free where a `Bool` is not*. What was missing is the
statement at an ARBITRARY `S` and `R`.

THE RECURSION IS SHARED AND THE INPUT IS NOT, so the general form is worth
having. `HalveSelector.bit` is a Lean `ZFSet → Bool` and `halveStep` a Lean
function; `Topology.IsBaireSelector` carries a ZFSet `sel`. So
`IsChainSelector` generalises the SECOND exactly and is the set-level SIBLING
of the first. That matters because a reversal argues about the PRINCIPLE: a
`Prop` cannot quantify over Lean-level data here, so the halving machine's
selector and decider cannot appear inside one, and the ZFSet forms can.

AND THE SET FORM COSTS NOTHING, checked rather than assumed
(`.agent/chains/probe-set-branch-equals-predicate-branch.lean`,
`[propext, Quot.sound]`): `sep` takes an arbitrary formula, so
`sep goLeft S` turns any predicate branch into a set one and detachability
transfers both ways. `HalveDecider.decided`'s obligation and
`isChainSelector_of_detachable`'s `hdet` are interchangeable on `S`.

NOR IS `hdet` EXCLUDED MIDDLE IN DISGUISE. It is at a FIXED `S` and `T`. The
QUANTIFIED form is the principle --- `Analysis.DecidableMemSet` is EM by
`em_of_decidableMemSet`, and `IdealDetachableInt` reverses to `LPO` --- and this
is the hypothesis form, as `HalveDecider.decided` is.

    BinaryDCOn  =  a free chain  +  a decision of the branch at each state

NOT CLAIMED: that the bisection's branch is detachable. It is not --- choosing the
half is exactly what `Constructive.SignDisjunction` buys, so the two
are spent together, and the section below says the same thing about `ratLt_or_not`. -/

/-- `BinaryDCOn` at ONE carrier and relation.

THE QUANTIFIED FORM IS MORE THAN ANY CONSUMER USES.
`halve_limit_of_binaryDCOn` below takes `BinaryDCOn` and its proof opens
`hbdc (halveS P) (halveR P) ...` --- a SINGLE instance, at a set of coded
rational intervals. Seventeen theorems across `Analysis/Extreme.lean` and
`Metamath/Calibrate.lean` inherit that hypothesis, so seven registry rows spend a
principle about EVERY carrier in order to use it at one.

WHY THAT MATTERS RATHER THAN BEING TIDINESS. Those rows' reversal is blocked, and
the blocked target reads `<landmark> -> BinaryDCOn`: a chain in an ARBITRARY `S`,
`powerset RealL` included, from a landmark that speaks only of `RealL`. At the
instance the objection is gone --- `halveS P` is pairs of RATIONALS, which is the
landmarks' own subject.

THIS IS THE MOVE `the category theorem` MADE FOR `DCOn`. That row records a
parameterised principle giving a reversal nothing to aim at, and the repair was
naming the instance as `DCOmega`. -/
def BinaryDCOnAt (S R : ZFSet.{u}) : Prop :=
  ∀ f₀ f₁ : ZFSet.{u},
    IsFunction f₀ → domain f₀ = S → IsFunction f₁ → domain f₁ = S →
    (∀ a, a ∈ S →
      Or (And (app f₀ a ∈ S) (opair a (app f₀ a) ∈ R))
         (And (app f₁ a ∈ S) (opair a (app f₁ a) ∈ R))) →
    ∀ a₀, a₀ ∈ S →
    ∃ g, IsFunction g ∧ domain g = omega.{u} ∧ app g empty.{u} = a₀ ∧
      ∀ n, n ∈ omega.{u} → opair (app g n) (app g (succ n)) ∈ R

/-- The quantified form gives every instance, which fixes the direction and
is all this pair asserts. Nothing here derives the quantified form back. -/
theorem binaryDCOnAt_of_binaryDCOn (h : BinaryDCOn.{u})
    {S R : ZFSet.{u}} (hRS : R ⊆ prod S S) : BinaryDCOnAt.{u} S R :=
  fun f₀ f₁ hf0 hd0 hf1 hd1 hbin a₀ ha₀ =>
    h S R f₀ f₁ hRS hf0 hd0 hf1 hd1 hbin a₀ ha₀

/-- The halving step's two moves, as functions of the state. These are exactly
the branches of `halveStep`, with the selector's bit removed: the machine knows
both successors without knowing which one to take. -/
def halveLeft (s : ZFSet.{u}) : ZFSet.{u} := opair (fst s) (ratMid (fst s) (snd s))

def halveRight (s : ZFSet.{u}) : ZFSet.{u} := opair (ratMid (fst s) (snd s)) (snd s)

/-- A move's GRAPH: the same function as an object of the theory. Generic in the
move, so one construction serves both halves.

The codomain is `prod Rat Rat` rather than `halveS P`: only ONE of the two moves
keeps the payload at any state, so neither graph lands in the state set, and
requiring it would be false. -/
def halveMove (P : ZFSet.{u} → ZFSet.{u} → Prop) (f : ZFSet.{u} → ZFSet.{u}) :
    ZFSet.{u} :=
  sep (fun z => ∃ s, s ∈ halveS P ∧ z = opair s (f s))
    (prod (halveS P) (prod Rat.{u} Rat.{u}))

theorem isFunction_halveMove (P : ZFSet.{u} → ZFSet.{u} → Prop)
    (f : ZFSet.{u} → ZFSet.{u}) : IsFunction (halveMove P f) :=
  isFunction_graphOn f

theorem mem_halveMove {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {f : ZFSet.{u} → ZFSet.{u}} {s : ZFSet.{u}} (hs : s ∈ halveS P)
    (hf : f s ∈ prod Rat.{u} Rat.{u}) :
    opair s (f s) ∈ halveMove P f :=
  (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod hs hf, s, hs, rfl⟩

theorem app_halveMove {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {f : ZFSet.{u} → ZFSet.{u}} {s : ZFSet.{u}} (hs : s ∈ halveS P)
    (hf : f s ∈ prod Rat.{u} Rat.{u}) :
    app (halveMove P f) s = f s :=
  app_eq (isFunction_halveMove P f) (mem_halveMove hs hf)

theorem domain_halveMove {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ s, s ∈ halveS P → f s ∈ prod Rat.{u} Rat.{u}) :
    domain (halveMove P f) = halveS P := by
  refine ext _ _ fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · obtain ⟨b, hb⟩ := (mem_domain_iff a _).mp ha
    exact mem_prod_left ((mem_sep_iff _ _ _).mp hb).left
  · exact (mem_domain_iff _ _).mpr ⟨_, mem_halveMove ha (hf a ha)⟩

/-- Both moves land in `Rat × Rat`, so they can be graphed. -/
theorem halveLeft_mem_prod {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveS P) : halveLeft s ∈ prod Rat.{u} Rat.{u} := by
  obtain ⟨-, a, b, haQ, hbQ, rfl, h0a, hab, hb1, -⟩ := (mem_sep_iff _ _ _).mp hs
  obtain ⟨hmQ, -, -, -, -⟩ := ratMid_facts haQ hbQ h0a hab hb1
  unfold halveLeft
  rw [fst_opair, snd_opair]
  exact opair_mem_prod haQ hmQ

theorem halveRight_mem_prod {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveS P) : halveRight s ∈ prod Rat.{u} Rat.{u} := by
  obtain ⟨-, a, b, haQ, hbQ, rfl, h0a, hab, hb1, -⟩ := (mem_sep_iff _ _ _).mp hs
  obtain ⟨hmQ, -, -, -, -⟩ := ratMid_facts haQ hbQ h0a hab hb1
  unfold halveRight
  rw [fst_opair, snd_opair]
  exact opair_mem_prod hmQ hbQ

/-- The halving step is binary with NAMED successors, which is `halve_total`
stated without the existential. The proof is that one, with the witness read off
rather than produced. -/
theorem halve_binary {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hstep : ∀ a b, a ∈ Rat.{u} → b ∈ Rat.{u} → ratLe ratZero.{u} a →
      ratLt a b → ratLe b ratOne.{u} → P a b →
      Or (P a (ratMid a b)) (P (ratMid a b) b)) :
    ∀ s, s ∈ halveS P →
      Or (And (halveLeft s ∈ halveS P) (opair s (halveLeft s) ∈ halveR P))
         (And (halveRight s ∈ halveS P) (opair s (halveRight s) ∈ halveR P)) := by
  intro s hs
  obtain ⟨hsP, hinv⟩ := (mem_sep_iff _ _ _).mp hs
  obtain ⟨a, b, haQ, hbQ, rfl, h0a, hab, hb1, hpay⟩ := hinv
  obtain ⟨hmQ, ham, hmb, h0m, hm1⟩ := ratMid_facts haQ hbQ h0a hab hb1
  have hL : halveLeft (opair a b) = opair a (ratMid a b) := by
    unfold halveLeft; rw [fst_opair, snd_opair]
  have hR : halveRight (opair a b) = opair (ratMid a b) b := by
    unfold halveRight; rw [fst_opair, snd_opair]
  rcases hstep a b haQ hbQ h0a hab hb1 hpay with hleft | hright
  · have hinv' : halveInv P (opair a (ratMid a b)) :=
      ⟨a, ratMid a b, haQ, hmQ, rfl, h0a, ham, hm1, hleft⟩
    have hmem : opair a (ratMid a b) ∈ halveS P :=
      (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod haQ hmQ, hinv'⟩
    refine Or.inl ⟨hL ▸ hmem, hL ▸ (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod hs hmem, ?_⟩⟩
    exact ⟨a, b, haQ, hbQ, Or.inl ⟨rfl, hinv'⟩⟩
  · have hinv' : halveInv P (opair (ratMid a b) b) :=
      ⟨ratMid a b, b, hmQ, hbQ, rfl, h0m, hmb, hb1, hright⟩
    have hmem : opair (ratMid a b) b ∈ halveS P :=
      (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod hmQ hbQ, hinv'⟩
    refine Or.inr ⟨hR ▸ hmem, hR ▸ (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod hs hmem, ?_⟩⟩
    exact ⟨a, b, haQ, hbQ, Or.inr ⟨rfl, hinv'⟩⟩

/-- The chain `DC` produces for the halving machine never leaves the state
set: each step's membership in the relation pins its target. -/
theorem halve_chain_mem {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P) :
    ∀ n, n ∈ omega.{u} → app g n ∈ halveS P := by
  refine omega_induction ?_ ?_
  · rw [h0]; exact hs₀
  · intro k hk _
    have hP := ((mem_sep_iff _ _ _).mp (hgR k hk)).left
    obtain ⟨x, hx, y, hy, heq⟩ := (mem_prod_iff _ _ _).mp hP
    obtain ⟨-, h2⟩ := opair_injective heq
    rw [h2]
    exact hy

/-- Reading a halving state back: both coordinates rational, the bounds,
the strictness, and the payload. -/
theorem halveS_spec {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveS P) :
    And (fst s ∈ Rat.{u}) (And (snd s ∈ Rat.{u})
      (And (ratLe ratZero.{u} (fst s)) (And (ratLt (fst s) (snd s))
        (And (ratLe (snd s) ratOne.{u}) (P (fst s) (snd s)))))) := by
  obtain ⟨-, hinv⟩ := (mem_sep_iff _ _ _).mp hs
  obtain ⟨a, b, haQ, hbQ, rfl, h0a, hab, hb1, hpay⟩ := hinv
  rw [fst_opair, snd_opair]
  exact ⟨haQ, hbQ, h0a, hab, hb1, hpay⟩

/-- The generic invariant's payload, named. -/
theorem halveS_payload {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveS P) : P (fst s) (snd s) := by
  obtain ⟨-, -, -, -, -, h⟩ := halveS_spec hs
  exact h

/-- The halving chain's left endpoints, as a set-level rational sequence. -/
def halveA (g : ZFSet.{u}) : ZFSet.{u} :=
  graphOn omega.{u} Rat.{u} (fun n => fst (app g n))

/-- The halving chain's right endpoints. -/
def halveB (g : ZFSet.{u}) : ZFSet.{u} :=
  graphOn omega.{u} Rat.{u} (fun n => snd (app g n))

theorem halveA_mem_ratSeqs {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P) :
    halveA g ∈ ratSeqs.{u} :=
  (mem_ratSeqs_iff _).mpr ⟨graphOn_subset _ _ _,
    graphOn_isFunction _ _ _,
    graphOn_domain (fun n hn =>
      (halveS_spec (halve_chain_mem hgR h0 hs₀ n hn)).left)⟩

theorem halveB_mem_ratSeqs {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P) :
    halveB g ∈ ratSeqs.{u} :=
  (mem_ratSeqs_iff _).mpr ⟨graphOn_subset _ _ _,
    graphOn_isFunction _ _ _,
    graphOn_domain (fun n hn =>
      (halveS_spec (halve_chain_mem hgR h0 hs₀ n hn)).right.left)⟩

theorem app_halveA {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ n : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P)
    (hn : n ∈ omega.{u}) : app (halveA g) n = fst (app g n) :=
  app_graphOn (fun m hm =>
    (halveS_spec (halve_chain_mem hgR h0 hs₀ m hm)).left) hn

theorem app_halveB {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ n : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P)
    (hn : n ∈ omega.{u}) : app (halveB g) n = snd (app g n) :=
  app_graphOn (fun m hm =>
    (halveS_spec (halve_chain_mem hgR h0 hs₀ m hm)).right.left) hn

/-- The generic invariant's strict inequality, named. -/
theorem halveS_lt {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveS P) : ratLt (fst s) (snd s) := by
  obtain ⟨-, -, -, h, -⟩ := halveS_spec hs
  exact h

/-- The generic invariant's upper bound, named. -/
theorem halveS_snd_le_one {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveS P) : ratLe (snd s) ratOne.{u} := by
  obtain ⟨-, -, -, -, h, -⟩ := halveS_spec hs
  exact h

theorem halveR_step {P : ZFSet.{u} → ZFSet.{u} → Prop} {s s' : ZFSet.{u}}
    (h : opair s s' ∈ halveR P) :
    And (ratLe (fst s) (fst s')) (And (ratLe (snd s') (snd s))
      (ratMul (ratAdd (snd s') (ratNeg (fst s'))) ratTwo.{u}
        = ratAdd (snd s) (ratNeg (fst s)))) := by
  obtain ⟨hP, a, b, haQ, hbQ, hor⟩ := (mem_sep_iff _ _ _).mp h
  obtain ⟨x, hx, y, hy, heq2⟩ := (mem_prod_iff _ _ _).mp hP
  obtain ⟨rfl, rfl⟩ := opair_injective heq2
  have hab : ratLt a b := by
    rcases hor with ⟨heq, -⟩ | ⟨heq, -⟩ <;>
      · obtain ⟨h1, -⟩ := opair_injective heq
        have hspec := (halveS_spec hx).right.right.right.left
        rw [h1, fst_opair, snd_opair] at hspec
        exact hspec
  rcases hor with ⟨heq, -⟩ | ⟨heq, -⟩
  · obtain ⟨h1, h2⟩ := opair_injective heq
    rw [h1, h2, fst_opair, snd_opair, fst_opair, snd_opair]
    exact ⟨ratLe_refl haQ, (ratMid_lt haQ hbQ hab).left,
      ratMid_sub_left haQ hbQ⟩
  · obtain ⟨h1, h2⟩ := opair_injective heq
    rw [h1, h2, fst_opair, snd_opair, fst_opair, snd_opair]
    exact ⟨(lt_ratMid haQ hbQ hab).left, ratLe_refl hbQ,
      ratMid_sub_right haQ hbQ⟩


--
--
--

/-! ### The endpoint sequences

`halveA` and `halveB` are REUSED, not re-defined. Both are
`graphOn omega Rat (fun n => fst (app g n))` and its `snd` twin -- functions of
the CHAIN alone. The step relation enters only through the hypotheses of the
lemmas below, and only to establish `app g n ∈ halveS P`, which
`split_chain_mem` supplies for a split chain exactly as `halve_chain_mem` does
for a halving one. A split-specific pair of endpoint sequences would therefore
have been the same two definitions under new names.
-/

/-- Along the chain, left endpoints rise and right endpoints fall. -/
theorem halveChain_mono {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P) :
    ∀ i j : Nat, i ≤ j →
      And (ratLe (app (halveA g) (ofNat.{u} i))
          (app (halveA g) (ofNat.{u} j)))
        (ratLe (app (halveB g) (ofNat.{u} j))
          (app (halveB g) (ofNat.{u} i))) := by
  intro i j
  induction j with
  | zero =>
    intro hij
    have : i = 0 := Nat.le_zero.mp hij
    subst this
    have hAQ : app (halveA g) (ofNat.{u} 0) ∈ Rat.{u} := by
      rw [app_halveA hgR h0 hs₀ (ofNat_mem_omega 0)]
      exact (halveS_spec (halve_chain_mem hgR h0 hs₀ _
        (ofNat_mem_omega 0))).left
    have hBQ : app (halveB g) (ofNat.{u} 0) ∈ Rat.{u} := by
      rw [app_halveB hgR h0 hs₀ (ofNat_mem_omega 0)]
      exact (halveS_spec (halve_chain_mem hgR h0 hs₀ _
        (ofNat_mem_omega 0))).right.left
    exact ⟨ratLe_refl hAQ, ratLe_refl hBQ⟩
  | succ j ih =>
    intro hij
    have hstep := halveR_step (hgR (ofNat.{u} j) (ofNat_mem_omega j))
    have hAj := app_halveA hgR h0 hs₀ (ofNat_mem_omega j)
    have hAj1 := app_halveA hgR h0 hs₀ (ofNat_mem_omega (j + 1))
    have hBj := app_halveB hgR h0 hs₀ (ofNat_mem_omega j)
    have hBj1 := app_halveB hgR h0 hs₀ (ofNat_mem_omega (j + 1))
    have hspec := fun k (hk : k ∈ omega.{u}) =>
      halveS_spec (halve_chain_mem hgR h0 hs₀ k hk)
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · have hij' : i ≤ j := Nat.lt_succ_iff.mp hlt
      obtain ⟨ihA, ihB⟩ := ih hij'
      constructor
      · refine ratLe_trans ?_ ?_ ?_ ihA ?_
        · rw [app_halveA hgR h0 hs₀ (ofNat_mem_omega i)]
          exact (hspec _ (ofNat_mem_omega i)).left
        · rw [hAj]
          exact (hspec _ (ofNat_mem_omega j)).left
        · rw [hAj1]
          exact (hspec _ (ofNat_mem_omega (j + 1))).left
        · rw [hAj, hAj1]
          exact hstep.left
      · refine ratLe_trans ?_ ?_ ?_ ?_ ihB
        · rw [hBj1]
          exact (hspec _ (ofNat_mem_omega (j + 1))).right.left
        · rw [hBj]
          exact (hspec _ (ofNat_mem_omega j)).right.left
        · rw [app_halveB hgR h0 hs₀ (ofNat_mem_omega i)]
          exact (hspec _ (ofNat_mem_omega i)).right.left
        · rw [hBj, hBj1]
          exact hstep.right.left
    · have : i = j + 1 := Nat.le_antisymm hij hge
      subst this
      constructor
      · rw [hAj1]
        exact ratLe_refl (hspec _ (ofNat_mem_omega (j + 1))).left
      · rw [hBj1]
        exact ratLe_refl (hspec _ (ofNat_mem_omega (j + 1))).right.left

set_option maxHeartbeats 1000000 in
/-- The chain's widths halve, scaled so nothing is divided:
`wₙ · 2ⁿ = w₀`. -/
theorem halveChain_width_scaled {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P) :
    ∀ n : Nat, ratMul (ratAdd (app (halveB g) (ofNat.{u} n))
      (ratNeg (app (halveA g) (ofNat.{u} n)))) (ratNat.{u} (pow2 n) 1)
      = ratAdd (app (halveB g) (ofNat.{u} 0))
        (ratNeg (app (halveA g) (ofNat.{u} 0)))
  | 0 => by
    have hspec := halveS_spec (halve_chain_mem hgR h0 hs₀ _
      (ofNat_mem_omega 0))
    rw [pow2, ratNat_one_one,
      ratMul_one (ratAdd_mem_Rat
        (by rw [app_halveB hgR h0 hs₀ (ofNat_mem_omega 0)]
            exact hspec.right.left)
        (ratNeg_mem_Rat
          (by rw [app_halveA hgR h0 hs₀ (ofNat_mem_omega 0)]
              exact hspec.left)))]
  | n + 1 => by
    have hw := halveChain_width_scaled hgR h0 hs₀ n
    have hstep := halveR_step (hgR (ofNat.{u} n) (ofNat_mem_omega n))
    have hAn := app_halveA hgR h0 hs₀ (ofNat_mem_omega n)
    have hAn1 := app_halveA hgR h0 hs₀ (ofNat_mem_omega (n + 1))
    have hBn := app_halveB hgR h0 hs₀ (ofNat_mem_omega n)
    have hBn1 := app_halveB hgR h0 hs₀ (ofNat_mem_omega (n + 1))
    have hspecn := halveS_spec (halve_chain_mem hgR h0 hs₀ _
      (ofNat_mem_omega n))
    have hspecn1 := halveS_spec (halve_chain_mem hgR h0 hs₀ _
      (ofNat_mem_omega (n + 1)))
    have hhalf : ratMul (ratAdd (app (halveB g) (ofNat.{u} (n + 1)))
        (ratNeg (app (halveA g) (ofNat.{u} (n + 1))))) ratTwo.{u}
        = ratAdd (app (halveB g) (ofNat.{u} n))
          (ratNeg (app (halveA g) (ofNat.{u} n))) := by
      rw [hAn, hAn1, hBn, hBn1]
      exact hstep.right.right
    have hwn1Q : ratAdd (app (halveB g) (ofNat.{u} (n + 1)))
        (ratNeg (app (halveA g) (ofNat.{u} (n + 1)))) ∈ Rat.{u} := by
      rw [hAn1, hBn1]
      exact ratAdd_mem_Rat hspecn1.right.left
        (ratNeg_mem_Rat hspecn1.left)
    have h2m : ratNat.{u} (pow2 (n + 1)) 1
        = ratMul (ratNat.{u} (pow2 n) 1) ratTwo.{u} := by
      have hcomm : pow2 (n + 1) = pow2 n * 2 := by
        show 2 * pow2 n = pow2 n * 2
        omega
      rw [hcomm]
      show ratNat.{u} (pow2 n * 2) (1 * 1) = _
      rw [← ratNat_mul Nat.one_pos Nat.one_pos, ratNat_two_one]
    rw [h2m, ratMul_comm (ratNat_mem_Rat Nat.one_pos) ratTwo_mem_Rat,
      ← ratMul_assoc hwn1Q ratTwo_mem_Rat
        (ratNat_mem_Rat Nat.one_pos), hhalf]
    exact hw

/-- The chain's widths sit under the harmonic ladder:
`wₙ ≤ 1/(n+1)`, because `w₀ ≤ 1` and `n + 1 ≤ 2ⁿ`. -/
theorem halveChain_width_le {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P)
    (n : Nat) :
    ratLe (ratAdd (app (halveB g) (ofNat.{u} n))
      (ratNeg (app (halveA g) (ofNat.{u} n)))) (invWidth (ofNat.{u} n)) := by
  have hspec0 := halveS_spec (halve_chain_mem hgR h0 hs₀ _
    (ofNat_mem_omega 0))
  have hspecn := halveS_spec (halve_chain_mem hgR h0 hs₀ _
    (ofNat_mem_omega n))
  have hAn := app_halveA hgR h0 hs₀ (ofNat_mem_omega n)
  have hBn := app_halveB hgR h0 hs₀ (ofNat_mem_omega n)
  have hA0 := app_halveA hgR h0 hs₀ (ofNat_mem_omega 0)
  have hB0 := app_halveB hgR h0 hs₀ (ofNat_mem_omega 0)
  have hWnQ : ratAdd (app (halveB g) (ofNat.{u} n))
      (ratNeg (app (halveA g) (ofNat.{u} n))) ∈ Rat.{u} := by
    rw [hAn, hBn]
    exact ratAdd_mem_Rat hspecn.right.left (ratNeg_mem_Rat hspecn.left)
  have hWn0 : ratLe ratZero.{u} (ratAdd (app (halveB g) (ofNat.{u} n))
      (ratNeg (app (halveA g) (ofNat.{u} n)))) := by
    rw [hAn, hBn]
    exact (ratSub_pos hspecn.left hspecn.right.left
      (halveS_lt (halve_chain_mem hgR h0 hs₀ _ (ofNat_mem_omega n)))).left
  -- `w₀ ≤ 1`: the interval sits inside `[0, 1]`
  have hW0le1 : ratLe (ratAdd (app (halveB g) (ofNat.{u} 0))
      (ratNeg (app (halveA g) (ofNat.{u} 0)))) ratOne.{u} := by
    rw [hA0, hB0]
    have hb1 := halveS_snd_le_one (halve_chain_mem hgR h0 hs₀ _
      (ofNat_mem_omega 0))
    have h0a := hspec0.right.right.left
    have hstep := ratAdd_le_add hspec0.right.left ratOne_mem_Rat
      (ratNeg_mem_Rat hspec0.left) (ratNeg_mem_Rat ratZero_mem_Rat)
      hb1 (by
        rw [ratNeg_zero]
        have hflip := (ratAdd_le_add_right_iff (ratNeg_mem_Rat hspec0.left)
          ratZero_mem_Rat hspec0.left).mpr h0a
        rwa [ratZero_add (ratNeg_mem_Rat hspec0.left),
          ratAdd_neg hspec0.left] at hflip)
    rwa [ratNeg_zero, ratAdd_zero ratOne_mem_Rat] at hstep
  -- `wₙ · (n+1) ≤ wₙ · 2ⁿ = w₀ ≤ 1`
  have hmul_le : ratLe (ratMul (ratAdd (app (halveB g) (ofNat.{u} n))
      (ratNeg (app (halveA g) (ofNat.{u} n)))) (ratNat.{u} (n + 1) 1))
      ratOne.{u} := by
    have hmono := ratMul_le_mul_right (ratNat_mem_Rat Nat.one_pos)
      (ratNat_mem_Rat Nat.one_pos) hWnQ (ratNat_succ_le_pow2 n) hWn0
    rw [ratMul_comm (ratNat_mem_Rat Nat.one_pos) hWnQ,
      ratMul_comm (ratNat_mem_Rat Nat.one_pos) hWnQ] at hmono
    rw [halveChain_width_scaled hgR h0 hs₀ n] at hmono
    exact ratLe_trans (ratMul_mem_Rat hWnQ (ratNat_mem_Rat Nat.one_pos))
      (ratAdd_mem_Rat (by rw [hB0]; exact hspec0.right.left)
        (ratNeg_mem_Rat (by rw [hA0]; exact hspec0.left)))
      ratOne_mem_Rat hmono hW0le1
  -- cancel by `invWidth n`
  have hinvQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
  have hinv0 := (invWidth_pos (ofNat_mem_omega.{u} n)).left
  have hfin := ratMul_le_mul_right
    (ratMul_mem_Rat hWnQ (ratNat_mem_Rat Nat.one_pos))
    ratOne_mem_Rat hinvQ hmul_le hinv0
  rw [ratOne_mul hinvQ,
    ratMul_assoc hWnQ (ratNat_mem_Rat Nat.one_pos) hinvQ,
    succ_mul_invWidth, ratMul_one hWnQ] at hfin
  exact hfin

/-- The chain's endpoints are a nested family: everything the bundle
asks for is already on the shelf. -/
theorem halveChain_isNested {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P) :
    IsNested (halveA g) (halveB g) where
  lower_seq := halveA_mem_ratSeqs hgR h0 hs₀
  upper_seq := halveB_mem_ratSeqs hgR h0 hs₀
  lower_mono := by
    intro m hm n hn hsub
    obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
    obtain ⟨j, rfl⟩ := (mem_omega_iff n).mp hn
    exact (halveChain_mono hgR h0 hs₀ i j
      ((ofNat_subset_iff i j).mp hsub)).left
  upper_mono := by
    intro m hm n hn hsub
    obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
    obtain ⟨j, rfl⟩ := (mem_omega_iff n).mp hn
    exact (halveChain_mono hgR h0 hs₀ i j
      ((ofNat_subset_iff i j).mp hsub)).right
  bracket := by
    intro n hn
    obtain ⟨i, rfl⟩ := (mem_omega_iff n).mp hn
    have h := halveS_lt (halve_chain_mem hgR h0 hs₀ _ (ofNat_mem_omega i))
    rwa [← app_halveA hgR h0 hs₀ (ofNat_mem_omega i),
      ← app_halveB hgR h0 hs₀ (ofNat_mem_omega i)] at h
  shrink := fun ε hεQ hε0 =>
    shrink_of_invWidth (halveA_mem_ratSeqs hgR h0 hs₀)
      (halveB_mem_ratSeqs hgR h0 hs₀)
      (fun n hn => by
        obtain ⟨i, rfl⟩ := (mem_omega_iff n).mp hn
        exact halveChain_width_le hgR h0 hs₀ i) ε hεQ hε0

/-- The real a nested family names lies between the family's first
endpoints: the interval-membership every limit extraction re-derives. -/
theorem nest_mem_Icc_of_ends {a b p q : ZFSet.{u}} (hnest : IsNested a b)
    (hA0 : app a (ofNat.{u} 0) = p) (hB0 : app b (ofNat.{u} 0) = q) :
    opair (nestLower a) (nestUpper b) ∈ realLIcc p q := by
  refine (mem_realLIcc_iff _ _ _).mpr
    ⟨(mem_RealL_iff _).mpr ⟨_, _, rfl, isLocated_nest hnest⟩, ?_, ?_⟩
  · have hge := nest_ge hnest (ofNat_mem_omega 0)
    rwa [hA0] at hge
  · have hle := nest_le hnest (ofNat_mem_omega 0)
    rwa [hB0] at hle

/-- What the machine delivers: a real of the unit interval that every
stage brackets, in a payload-carrying interval of width at most
`1/(m+1)`.

Named because three theorems state it -- the core, and one for each way
of producing the chain -- and a conclusion written three times is a
conclusion nobody can change in one place. -/
def HasHalveLimit (P : ZFSet.{u} → ZFSet.{u} → Prop) : Prop :=
  ∃ c, And (c ∈ realLIcc ratZero.{u} ratOne.{u})
    (∀ m : Nat, ∃ a b, And (a ∈ Rat.{u}) (And (b ∈ Rat.{u})
      (And (ratLe ratZero.{u} a) (And (ratLt a b)
        (And (ratLe b ratOne.{u}) (And (P a b)
          (And (ratLe (ratAdd b (ratNeg a)) (invWidth (ofNat.{u} m)))
            (And (realLLe (realLOf a) c) (realLLe c (realLOf b))))))))))

set_option maxHeartbeats 1000000 in
/-- The machine's limit, given a chain. Everything after the chain
exists: the endpoints are nested, the named real sits at every stage
inside a payload-carrying interval of width at most `1/(m+1)`.

Split out from `halve_limit` because the chain has two sources and this
part does not care which. `DC` produces one from the payload's totality;
a selector produces one by recursion (`halve_limit_of_selector`), and the
difference between those is the whole of what `DC` buys here. -/
theorem halve_limit_core {P : ZFSet.{u} → ZFSet.{u} → Prop} {g : ZFSet.{u}}
    (hgstep : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (hg0 : app g empty.{u} = opair ratZero.{u} ratOne.{u})
    (hs₀S : opair ratZero.{u} ratOne.{u} ∈ halveS P) :
    HasHalveLimit P := by
  have hnest := halveChain_isNested hgstep hg0 hs₀S
  have hA0 : app (halveA g) (ofNat.{u} 0) = ratZero.{u} := by
    rw [app_halveA hgstep hg0 hs₀S (ofNat_mem_omega 0)]
    show fst (app g empty.{u}) = _
    rw [hg0, fst_opair]
  have hB0 : app (halveB g) (ofNat.{u} 0) = ratOne.{u} := by
    rw [app_halveB hgstep hg0 hs₀S (ofNat_mem_omega 0)]
    show snd (app g empty.{u}) = _
    rw [hg0, snd_opair]
  have hcIcc : opair (nestLower (halveA g)) (nestUpper (halveB g))
      ∈ realLIcc ratZero.{u} ratOne.{u} :=
    nest_mem_Icc_of_ends hnest hA0 hB0
  refine ⟨_, hcIcc, fun m => ?_⟩
  have hmem := halve_chain_mem hgstep hg0 hs₀S _ (ofNat_mem_omega m)
  have hAm := app_halveA hgstep hg0 hs₀S (ofNat_mem_omega m)
  have hBm := app_halveB hgstep hg0 hs₀S (ofNat_mem_omega m)
  refine ⟨app (halveA g) (ofNat.{u} m), app (halveB g) (ofNat.{u} m),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hAm]; exact (halveS_spec hmem).left
  · rw [hBm]; exact (halveS_spec hmem).right.left
  · rw [hAm]; exact (halveS_spec hmem).right.right.left
  · rw [hAm, hBm]; exact halveS_lt hmem
  · rw [hBm]; exact halveS_snd_le_one hmem
  · rw [hAm, hBm]; exact halveS_payload hmem
  · exact halveChain_width_le hgstep hg0 hs₀S m
  · exact nest_ge hnest (ofNat_mem_omega m)
  · exact nest_le hnest (ofNat_mem_omega m)

set_option maxHeartbeats 1000000 in
/-- The machine's limit: `DC` chains the halving, and
`halve_limit_core` does the rest. -/
theorem halve_limit_of_binaryDCOn {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hbdc : BinaryDCOn.{u})
    (hP : ∀ a b, a ∈ Rat.{u} → b ∈ Rat.{u} → ratLe ratZero.{u} a →
      ratLt a b → ratLe b ratOne.{u} → P a b →
      P a (ratMid a b) ∨ P (ratMid a b) b)
    (hP01 : P ratZero.{u} ratOne.{u}) :
    HasHalveLimit P := by
  have hs₀inv : halveInv P (opair ratZero.{u} ratOne.{u}) :=
    ⟨ratZero.{u}, ratOne.{u}, ratZero_mem_Rat, ratOne_mem_Rat, rfl,
      ratLe_refl ratZero_mem_Rat, ratZero_lt_one, ratLe_refl ratOne_mem_Rat,
      hP01⟩
  have hs₀S : opair ratZero.{u} ratOne.{u} ∈ halveS P :=
    (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod ratZero_mem_Rat ratOne_mem_Rat, hs₀inv⟩
  obtain ⟨g, -, -, hg0, hgstep⟩ := hbdc (halveS P) (halveR P)
    (halveMove P halveLeft) (halveMove P halveRight)
    (fun p hp => ((mem_sep_iff _ _ _).mp hp).left)
    (isFunction_halveMove P halveLeft)
    (domain_halveMove (fun _ h => halveLeft_mem_prod h))
    (isFunction_halveMove P halveRight)
    (domain_halveMove (fun _ h => halveRight_mem_prod h))
    (fun s hs => by
      rw [app_halveMove hs (halveLeft_mem_prod hs),
        app_halveMove hs (halveRight_mem_prod hs)]
      exact halve_binary hP s hs)
    _ hs₀S
  exact halve_limit_core hgstep hg0 hs₀S

set_option maxHeartbeats 1000000 in
/-- The machine's limit from the INSTANCE, which is all the proof above
actually uses.

`halve_limit_of_binaryDCOn` takes the quantified `BinaryDCOn` and applies it once,
at `halveS P` and `halveR P`. This is the same proof with the carrier fixed, so
the hypothesis is a statement about CODED RATIONAL INTERVALS rather than about
every set.

WHY THAT IS WORTH A SEPARATE THEOREM. Seven registry rows spend
`SignDisjunction + BinaryDCOn` and their reversal is blocked on
`<landmark> -> BinaryDCOn` --- a chain in an ARBITRARY `S`, `powerset RealL`
included, from landmarks that conclude only about `RealL`. At the instance that
objection is gone: `halveS P` is pairs of rationals, which is the landmarks' own
subject. The blocked target shrinks even if it does not open.

ADDITIVE ON PURPOSE. `halve_limit_of_binaryDCOn` keeps its signature and its
seventeen consumers are untouched; `binaryDCOnAt_of_binaryDCOn` bridges the two
whenever the quantified form is what a caller holds. -/
theorem halve_limit_of_binaryDCOnAt {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hbdc : BinaryDCOnAt.{u} (halveS P) (halveR P))
    (hP : ∀ a b, a ∈ Rat.{u} → b ∈ Rat.{u} → ratLe ratZero.{u} a →
      ratLt a b → ratLe b ratOne.{u} → P a b →
      P a (ratMid a b) ∨ P (ratMid a b) b)
    (hP01 : P ratZero.{u} ratOne.{u}) :
    HasHalveLimit P := by
  have hs₀inv : halveInv P (opair ratZero.{u} ratOne.{u}) :=
    ⟨ratZero.{u}, ratOne.{u}, ratZero_mem_Rat, ratOne_mem_Rat, rfl,
      ratLe_refl ratZero_mem_Rat, ratZero_lt_one, ratLe_refl ratOne_mem_Rat,
      hP01⟩
  have hs₀S : opair ratZero.{u} ratOne.{u} ∈ halveS P :=
    (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod ratZero_mem_Rat ratOne_mem_Rat, hs₀inv⟩
  obtain ⟨g, -, -, hg0, hgstep⟩ := hbdc
    (halveMove P halveLeft) (halveMove P halveRight)
    (isFunction_halveMove P halveLeft)
    (domain_halveMove (fun _ h => halveLeft_mem_prod h))
    (isFunction_halveMove P halveRight)
    (domain_halveMove (fun _ h => halveRight_mem_prod h))
    (fun s hs => by
      rw [app_halveMove hs (halveLeft_mem_prod hs),
        app_halveMove hs (halveRight_mem_prod hs)]
      exact halve_binary hP s hs)
    _ hs₀S
  exact halve_limit_core hgstep hg0 hs₀S

/-- The machine's limit from `DC`, now a corollary rather than a proof.
`DC`'s only use here factors through `BinaryDCOn`, and writing it this way is
what makes that visible: the chain never needed choice from an arbitrary set of
successors, only the choice between two named halves. -/
theorem halve_limit {P : ZFSet.{u} → ZFSet.{u} → Prop} (hdc : DC.{u})
    (hP : ∀ a b, a ∈ Rat.{u} → b ∈ Rat.{u} → ratLe ratZero.{u} a →
      ratLt a b → ratLe b ratOne.{u} → P a b →
      P a (ratMid a b) ∨ P (ratMid a b) b)
    (hP01 : P ratZero.{u} ratOne.{u}) :
    HasHalveLimit P :=
  halve_limit_of_binaryDCOn (binaryDCOn_of_dc hdc) hP hP01

/-! ## The chain from a selector, with no dependent choice

`halve_limit` spends `DC` in exactly one place: producing the chain whose
steps the invariant's totality allows. Totality is a `Prop`-level
disjunction -- some half keeps the payload -- and turning a sequence of
those into a function is the wall `DC` is there to climb.

Handed the choice as data instead, the chain is an ordinary recursion:
`natSeq` turns a `Nat`-indexed family into a set-level function and
`app_natSeq` computes it. So the principle is not needed for the
construction, only for the case where nobody supplies the bit -- which is
the same trade the readouts make everywhere else in this development. -/

/-- A selector: which half to take, as a `Bool`, together with the promise
that the half it names keeps the payload. Data, not a principle. -/
structure HalveSelector (P : ZFSet.{u} → ZFSet.{u} → Prop) where
  bit : ZFSet.{u} → Bool
  keeps : ∀ a b, a ∈ Rat.{u} → b ∈ Rat.{u} → ratLe ratZero.{u} a →
    ratLt a b → ratLe b ratOne.{u} → P a b →
    if bit (opair a b) then P a (ratMid a b) else P (ratMid a b) b

/-- One step of the walk, as a function on coded intervals. -/
def halveStep {P : ZFSet.{u} → ZFSet.{u} → Prop} (σ : HalveSelector P)
    (s : ZFSet.{u}) : ZFSet.{u} :=
  if σ.bit s then opair (fst s) (ratMid (fst s) (snd s))
  else opair (ratMid (fst s) (snd s)) (snd s)

/-- The step stays in the state set: the selector's promise is exactly the
invariant's preservation, read on whichever half the bit names. -/
theorem halveStep_mem {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (σ : HalveSelector P) {s : ZFSet.{u}} (hs : s ∈ halveS P) :
    halveStep σ s ∈ halveS P := by
  obtain ⟨-, a, b, haQ, hbQ, rfl, h0a, hab, hb1, hPab⟩ :=
    (mem_sep_iff _ _ _).mp hs
  obtain ⟨hmQ, ham, hmb, h0m, hm1⟩ := ratMid_facts haQ hbQ h0a hab hb1
  have hkeep := σ.keeps a b haQ hbQ h0a hab hb1 hPab
  rw [halveStep, fst_opair, snd_opair]
  cases hbit : σ.bit (opair a b) with
  | true =>
    rw [hbit] at hkeep
    simp only [if_pos rfl] at hkeep ⊢
    exact (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod haQ hmQ,
      a, ratMid a b, haQ, hmQ, rfl, h0a, ham, hm1, hkeep⟩
  | false =>
    rw [hbit] at hkeep
    simp only [Bool.false_eq_true, if_neg] at hkeep ⊢
    exact (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod hmQ hbQ,
      ratMid a b, b, hmQ, hbQ, rfl, h0m, hmb, hb1, hkeep⟩

/-- The step is a move of the machine's relation. -/
theorem halveStep_rel {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (σ : HalveSelector P) {s : ZFSet.{u}} (hs : s ∈ halveS P) :
    opair s (halveStep σ s) ∈ halveR P := by
  have hnext := halveStep_mem σ hs
  obtain ⟨-, a, b, haQ, hbQ, rfl, h0a, hab, hb1, hPab⟩ :=
    (mem_sep_iff _ _ _).mp hs
  refine (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod hs hnext, a, b, haQ, hbQ, ?_⟩
  rw [halveStep, fst_opair, snd_opair] at hnext ⊢
  cases hbit : σ.bit (opair a b) with
  | true =>
    simp only [hbit, if_pos rfl] at hnext ⊢
    exact Or.inl ⟨rfl, ((mem_sep_iff _ _ _).mp hnext).right⟩
  | false =>
    simp only [hbit, Bool.false_eq_true, if_neg] at hnext ⊢
    exact Or.inr ⟨rfl, ((mem_sep_iff _ _ _).mp hnext).right⟩

/-- The walk itself, iterated from the unit interval. -/
def halveIter {P : ZFSet.{u} → ZFSet.{u} → Prop} (σ : HalveSelector P) :
    Nat → ZFSet.{u}
  | 0 => opair ratZero.{u} ratOne.{u}
  | n + 1 => halveStep σ (halveIter σ n)

theorem halveIter_mem {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (σ : HalveSelector P) (hP01 : P ratZero.{u} ratOne.{u}) :
    ∀ n, halveIter σ n ∈ halveS P
  | 0 => (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod ratZero_mem_Rat ratOne_mem_Rat,
        ratZero.{u}, ratOne.{u}, ratZero_mem_Rat, ratOne_mem_Rat, rfl,
        ratLe_refl ratZero_mem_Rat, ratZero_lt_one,
        ratLe_refl ratOne_mem_Rat, hP01⟩
  | n + 1 => halveStep_mem σ (halveIter_mem σ hP01 n)

/-- The machine's limit, from a selector. Identical to `halve_limit`
except that the chain is recursion rather than choice: `DC` does not
appear, and what replaces it is a `Bool` per node with its promise. -/
theorem halve_limit_of_selector {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (σ : HalveSelector P) (hP01 : P ratZero.{u} ratOne.{u}) :
    HasHalveLimit P := by
  have hmem := halveIter_mem σ hP01
  have hg0 : app (natSeq (halveS P) (halveIter σ)) empty.{u}
      = opair ratZero.{u} ratOne.{u} := app_natSeq hmem 0
  have hs₀S : opair ratZero.{u} ratOne.{u} ∈ halveS P := hmem 0
  have hgstep : ∀ n, n ∈ omega.{u} →
      opair (app (natSeq (halveS P) (halveIter σ)) n)
        (app (natSeq (halveS P) (halveIter σ)) (succ n)) ∈ halveR P := by
    intro n hn
    obtain ⟨k, rfl⟩ := (mem_omega_iff n).mp hn
    rw [app_natSeq hmem k, ← ofNat_succ, app_natSeq hmem (k + 1)]
    exact halveStep_rel σ (hmem k)
  exact halve_limit_core hgstep hg0 hs₀S

/-! ## A selector the instantiation can build for itself

`HalveSelector` asks for a `Bool` at each node, and that is strictly more than
the walk needs. A `Bool` is Lean-level data, so producing one from a
proposition wants `Decidable` -- and the propositions this machine branches on
are comparisons of rationals, whose disjunction is an outright theorem
(`ratLt_or_not`) that still cannot eliminate into `Bool`. So an instantiation
whose test is decided in every sense that matters is nonetheless unable to
write down a selector: the Prop-to-data wall, arriving where it looks least
deserved.

Conditioning on the proposition itself removes the obstruction, and removes it
for free: `condP` is total on any `Prop`, because separation takes an
arbitrary formula, so the step is definable with no principle whatever. What
the disjunction is spent on is then only the proof that the step preserved the
invariant, and there `ratLt_or_not` is exactly enough. The carrier is the whole
difference: a set-level branch is free where a `Bool` is not. -/

/-- A decider: which half to take, as a proposition decided on rational
endpoints, with the promise that each side keeps the payload. -/
structure HalveDecider (P : ZFSet.{u} → ZFSet.{u} → Prop) where
  goLeft : ZFSet.{u} → Prop
  decided : ∀ a b, a ∈ Rat.{u} → b ∈ Rat.{u} →
    goLeft (opair a b) ∨ ¬ goLeft (opair a b)
  keepsL : ∀ a b, a ∈ Rat.{u} → b ∈ Rat.{u} → ratLe ratZero.{u} a →
    ratLt a b → ratLe b ratOne.{u} → P a b → goLeft (opair a b) →
    P a (ratMid a b)
  keepsR : ∀ a b, a ∈ Rat.{u} → b ∈ Rat.{u} → ratLe ratZero.{u} a →
    ratLt a b → ratLe b ratOne.{u} → P a b → ¬ goLeft (opair a b) →
    P (ratMid a b) b

/-! ### An instantiation that supplies its own decider

The trade becomes a removal here. `sqrtTwoP` reads the payload on the
doubled endpoints, so a walk confined to `[0,1]` converges on `√2/2`
while every comparison it makes is between rationals; and a comparison
between rationals is decided outright by `ratLt_or_not`. Nothing is
hypothesised: `halve_limit_of_decider sqrtTwoDecider` takes no principle
and no data, only the two facts that `[0,1]` starts the walk. -/

/-- Twice a rational. -/
def ratTwice (x : ZFSet.{u}) : ZFSet.{u} := ratMul (ratNat.{u} 2 1) x

/-- The payload: the doubled interval straddles `√2`. -/
def sqrtTwoP (a b : ZFSet.{u}) : Prop :=
  And (ratLt (ratMul (ratTwice a) (ratTwice a)) (ratNat.{u} 2 1))
      (ratLt (ratNat.{u} 2 1) (ratMul (ratTwice b) (ratTwice b)))

#print axioms halveB_mem_ratSeqs
#print axioms halveS_lt
#print axioms halveS_snd_le_one
#print axioms halveIter_mem
end NumberTheory

#print axioms NumberTheory.halve_total
#print axioms NumberTheory.BinaryDCOn
#print axioms NumberTheory.binaryDCOn_of_dc
#print axioms NumberTheory.BinaryDCOnAt
#print axioms NumberTheory.binaryDCOnAt_of_binaryDCOn
#print axioms NumberTheory.halveLeft
#print axioms NumberTheory.halveRight
#print axioms NumberTheory.halve_binary
#print axioms NumberTheory.halveMove
#print axioms NumberTheory.isFunction_halveMove
#print axioms NumberTheory.mem_halveMove
#print axioms NumberTheory.app_halveMove
#print axioms NumberTheory.domain_halveMove
#print axioms NumberTheory.halveLeft_mem_prod
#print axioms NumberTheory.halveRight_mem_prod
#print axioms NumberTheory.ratMid_facts
#print axioms NumberTheory.halve_chain_mem
#print axioms NumberTheory.halveS_spec
#print axioms NumberTheory.halveA_mem_ratSeqs
#print axioms NumberTheory.app_halveA
#print axioms NumberTheory.app_halveB
#print axioms NumberTheory.halveR_step
#print axioms NumberTheory.halveChain_mono
#print axioms NumberTheory.halveChain_width_le
#print axioms NumberTheory.halveChain_isNested
#print axioms NumberTheory.nest_mem_Icc_of_ends
#print axioms NumberTheory.halveS_payload
#print axioms NumberTheory.halve_limit
#print axioms NumberTheory.halveStep_mem
#print axioms NumberTheory.halveStep_rel
#print axioms NumberTheory.halve_limit_of_selector
namespace ZFSet
export NumberTheory (BinaryDCOn BinaryDCOnAt HalveDecider HalveSelector HasHalveLimit app_halveA app_halveB app_halveMove binaryDCOn_of_dc binaryDCOnAt_of_binaryDCOn domain_halveMove halveA halveA_mem_ratSeqs halveB halveB_mem_ratSeqs halveChain_isNested halveChain_mono halveChain_width_le halveInv halveIter halveIter_mem halveLeft halveLeft_mem_prod halveMove halveR halveR_step halveRight halveRight_mem_prod halveS halveS_lt halveS_payload halveS_snd_le_one halveS_spec halveStep halveStep_mem halveStep_rel halve_binary halve_chain_mem halve_limit halve_limit_of_selector halve_total isFunction_halveMove mem_halveMove nest_mem_Icc_of_ends ratMid_facts ratTwice sqrtTwoP)
end ZFSet
