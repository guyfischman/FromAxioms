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

import FromAxioms.Analysis.IVT
import FromAxioms.Constructive.Vanishing

universe u

open Analysis Constructive SetTheory
namespace NumberTheory

/-- The midpoint's five facts at an arbitrary ambient interval.  The
unit-interval form `ratMid_facts` is this at `p = 0`, `q = 1`.

Three of the five --- membership, `a < mid` and `mid < b` --- mention no ambient
at all and are cited unchanged. The other two are transitivity against the
bounds on `a` and `b`, so the unit interval was never doing any work
here: it was in the statement and not in the mathematics. -/
theorem ratMid_facts_on {p q a b : ZFSet.{u}} (hp : p ∈ Rat.{u})
    (hq : q ∈ Rat.{u}) (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u})
    (hpa : ratLe p a) (hab : ratLt a b) (hbq : ratLe b q) :
    And (ratMid a b ∈ Rat.{u}) (And (ratLt a (ratMid a b))
      (And (ratLt (ratMid a b) b) (And (ratLe p (ratMid a b))
        (ratLe (ratMid a b) q)))) := by
  have hmQ := ratMid_mem_Rat ha hb
  have ham := lt_ratMid ha hb hab
  have hmb := ratMid_lt ha hb hab
  refine ⟨hmQ, ham, hmb, ?_, ?_⟩
  · exact ratLe_trans hp ha hmQ hpa (ratLe_of_lt ha hmQ ham)
  · exact ratLe_trans hmQ hb hq (ratLe_of_lt hmQ hb hmb) hbq

/-- The midpoint facts every halving step re-derives: membership, the two
strict inequalities, and the unit-interval bounds.

`ratMid_facts_on` above at `p = 0`, `q = 1`: substituting the literals for the
ambient parameters gives this statement, so the citation is the whole proof. -/
theorem ratMid_facts {a b : ZFSet.{u}} (ha : a ∈ Rat.{u}) (hb : b ∈ Rat.{u})
    (h0a : ratLe ratZero.{u} a) (hab : ratLt a b)
    (hb1 : ratLe b ratOne.{u}) :
    And (ratMid a b ∈ Rat.{u}) (And (ratLt a (ratMid a b))
      (And (ratLt (ratMid a b) b) (And (ratLe ratZero.{u} (ratMid a b))
        (ratLe (ratMid a b) ratOne.{u})))) :=
  ratMid_facts_on ratZero_mem_Rat ratOne_mem_Rat ha hb h0a hab hb1

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

/-- A halving state at an arbitrary ambient interval.  `halveInv` is this
at `p = 0`, `q = 1`; see `halveInv_iff_on` for the bridge, which is `Iff.rfl`.

The ambient lives in the body of `halveInv`, not its signature, so
every lemma about `halveS` inherits the unit interval without naming it. -/
def halveInvOn (p q : ZFSet.{u}) (P : ZFSet.{u} → ZFSet.{u} → Prop)
    (s : ZFSet.{u}) : Prop :=
  ∃ a b, a ∈ Rat.{u} ∧ b ∈ Rat.{u} ∧ s = opair a b ∧
    ratLe p a ∧ ratLt a b ∧ ratLe b q ∧ P a b

/-- The halving machine's state set at an arbitrary ambient interval. -/
def halveSOn (p q : ZFSet.{u}) (P : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  sep (halveInvOn p q P) (prod Rat.{u} Rat.{u})

/-- The halving machine's step relation at an arbitrary ambient interval. -/
def halveROn (p q : ZFSet.{u}) (P : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  sep (fun z => ∃ a b, a ∈ Rat.{u} ∧ b ∈ Rat.{u} ∧
    ((z = opair (opair a b) (opair a (ratMid a b))
        ∧ halveInvOn p q P (opair a (ratMid a b)))
      ∨ (z = opair (opair a b) (opair (ratMid a b) b)
        ∧ halveInvOn p q P (opair (ratMid a b) b))))
    (prod (halveSOn p q P) (halveSOn p q P))

/-- Binary dependent choice on a set. `DC` with the totality hypothesis
replaced by a disjunction between two named successors.

Weaker than `DC` by inspection -- the hypothesis is strictly stronger, since a
disjunction between two named moves yields totality while totality names
nothing -- and `binaryDCOn_of_dc` proves that direction. Whether it is strictly
weaker is a question about models and is not settled here.

The successors are set functions, not Lean functions. `DC` quantifies over
`S R : ZFSet`, so a Lean-level `f₀ : ZFSet → ZFSet` would make the two
principles comparable in Lean and not comparable inside the theory -- a Lean
function cannot be a bound
variable of the object language, so *there is a model where this holds and `DC`
fails* would be unsayable about it.

`f₀` and `f₁` are named in advance, and a construction must supply them to be
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

Two producers conclude `BinaryDCOn` and both are principles --- the join
projecting, and `binaryDCOn_of_dc` above. No landmark yields it, so the seven
theorems spending this pair cannot be repointed at `BisectionSearch`: a
reversal would then have to conclude the join, and this half has no producer
that is not already a principle.

The argument below is not new and its generality is. This tree runs the same
`natSeq` recursion three times, each hard-wired to one state set:
`halveIter`/`halve_limit_of_selector` and `halveStepD`/`halveIterD` further
down this file, and `Topology.exists_baire_walk_of_selector` at `baireState`.
The insight is already in this file's own prose, one section below --- *`condP`
is total on any `Prop` ... the step is definable with no principle whatever ...
a set-level branch is free where a `Bool` is not*. What was missing is the
statement at an arbitrary `S` and `R`.

The recursion is shared and the input is not, so the general form is worth
having. `HalveSelector.bit` is a Lean `ZFSet → Bool` and `halveStep` a Lean
function; `Topology.IsBaireSelector` carries a ZFSet `sel`. So
`IsChainSelector` generalises the second exactly and is the set-level sibling
of the first. That matters because a reversal argues about the principle: a
`Prop` cannot quantify over Lean-level data here, so the halving machine's
selector and decider cannot appear inside one, and the ZFSet forms can.

And the set form costs nothing, at `[propext, Quot.sound]`: `sep` takes an
arbitrary formula, so `sep goLeft S` turns any predicate branch into a set one
and detachability transfers both ways. `HalveDecider.decided`'s obligation and
`isChainSelector_of_detachable`'s `hdet` are interchangeable on `S`.

Nor is `hdet` excluded middle in disguise. It is at a fixed `S` and `T`. The
quantified form is the principle --- `Analysis.DecidableMemSet` is EM by
`em_of_decidableMemSet`, and `IdealDetachableInt` reverses to `LPO` --- and this
is the hypothesis form, as `HalveDecider.decided` is.

    BinaryDCOn  =  a free chain  +  a decision of the branch at each state

Not claimed: that the bisection's branch is detachable. It is not --- choosing the
half is exactly what `Constructive.SignDisjunction` buys, so the two
are spent together, and the section below says the same thing about `ratLt_or_not`. -/

/-- `BinaryDCOn` at one carrier and relation.

The quantified form is more than any consumer uses.
`halve_limit_of_binaryDCOn` below takes `BinaryDCOn` and its proof opens
`hbdc (halveS P) (halveR P) ...` --- a single instance, at a set of coded
rational intervals. Seventeen theorems across `Analysis/Extreme.lean` and
`Metamath/Calibrate.lean` inherit that hypothesis, so seven registry rows spend a
principle about every carrier in order to use it at one.

Why that matters rather than being tidiness. Those rows' reversal is blocked, and
the blocked target reads `<landmark> -> BinaryDCOn`: a chain in an arbitrary `S`,
`powerset RealL` included, from a landmark that speaks only of `RealL`. At the
instance the objection is gone --- `halveS P` is pairs of rationals, which is the
landmarks' own subject.

This is the move `the category theorem` made for `DCOn`. That row records a
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

/-- A move's graph: the same function as an object of the theory. Generic in the
move, so one construction serves both halves.

The codomain is `prod Rat Rat` rather than `halveS P`: only one of the two moves
keeps the payload at any state, so neither graph lands in the state set, and
requiring it would be false. -/
def halveMove (P : ZFSet.{u} → ZFSet.{u} → Prop) (f : ZFSet.{u} → ZFSet.{u}) :
    ZFSet.{u} :=
  sep (fun z => ∃ s, s ∈ halveS P ∧ z = opair s (f s))
    (prod (halveS P) (prod Rat.{u} Rat.{u}))

theorem mem_halveMove {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {f : ZFSet.{u} → ZFSet.{u}} {s : ZFSet.{u}} (hs : s ∈ halveS P)
    (hf : f s ∈ prod Rat.{u} Rat.{u}) :
    opair s (f s) ∈ halveMove P f :=
  (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod hs hf, s, hs, rfl⟩

/-- The halving chain's left endpoints, as a set-level rational sequence. -/
def halveA (g : ZFSet.{u}) : ZFSet.{u} :=
  graphOn omega.{u} Rat.{u} (fun n => fst (app g n))

/-- The halving chain's right endpoints. -/
def halveB (g : ZFSet.{u}) : ZFSet.{u} :=
  graphOn omega.{u} Rat.{u} (fun n => snd (app g n))

/-- The halving state's five facts at an arbitrary ambient.
`halveS_spec` is this at `p = 0`, `q = 1`. -/
theorem halveS_spec_on {p q : ZFSet.{u}} {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {s : ZFSet.{u}} (hs : s ∈ halveSOn p q P) :
    And (fst s ∈ Rat.{u}) (And (snd s ∈ Rat.{u})
      (And (ratLe p (fst s)) (And (ratLt (fst s) (snd s))
        (And (ratLe (snd s) q) (P (fst s) (snd s)))))) := by
  obtain ⟨-, hinv⟩ := (mem_sep_iff _ _ _).mp hs
  obtain ⟨a, b, haQ, hbQ, rfl, hpa, hab, hbq, hpay⟩ := hinv
  rw [fst_opair, snd_opair]
  exact ⟨haQ, hbQ, hpa, hab, hbq, hpay⟩

/-- Reading a halving state back: both coordinates rational, the bounds,
the strictness, and the payload. -/
theorem halveS_spec {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveS P) :
    And (fst s ∈ Rat.{u}) (And (snd s ∈ Rat.{u})
      (And (ratLe ratZero.{u} (fst s)) (And (ratLt (fst s) (snd s))
        (And (ratLe (snd s) ratOne.{u}) (P (fst s) (snd s)))))) :=
  halveS_spec_on (p := ratZero.{u}) (q := ratOne.{u}) hs

/-- The state's right endpoint is below the ambient's. -/
theorem halveS_snd_le_q_on {p q : ZFSet.{u}}
    {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveSOn p q P) : ratLe (snd s) q := by
  obtain ⟨-, -, -, -, h, -⟩ := halveS_spec_on hs
  exact h

/-- Totality of the halving step at an arbitrary ambient.  `halve_total`
is this at `p = 0`, `q = 1`. -/
theorem halve_total_on {p q : ZFSet.{u}} (hp : p ∈ Rat.{u}) (hq : q ∈ Rat.{u})
    {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hstep : ∀ a b, a ∈ Rat.{u} → b ∈ Rat.{u} → ratLe p a →
      ratLt a b → ratLe b q → P a b →
      Or (P a (ratMid a b)) (P (ratMid a b) b)) :
    ∀ s, s ∈ halveSOn p q P →
      ∃ s', s' ∈ halveSOn p q P ∧ opair s s' ∈ halveROn p q P := by
  intro s hs
  obtain ⟨hsP, hinv⟩ := (mem_sep_iff _ _ _).mp hs
  obtain ⟨a, b, haQ, hbQ, rfl, hpa, hab, hbq, hpay⟩ := hinv
  obtain ⟨hmQ, ham, hmb, hpm, hmq⟩ := ratMid_facts_on hp hq haQ hbQ hpa hab hbq
  rcases hstep a b haQ hbQ hpa hab hbq hpay with hleft | hright
  · have hinv' : halveInvOn p q P (opair a (ratMid a b)) :=
      ⟨a, ratMid a b, haQ, hmQ, rfl, hpa, ham, hmq, hleft⟩
    refine ⟨opair a (ratMid a b), (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod haQ hmQ, hinv'⟩, (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod hs ((mem_sep_iff _ _ _).mpr
        ⟨opair_mem_prod haQ hmQ, hinv'⟩), ?_⟩⟩
    exact ⟨a, b, haQ, hbQ, Or.inl ⟨rfl, hinv'⟩⟩
  · have hinv' : halveInvOn p q P (opair (ratMid a b) b) :=
      ⟨ratMid a b, b, hmQ, hbQ, rfl, hpm, hmb, hbq, hright⟩
    refine ⟨opair (ratMid a b) b, (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod hmQ hbQ, hinv'⟩, (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod hs ((mem_sep_iff _ _ _).mpr
        ⟨opair_mem_prod hmQ hbQ, hinv'⟩), ?_⟩⟩
    exact ⟨a, b, haQ, hbQ, Or.inr ⟨rfl, hinv'⟩⟩

/-- Both moves land in `Rat × Rat`, at an arbitrary ambient interval.
`halveLeft_mem_prod` is this at `p = 0`, `q = 1`; the ambient enters only
through `ratMid_facts_on`, so `hp` and `hq` appear here and not
there. -/
theorem halveLeft_mem_prod_on {p q : ZFSet.{u}} (hp : p ∈ Rat.{u})
    (hq : q ∈ Rat.{u}) {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveSOn p q P) : halveLeft s ∈ prod Rat.{u} Rat.{u} := by
  obtain ⟨-, a, b, haQ, hbQ, rfl, hpa, hab, hbq, -⟩ := (mem_sep_iff _ _ _).mp hs
  obtain ⟨hmQ, -, -, -, -⟩ := ratMid_facts_on hp hq haQ hbQ hpa hab hbq
  unfold halveLeft
  rw [fst_opair, snd_opair]
  exact opair_mem_prod haQ hmQ

theorem halveRight_mem_prod_on {p q : ZFSet.{u}} (hp : p ∈ Rat.{u})
    (hq : q ∈ Rat.{u}) {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveSOn p q P) : halveRight s ∈ prod Rat.{u} Rat.{u} := by
  obtain ⟨-, a, b, haQ, hbQ, rfl, hpa, hab, hbq, -⟩ := (mem_sep_iff _ _ _).mp hs
  obtain ⟨hmQ, -, -, -, -⟩ := ratMid_facts_on hp hq haQ hbQ hpa hab hbq
  unfold halveRight
  rw [fst_opair, snd_opair]
  exact opair_mem_prod hmQ hbQ

/-- A move's graph at an arbitrary ambient: `graphOn` at this state set.
`halveMove` is the same object at `p = 0`, `q = 1`. -/
def halveMoveOn (p q : ZFSet.{u}) (P : ZFSet.{u} → ZFSet.{u} → Prop)
    (f : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  graphOn (halveSOn p q P) (prod Rat.{u} Rat.{u}) f

theorem isFunction_halveMoveOn (p q : ZFSet.{u})
    (P : ZFSet.{u} → ZFSet.{u} → Prop) (f : ZFSet.{u} → ZFSet.{u}) :
    IsFunction (halveMoveOn p q P f) := graphOn_isFunction _ _ _

theorem domain_halveMoveOn {p q : ZFSet.{u}} {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ s, s ∈ halveSOn p q P → f s ∈ prod Rat.{u} Rat.{u}) :
    domain (halveMoveOn p q P f) = halveSOn p q P := graphOn_domain hf

/-- The move's value, from membership at the point.  `graphOn`'s own
`app_graphOn` asks for the codomain condition at every state; this asks for it
at `s` alone, which is all the graph's defining `sep` ever looks at. -/
theorem app_halveMoveOn {p q : ZFSet.{u}} {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {f : ZFSet.{u} → ZFSet.{u}} {s : ZFSet.{u}}
    (hf : f s ∈ prod Rat.{u} Rat.{u})
    (hs : s ∈ halveSOn p q P) : app (halveMoveOn p q P f) s = f s :=
  app_eq (isFunction_halveMoveOn p q P f)
    (show opair s (f s) ∈
        graphOn (halveSOn p q P) (prod Rat.{u} Rat.{u}) f from
      (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod hs hf, s, hs, rfl⟩)

/-- The halving step is binary with named successors, at an arbitrary
ambient.  `halve_binary` is this at `p = 0`, `q = 1`, and `halve_total_on`
is this with the witness hidden behind an existential.

The distinction is what `BinaryDCOn` records: a step that merely has a
successor needs `DC` to keep choosing one, while a step whose two successors
are named in advance needs only the choice between them. -/
theorem halve_binary_on {p q : ZFSet.{u}} (hp : p ∈ Rat.{u}) (hq : q ∈ Rat.{u})
    {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hstep : ∀ a b, a ∈ Rat.{u} → b ∈ Rat.{u} → ratLe p a →
      ratLt a b → ratLe b q → P a b →
      Or (P a (ratMid a b)) (P (ratMid a b) b)) :
    ∀ s, s ∈ halveSOn p q P →
      Or (And (halveLeft s ∈ halveSOn p q P)
            (opair s (halveLeft s) ∈ halveROn p q P))
         (And (halveRight s ∈ halveSOn p q P)
            (opair s (halveRight s) ∈ halveROn p q P)) := by
  intro s hs
  obtain ⟨hsP, hinv⟩ := (mem_sep_iff _ _ _).mp hs
  obtain ⟨a, b, haQ, hbQ, rfl, hpa, hab, hbq, hpay⟩ := hinv
  obtain ⟨hmQ, ham, hmb, hpm, hmq⟩ := ratMid_facts_on hp hq haQ hbQ hpa hab hbq
  have hL : halveLeft (opair a b) = opair a (ratMid a b) := by
    unfold halveLeft; rw [fst_opair, snd_opair]
  have hR : halveRight (opair a b) = opair (ratMid a b) b := by
    unfold halveRight; rw [fst_opair, snd_opair]
  rcases hstep a b haQ hbQ hpa hab hbq hpay with hleft | hright
  · have hinv' : halveInvOn p q P (opair a (ratMid a b)) :=
      ⟨a, ratMid a b, haQ, hmQ, rfl, hpa, ham, hmq, hleft⟩
    have hmem : opair a (ratMid a b) ∈ halveSOn p q P :=
      (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod haQ hmQ, hinv'⟩
    refine Or.inl ⟨hL ▸ hmem, hL ▸ (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod hs hmem, ?_⟩⟩
    exact ⟨a, b, haQ, hbQ, Or.inl ⟨rfl, hinv'⟩⟩
  · have hinv' : halveInvOn p q P (opair (ratMid a b) b) :=
      ⟨ratMid a b, b, hmQ, hbQ, rfl, hpm, hmb, hbq, hright⟩
    have hmem : opair (ratMid a b) b ∈ halveSOn p q P :=
      (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod hmQ hbQ, hinv'⟩
    refine Or.inr ⟨hR ▸ hmem, hR ▸ (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod hs hmem, ?_⟩⟩
    exact ⟨a, b, haQ, hbQ, Or.inr ⟨rfl, hinv'⟩⟩

/-- The state's endpoints are ordered, at an arbitrary ambient.  A
projection of `halveS_spec_on`'s fourth component; the ambient plays no part,
so this is general in `p q` without mentioning either. -/
theorem halveS_lt_on {p q : ZFSet.{u}} {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {s : ZFSet.{u}} (hs : s ∈ halveSOn p q P) : ratLt (fst s) (snd s) := by
  obtain ⟨-, -, -, h, -⟩ := halveS_spec_on hs
  exact h

/-- The state carries its payload, at an arbitrary ambient.  The sixth
component, and likewise ambient-free in its conclusion. -/
theorem halveS_payload_on {p q : ZFSet.{u}} {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {s : ZFSet.{u}} (hs : s ∈ halveSOn p q P) : P (fst s) (snd s) := by
  obtain ⟨-, -, -, -, -, h⟩ := halveS_spec_on hs
  exact h

/-- The generic invariant's upper bound, named.

`halveS_snd_le_q_on` at `p = 0`, `q = 1`. -/
theorem halveS_snd_le_one {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveS P) : ratLe (snd s) ratOne.{u} :=
  halveS_snd_le_q_on (p := ratZero.{u}) (q := ratOne.{u}) hs

/-! ### The chain lemmas, on the state set alone

The two families generalise along different axes and neither axis is what the
proofs read. The halving family is parameterised by an arbitrary ambient
`p, q` at the fixed ratio `2:1`; the split family is parameterised by an
arbitrary cut `lo, hi` at an arbitrary ratio `p:q` inside the unit ambient. So
neither is an instance of the other.

What every one of those proofs actually consumes is smaller than either axis:
a state set `S`, the two projections `fst s, snd s ∈ Rat` on it, and --- where a
step is needed at all --- a step law read at the chain's own entries. Nothing
below mentions `halveROn`, `splitR`, a ratio or a cut. `halveSOn p q P` and
`splitS P` are then just two values of `S`.

The generics are stated with a bare `S` rather than beside either family. -/

/-- A step-monotone rational sequence is monotone. The machine proves one
step at a time; `Topology.isNested_of_nat` asks across arbitrary `m ≤ n`, and
this is the induction between them. Stated over an arbitrary sequence so the
halving tower can use it too.
-/
theorem ratSeq_mono_of_step {K : Nat → ZFSet.{u}} (hK : ∀ n, K n ∈ Rat.{u})
    (hstep : ∀ n, ratLe (K n) (K (n + 1))) :
    ∀ m n : Nat, m ≤ n → ratLe (K m) (K n) := by
  intro m n hmn
  induction n with
  | zero =>
      have : m = 0 := Nat.le_zero.mp hmn
      subst this
      exact ratLe_refl (hK 0)
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact ratLe_trans (hK m) (hK k) (hK (k + 1))
          (ih (Nat.le_of_lt_succ hlt)) (hstep k)
      · have : m = k + 1 := Nat.le_antisymm hmn hge
        subst this
        exact ratLe_refl (hK (k + 1))

#print axioms ratSeq_mono_of_step

/-- And the decreasing mirror, for the upper endpoints. -/
theorem ratSeq_anti_of_step {L : Nat → ZFSet.{u}} (hL : ∀ n, L n ∈ Rat.{u})
    (hstep : ∀ n, ratLe (L (n + 1)) (L n)) :
    ∀ m n : Nat, m ≤ n → ratLe (L n) (L m) := by
  intro m n hmn
  induction n with
  | zero =>
      have : m = 0 := Nat.le_zero.mp hmn
      subst this
      exact ratLe_refl (hL 0)
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact ratLe_trans (hL (k + 1)) (hL k) (hL m)
          (hstep k) (ih (Nat.le_of_lt_succ hlt))
      · have : m = k + 1 := Nat.le_antisymm hmn hge
        subst this
        exact ratLe_refl (hL (k + 1))

#print axioms ratSeq_anti_of_step

/-- A step-scaled rational sequence is geometrically scaled. One step law
`w (n+1) * q = w n * p` iterates to `w n * q^n = w 0 * p^n`.

Stated over an arbitrary `w` rather than over a chain's width: nothing here
mentions a chain, a cut, a ratio or a predicate. `ratSeq_le_ratPow` is the
inequality at `w 0 = ratOne`; this is the equation at an arbitrary `w 0`, and
neither subsumes the other.
-/
theorem ratSeq_scaled_of_step {w : Nat → ZFSet.{u}} {p q : ZFSet.{u}}
    (hp : p ∈ Rat.{u}) (hq : q ∈ Rat.{u})
    (hw : ∀ n, w n ∈ Rat.{u})
    (hstep : ∀ n, ratMul (w (n + 1)) q = ratMul (w n) p) :
    ∀ n : Nat, ratMul (w n) (ratPow q n) = ratMul (w 0) (ratPow p n)
  | 0 => rfl
  | n + 1 => by
    have hind := ratSeq_scaled_of_step hp hq hw hstep n
    have hqn := ratPow_mem hq n
    have hpn := ratPow_mem hp n
    rw [ratPow_succ, ratPow_succ,
      ratMul_comm hqn hq, ← ratMul_assoc (hw (n + 1)) hq hqn, hstep n,
      ratMul_assoc (hw n) hp hqn, ratMul_comm hp hqn,
      ← ratMul_assoc (hw n) hqn hp, hind, ratMul_assoc (hw 0) hpn hp]

#print axioms ratSeq_scaled_of_step

/-- A chain stays in the state set, from `sep` out of `prod S S` alone.
The membership is carried by the second component of the product; the separating
predicate `Q` is never read, and neither is any order or width content. This is
`halve_chain_mem_on` and `split_chain_mem` at once. -/
theorem chain_mem_of_sep_prod {S g s₀ : ZFSet.{u}} {Q : ZFSet.{u} → Prop}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ sep Q (prod S S))
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ S) :
    ∀ n, n ∈ omega.{u} → app g n ∈ S := by
  refine omega_induction ?_ ?_
  · rw [h0]; exact hs₀
  · intro k hk _
    have hP := ((mem_sep_iff _ _ _).mp (hgR k hk)).left
    obtain ⟨x, hx, y, hy, heq⟩ := (mem_prod_iff _ _ _).mp hP
    obtain ⟨-, h2⟩ := opair_injective heq
    rw [h2]
    exact hy

#print axioms chain_mem_of_sep_prod

/-- The lower endpoint sequence is a rational sequence, given only that the
chain lands in `S` and that `S` has rational first coordinates. -/
theorem halveA_mem_ratSeqs_of_chain {S g : ZFSet.{u}}
    (hmem : ∀ n, n ∈ omega.{u} → app g n ∈ S)
    (hfst : ∀ s, s ∈ S → fst s ∈ Rat.{u}) :
    halveA g ∈ ratSeqs.{u} :=
  (mem_ratSeqs_iff _).mpr ⟨graphOn_subset _ _ _, graphOn_isFunction _ _ _,
    graphOn_domain (fun n hn => hfst _ (hmem n hn))⟩

#print axioms halveA_mem_ratSeqs_of_chain

/-- The `snd` twin of `halveA_mem_ratSeqs_of_chain`. -/
theorem halveB_mem_ratSeqs_of_chain {S g : ZFSet.{u}}
    (hmem : ∀ n, n ∈ omega.{u} → app g n ∈ S)
    (hsnd : ∀ s, s ∈ S → snd s ∈ Rat.{u}) :
    halveB g ∈ ratSeqs.{u} :=
  (mem_ratSeqs_iff _).mpr ⟨graphOn_subset _ _ _, graphOn_isFunction _ _ _,
    graphOn_domain (fun n hn => hsnd _ (hmem n hn))⟩

#print axioms halveB_mem_ratSeqs_of_chain

/-- Reading the lower sequence at an index. -/
theorem app_halveA_of_chain {S g n : ZFSet.{u}}
    (hmem : ∀ m, m ∈ omega.{u} → app g m ∈ S)
    (hfst : ∀ s, s ∈ S → fst s ∈ Rat.{u})
    (hn : n ∈ omega.{u}) : app (halveA g) n = fst (app g n) :=
  app_graphOn (fun m hm => hfst _ (hmem m hm)) hn

#print axioms app_halveA_of_chain

/-- The `snd` twin of `app_halveA_of_chain`. -/
theorem app_halveB_of_chain {S g n : ZFSet.{u}}
    (hmem : ∀ m, m ∈ omega.{u} → app g m ∈ S)
    (hsnd : ∀ s, s ∈ S → snd s ∈ Rat.{u})
    (hn : n ∈ omega.{u}) : app (halveB g) n = snd (app g n) :=
  app_graphOn (fun m hm => hsnd _ (hmem m hm)) hn

#print axioms app_halveB_of_chain

/-- The endpoints move inward, from a per-step order law alone. No ratio, no
cut, no width: the induction reads `hstep` and the two projections. This is
`halveChain_mono_on` and `splitChain_mono` at once. -/
theorem chain_mono_of_step {S g : ZFSet.{u}}
    (hmem : ∀ n, n ∈ omega.{u} → app g n ∈ S)
    (hfst : ∀ s, s ∈ S → fst s ∈ Rat.{u})
    (hsnd : ∀ s, s ∈ S → snd s ∈ Rat.{u})
    (hstep : ∀ n, n ∈ omega.{u} →
      And (ratLe (fst (app g n)) (fst (app g (succ n))))
        (ratLe (snd (app g (succ n))) (snd (app g n)))) :
    ∀ i j : Nat, i ≤ j →
      And (ratLe (app (halveA g) (ofNat.{u} i))
          (app (halveA g) (ofNat.{u} j)))
        (ratLe (app (halveB g) (ofNat.{u} j))
          (app (halveB g) (ofNat.{u} i))) := by
  have hAQ : ∀ n : Nat, app (halveA g) (ofNat.{u} n) ∈ Rat.{u} :=
    fun n => by
      rw [app_halveA_of_chain hmem hfst (ofNat_mem_omega n)]
      exact hfst _ (hmem _ (ofNat_mem_omega n))
  have hBQ : ∀ n : Nat, app (halveB g) (ofNat.{u} n) ∈ Rat.{u} :=
    fun n => by
      rw [app_halveB_of_chain hmem hsnd (ofNat_mem_omega n)]
      exact hsnd _ (hmem _ (ofNat_mem_omega n))
  exact fun i j hij =>
    ⟨ratSeq_mono_of_step hAQ (fun n => by
        rw [app_halveA_of_chain hmem hfst (ofNat_mem_omega n),
          app_halveA_of_chain hmem hfst (ofNat_mem_omega (n + 1))]
        exact (hstep (ofNat.{u} n) (ofNat_mem_omega n)).left) i j hij,
      ratSeq_anti_of_step hBQ (fun n => by
        rw [app_halveB_of_chain hmem hsnd (ofNat_mem_omega n),
          app_halveB_of_chain hmem hsnd (ofNat_mem_omega (n + 1))]
        exact (hstep (ofNat.{u} n) (ofNat_mem_omega n)).right) i j hij⟩

#print axioms chain_mono_of_step

/-- The width scales geometrically, from a per-step width law alone.

`splitChain_width_scaled` carries an arbitrary `p:q` and concludes in `ratPow`;
`halveChain_width_scaled_on` is fixed at `2:1` and concludes
`w n * ratNat (pow2 n) 1 = w 0`. Neither induction reads the ratio, only the
step law; the halve side reaches its own shape through `ratPow_ratTwo` below.
The induction itself is `ratSeq_scaled_of_step` above; this adds the rewrite
from the chain's two projections to that sequence. -/
theorem chain_width_scaled_of_step {S g p q : ZFSet.{u}}
    (hp : p ∈ Rat.{u}) (hq : q ∈ Rat.{u})
    (hmem : ∀ n, n ∈ omega.{u} → app g n ∈ S)
    (hfst : ∀ s, s ∈ S → fst s ∈ Rat.{u})
    (hsnd : ∀ s, s ∈ S → snd s ∈ Rat.{u})
    (hstep : ∀ n, n ∈ omega.{u} →
      ratMul (ratAdd (snd (app g (succ n))) (ratNeg (fst (app g (succ n))))) q
        = ratMul (ratAdd (snd (app g n)) (ratNeg (fst (app g n)))) p) :
    ∀ n : Nat,
      ratMul (ratAdd (app (halveB g) (ofNat.{u} n))
        (ratNeg (app (halveA g) (ofNat.{u} n)))) (ratPow q n)
      = ratMul (ratAdd (app (halveB g) (ofNat.{u} 0))
        (ratNeg (app (halveA g) (ofNat.{u} 0)))) (ratPow p n) := by
  have hrw : ∀ n : Nat,
      ratAdd (app (halveB g) (ofNat.{u} n))
        (ratNeg (app (halveA g) (ofNat.{u} n)))
      = ratAdd (snd (app g (ofNat.{u} n)))
        (ratNeg (fst (app g (ofNat.{u} n)))) := fun n => by
    rw [app_halveA_of_chain hmem hfst (ofNat_mem_omega n),
      app_halveB_of_chain hmem hsnd (ofNat_mem_omega n)]
  exact ratSeq_scaled_of_step hp hq
    (fun n => by
      rw [hrw n]
      exact ratAdd_mem_Rat (hsnd _ (hmem _ (ofNat_mem_omega n)))
        (ratNeg_mem_Rat (hfst _ (hmem _ (ofNat_mem_omega n)))))
    (fun n => by
      rw [hrw n, hrw (n + 1)]
      exact hstep (ofNat.{u} n) (ofNat_mem_omega n))

#print axioms chain_width_scaled_of_step

/-- `pow2` is `2 ^ ·`. Stated because `pow2` is built by iteration and the
`ratPow` bridge below needs the numeral form. -/
theorem pow2_eq_two_pow : ∀ n : Nat, pow2 n = 2 ^ n
  | 0 => rfl
  | n + 1 => by rw [pow2, pow2_eq_two_pow n, Nat.pow_succ]; omega

#print axioms pow2_eq_two_pow

/-- `ratPow ratTwo n = ratNat (pow2 n) 1`, the bridge that lets the halving
width lemma reach its own statement shape from `chain_width_scaled_of_step`.

`ratTwo` is `ratAdd ratOne ratOne`, not `ratNat 2 1`, so the two spellings of
two need `ratTwo_as_ratNat` to meet. -/
theorem ratPow_ratTwo (n : Nat) :
    ratPow ratTwo.{u} n = ratNat.{u} (pow2 n) 1 := by
  rw [pow2_eq_two_pow, Constructive.ratTwo_as_ratNat, ratPow_ratNat]

#print axioms ratPow_ratTwo

/-! ### The endpoint sequences

`halveA` and `halveB` are `graphOn omega Rat (fun n => fst (app g n))` and its
`snd` twin, functions of the chain alone. The step relation enters only through
the hypotheses of the lemmas below, to establish `app g n ∈ halveS P`, which
`split_chain_mem` supplies for a split chain as `halve_chain_mem` does for a
halving one.
-/

/-- What one step of the machine does, at an arbitrary ambient: the left
endpoint rises, the right falls, and the width halves.  `halveR_step` is this
at `p = 0`, `q = 1`; the ambient enters only through `halveS_spec_on`, and only
to know `a < b`. -/
theorem halveR_step_on {p q : ZFSet.{u}} {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {s s' : ZFSet.{u}} (h : opair s s' ∈ halveROn p q P) :
    And (ratLe (fst s) (fst s')) (And (ratLe (snd s') (snd s))
      (ratMul (ratAdd (snd s') (ratNeg (fst s'))) ratTwo.{u}
        = ratAdd (snd s) (ratNeg (fst s)))) := by
  obtain ⟨hP, a, b, haQ, hbQ, hor⟩ := (mem_sep_iff _ _ _).mp h
  obtain ⟨x, hx, y, hy, heq2⟩ := (mem_prod_iff _ _ _).mp hP
  obtain ⟨rfl, rfl⟩ := opair_injective heq2
  have hab : ratLt a b := by
    rcases hor with ⟨heq, -⟩ | ⟨heq, -⟩ <;>
      · obtain ⟨h1, -⟩ := opair_injective heq
        have hspec := (halveS_spec_on hx).right.right.right.left
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

/-- Every state the chain reaches is a state, at an arbitrary ambient.
`halve_chain_mem` is this at `p = 0`, `q = 1`; the proof never looks at the
ambient, reading membership out of `halveROn`'s product instead. -/
theorem halve_chain_mem_on {p q : ZFSet.{u}}
    {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveROn p q P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveSOn p q P) :
    ∀ n, n ∈ omega.{u} → app g n ∈ halveSOn p q P :=
  chain_mem_of_sep_prod hgR h0 hs₀

/-- The left-endpoint sequence reads off `fst`, at an arbitrary ambient. -/
theorem app_halveA_on {p q : ZFSet.{u}} {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {g s₀ n : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveROn p q P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveSOn p q P)
    (hn : n ∈ omega.{u}) : app (halveA g) n = fst (app g n) :=
  app_halveA_of_chain (halve_chain_mem_on hgR h0 hs₀)
    (fun _ hs => (halveS_spec_on hs).left) hn

/-- The right-endpoint sequence reads off `snd`, at an arbitrary ambient. -/
theorem app_halveB_on {p q : ZFSet.{u}} {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {g s₀ n : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveROn p q P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveSOn p q P)
    (hn : n ∈ omega.{u}) : app (halveB g) n = snd (app g n) :=
  app_halveB_of_chain (halve_chain_mem_on hgR h0 hs₀)
    (fun _ hs => (halveS_spec_on hs).right.left) hn

/-- The left-endpoint sequence is a rational sequence, at an arbitrary
ambient.  A pure citation, as its unit-interval original is. -/
theorem halveA_mem_ratSeqs_on {p q : ZFSet.{u}}
    {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveROn p q P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveSOn p q P) :
    halveA g ∈ ratSeqs.{u} :=
  halveA_mem_ratSeqs_of_chain (halve_chain_mem_on hgR h0 hs₀)
    (fun _ hs => (halveS_spec_on hs).left)

/-- The right-endpoint sequence is a rational sequence, at an arbitrary
ambient. -/
theorem halveB_mem_ratSeqs_on {p q : ZFSet.{u}}
    {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveROn p q P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveSOn p q P) :
    halveB g ∈ ratSeqs.{u} :=
  halveB_mem_ratSeqs_of_chain (halve_chain_mem_on hgR h0 hs₀)
    (fun _ hs => (halveS_spec_on hs).right.left)

/-- The width halves exactly, at an arbitrary ambient: `width n * 2^n` is
the initial width. Its unit-interval sibling `halveChain_width_le` asserts the
initial width is at most 1, a fact about `[0,1]` that becomes `q - p` here. -/
theorem halveChain_width_scaled_on {p q : ZFSet.{u}}
    {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveROn p q P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveSOn p q P) :
    ∀ n : Nat, ratMul (ratAdd (app (halveB g) (ofNat.{u} n))
      (ratNeg (app (halveA g) (ofNat.{u} n)))) (ratNat.{u} (pow2 n) 1)
      = ratAdd (app (halveB g) (ofNat.{u} 0))
        (ratNeg (app (halveA g) (ofNat.{u} 0))) := by
  have hmem := halve_chain_mem_on hgR h0 hs₀
  have hfst : ∀ s, s ∈ halveSOn p q P → fst s ∈ Rat.{u} :=
    fun _ hs => (halveS_spec_on hs).left
  have hsnd : ∀ s, s ∈ halveSOn p q P → snd s ∈ Rat.{u} :=
    fun _ hs => (halveS_spec_on hs).right.left
  have hgen := chain_width_scaled_of_step ratOne_mem_Rat ratTwo_mem_Rat
    hmem hfst hsnd
    (fun m hm => by
      have hw : ratAdd (snd (app g m)) (ratNeg (fst (app g m))) ∈ Rat.{u} :=
        ratAdd_mem_Rat (hsnd _ (hmem m hm))
          (ratNeg_mem_Rat (hfst _ (hmem m hm)))
      rw [ratMul_one hw]
      exact (halveR_step_on (hgR m hm)).right.right)
  intro n
  have h := hgen n
  rw [ratPow_ratTwo, ratPow_ratOne] at h
  have hw0 : ratAdd (app (halveB g) (ofNat.{u} 0))
      (ratNeg (app (halveA g) (ofNat.{u} 0))) ∈ Rat.{u} := by
    rw [app_halveA_on hgR h0 hs₀ (ofNat_mem_omega 0),
      app_halveB_on hgR h0 hs₀ (ofNat_mem_omega 0)]
    exact ratAdd_mem_Rat (hsnd _ (hmem _ (ofNat_mem_omega 0)))
      (ratNeg_mem_Rat (hfst _ (hmem _ (ofNat_mem_omega 0))))
  rwa [ratMul_one hw0] at h

/-- The chain's endpoints move monotonically, at an arbitrary ambient.
`halveChain_mono` is this at `p = 0`, `q = 1`.

The proof reaches the ambient only through `halveS_spec_on`, `app_halveA_on`,
`app_halveB_on` and `halveR_step_on`. -/
theorem halveChain_mono_on {p q : ZFSet.{u}}
    {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveROn p q P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveSOn p q P) :
    ∀ i j : Nat, i ≤ j →
      And (ratLe (app (halveA g) (ofNat.{u} i))
          (app (halveA g) (ofNat.{u} j)))
        (ratLe (app (halveB g) (ofNat.{u} j))
          (app (halveB g) (ofNat.{u} i))) :=
  chain_mono_of_step (halve_chain_mem_on hgR h0 hs₀)
    (fun _ hs => (halveS_spec_on hs).left)
    (fun _ hs => (halveS_spec_on hs).right.left)
    (fun m hm =>
      ⟨(halveR_step_on (hgR m hm)).left,
        (halveR_step_on (hgR m hm)).right.left⟩)

/-- The width shrinks, at an arbitrary ambient: `width n` is at most
`(q - p) * invWidth n`.

`halveChain_width_le` is this at `p = 0`, `q = 1`, where `q - p` is 1 and
disappears. -/
theorem halveChain_width_le_on {p q : ZFSet.{u}}
    (hp : p ∈ Rat.{u}) (hq : q ∈ Rat.{u})
    {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveROn p q P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveSOn p q P)
    (n : Nat) :
    ratLe (ratAdd (app (halveB g) (ofNat.{u} n))
      (ratNeg (app (halveA g) (ofNat.{u} n))))
      (ratMul (ratAdd q (ratNeg p)) (invWidth (ofNat.{u} n))) := by
  have hspec0 := halveS_spec_on (halve_chain_mem_on hgR h0 hs₀ _
    (ofNat_mem_omega 0))
  have hspecn := halveS_spec_on (halve_chain_mem_on hgR h0 hs₀ _
    (ofNat_mem_omega n))
  have hAn := app_halveA_on hgR h0 hs₀ (ofNat_mem_omega n)
  have hBn := app_halveB_on hgR h0 hs₀ (ofNat_mem_omega n)
  have hA0 := app_halveA_on hgR h0 hs₀ (ofNat_mem_omega 0)
  have hB0 := app_halveB_on hgR h0 hs₀ (ofNat_mem_omega 0)
  have hWQ : ratAdd q (ratNeg p) ∈ Rat.{u} :=
    ratAdd_mem_Rat hq (ratNeg_mem_Rat hp)
  have hWnQ : ratAdd (app (halveB g) (ofNat.{u} n))
      (ratNeg (app (halveA g) (ofNat.{u} n))) ∈ Rat.{u} := by
    rw [hAn, hBn]
    exact ratAdd_mem_Rat hspecn.right.left (ratNeg_mem_Rat hspecn.left)
  have hWn0 : ratLe ratZero.{u} (ratAdd (app (halveB g) (ofNat.{u} n))
      (ratNeg (app (halveA g) (ofNat.{u} n)))) := by
    rw [hAn, hBn]
    exact (ratSub_pos hspecn.left hspecn.right.left
      (halveS_lt_on (halve_chain_mem_on hgR h0 hs₀ _ (ofNat_mem_omega n)))).left
  -- `w0 <= q - p`: the interval sits inside `[p, q]`
  have hW0leW : ratLe (ratAdd (app (halveB g) (ofNat.{u} 0))
      (ratNeg (app (halveA g) (ofNat.{u} 0)))) (ratAdd q (ratNeg p)) := by
    rw [hA0, hB0]
    exact ratAdd_le_add hspec0.right.left hq
      (ratNeg_mem_Rat hspec0.left) (ratNeg_mem_Rat hp)
      (halveS_snd_le_q_on (halve_chain_mem_on hgR h0 hs₀ _
        (ofNat_mem_omega 0)))
      ((ratNeg_le_neg_iff hspec0.left hp).mpr hspec0.right.right.left)
  have hmul_le : ratLe (ratMul (ratAdd (app (halveB g) (ofNat.{u} n))
      (ratNeg (app (halveA g) (ofNat.{u} n)))) (ratNat.{u} (n + 1) 1))
      (ratAdd q (ratNeg p)) := by
    have hmono := ratMul_le_mul_right (ratNat_mem_Rat Nat.one_pos)
      (ratNat_mem_Rat Nat.one_pos) hWnQ (ratNat_succ_le_pow2 n) hWn0
    rw [ratMul_comm (ratNat_mem_Rat Nat.one_pos) hWnQ,
      ratMul_comm (ratNat_mem_Rat Nat.one_pos) hWnQ] at hmono
    rw [halveChain_width_scaled_on hgR h0 hs₀ n] at hmono
    exact ratLe_trans (ratMul_mem_Rat hWnQ (ratNat_mem_Rat Nat.one_pos))
      (ratAdd_mem_Rat (by rw [hB0]; exact hspec0.right.left)
        (ratNeg_mem_Rat (by rw [hA0]; exact hspec0.left)))
      hWQ hmono hW0leW
  have hinvQ := invWidth_mem_Rat (ofNat_mem_omega.{u} n)
  have hinv0 := (invWidth_pos (ofNat_mem_omega.{u} n)).left
  have hfin := ratMul_le_mul_right
    (ratMul_mem_Rat hWnQ (ratNat_mem_Rat Nat.one_pos))
    hWQ hinvQ hmul_le hinv0
  rw [ratMul_assoc hWnQ (ratNat_mem_Rat Nat.one_pos) hinvQ,
    succ_mul_invWidth, ratMul_one hWnQ] at hfin
  exact hfin

/-- The halving chain is a nested family, at an arbitrary ambient.
`halveChain_isNested` is this at `p = 0`, `q = 1`.

The only field that changes is `shrink`: the width bound carries a factor
`q - p`, so it needs `shrink_of_scaled_invWidth` rather than the unscaled form.
Everything else is the original with `halveSOn`/`halveROn` in place of the
unit-interval sets. -/
theorem halveChain_isNested_on {p q : ZFSet.{u}}
    (hp : p ∈ Rat.{u}) (hq : q ∈ Rat.{u})
    {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveROn p q P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveSOn p q P) :
    IsNested (halveA g) (halveB g) where
  lower_seq := halveA_mem_ratSeqs_on hgR h0 hs₀
  upper_seq := halveB_mem_ratSeqs_on hgR h0 hs₀
  lower_mono := by
    intro m hm n hn hsub
    obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
    obtain ⟨j, rfl⟩ := (mem_omega_iff n).mp hn
    exact (halveChain_mono_on hgR h0 hs₀ i j
      ((ofNat_subset_iff i j).mp hsub)).left
  upper_mono := by
    intro m hm n hn hsub
    obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
    obtain ⟨j, rfl⟩ := (mem_omega_iff n).mp hn
    exact (halveChain_mono_on hgR h0 hs₀ i j
      ((ofNat_subset_iff i j).mp hsub)).right
  bracket := by
    intro n hn
    obtain ⟨i, rfl⟩ := (mem_omega_iff n).mp hn
    have h := halveS_lt_on (halve_chain_mem_on hgR h0 hs₀ _ (ofNat_mem_omega i))
    rwa [← app_halveA_on hgR h0 hs₀ (ofNat_mem_omega i),
      ← app_halveB_on hgR h0 hs₀ (ofNat_mem_omega i)] at h
  shrink := fun ε hεQ hε0 =>
    -- `0 < q - p` is derived from the seed state: `p <= a0`, `a0 < b0` and
    -- `b0 <= q` give `p < q`.
    have hspec0 := halveS_spec_on hs₀
    have hpq : ratLt p q :=
      ratLt_of_le_of_lt hp hspec0.left hq hspec0.right.right.left
        (ratLt_of_lt_of_le hspec0.left hspec0.right.left hq
          (halveS_lt_on hs₀) (halveS_snd_le_q_on hs₀))
    shrink_of_scaled_invWidth (halveA_mem_ratSeqs_on hgR h0 hs₀)
      (halveB_mem_ratSeqs_on hgR h0 hs₀)
      (ratAdd_mem_Rat hq (ratNeg_mem_Rat hp)) (ratSub_pos hp hq hpq)
      (fun n hn => by
        obtain ⟨i, rfl⟩ := (mem_omega_iff n).mp hn
        exact halveChain_width_le_on hp hq hgR h0 hs₀ i) ε hεQ hε0

theorem isFunction_halveMove (P : ZFSet.{u} → ZFSet.{u} → Prop)
    (f : ZFSet.{u} → ZFSet.{u}) : IsFunction (halveMove P f) :=
  isFunction_halveMoveOn ratZero.{u} ratOne.{u} P f

theorem app_halveMove {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {f : ZFSet.{u} → ZFSet.{u}} {s : ZFSet.{u}} (hs : s ∈ halveS P)
    (hf : f s ∈ prod Rat.{u} Rat.{u}) :
    app (halveMove P f) s = f s :=
  app_halveMoveOn (p := ratZero.{u}) (q := ratOne.{u}) hf hs

theorem domain_halveMove {P : ZFSet.{u} → ZFSet.{u} → Prop}
    {f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ s, s ∈ halveS P → f s ∈ prod Rat.{u} Rat.{u}) :
    domain (halveMove P f) = halveS P :=
  domain_halveMoveOn (p := ratZero.{u}) (q := ratOne.{u}) hf

/-- Both moves land in `Rat × Rat`, so they can be graphed. -/
theorem halveLeft_mem_prod {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveS P) : halveLeft s ∈ prod Rat.{u} Rat.{u} :=
  halveLeft_mem_prod_on ratZero_mem_Rat ratOne_mem_Rat hs

theorem halveRight_mem_prod {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveS P) : halveRight s ∈ prod Rat.{u} Rat.{u} :=
  halveRight_mem_prod_on ratZero_mem_Rat ratOne_mem_Rat hs

/-- The halving step is binary with named successors, which is `halve_total`
stated without the existential. The proof is that one, with the witness read off
rather than produced. -/
theorem halve_binary {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hstep : ∀ a b, a ∈ Rat.{u} → b ∈ Rat.{u} → ratLe ratZero.{u} a →
      ratLt a b → ratLe b ratOne.{u} → P a b →
      Or (P a (ratMid a b)) (P (ratMid a b) b)) :
    ∀ s, s ∈ halveS P →
      Or (And (halveLeft s ∈ halveS P) (opair s (halveLeft s) ∈ halveR P))
         (And (halveRight s ∈ halveS P) (opair s (halveRight s) ∈ halveR P)) :=
  halve_binary_on ratZero_mem_Rat ratOne_mem_Rat hstep

/-- The chain `DC` produces for the halving machine never leaves the state
set: each step's membership in the relation pins its target. -/
theorem halve_chain_mem {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P) :
    ∀ n, n ∈ omega.{u} → app g n ∈ halveS P :=
  halve_chain_mem_on (p := ratZero.{u}) (q := ratOne.{u}) hgR h0 hs₀

/-- The generic invariant's payload, named. -/
theorem halveS_payload {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveS P) : P (fst s) (snd s) :=
  halveS_payload_on (p := ratZero.{u}) (q := ratOne.{u}) hs

theorem halveA_mem_ratSeqs {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P) :
    halveA g ∈ ratSeqs.{u} :=
  halveA_mem_ratSeqs_on (p := ratZero.{u}) (q := ratOne.{u}) hgR h0 hs₀

theorem halveB_mem_ratSeqs {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P) :
    halveB g ∈ ratSeqs.{u} :=
  halveB_mem_ratSeqs_on (p := ratZero.{u}) (q := ratOne.{u}) hgR h0 hs₀

theorem app_halveA {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ n : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P)
    (hn : n ∈ omega.{u}) : app (halveA g) n = fst (app g n) :=
  app_halveA_on (p := ratZero.{u}) (q := ratOne.{u}) hgR h0 hs₀ hn

theorem app_halveB {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ n : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P)
    (hn : n ∈ omega.{u}) : app (halveB g) n = snd (app g n) :=
  app_halveB_on (p := ratZero.{u}) (q := ratOne.{u}) hgR h0 hs₀ hn

/-- The generic invariant's strict inequality, named. -/
theorem halveS_lt {P : ZFSet.{u} → ZFSet.{u} → Prop} {s : ZFSet.{u}}
    (hs : s ∈ halveS P) : ratLt (fst s) (snd s) :=
  halveS_lt_on (p := ratZero.{u}) (q := ratOne.{u}) hs

theorem halveR_step {P : ZFSet.{u} → ZFSet.{u} → Prop} {s s' : ZFSet.{u}}
    (h : opair s s' ∈ halveR P) :
    And (ratLe (fst s) (fst s')) (And (ratLe (snd s') (snd s))
      (ratMul (ratAdd (snd s') (ratNeg (fst s'))) ratTwo.{u}
        = ratAdd (snd s) (ratNeg (fst s)))) :=
  halveR_step_on (p := ratZero.{u}) (q := ratOne.{u}) h

/-- Totality of the generic halving step: a payload that survives into
one half at every strict subinterval keeps the machine running. -/
theorem halve_total {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hstep : ∀ a b, a ∈ Rat.{u} → b ∈ Rat.{u} → ratLe ratZero.{u} a →
      ratLt a b → ratLe b ratOne.{u} → P a b →
      Or (P a (ratMid a b)) (P (ratMid a b) b)) :
    ∀ s, s ∈ halveS P → ∃ s', s' ∈ halveS P ∧ opair s s' ∈ halveR P :=
  halve_total_on ratZero_mem_Rat ratOne_mem_Rat hstep

/-- Along the chain, left endpoints rise and right endpoints fall. -/
theorem halveChain_mono {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P) :
    ∀ i j : Nat, i ≤ j →
      And (ratLe (app (halveA g) (ofNat.{u} i))
          (app (halveA g) (ofNat.{u} j)))
        (ratLe (app (halveB g) (ofNat.{u} j))
          (app (halveB g) (ofNat.{u} i))) :=
  halveChain_mono_on (p := ratZero.{u}) (q := ratOne.{u}) hgR h0 hs₀

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
        (ratNeg (app (halveA g) (ofNat.{u} 0))) :=
  halveChain_width_scaled_on (p := ratZero.{u}) (q := ratOne.{u}) hgR h0 hs₀

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
  have h := halveChain_width_le_on ratZero_mem_Rat ratOne_mem_Rat hgR h0 hs₀ n
  rwa [ratNeg_zero, ratAdd_zero ratOne_mem_Rat,
    ratOne_mul (invWidth_mem_Rat (ofNat_mem_omega n))] at h

/-- The chain's endpoints are a nested family: everything the bundle
asks for is already on the shelf.

`halveChain_isNested_on` above at `p = 0`, `q = 1`: the only field that differs
is `shrink`, which carries the factor `q - p`, and at `q - p = 1` the scaled
bound is the unscaled one. -/
theorem halveChain_isNested {P : ZFSet.{u} → ZFSet.{u} → Prop} {g s₀ : ZFSet.{u}}
    (hgR : ∀ n, n ∈ omega.{u} →
      opair (app g n) (app g (succ n)) ∈ halveR P)
    (h0 : app g empty.{u} = s₀) (hs₀ : s₀ ∈ halveS P) :
    IsNested (halveA g) (halveB g) :=
  halveChain_isNested_on ratZero_mem_Rat ratOne_mem_Rat hgR h0 hs₀

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
/-- The machine's limit from the instance, which is all the proof above
actually uses.

`halve_limit_of_binaryDCOn` takes the quantified `BinaryDCOn` and applies it once,
at `halveS P` and `halveR P`. This is the same proof with the carrier fixed, so
the hypothesis is a statement about coded rational intervals rather than about
every set.

Why that is worth a separate theorem. Seven registry rows spend
`SignDisjunction + BinaryDCOn` and their reversal is blocked on
`<landmark> -> BinaryDCOn` --- a chain in an arbitrary `S`, `powerset RealL`
included, from landmarks that conclude only about `RealL`. At the instance that
objection is gone: `halveS P` is pairs of rationals, which is the landmarks' own
subject. The blocked target shrinks even if it does not open.

ADDITIVE: `halve_limit_of_binaryDCOn` keeps its signature and its seventeen
consumers are untouched; `binaryDCOnAt_of_binaryDCOn` bridges the two whenever
the quantified form is what a caller holds. -/
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

/-- One step, conditioned on the proposition rather than on a `Bool`. -/
def halveStepD {P : ZFSet.{u} → ZFSet.{u} → Prop} (δ : HalveDecider P)
    (s : ZFSet.{u}) : ZFSet.{u} :=
  condP (δ.goLeft s) (opair (fst s) (ratMid (fst s) (snd s)))
    (opair (ratMid (fst s) (snd s)) (snd s))

theorem halveStepD_mem {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (δ : HalveDecider P) {s : ZFSet.{u}} (hs : s ∈ halveS P) :
    halveStepD δ s ∈ halveS P := by
  obtain ⟨-, a, b, haQ, hbQ, rfl, h0a, hab, hb1, hPab⟩ :=
    (mem_sep_iff _ _ _).mp hs
  obtain ⟨hmQ, ham, hmb, h0m, hm1⟩ := ratMid_facts haQ hbQ h0a hab hb1
  rw [halveStepD, fst_opair, snd_opair]
  rcases δ.decided a b haQ hbQ with hgo | hgo
  · rw [condP_pos hgo]
    exact (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod haQ hmQ,
      a, ratMid a b, haQ, hmQ, rfl, h0a, ham, hm1,
      δ.keepsL a b haQ hbQ h0a hab hb1 hPab hgo⟩
  · rw [condP_neg hgo]
    exact (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod hmQ hbQ,
      ratMid a b, b, hmQ, hbQ, rfl, h0m, hmb, hb1,
      δ.keepsR a b haQ hbQ h0a hab hb1 hPab hgo⟩

theorem halveStepD_rel {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (δ : HalveDecider P) {s : ZFSet.{u}} (hs : s ∈ halveS P) :
    opair s (halveStepD δ s) ∈ halveR P := by
  have hnext := halveStepD_mem δ hs
  obtain ⟨-, a, b, haQ, hbQ, rfl, h0a, hab, hb1, hPab⟩ :=
    (mem_sep_iff _ _ _).mp hs
  refine (mem_sep_iff _ _ _).mpr ⟨opair_mem_prod hs hnext, a, b, haQ, hbQ, ?_⟩
  rw [halveStepD, fst_opair, snd_opair] at hnext ⊢
  rcases δ.decided a b haQ hbQ with hgo | hgo
  · rw [condP_pos hgo] at hnext ⊢
    exact Or.inl ⟨rfl, ((mem_sep_iff _ _ _).mp hnext).right⟩
  · rw [condP_neg hgo] at hnext ⊢
    exact Or.inr ⟨rfl, ((mem_sep_iff _ _ _).mp hnext).right⟩

def halveIterD {P : ZFSet.{u} → ZFSet.{u} → Prop} (δ : HalveDecider P) :
    Nat → ZFSet.{u}
  | 0 => opair ratZero.{u} ratOne.{u}
  | n + 1 => halveStepD δ (halveIterD δ n)

theorem halveIterD_mem {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (δ : HalveDecider P) (hP01 : P ratZero.{u} ratOne.{u}) :
    ∀ n, halveIterD δ n ∈ halveS P
  | 0 => (mem_sep_iff _ _ _).mpr
      ⟨opair_mem_prod ratZero_mem_Rat ratOne_mem_Rat,
        ratZero.{u}, ratOne.{u}, ratZero_mem_Rat, ratOne_mem_Rat, rfl,
        ratLe_refl ratZero_mem_Rat, ratZero_lt_one,
        ratLe_refl ratOne_mem_Rat, hP01⟩
  | n + 1 => halveStepD_mem δ (halveIterD_mem δ hP01 n)

/-- The machine's limit, from a decider. As `halve_limit_of_selector`,
except that what is supplied is a proposition decided on rational endpoints
rather than a `Bool` -- which is the form an instantiation can actually
produce. -/
theorem halve_limit_of_decider {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (δ : HalveDecider P) (hP01 : P ratZero.{u} ratOne.{u}) :
    HasHalveLimit P := by
  have hmem := halveIterD_mem δ hP01
  have hg0 : app (natSeq (halveS P) (halveIterD δ)) empty.{u}
      = opair ratZero.{u} ratOne.{u} := app_natSeq hmem 0
  have hs₀S : opair ratZero.{u} ratOne.{u} ∈ halveS P := hmem 0
  have hgstep : ∀ n, n ∈ omega.{u} →
      opair (app (natSeq (halveS P) (halveIterD δ)) n)
        (app (natSeq (halveS P) (halveIterD δ)) (succ n)) ∈ halveR P := by
    intro n hn
    obtain ⟨k, rfl⟩ := (mem_omega_iff n).mp hn
    rw [app_natSeq hmem k, ← ofNat_succ, app_natSeq hmem (k + 1)]
    exact halveStepD_rel δ (hmem k)
  exact halve_limit_core hgstep hg0 hs₀S

/-- A `Bool` selector is a decider. -/
def HalveSelector.toDecider {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (σ : HalveSelector P) : HalveDecider P where
  goLeft s := σ.bit s = true
  decided a b _ _ := by
    cases h : σ.bit (opair a b) with
    | true => exact Or.inl rfl
    | false => exact Or.inr (fun hc => Bool.noConfusion hc)
  keepsL a b haQ hbQ h0a hab hb1 hPab hgo := by
    have hk := σ.keeps a b haQ hbQ h0a hab hb1 hPab
    rw [hgo] at hk
    simpa using hk
  keepsR a b haQ hbQ h0a hab hb1 hPab hgo := by
    have hk := σ.keeps a b haQ hbQ h0a hab hb1 hPab
    have : σ.bit (opair a b) = false := by
      cases h : σ.bit (opair a b) with
      | true => exact absurd h hgo
      | false => rfl
    rw [this] at hk
    simpa using hk

/-- The machine's limit, from a selector. Identical to `halve_limit`
except that the chain is recursion rather than choice: `DC` does not
appear, and what replaces it is a `Bool` per node with its promise.

Proved through `HalveSelector.toDecider` rather than by repeating
`halve_limit_of_decider`'s walk.

The chains are not definitionally equal --- `halveIter σ = halveIterD
σ.toDecider` fails by `rfl`, and so does the `halveStep` pair --- so the rest of
the family collapses at a price rather than not at all. Propositional equality
is what the transfers consume, and it is proved just below: `bridgeStep` and
`bridgeIter` cost two lemmas, and past them the three invariants transfer in a
line each. -/
theorem halve_limit_of_selector {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (σ : HalveSelector P) (hP01 : P ratZero.{u} ratOne.{u}) :
    HasHalveLimit P :=
  halve_limit_of_decider σ.toDecider hP01

/-! ### The selector's walk

`halveStep` and `halveIter` are the concrete `Bool`-branching walk the section
above motivates; their invariants are read off the decider's through
`bridgeStep` and `bridgeIter`.
-/

/-- One step of the walk, as a function on coded intervals. -/
def halveStep {P : ZFSet.{u} → ZFSet.{u} → Prop} (σ : HalveSelector P)
    (s : ZFSet.{u}) : ZFSet.{u} :=
  if σ.bit s then opair (fst s) (ratMid (fst s) (snd s))
  else opair (ratMid (fst s) (snd s)) (snd s)

/-- The `Bool` step and the induced decider's `condP` step agree.

Not `rfl`: `if` eliminates a `Bool` and `condP` separates on a `Prop`, so the
two have different normal forms and only a case split identifies them. -/
theorem bridgeStep {P : ZFSet.{u} → ZFSet.{u} → Prop} (σ : HalveSelector P)
    (s : ZFSet.{u}) : halveStep σ s = halveStepD σ.toDecider s := by
  rw [halveStep, halveStepD]
  simp only [HalveSelector.toDecider]
  cases h : σ.bit s with
  | true => rw [condP_pos (rfl : (true : Bool) = true)]; simp
  | false => rw [condP_neg (by simp : ¬ ((false : Bool) = true))]; simp

/-- The step stays in the state set. The selector's promise is what proves it,
but `toDecider` has already spent that promise, so this reads it back off the
decider's own invariant rather than repeating the case split. -/
theorem halveStep_mem {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (σ : HalveSelector P) {s : ZFSet.{u}} (hs : s ∈ halveS P) :
    halveStep σ s ∈ halveS P := by
  rw [bridgeStep]
  exact halveStepD_mem σ.toDecider hs

/-- The step is a move of the machine's relation. -/
theorem halveStep_rel {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (σ : HalveSelector P) {s : ZFSet.{u}} (hs : s ∈ halveS P) :
    opair s (halveStep σ s) ∈ halveR P := by
  rw [bridgeStep]
  exact halveStepD_rel σ.toDecider hs

/-- The walk itself, iterated from the unit interval. -/
def halveIter {P : ZFSet.{u} → ZFSet.{u} → Prop} (σ : HalveSelector P) :
    Nat → ZFSet.{u}
  | 0 => opair ratZero.{u} ratOne.{u}
  | n + 1 => halveStep σ (halveIter σ n)

/-- The two walks agree at every stage, by `bridgeStep` under the
recursion. The base case is `rfl` because both walks start at the same coded
unit interval; only the step needed a bridge. -/
theorem bridgeIter {P : ZFSet.{u} → ZFSet.{u} → Prop} (σ : HalveSelector P) :
    ∀ n, halveIter σ n = halveIterD σ.toDecider n
  | 0 => rfl
  | n + 1 => by
    rw [halveIter, halveIterD, bridgeIter σ n, bridgeStep]

/-- The walk stays in the state set at every stage, by `bridgeIter`. -/
theorem halveIter_mem {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (σ : HalveSelector P) (hP01 : P ratZero.{u} ratOne.{u}) :
    ∀ n, halveIter σ n ∈ halveS P := by
  intro n
  rw [bridgeIter]
  exact halveIterD_mem σ.toDecider hP01 n

/-! ### An instantiation that supplies its own decider

The trade becomes a removal here. `sqrtTwoP` reads the payload on the
doubled endpoints, so a walk confined to `[0,1]` converges on `√2/2`
while every comparison it makes is between rationals; and a comparison
between rationals is decided outright by `ratLt_or_not`. Nothing is
hypothesised: `halve_limit_of_decider sqrtTwoDecider` takes no principle
and no data, only the two facts that `[0,1]` starts the walk.

The one place irrationality is spent is `keepsR`, and it is spent to turn
`¬ (2 < y)` into `y < 2` -- which needs `y ≠ 2`, and that is exactly
`no_rat_sq_two`. Without it the right half would have to carry a
non-strict bound and the interval could stall on the root. -/

/-- Twice a rational. -/
def ratTwice (x : ZFSet.{u}) : ZFSet.{u} := ratMul (ratNat.{u} 2 1) x

theorem ratTwice_mem_Rat {x : ZFSet.{u}} (hx : x ∈ Rat.{u}) :
    ratTwice x ∈ Rat.{u} :=
  ratMul_mem_Rat (ratNat_mem_Rat (by omega)) hx

/-- The payload: the doubled interval straddles `√2`. -/
def sqrtTwoP (a b : ZFSet.{u}) : Prop :=
  And (ratLt (ratMul (ratTwice a) (ratTwice a)) (ratNat.{u} 2 1))
      (ratLt (ratNat.{u} 2 1) (ratMul (ratTwice b) (ratTwice b)))

/-- A straddle read through a rational-valued `g`: the target sits between
`g a` and `g b`. -/
def ratStraddleP (g : ZFSet.{u} → ZFSet.{u}) (c a b : ZFSet.{u}) : Prop :=
  And (ratLt (g a) c) (ratLt c (g b))

/-- What makes a decider free, stated in general: apartness from the
target. The branch is a rational comparison and rational order is decided,
so `decided` and `keepsL` cost nothing; the whole of the work is in `keepsR`,
where `¬ (c < g m)` gives only `g m ≤ c` and the strict inequality the
straddle wants needs `g m ≠ c`.

`sqrtTwoDecider` is this with `g x = (2x)²` and `c = 2`, and its `hne` is
`no_rat_sq_two`: irrationality of the target is the hypothesis that keeps the
bisection decidable, and a rational target would break it at the midpoint that
hits it. -/
def ratStraddleDecider (g : ZFSet.{u} → ZFSet.{u})
    (hg : ∀ x, x ∈ Rat.{u} → g x ∈ Rat.{u}) {c : ZFSet.{u}} (hc : c ∈ Rat.{u})
    (hne : ∀ x, x ∈ Rat.{u} → g x ≠ c) : HalveDecider (ratStraddleP g c) where
  goLeft s := ratLt c (g (ratMid (fst s) (snd s)))
  decided a b haQ hbQ := by
    rw [fst_opair, snd_opair]
    exact ratLt_or_not hc (hg _ (ratMid_mem_Rat haQ hbQ))
  keepsL a b _ _ _ _ _ hPab hgo := by
    rw [fst_opair, snd_opair] at hgo
    exact ⟨hPab.left, hgo⟩
  keepsR a b haQ hbQ _ _ _ hPab hgo := by
    rw [fst_opair, snd_opair] at hgo
    refine ⟨?_, hPab.right⟩
    rcases ratLt_trichotomy (hg _ (ratMid_mem_Rat haQ hbQ)) hc with h | h | h
    · exact h
    · exact absurd h (hne _ (ratMid_mem_Rat haQ hbQ))
    · exact absurd h hgo


/-- The decider for the `√2` straddle, built outright from `ratStraddleDecider`:
no principle and no supplied data. -/
def sqrtTwoDecider : HalveDecider sqrtTwoP.{u} :=
  ratStraddleDecider (fun x => ratMul (ratTwice x) (ratTwice x))
    (fun x hx => ratMul_mem_Rat (ratTwice_mem_Rat hx) (ratTwice_mem_Rat hx))
    (ratNat_mem_Rat (by omega))
    (fun x hx => no_rat_sq_two (ratTwice_mem_Rat hx))

#print axioms halveB_mem_ratSeqs
#print axioms halveS_lt
#print axioms halveS_snd_le_one
#print axioms halveIter_mem
#print axioms halveIterD_mem
#print axioms bridgeStep
#print axioms bridgeIter

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
#print axioms NumberTheory.halveLeft_mem_prod_on
#print axioms NumberTheory.halveRight_mem_prod_on
#print axioms NumberTheory.halveMoveOn
#print axioms NumberTheory.isFunction_halveMoveOn
#print axioms NumberTheory.domain_halveMoveOn
#print axioms NumberTheory.app_halveMoveOn
#print axioms NumberTheory.halve_binary_on
#print axioms NumberTheory.ratMid_facts
#print axioms NumberTheory.halve_chain_mem
#print axioms NumberTheory.halveS_spec
#print axioms NumberTheory.halveA_mem_ratSeqs
#print axioms NumberTheory.app_halveA
#print axioms NumberTheory.app_halveB
#print axioms NumberTheory.halveR_step
#print axioms NumberTheory.halveChain_mono
#print axioms NumberTheory.halveChain_width_scaled
#print axioms NumberTheory.halveChain_width_le
#print axioms NumberTheory.halveChain_isNested
#print axioms NumberTheory.nest_mem_Icc_of_ends
#print axioms NumberTheory.halveS_payload
#print axioms NumberTheory.halve_limit
#print axioms NumberTheory.halveStep_mem
#print axioms NumberTheory.halveStep_rel
#print axioms NumberTheory.halve_limit_of_selector
#print axioms NumberTheory.halveStepD_mem
#print axioms NumberTheory.halveStepD_rel
#print axioms NumberTheory.halve_limit_of_decider
#print axioms NumberTheory.HalveSelector.toDecider
#print axioms NumberTheory.ratTwice_mem_Rat
#print axioms NumberTheory.sqrtTwoDecider
#print axioms NumberTheory.ratStraddleP
#print axioms NumberTheory.ratStraddleDecider
#print axioms NumberTheory.ratMid_facts_on
#print axioms NumberTheory.halveInvOn
#print axioms NumberTheory.halveSOn
#print axioms NumberTheory.halveROn
#print axioms NumberTheory.halveS_spec_on
#print axioms NumberTheory.halveS_snd_le_q_on
#print axioms NumberTheory.halve_total_on
#print axioms NumberTheory.halveS_lt_on
#print axioms NumberTheory.halveS_payload_on
#print axioms NumberTheory.halveR_step_on
#print axioms NumberTheory.halveA_mem_ratSeqs_on
#print axioms NumberTheory.halveB_mem_ratSeqs_on
#print axioms NumberTheory.halveChain_width_scaled_on
#print axioms NumberTheory.halve_chain_mem_on
#print axioms NumberTheory.app_halveA_on
#print axioms NumberTheory.app_halveB_on
#print axioms NumberTheory.halveChain_mono_on
#print axioms NumberTheory.halveChain_width_le_on
#print axioms NumberTheory.halveChain_isNested_on

namespace ZFSet
export NumberTheory (ratSeq_mono_of_step ratSeq_anti_of_step ratSeq_scaled_of_step BinaryDCOn BinaryDCOnAt HalveDecider HalveSelector HasHalveLimit app_halveA app_halveA_of_chain app_halveA_on app_halveB app_halveB_of_chain app_halveB_on app_halveMove app_halveMoveOn binaryDCOn_of_dc binaryDCOnAt_of_binaryDCOn bridgeIter bridgeStep chain_mem_of_sep_prod chain_mono_of_step chain_width_scaled_of_step domain_halveMove domain_halveMoveOn halveA halveA_mem_ratSeqs halveA_mem_ratSeqs_of_chain halveA_mem_ratSeqs_on halveB halveB_mem_ratSeqs halveB_mem_ratSeqs_of_chain halveB_mem_ratSeqs_on halveChain_isNested halveChain_isNested_on halveChain_mono halveChain_mono_on halveChain_width_le halveChain_width_le_on halveChain_width_scaled halveChain_width_scaled_on halveInv halveInvOn halveIter halveIterD halveIterD_mem halveIter_mem halveLeft halveLeft_mem_prod halveLeft_mem_prod_on halveMove halveMoveOn halveR halveROn halveR_step halveR_step_on halveRight halveRight_mem_prod halveRight_mem_prod_on halveS halveSOn halveS_lt halveS_lt_on halveS_payload halveS_payload_on halveS_snd_le_one halveS_snd_le_q_on halveS_spec halveS_spec_on halveStep halveStepD halveStepD_mem halveStepD_rel halveStep_mem halveStep_rel halve_binary halve_binary_on halve_chain_mem halve_chain_mem_on halve_limit halve_limit_of_decider halve_limit_of_selector halve_total halve_total_on isFunction_halveMove isFunction_halveMoveOn mem_halveMove nest_mem_Icc_of_ends pow2_eq_two_pow ratMid_facts ratMid_facts_on ratPow_ratTwo ratStraddleDecider ratStraddleP ratTwice ratTwice_mem_Rat sqrtTwoDecider sqrtTwoP)
end ZFSet
