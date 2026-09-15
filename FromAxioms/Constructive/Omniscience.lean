/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# The omniscience principles.

`EM` and `WEM` are the only two strengths the audit could name until now, and
for a development that measures exact cost that is a coarse ruler. Between them
and constructive provability sit the principles that talk about sequences
rather than arbitrary propositions:

    LPO    every binary sequence either fires somewhere or is identically zero
    WLPO   ... either is identically zero, or is not
    MP     a sequence that cannot be identically zero fires somewhere
    LLPO   of two sequences that cannot both fire, one is identically zero

The sequences are `Nat → Bool`, so `α n = true` is decidable and the principles
say something about search rather than about logic in general: a statement
quantified over arbitrary propositions reverses to `EM`, and the same statement
restricted to objects built from a sequence typically reverses only to `LPO` or
`LLPO`.

`lpo_of_ternary_decidable` is that difference made concrete. Deciding whether
`0` lies in the lower cut of an arbitrary real is `EM`; deciding
it for a real produced by the ternary walk from a binary sequence is exactly
`LPO`, and the two directions are both here.
-/

import FromAxioms.Analysis.Ternary
import FromAxioms.Constructive.Reverse
import FromAxioms.SetTheory.Search

set_option autoImplicit false

universe u

open Analysis Core NumberTheory SetTheory
namespace Constructive

/-! ## The principles -/

/-- The limited principle of omniscience. -/
def LPO : Prop := ∀ α : Nat → Bool, (∃ n, α n = true) ∨ (∀ n, α n = false)

/-- `LPO`'s disjunction is NOT-NOT true at every sequence, so the principle
is precisely the gap between `¬¬P` and `P` -- and no argument whose conclusions
are ¬¬-STABLE can ever reach it.

That is a general bound rather than a remark. `withinOf_of_cases` and its
family dispose of an arbitrary `Prop` for free, and ENTIRELY by stability: the
proof is `withinOf_stable` applied to a double negation. So the technique is
available exactly when the target is stable, `WLPO` and `LLPO` are disjunctions
too, and any claim of the form this is free because the conclusion is stable
is automatically not a route to an omniscience principle. -/
theorem not_not_lpo_pointwise (α : Nat → Bool) :
    ¬¬ ((∃ n, α n = true) ∨ (∀ n, α n = false)) := by
  intro h
  exact h (Or.inr (fun n => by
    cases hn : α n with
    | true => exact absurd (h (Or.inl ⟨n, hn⟩)) (fun x => x)
    | false => rfl))

/-- Its weak form: decide only whether the sequence is identically zero. -/
def WLPO : Prop := ∀ α : Nat → Bool, (∀ n, α n = false) ∨ ¬ (∀ n, α n = false)

/-- Markov's principle. -/
def MP : Prop := ∀ α : Nat → Bool, ¬ (∀ n, α n = false) → ∃ n, α n = true

/-- The lesser limited principle of omniscience. -/
def LLPO : Prop := ∀ α β : Nat → Bool,
  ¬ ((∃ n, α n = true) ∧ (∃ n, β n = true)) →
    (∀ n, α n = false) ∨ (∀ n, β n = false)

/-! ## The lattice

`EM → LPO → WLPO → LLPO` and `LPO → MP`, each proved choice-free, so the
ordering is a checked object rather than a claim in a comment. -/

/-- A `Bool` never taking `true` takes `false` everywhere -- case analysis,
not a principle. Public because `Integral.lean` proves the same conclusion and
the duplicate is the one that goes. -/
theorem not_exists_true {α : Nat → Bool} (h : ¬ ∃ n, α n = true) :
    ∀ n, α n = false := by
  intro n
  cases hn : α n with
  | false => rfl
  | true => exact absurd ⟨n, hn⟩ h

theorem wlpo_of_lpo (hlpo : LPO) : WLPO := by
  intro α
  rcases hlpo α with ⟨n, hn⟩ | h
  · exact Or.inr (fun hall => by rw [hall n] at hn; exact Bool.noConfusion hn)
  · exact Or.inl h

theorem mp_of_lpo (hlpo : LPO) : MP := by
  intro α h
  rcases hlpo α with hex | hall
  · exact hex
  · exact absurd hall h

/-- The step that does real work: `β` firing forces `α` not to, and a `Bool` is
decidable, so the conclusion is reached without deciding anything else. -/
theorem llpo_of_wlpo (hwlpo : WLPO) : LLPO := by
  intro α β hdisj
  rcases hwlpo α with hα | hα
  · exact Or.inl hα
  · refine Or.inr (fun n => ?_)
    cases hn : β n with
    | false => rfl
    | true =>
      exact absurd (not_exists_true (fun hex => hdisj ⟨hex, ⟨n, hn⟩⟩)) hα

/-- `LPO` is exactly `WLPO` together with `MP`.

The lattice records both projections -- `wlpo_of_lpo` and `mp_of_lpo` -- and
this is the converse, which closes the pair into an equivalence.

Each half does one job and neither does the other's: `WLPO` decides whether the
sequence ever fires but produces no index, `MP` produces an index but only once
firing is known not to be impossible. Running them in that order is `LPO`. -/
theorem lpo_of_wlpo_of_mp (hwlpo : WLPO) (hmp : MP) : LPO := by
  intro α
  rcases hwlpo α with hall | hnot
  · exact Or.inr hall
  · exact Or.inl (hmp α hnot)

/-! ## Where `LPO` is the exact strength

A binary sequence gives ternary digits without any decision -- `Bool` is already
data -- so the walk of `Ternary.lean` turns `α` into a real. The walk moves right
exactly when a digit fires, so `0` is in the lower cut precisely when `α` does. -/

def boolDigit (α : Nat → Bool) (n : Nat) : Nat := if α n then 1 else 0

theorem boolDigit_le_one (α : Nat → Bool) (n : Nat) : boolDigit α n ≤ 1 := by
  rw [boolDigit]
  split <;> omega

theorem boolDigit_eq_one_iff {α : Nat → Bool} {n : Nat} :
    boolDigit α n = 1 ↔ α n = true := by
  rw [boolDigit]
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h => exact ⟨fun he => absurd he (by decide), fun hα => absurd hα h⟩

/-- The numerator is positive exactly when some earlier digit fired. -/
theorem tnum_pos_iff (c : Nat → Nat) : ∀ m : Nat,
    0 < tnum c m ↔ ∃ n, n < m ∧ 0 < c n
  | 0 => by
    simp only [tnum]
    constructor
    · intro h
      exact absurd h (by omega)
    · rintro ⟨n, hn, -⟩
      omega
  | m + 1 => by
    constructor
    · intro h
      simp only [tnum] at h
      rcases Nat.lt_or_ge 0 (c m) with hc | hc
      · exact ⟨m, by omega, hc⟩
      · obtain ⟨n, hn, hcn⟩ := (tnum_pos_iff c m).mp (by omega)
        exact ⟨n, by omega, hcn⟩
    · rintro ⟨n, hn, hcn⟩
      simp only [tnum]
      rcases Nat.lt_or_ge n m with hlt | hge
      · have := (tnum_pos_iff c m).mpr ⟨n, hlt, hcn⟩
        omega
      · have : n = m := by omega
        rw [this] at hcn
        omega

/-- `0` is in the walk's lower cut exactly when the sequence fires. -/
theorem zero_mem_ternary_iff (α : Nat → Bool) :
    ratZero.{u} ∈ nestLower (tlowSeq.{u} (boolDigit α)) ↔ ∃ n, α n = true := by
  rw [mem_nestLower_iff]
  constructor
  · rintro ⟨-, m, hm, hlt⟩
    obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
    rw [app_tlowSeq, tlow, ratZero_eq_ratNat,
      ratNat_lt_iff (by omega) (pow3_pos i)] at hlt
    obtain ⟨n, -, hcn⟩ := (tnum_pos_iff (boolDigit α) i).mp (by omega)
    refine ⟨n, ?_⟩
    have := boolDigit_le_one α n
    exact boolDigit_eq_one_iff.mp (by omega)
  · rintro ⟨n, hn⟩
    refine ⟨ratZero_mem_Rat, ofNat.{u} (n + 1), ofNat_mem_omega _, ?_⟩
    rw [app_tlowSeq, tlow, ratZero_eq_ratNat, ratNat_lt_iff (by omega) (pow3_pos (n + 1))]
    have hpos : 0 < tnum (boolDigit α) (n + 1) :=
      (tnum_pos_iff (boolDigit α) (n + 1)).mpr
        ⟨n, by omega, by rw [boolDigit_eq_one_iff.mpr hn]; omega⟩
    have := pow3_pos (n + 1)
    have e : tnum (boolDigit α) (n + 1) * 1 = tnum (boolDigit α) (n + 1) := by omega
    omega

/-- Deciding `0`'s membership in the cut of a walk-built real. -/
def TernaryDecidable : Prop := ∀ α : Nat → Bool,
  ratZero.{u} ∈ nestLower (tlowSeq.{u} (boolDigit α)) ∨
    ratZero.{u} ∉ nestLower (tlowSeq.{u} (boolDigit α))

theorem lpo_of_ternary_decidable (h : TernaryDecidable.{u}) : LPO := by
  intro α
  rcases h α with hin | hout
  · exact Or.inl ((zero_mem_ternary_iff α).mp hin)
  · exact Or.inr (not_exists_true (fun hex => hout ((zero_mem_ternary_iff α).mpr hex)))

theorem ternary_decidable_of_lpo (hlpo : LPO) : TernaryDecidable.{u} := by
  intro α
  rcases hlpo α with hex | hall
  · exact Or.inl ((zero_mem_ternary_iff α).mpr hex)
  · refine Or.inr (fun hin => ?_)
    obtain ⟨n, hn⟩ := (zero_mem_ternary_iff α).mp hin
    rw [hall n] at hn
    exact Bool.noConfusion hn

/-! ## Where `WLPO` and `MP` are the exact strengths

Equality with zero is one quantifier weaker than membership: the cut of the walk
is the cut of `0` exactly when no digit fires, which is a `Π` statement, so
deciding it is `WLPO` rather than `LPO`. Markov's principle is the step from one
to the other -- a walk that cannot be zero does fire. -/

theorem tnum_eq_zero {c : Nat → Nat} (h : ∀ n, c n = 0) : ∀ m : Nat, tnum c m = 0
  | 0 => rfl
  | m + 1 => by
    simp only [tnum, tnum_eq_zero h m, h m]

theorem ternary_eq_zero_iff (α : Nat → Bool) :
    nestLower (tlowSeq.{u} (boolDigit α)) = ratCut ratZero.{u} ↔ ∀ n, α n = false := by
  constructor
  · intro he n
    cases hn : α n with
    | false => rfl
    | true =>
      have h0 : ratZero.{u} ∈ nestLower (tlowSeq.{u} (boolDigit α)) :=
        (zero_mem_ternary_iff α).mpr ⟨n, hn⟩
      rw [he] at h0
      exact absurd ((mem_ratCut_iff ratZero.{u} ratZero.{u}).mp h0).right ratLt_irrefl
  · intro hall
    have hc : ∀ n, boolDigit α n = 0 := by
      intro n
      rw [boolDigit, hall n]
      rfl
    refine ext _ _ fun q => Iff.trans (mem_nestLower_iff _ q) ?_
    refine Iff.trans ?_ (mem_ratCut_iff ratZero.{u} q).symm
    constructor
    · rintro ⟨hqQ, m, hm, hlt⟩
      obtain ⟨i, rfl⟩ := (mem_omega_iff m).mp hm
      rw [app_tlowSeq, tlow, tnum_eq_zero hc i, ratNat_zero (pow3_pos i)] at hlt
      exact ⟨hqQ, hlt⟩
    · rintro ⟨hqQ, hlt⟩
      refine ⟨hqQ, ofNat.{u} 0, ofNat_mem_omega 0, ?_⟩
      rw [app_tlowSeq, tlow, tnum_eq_zero hc 0, ratNat_zero (pow3_pos 0)]
      exact hlt

/-- Deciding whether a walk-built real is zero. -/
def TernaryZeroDecidable : Prop := ∀ α : Nat → Bool,
  nestLower (tlowSeq.{u} (boolDigit α)) = ratCut ratZero.{u} ∨
    nestLower (tlowSeq.{u} (boolDigit α)) ≠ ratCut ratZero.{u}

/-- Deciding any predicate equivalent to `α` never fires IS `WLPO`.

THIS IS THE LOCAL CONVENTION, NOT A NEW IDEA. `LLPO` is already factored
exactly this way one principle over: `llpo_of_signDisjunction`
(`Vanishing.lean`) is the transport --- its own comment says the principle is
spent in ONE place --- with fourteen `signDisjunction_of_*` bridges and eight
one-line citations in `Calibrate.lean`, e.g.

    llpo_of_rolle01 h := llpo_of_signDisjunction (signDisjunction_of_rolle01 h)

FOUR `WLPO` CARRIERS WERE NEVER BROUGHT INTO IT: `TernaryZeroDecidable` here,
`DiscIsoDecidable`, `SetCatIsoDecidable` and `EqualizerInitialDecidable`. Each
already has its own bridge `S α ↔ ∀ n, α n = false` and then writes the same
four-line `rcases` out again --- character-for-character identical but for the
bridge cited, in both directions, so eight copies. The content of each row is
its bridge; the reversal was boilerplate.

A FIFTH IS NOT IN THIS CLASS and is easy to miscount as one:
`wlpo_of_meet_coincidence_decidable` already CITES the ternary transport and
composes three bridges inside a lambda. It was the one that had been factored
before, which is exactly the member a grouping-by-appearance gets wrong. -/
theorem wlpo_of_decidable_bridge {S : (Nat → Bool) → Prop}
    (hiff : ∀ α, S α ↔ ∀ n, α n = false)
    (hdec : ∀ α, S α ∨ ¬ S α) : WLPO := by
  intro α
  rcases hdec α with h | h
  · exact Or.inl ((hiff α).mp h)
  · exact Or.inr (fun hall => h ((hiff α).mpr hall))

/-- And `WLPO` supplies it, so each carrier is an EQUIVALENCE rather than a
lower bound --- the half that makes the five transports and not five prices. -/
theorem decidable_bridge_of_wlpo {S : (Nat → Bool) → Prop}
    (hiff : ∀ α, S α ↔ ∀ n, α n = false)
    (hwlpo : WLPO) : ∀ α, S α ∨ ¬ S α := by
  intro α
  rcases hwlpo α with h | h
  · exact Or.inl ((hiff α).mpr h)
  · exact Or.inr (fun hs => h ((hiff α).mp hs))

theorem wlpo_of_ternary_zero_decidable (h : TernaryZeroDecidable.{u}) : WLPO :=
  wlpo_of_decidable_bridge ternary_eq_zero_iff h

theorem ternary_zero_decidable_of_wlpo (hwlpo : WLPO) : TernaryZeroDecidable.{u} :=
  decidable_bridge_of_wlpo ternary_eq_zero_iff hwlpo

/-! ## Where `LLPO` is the exact strength

Two walk-built reals are both `≥ 0`, and each is `> 0` exactly when its
sequence fires. So "of two reals that cannot both be positive, one is `≤ 0`" is
`LLPO` read off the cuts -- the analytic form the principle is usually quoted
in, and the ternary walk states it without needing a sign. -/

def TernaryLLPO : Prop := ∀ α β : Nat → Bool,
  ¬ ((∃ n, α n = true) ∧ (∃ n, β n = true)) →
    ratZero.{u} ∉ nestLower (tlowSeq.{u} (boolDigit α)) ∨
      ratZero.{u} ∉ nestLower (tlowSeq.{u} (boolDigit β))

theorem llpo_of_ternary_llpo (h : TernaryLLPO.{u}) : LLPO := by
  intro α β hdisj
  rcases h α β hdisj with hα | hβ
  · exact Or.inl (not_exists_true (fun hex => hα ((zero_mem_ternary_iff α).mpr hex)))
  · exact Or.inr (not_exists_true (fun hex => hβ ((zero_mem_ternary_iff β).mpr hex)))

theorem ternary_llpo_of_llpo (hllpo : LLPO) : TernaryLLPO.{u} := by
  intro α β hdisj
  rcases hllpo α β hdisj with hα | hβ
  · refine Or.inl (fun hin => ?_)
    obtain ⟨n, hn⟩ := (zero_mem_ternary_iff α).mp hin
    rw [hα n] at hn
    exact Bool.noConfusion hn
  · refine Or.inr (fun hin => ?_)
    obtain ⟨n, hn⟩ := (zero_mem_ternary_iff β).mp hin
    rw [hβ n] at hn
    exact Bool.noConfusion hn

/-! ## The fan theorem

Brouwer's principle, and the same kind of object as `LPO` and friends of object
-- a statement about `Nat → Bool` that is classically true, is not
constructively provable, and is false under Russian constructivism, which
makes it a boundary rather than a theorem.

Stated over `List Bool` for the finite paths. A bar is a set of finite paths
that every infinite path meets; the theorem says a bar is met uniformly, at a
depth not depending on the path. The direction that needs no principle is the
converse, and it is here so the statement's two halves can be told apart.
-/

/-- The first `n` values of a sequence, as a path. -/
def take (α : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => take α n ++ [α n]

theorem length_take (α : Nat → Bool) : ∀ n, (take α n).length = n
  | 0 => rfl
  | n + 1 => by simp [take, length_take α n]

/-- A `Π⁰₁` predicate is double-negation stable, and freely so.

THIS NESTS THE TWO STABLE FAN THEOREMS. Diener (arXiv:1804.05495v3, Section
3.6) defines a STABLE BAR by `u ∈ B ↔ ∀ n, (u, n) ∈ S` with `S` decidable,
adding that stable bars *are exactly bars that are the complement of a
countable set*. That is `Π⁰₁`.

This lemma does the work directly: every
literature-stable bar is `Π⁰₁`, hence `¬¬`-stable, hence one of the bars our
`FANstable` quantifies over. So the classes are ORDERED, not incomparable, and
our principle is the stronger one:

    FANstable (this tree)  →  FANstable (Diener)

The consequence that mattered is unchanged and better founded: the published
`WLPO → FANstable` lands on the smaller class, so it does not give ours.

`mp_iff_sigma01_stable` below is a true statement about a DIFFERENT class and
does not bear on this comparison; composing the two into an incomparability
claim is the mistake this paragraph replaces. -/
theorem nnStable_forall {D : Nat → Prop} (hdec : ∀ n, D n ∨ ¬ D n)
    (h : ¬ ¬ (∀ n, D n)) : ∀ n, D n := by
  intro n
  rcases hdec n with hd | hd
  · exact hd
  · exact absurd (fun hall => hd (hall n)) h

/-- Markov's principle IS the double-negation stability of a `Σ⁰₁` statement,
stated over the `Nat → Bool` shape `MP` uses.

This is the other half: a `Σ⁰₁` bar is `¬¬`-stable exactly when `MP` holds, so
the literature's stability condition does not give this tree's for free. `MP` is
a lattice node here, not a theorem. -/
theorem mp_iff_sigma01_stable :
    MP ↔ ∀ α : Nat → Bool, ¬ ¬ (∃ n, α n = true) → ∃ n, α n = true := by
  constructor
  · intro hmp α hnn
    refine hmp α (fun hall => hnn (fun ⟨n, hn⟩ => ?_))
    rw [hall n] at hn
    exact Bool.noConfusion hn
  · intro h α hnot
    refine h α (fun hne => hnot (fun n => ?_))
    cases hα : α n with
    | false => rfl
    | true => exact absurd ⟨n, hα⟩ hne

#print axioms Constructive.nnStable_forall
#print axioms Constructive.mp_iff_sigma01_stable
#print axioms Constructive.wlpo_of_lpo
#print axioms Constructive.WLPO
#print axioms Constructive.wlpo_of_decidable_bridge
#print axioms Constructive.decidable_bridge_of_wlpo
#print axioms Constructive.LPO

/-- `B` is met by every infinite path. -/
def IsBar (B : List Bool → Prop) : Prop :=
  ∀ α : Nat → Bool, ∃ n, B (take α n)

/-- `B` is met by every infinite path at a bounded depth. -/
def IsUniformBar (B : List Bool → Prop) : Prop :=
  ∃ N, ∀ α : Nat → Bool, ∃ n, n ≤ N ∧ B (take α n)

/-- The fan theorem for decidable bars: a decidable bar is uniform.

Decidability is part of the statement, not a convenience. Without it the
principle is stronger than Brouwer's and is inconsistent with the recursive
interpretation; with it, this is exactly the compactness of `2^ω` read
constructively.

THE SUBSCRIPT IS THE LITERATURE'S AND THE UNQUALIFIED NAME IS TAKEN. Diener,
Constructive Reverse Mathematics (arXiv:1804.05495), §3.0, states four:

    FAN_Δ    : Every decidable bar is uniform.
    FAN_c    : Every c-bar is uniform.
    FAN_Π⁰₁  : Every Π⁰₁-bar is uniform.
    FAN_full : Every bar is uniform.

ordered `FAN_full ⟹ FAN_Π⁰₁ ⟹ FAN_c ⟹ FAN_Δ`. So an unqualified FAN is the
TOP of that chain, three rungs above this, and naming this one `FAN` claimed a
principle the tree does not state.

OF DIENER'S FOUR THIS TREE STATES EXACTLY ONE: only `FAN_Δ`. `FAN_c`,
`FAN_Π⁰₁` and `FAN_full` are all absent --- no `def` matching a fan shape
anywhere in `FromAxioms` beyond the three below, and no `Prop` of the
premise-free form `∀ B, IsBar B → IsUniformBar B`.

What the tree has beside `FAN_Δ` is `FANstable` (Diener §3.6, NOT a rung of the
four-chain) and `FANBool` (a carrier variant, not Diener's at all). So the
chain's top is unstated, and `fanstable` consequently has NOTHING above it in
`lattice.json` --- so a reversal to it would be the first of its kind. -/
def FANΔ : Prop :=
  ∀ B : List Bool → Prop, (∀ s, B s ∨ ¬ B s) → IsBar B → IsUniformBar B

/-- The fan theorem for a double-negation-stable bar.

`FANΔ` asks the bar to be decidable, and the bars analysis actually meets are
not: the oscillation of a function on a subinterval is a statement about
located reals, so what `realLLe` delivers is a negation. A negation IS
double-negation-stable, which is the premise here.

Strictly between `FANΔ` and the premise-free form: dropping decidability to
stability is weaker than dropping it altogether. The gap matters because a
theorem may reach one and not the other, and with only the endpoints named
that question cannot be asked.

THE NAME IS DIENER'S, AND HE LOCATES IT TWO RUNGS SHARPER THAN THE SENTENCE
ABOVE. Constructive Reverse Mathematics (arXiv:1804.05495), §3.6, defines a
STABLE bar as one satisfying only the first of the two conditions on a Π⁰₁-bar,
states `FAN_stable : Every stable bar is uniform`, and places it

    FAN_full ⟹ FAN_stable ⟹ FAN_Π⁰₁     (⟹ FAN_c ⟹ FAN_Δ)

with the converses unlikely. So strictly between is true and coarse: two
named rungs, `FAN_Π⁰₁` and `FAN_c`, sit between this and `FANΔ`, and neither is
stated in this tree.

WHAT IS NOT CLAIMED BY THE RENAME. Diener's stable bar is defined by
COMPLEXITY; the premise here is that the bar PREDICATE is
double-negation-stable. That the two classes coincide is an argument nobody
here has made. The name is taken because it is the right rung's name, not
because the identification is proved.

Registered, and priced against. `fanstable` is a node in
`tools/lattice.json`, carrying the edge `fanstable -> fanΔ` witnessed by
`fanΔ_of_fanStable`, and *the fundamental theorem of calculus: the derivative
of the integral* is priced at it. Four theorems are derived from it --- that
edge, `uniformlyContinuousOn_of_fanStable`, `pointwiseToUniform_of_fanStable`
and `weierstrassApprox_of_fanStable` --- and `fanStable_of_decider` produces
it.

WHAT STILL HAS NO INCOMING EDGE FROM THE LITERATURE, and that is a
measurement rather than unfinished reading. Sources stating *WLPO implies the
stable fan theorem* mean a Σ⁰₁-DEFINABLE bar; the premise here is
double-negation stability, and the two are incomparable in this tree.
`mp_iff_sigma01_stable` shows Σ⁰₁-to-stable is EXACTLY Markov's principle, and
`nnStable_forall` exhibits a Π⁰₁ family that is stable and not Σ⁰₁; both print no
axioms at all. So `wlpo -> fanstable` must not be minted from that reading ---
`lattice.json`'s README records the decline. -/
def FANstable : Prop :=
  ∀ B : List Bool → Prop, (∀ s, ¬ ¬ B s → B s) → IsBar B → IsUniformBar B

/-- A decidable bar is double-negation-stable, so `FANstable` implies `FANΔ`.

The premise-drop direction, and free: `B s ∨ ¬ B s` settles `¬ ¬ B s → B s`
by cases without any principle. -/
theorem fanΔ_of_fanStable (h : FANstable) : FANΔ :=
  fun B hdec hbar =>
    h B (fun s hnn => (hdec s).elim id (fun hn => absurd hn hnn)) hbar

/-- The fan theorem over a bar given by a bit. `FANΔ`'s premise has the
same shape as `WKL`'s -- a disjunction in `Prop` -- so the carrier axis of the
same carrier axis applies here, and asking the question on both principles
locates the fan-to-Koenig gap on that axis rather than only along the lattice.
-/
def FANBool : Prop :=
  ∀ B : List Bool → Bool, IsBar (fun s => B s = true) →
    IsUniformBar (fun s => B s = true)

/-! ## Where the fan theorem comes from, and what it actually costs

Classically `FANΔ` is compactness of `2^ω`, proved by Koenig: if the unbarred
paths reach every depth, walk down them and the resulting infinite path never
meets `B`. The walk carries the cost.

`EM` does not pay for it. The walk must produce an `α : Nat → Bool`, and the
choice of child at each node is a decision about a `Prop`; `EM` offers a
disjunction, and a disjunction cannot be eliminated into `Bool`. Converting one
into the other is `decider_of_em`, which is noncomputable and spends the
declared `choice`. So the hypothesis below is a `Decider`, and `em_of_decider`
records that this is no weaker than `EM`.

Every step other than the branch is choice-free, which is the measurement worth
having: the classical proof of `FANΔ` is not classical logic plus bookkeeping, it
is one appeal to a decision procedure with a constructive argument around it. -/

/-- A finite path is uniformly barred when every infinite extension of it
meets `B` at a bounded depth. `IsUniformBar B` is exactly this at the empty
path, so the fan theorem is the single statement `Ubar B []`. -/
def Ubar (B : List Bool → Prop) (s : List Bool) : Prop :=
  ∃ N, ∀ α : Nat → Bool, take α s.length = s → ∃ n, n ≤ N ∧ B (take α n)

/-- A barred path is uniformly barred, at its own length. -/
theorem ubar_of_mem {B : List Bool → Prop} {s : List Bool} (h : B s) :
    Ubar B s :=
  ⟨s.length, fun _ hα => ⟨s.length, Nat.le_refl _, by rw [hα]; exact h⟩⟩

/-- The combinatorial step, and it needs no principle. If both children of
`s` are uniformly barred then so is `s`: take the larger of the two bounds, and
split on the single bit `α s.length`, which is a `Bool` and so needs no
decision. -/
theorem ubar_of_children {B : List Bool → Prop} {s : List Bool}
    (h0 : Ubar B (s ++ [false])) (h1 : Ubar B (s ++ [true])) : Ubar B s := by
  obtain ⟨N0, hN0⟩ := h0
  obtain ⟨N1, hN1⟩ := h1
  refine ⟨max N0 N1, fun α hα => ?_⟩
  have hstep : take α (s.length + 1) = s ++ [α s.length] := by
    show take α s.length ++ [α s.length] = _
    rw [hα]
  have hlen : ∀ b : Bool, (s ++ [b]).length = s.length + 1 := by
    intro b; simp
  cases hb : α s.length with
  | false =>
    obtain ⟨n, hn, hB⟩ := hN0 α (by rw [hlen, hstep, hb])
    exact ⟨n, Nat.le_trans hn (Nat.le_max_left _ _), hB⟩
  | true =>
    obtain ⟨n, hn, hB⟩ := hN1 α (by rw [hlen, hstep, hb])
    exact ⟨n, Nat.le_trans hn (Nat.le_max_right _ _), hB⟩

/-- The child to walk into: `true` when the `false` child is already uniformly
barred, so that the step below can keep the walk unbarred. This is the one
place data is produced from a decision, so the hypothesis is a `Decider`
rather than `EM`. -/
def fanBit (B : List Bool → Prop) (dec : ∀ s : List Bool, Decider (Ubar B s))
    (s : List Bool) : Bool :=
  match dec (s ++ [false]) with
  | .isTrue _ => true
  | .isFalse _ => false

/-- The walk itself: the path built by following `fanBit` from the root. -/
def fanWalk (B : List Bool → Prop) (dec : ∀ s : List Bool, Decider (Ubar B s)) :
    Nat → List Bool
  | 0 => []
  | k + 1 => fanWalk B dec k ++ [fanBit B dec (fanWalk B dec k)]

/-- The walk stays unbarred. By `ubar_of_children`, a node that is not
uniformly barred has a child that is not either, and `fanBit` names it. -/
theorem not_ubar_fanBit {B : List Bool → Prop} {dec : ∀ s : List Bool, Decider (Ubar B s)}
    {s : List Bool} (h : ¬ Ubar B s) :
    ¬ Ubar B (s ++ [fanBit B dec s]) := by
  show ¬ Ubar B (s ++ [match dec (s ++ [false]) with
    | .isTrue _ => true | .isFalse _ => false])
  cases hd : dec (s ++ [false]) with
  | isTrue h0 => exact fun h1 => h (ubar_of_children h0 h1)
  | isFalse h0 => exact h0

/-- The walk, as a sequence. -/
def fanSeq (B : List Bool → Prop) (dec : ∀ s : List Bool, Decider (Ubar B s)) (n : Nat) :
    Bool :=
  fanBit B dec (fanWalk B dec n)

/-- Reading the walk back off its own sequence. -/
theorem take_fanSeq (B : List Bool → Prop) (dec : ∀ s : List Bool, Decider (Ubar B s)) :
    ∀ k, take (fanSeq B dec) k = fanWalk B dec k
  | 0 => rfl
  | k + 1 => by
    show take (fanSeq B dec) k ++ [fanSeq B dec k] = _
    rw [take_fanSeq B dec k]
    rfl

/-- No prefix of the walk is uniformly barred, given that the root is not. -/
theorem not_ubar_fanWalk {B : List Bool → Prop} {dec : ∀ s : List Bool, Decider (Ubar B s)}
    (h : ¬ Ubar B []) : ∀ k, ¬ Ubar B (fanWalk B dec k)
  | 0 => h
  | k + 1 => not_ubar_fanBit (not_ubar_fanWalk h k)

/-- The fan theorem for STABLE bars, from a decider. The bar's own premise
is not what the proof spends: it needs to decide `Ubar`, which is an existential
over sequences and not a property of the bar at a node. That is why the
hypothesis is a universal `Decider` and why this is not `fan_of_em` -- see the
section note above, and `em_of_decider` for the direction that is free.

Because that premise is never read, it can be the WEAKER one: double-negation
stability rather than decidability. `fanΔ_of_decider` below is this statement
followed by `fanΔ_of_fanStable`, so the two are a generalisation and its
instance rather than one argument written out twice.
-/
theorem fanStable_of_ubarDecider
    (dec : ∀ (B : List Bool → Prop) (s : List Bool), Decider (Ubar B s)) :
    FANstable := by
  intro B _hstable hbar
  have hroot : Ubar B [] := by
    cases dec B [] with
    | isTrue h => exact h
    | isFalse h =>
      obtain ⟨n, hn⟩ := hbar (fanSeq B (dec B))
      rw [take_fanSeq] at hn
      exact absurd (ubar_of_mem hn) (not_ubar_fanWalk h n)
  obtain ⟨N, hN⟩ := hroot
  exact ⟨N, fun α => hN α rfl⟩

#print axioms Constructive.fanStable_of_ubarDecider

/-- The fan theorem for STABLE bars, from a decider, now an instance of
`fanStable_of_ubarDecider` at `fun s => dec (Ubar B s)`. The statement is
unchanged, so `fanΔ_of_decider` and every other consumer is untouched; what has
moved is that the proof no longer asks for more than it spends. -/
theorem fanStable_of_decider (dec : ∀ q : Prop, Decider q) : FANstable :=
  fanStable_of_ubarDecider (fun B s => dec (Ubar B s))

/-- The fan theorem, from a decider, as the decidable-bar instance of
`fanStable_of_decider`: a decidable bar is double-negation-stable, which is the
step `fanΔ_of_fanStable` takes. -/
theorem fanΔ_of_ubarDecider
    (dec : ∀ (B : List Bool → Prop) (s : List Bool), Decider (Ubar B s)) : FANΔ :=
  fanΔ_of_fanStable (fanStable_of_ubarDecider dec)

#print axioms Constructive.fanΔ_of_ubarDecider

/-- The fan theorem, from a decider, now an instance of
`fanΔ_of_ubarDecider`. Unchanged statement; what moved is that the proof under it
no longer asks to decide every proposition. -/
theorem fanΔ_of_decider (dec : ∀ q : Prop, Decider q) : FANΔ :=
  fanΔ_of_ubarDecider (fun B s => dec (Ubar B s))

/-! ## What the fan theorem says about trees

The contrapositive reading, and the one that makes `FANΔ` recognisable as
compactness: a decidable tree in which every path dies out is bounded -- there
is a depth past which it is empty. Constructively "every path dies out" has to be
positive (`∀ α, ∃ n, ¬ T (take α n)`), not the negation of "there is a path",
so the statement below reads that way.
-/

/-- Prefix-closed: a path in the tree has all its prefixes in the tree. -/
def IsTree (T : List Bool → Prop) : Prop :=
  ∀ s b, T (s ++ [b]) → T s

/-- Every infinite path leaves the tree. -/
def PathsDieOut (T : List Bool → Prop) : Prop :=
  ∀ α : Nat → Bool, ∃ n, ¬ T (take α n)

/-- Empty past some depth. -/
def IsBounded (T : List Bool → Prop) : Prop :=
  ∃ N, ∀ s : List Bool, s.length = N → ¬ T s

/-- Any finite path, continued with `false` forever. -/
def extend (s : List Bool) : Nat → Bool := fun i => (s[i]?).getD false

theorem take_extend (s : List Bool) : ∀ k, k ≤ s.length →
    take (extend s) k = List.take k s
  | 0, _ => rfl
  | k + 1, hk => by
    have hlt : k < s.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
    rw [take, take_extend s k (Nat.le_of_lt hlt), List.take_succ,
      List.getElem?_eq_getElem hlt]
    simp [extend, List.getElem?_eq_getElem hlt]

/-- A uniform bar closed under EXTENSION holds on every string at its depth.

`IsUniformBar` says every path meets the bar by depth `N`; this says every
string OF length `N` is in it, which is the form a covering argument consumes.
`extend` turns a string into a path, `take_extend` identifies that path's
prefix, and the monotonicity hypothesis carries the bar up from whichever
prefix the path happened to meet.

Nothing here is about any particular bar. `Analysis.wideOsc_at_depth` was this
proof with `WideOsc` inlined, and its `wideOsc_mono` discharges the hypothesis
as it stands --- the hypothesis is in the APPEND form the tree's `_mono` lemmas
already use. -/
theorem forall_length_of_isUniformBar {B : List Bool → Prop}
    (hmono : ∀ s t : List Bool, B s → B (s ++ t))
    (huni : IsUniformBar B) :
    ∃ N : Nat, ∀ s : List Bool, s.length = N → B s := by
  obtain ⟨N, hN⟩ := huni
  refine ⟨N, fun s hs => ?_⟩
  obtain ⟨n, hnN, hbar⟩ := hN (extend s)
  rw [take_extend s n (by omega)] at hbar
  rw [← List.take_append_drop n s]
  exact hmono (List.take n s) (List.drop n s) hbar

#print axioms Constructive.forall_length_of_isUniformBar

/-- Prefixes stay in a tree, so leaving it once means leaving it for good. -/
theorem not_mem_of_prefix {T : List Bool → Prop} (hT : IsTree T) :
    ∀ s : List Bool, ∀ k, k ≤ s.length → ¬ T (List.take k s) → ¬ T s := by
  intro s
  suffices h : ∀ j k, k + j = s.length → ¬ T (List.take k s) → ¬ T s by
    intro k hk hnot
    exact h (s.length - k) k (by omega) hnot
  intro j
  induction j with
  | zero =>
    intro k hk hnot
    rw [show k = s.length by omega, List.take_length] at hnot
    exact hnot
  | succ j ih =>
    intro k hk hnot
    refine ih (k + 1) (by omega) ?_
    intro hmem
    have hlt : k < s.length := by omega
    have hstep : List.take (k + 1) s = List.take k s ++ [s[k]] := by
      rw [List.take_succ, List.getElem?_eq_getElem hlt]; rfl
    rw [hstep] at hmem
    exact hnot (hT (List.take k s) s[k] hmem)

/-- A decidable tree whose paths all die out is bounded -- the fan theorem,
read as compactness. -/
theorem isBounded_of_fanΔ (hfan : FANΔ) {T : List Bool → Prop}
    (hdec : ∀ s, T s ∨ ¬ T s) (hT : IsTree T) (hdie : PathsDieOut T) :
    IsBounded T := by
  obtain ⟨N, hN⟩ := hfan (fun s => ¬ T s) (fun s => (hdec s).symm.imp id
    (fun h hc => hc h)) hdie
  refine ⟨N, fun s hs => ?_⟩
  obtain ⟨n, hnN, hnot⟩ := hN (extend s)
  rw [take_extend s n (by omega)] at hnot
  exact not_mem_of_prefix hT s n (by omega) hnot

/-! ## Weak König's lemma

`FANΔ` says a decidable bar is uniform -- compactness of `2^ω`, and
intuitionistically acceptable. `WKL` is its classical twin: an infinite
decidable tree has an infinite path. The two look like contrapositives and are
not interchangeable here, so both are stated: `FANΔ` is a theorem of Brouwer's
mathematics, while `WKL` implies `LLPO` and so is not.

Stated over the same detachable `List Bool → Prop` trees `FANΔ` uses, so
the comparison is between principles and not between encodings. In
Simpson's second-order arithmetic the corresponding subsystem is the
second of the five, and its correspondence is with the classical
hierarchy; the reversal below is what pins this statement to a rung of
the constructive one. -/

/-- A tree with a path of every length. Positive, as `PathsDieOut` is:
the negation of boundedness would say less. -/
def IsInfiniteTree (T : List Bool → Prop) : Prop :=
  ∀ N : Nat, ∃ s : List Bool, s.length = N ∧ T s

/-- An infinite path: a sequence all of whose prefixes stay in the tree. -/
def HasPath (T : List Bool → Prop) : Prop :=
  ∃ α : Nat → Bool, ∀ n, T (take α n)

/-- Weak König's lemma: an infinite decidable tree has a path. -/
def WKL : Prop :=
  ∀ T : List Bool → Prop, (∀ s, T s ∨ ¬ T s) → IsTree T →
    IsInfiniteTree T → HasPath T

/-- The same lemma over a tree given by a `Bool`. `WKL`'s membership
hypothesis is `∀ s, T s ∨ ¬ T s` -- a disjunction in `Prop` -- and this asks
instead for a decision procedure, which is data.

The two are not the same assumption, and the difference matters: `WKL` already
performs a carrier upgrade, turning a tree decidable only in `Prop` into a
`Nat → Bool` path. Splitting the hypothesis says how much of that upgrade is in
the premise. -/
def WKLBool : Prop :=
  ∀ T : List Bool → Bool, IsTree (fun s => T s = true) →
    IsInfiniteTree (fun s => T s = true) → HasPath (fun s => T s = true)

/-- Bounded search is decidable: whether a sequence has fired below a
given index is settled by looking, and the induction is the looking. -/
theorem fired_below_or_not (α : Nat → Bool) :
    ∀ n : Nat, (∃ k, k < n ∧ α k = true) ∨ ¬ (∃ k, k < n ∧ α k = true)
  | 0 => Or.inr (by rintro ⟨k, hk, -⟩; omega)
  | n + 1 => by
    rcases fired_below_or_not α n with hyes | hno
    · obtain ⟨k, hk, hα⟩ := hyes
      exact Or.inl ⟨k, by omega, hα⟩
    · cases hn : α n with
      | true => exact Or.inl ⟨n, Nat.lt_succ_self n, hn⟩
      | false =>
        refine Or.inr ?_
        rintro ⟨k, hk, hα⟩
        rcases Nat.lt_or_ge k n with hlt | hge
        · exact hno ⟨k, hlt, hα⟩
        · have : k = n := by omega
          subst this
          rw [hn] at hα
          exact Bool.noConfusion hα

/-- The tree behind the reversal: the first bit chooses which of the two
sequences is promised never to fire, and the depth is how far that
promise has been checked. Nothing below the first bit is constrained,
so the tree is as wide as it needs to be. -/
def llpoTree (α β : Nat → Bool) (s : List Bool) : Prop :=
  And (s[0]? = some false → ¬ (∃ k, k < s.length ∧ α k = true))
    (s[0]? = some true → ¬ (∃ k, k < s.length ∧ β k = true))

theorem llpoTree_nil (α β : Nat → Bool) : llpoTree α β [] :=
  ⟨fun h => by simp at h, fun h => by simp at h⟩

theorem llpoTree_decidable (α β : Nat → Bool) (s : List Bool) :
    llpoTree α β s ∨ ¬ llpoTree α β s := by
  cases hs : s[0]? with
  | none =>
    exact Or.inl ⟨fun h => by simp [hs] at h, fun h => by simp [hs] at h⟩
  | some b =>
    cases b with
    | false =>
      rcases fired_below_or_not α s.length with hα | hα
      · exact Or.inr (fun h => h.left hs hα)
      · exact Or.inl ⟨fun _ => hα, fun h => by simp [hs] at h⟩
    | true =>
      rcases fired_below_or_not β s.length with hβ | hβ
      · exact Or.inr (fun h => h.right hs hβ)
      · exact Or.inl ⟨fun h => by simp [hs] at h, fun _ => hβ⟩

theorem llpoTree_isTree (α β : Nat → Bool) : IsTree (llpoTree α β) := by
  intro s b hs
  cases s with
  | nil => exact llpoTree_nil α β
  | cons c t =>
    refine ⟨fun h hfire => ?_, fun h hfire => ?_⟩
    · refine hs.left (by simpa using h) ?_
      obtain ⟨k, hk, hα⟩ := hfire
      exact ⟨k, by simp at hk ⊢; omega, hα⟩
    · refine hs.right (by simpa using h) ?_
      obtain ⟨k, hk, hβ⟩ := hfire
      exact ⟨k, by simp at hk ⊢; omega, hβ⟩

/-- A constant string of the chosen bit, of the length asked for. -/
def repeatBit (b : Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => b :: repeatBit b n

theorem length_repeatBit (b : Bool) : ∀ n, (repeatBit b n).length = n
  | 0 => rfl
  | n + 1 => by simp [repeatBit, length_repeatBit b n]

theorem head_repeatBit (b : Bool) (n : Nat) :
    (repeatBit b (n + 1))[0]? = some b := rfl

/-- The tree is infinite, given that the two sequences cannot both
fire: at each depth the bounded search says which side is still clean,
and one of them must be. -/
theorem llpoTree_infinite {α β : Nat → Bool}
    (h : ¬ ((∃ n, α n = true) ∧ (∃ n, β n = true))) :
    IsInfiniteTree (llpoTree α β) := by
  intro N
  cases N with
  | zero => exact ⟨[], rfl, llpoTree_nil α β⟩
  | succ n =>
    rcases fired_below_or_not α (n + 1) with hα | hα
    · -- `α` has fired, so `β` never does; take the `true` branch
      refine ⟨repeatBit true (n + 1), length_repeatBit true (n + 1),
        fun heq => ?_, fun _ hfire => ?_⟩
      · rw [head_repeatBit] at heq
        exact Bool.noConfusion (Option.some.inj heq)
      · obtain ⟨k, -, hβ⟩ := hfire
        obtain ⟨j, -, hαj⟩ := hα
        exact h ⟨⟨j, hαj⟩, ⟨k, hβ⟩⟩
    · -- `α` is still clean below this depth; take the `false` branch
      refine ⟨repeatBit false (n + 1), length_repeatBit false (n + 1),
        fun _ hfire => ?_, fun heq => ?_⟩
      · obtain ⟨k, hk, hαk⟩ := hfire
        rw [length_repeatBit] at hk
        exact hα ⟨k, hk, hαk⟩
      · rw [head_repeatBit] at heq
        exact Bool.noConfusion (Option.some.inj heq)

/-- Every nonempty prefix of a sequence starts with its first value. -/
theorem head_take (γ : Nat → Bool) : ∀ n, (take γ (n + 1))[0]? = some (γ 0)
  | 0 => rfl
  | n + 1 => by
    rw [take]
    rw [List.getElem?_append_left (by rw [length_take]; omega)]
    exact head_take γ n

/-- Reading the path decides. The first bit is a `Bool`, so no
decision is made in looking at it; every prefix carries the promise, and
the promise at depth `n + 1` is exactly that the chosen sequence has not
fired below `n + 1`. Shared by both reversals below. -/
theorem llpo_of_llpoTree_path {α β γ : Nat → Bool}
    (hγ : ∀ n, llpoTree α β (take γ n)) :
    (∀ n, α n = false) ∨ (∀ n, β n = false) := by
  cases hg : γ 0 with
  | false =>
    refine Or.inl (fun n => ?_)
    cases hn : α n with
    | false => rfl
    | true =>
      exfalso
      refine (hγ (n + 1)).left ?_ ⟨n, ?_, hn⟩
      · rw [head_take, hg]
      · rw [length_take]; omega
  | true =>
    refine Or.inr (fun n => ?_)
    cases hn : β n with
    | false => rfl
    | true =>
      exfalso
      refine (hγ (n + 1)).right ?_ ⟨n, ?_, hn⟩
      · rw [head_take, hg]
      · rw [length_take]; omega

/-- Weak König's lemma yields `LLPO` -- the reversal that separates
it from `FANΔ`. -/
theorem llpo_of_wkl (hwkl : WKL) : LLPO := fun α β h =>
  Exists.elim (hwkl (llpoTree α β) (llpoTree_decidable α β)
      (llpoTree_isTree α β) (llpoTree_infinite h))
    (fun _ hγ => llpo_of_llpoTree_path hγ)

/-! ## What `WKL` has that `FANΔ` does not

The two principles are stated over the same trees, so the gap between
them can be located rather than merely asserted. Three of the four
links are free:

    PathsDieOut T  →  ¬ HasPath T          (a path would survive)
    IsInfiniteTree T  →  ¬ IsBounded T     (a long enough string survives)
    FANΔ, T infinite   →  ¬ PathsDieOut T   (else FANΔ bounds it)

and the fourth is not: turning `¬ PathsDieOut T` -- no sequence is known
to leave the tree -- into an actual path is the step `WKL` performs and
`FANΔ` cannot. Naming that step (`PathSelection`) makes the difference an
object: `FANΔ` together with it is `WKL`, so everything `WKL` buys beyond
compactness is the selection. -/

/-- An infinite tree is not bounded: the bound's own depth has a string. -/
theorem not_isBounded_of_isInfiniteTree {T : List Bool → Prop}
    (h : IsInfiniteTree T) : ¬ IsBounded T := by
  rintro ⟨N, hN⟩
  obtain ⟨s, hlen, hs⟩ := h N
  exact hN s hlen hs

/-- The reversal's tree needs no compactness to stay alive. Feeding
`PathsDieOut` the two constant sequences makes both `α` and `β` fire,
which the hypothesis forbids. Each firing is recovered from a double
negation by `fired_below_or_not`, so the step is a decidable search and
not a principle -- so `FANΔ` plays no part here. -/
theorem not_pathsDieOut_llpoTree {α β : Nat → Bool}
    (h : ¬ ((∃ n, α n = true) ∧ (∃ n, β n = true))) :
    ¬ PathsDieOut (llpoTree α β) := by
  intro hdie
  obtain ⟨n, hn⟩ := hdie (fun _ => false)
  obtain ⟨m, hm⟩ := hdie (fun _ => true)
  cases n with
  | zero => exact hn (llpoTree_nil α β)
  | succ n' =>
    cases m with
    | zero => exact hm (llpoTree_nil α β)
    | succ m' =>
      have hA : ∃ k, k < n' + 1 ∧ α k = true := by
        rcases fired_below_or_not α (n' + 1) with hyes | hno
        · exact hyes
        · exact absurd
            ⟨fun _ => by rw [length_take]; exact hno,
             fun heq => by
               rw [head_take] at heq
               exact Bool.noConfusion (Option.some.inj heq)⟩ hn
      have hB : ∃ k, k < m' + 1 ∧ β k = true := by
        rcases fired_below_or_not β (m' + 1) with hyes | hno
        · exact hyes
        · exact absurd
            ⟨fun heq => by
               rw [head_take] at heq
               exact Bool.noConfusion (Option.some.inj heq),
             fun _ => by rw [length_take]; exact hno⟩ hm
      obtain ⟨k, -, hαk⟩ := hA
      obtain ⟨j, -, hβj⟩ := hB
      exact h ⟨⟨k, hαk⟩, ⟨j, hβj⟩⟩

/-- The step `FANΔ` does not take: a tree no sequence is known to leave
has a path. Named as a principle so the gap it fills can be measured
rather than described. -/
def PathSelection : Prop :=
  ∀ T : List Bool → Prop, (∀ s, T s ∨ ¬ T s) → IsTree T →
    ¬ PathsDieOut T → HasPath T

/-- Path selection alone yields `LLPO` -- sharper than going through
`WKL`, and the gap located above is the whole of it: the reversal's tree stays
alive by a decidable search, so `FANΔ` contributes nothing and the selection
carries the entire strength. -/
theorem llpo_of_pathSelection (hsel : PathSelection) : LLPO := fun α β h =>
  Exists.elim (hsel (llpoTree α β) (llpoTree_decidable α β)
      (llpoTree_isTree α β) (not_pathsDieOut_llpoTree h))
    (fun _ hγ => llpo_of_llpoTree_path hγ)

/-! ## Where the selection's strength sits

`PathSelection` is at least `LLPO`. For the upper bound
the classical construction is greedy: stand at a node whose subtree
still reaches every depth, and step to a child that does the same. The
step is what this section proves, and it is constructive -- given that
the left child fails, the right one succeeds, with no principle spent.

What is not free is knowing which child fails, and that is a decision about a
`Π` statement. So the honest form takes it as data, exactly as
`bdn_of_mp_readout` does: the principle is spent on reading the step's premise
rather than on the step. -/

/-- The subtree above `s` reaches depth `N`. -/
def Extendable (T : List Bool → Prop) (s : List Bool) (N : Nat) : Prop :=
  ∃ t : List Bool, t.length = N ∧ T (s ++ t)

/-- The subtree above `s` reaches every depth. -/
def Unbounded (T : List Bool → Prop) (s : List Bool) : Prop :=
  ∀ N, Extendable T s N

/-! ## The path from a readout -/

/-- Which child to descend to, as data, with the promise that the child
it names stays unbounded. -/
structure TreeReadout (T : List Bool → Prop) where
  bit : List Bool → Bool
  keeps : ∀ s, Unbounded T s → Unbounded T (s ++ [bit s])

/-- The node reached at depth `n`, by following the readout. -/
def pathAt {T : List Bool → Prop} (r : TreeReadout T) : Nat → List Bool
  | 0 => []
  | n + 1 => pathAt r n ++ [r.bit (pathAt r n)]

theorem pathAt_unbounded {T : List Bool → Prop} (r : TreeReadout T)
    (h0 : Unbounded T []) : ∀ n, Unbounded T (pathAt r n)
  | 0 => h0
  | n + 1 => r.keeps _ (pathAt_unbounded r h0 n)

/-- An unbounded node is in the tree: it reaches depth zero, and the only
string of length zero is the empty one. -/
theorem mem_of_unbounded {T : List Bool → Prop} {s : List Bool}
    (h : Unbounded T s) : T s := by
  obtain ⟨t, hlen, hmem⟩ := h 0
  have : t = [] := List.eq_nil_of_length_eq_zero hlen
  subst this
  simpa using hmem

/-- The sequence the readout names, and its prefixes are its nodes. -/
theorem take_pathAt {T : List Bool → Prop} (r : TreeReadout T) :
    ∀ n, take (fun k => r.bit (pathAt r k)) n = pathAt r n
  | 0 => rfl
  | n + 1 => by rw [take, take_pathAt r n, pathAt]

/-- A readout gives a path: descend by the bit at each node, and the
promise carries unboundedness -- hence membership -- all the way down.
No principle is spent, because nothing is decided: the bit is given. -/
theorem hasPath_of_readout {T : List Bool → Prop} (r : TreeReadout T)
    (h0 : Unbounded T []) : HasPath T := by
  refine ⟨fun k => r.bit (pathAt r k), fun n => ?_⟩
  rw [take_pathAt r n]
  exact mem_of_unbounded (pathAt_unbounded r h0 n)

/-! ## Ishihara's boundedness principle

`BD-N`: every countable pseudobounded subset of `Nat` is bounded. Stated over
enumerations, as the omniscience principles are stated over sequences: the
subset is the range of `f`, and a sequence into the range is pseudobounded
when it is eventually dominated by its index. -/

/-- Every sequence drawn from the range of `f` is eventually below its index. -/
def Pseudobounded (f : Nat → Nat) : Prop :=
  ∀ a : Nat → Nat, (∀ n, ∃ m, a n = f m) → ∃ N, ∀ n, N ≤ n → a n ≤ n


/-! ## The readout alone, without Markov's principle

Transplanted, the fallback is `f 0` and the decided predicate is this tree's
`d`, which reads whether the range clears a level rather than whether a number
is a member. The two hypotheses are different and neither is the other, so what
carries across is the proof idea. -/

/-- The total sequence: the found element where the readout fires, `f 0` where
it does not.

The `dite` branches on `d k = true`, whose `Decidable` instance is `Bool`'s own
structural one, not a classical instance conjured for an arbitrary `Prop`. -/
noncomputable def readoutSeq (f : Nat → Nat) (d : Nat → Bool)
    (hd : ∀ k, d k = true ↔ ∃ n, Nat.ble (k + 1) (f n) = true) (k : Nat) : Nat :=
  if h : d k = true then
    f (natFind (fun n => Nat.ble (k + 1) (f n)) ((hd k).mp h))
  else f 0

/-- Every term is drawn from the range of `f`, which is what `Pseudobounded`
quantifies over: both branches are `f` of something. -/
theorem readoutSeq_mem (f : Nat → Nat) (d : Nat → Bool)
    (hd : ∀ k, d k = true ↔ ∃ n, Nat.ble (k + 1) (f n) = true) (k : Nat) :
    ∃ m, readoutSeq f d hd k = f m := by
  unfold readoutSeq
  split
  · rename_i h
    exact ⟨natFind (fun n => Nat.ble (k + 1) (f n)) ((hd k).mp h), rfl⟩
  · exact ⟨0, rfl⟩

/-! ## Deciding a bounded search over the tree

`PathSelection` already takes `T`'s decidability as a hypothesis, and that
hypothesis is enough to decide a bounded question outright: whether some
string of a given length is in the tree is a search over finitely many
strings, so it needs no principle at all. What was missing was the finitely
many strings.

The consequence is that `¬ PathsDieOut T → Unbounded T []` is free. If the
tree reaches no depth `N`, then every sequence's first `N` values already
lie outside it, so every path escapes -- which is exactly `PathsDieOut`. So
the negation gives `¬ ¬ Extendable`, and the enumeration discharges the
double negation without a principle. What is left of `PathSelection` after
this is the readout alone. -/

/-- Every list in `l`, with `b` in front. -/
def consAll (b : Bool) : List (List Bool) → List (List Bool)
  | [] => []
  | s :: rest => (b :: s) :: consAll b rest

theorem mem_consAll {b : Bool} {x : List Bool} :
    ∀ l : List (List Bool), x ∈ consAll b l → ∃ s, s ∈ l ∧ x = b :: s
  | [], h => absurd h (fun hc => by cases hc)
  | s :: rest, h => by
    rcases List.mem_cons.mp h with he | hrest
    · exact ⟨s, List.mem_cons_self, he⟩
    · obtain ⟨t, ht, rfl⟩ := mem_consAll rest hrest
      exact ⟨t, List.mem_cons_of_mem _ ht, rfl⟩

theorem mem_consAll_of_mem {b : Bool} {s : List Bool} :
    ∀ l : List (List Bool), s ∈ l → (b :: s) ∈ consAll b l
  | [], h => absurd h (fun hc => by cases hc)
  | t :: rest, h => by
    rcases List.mem_cons.mp h with rfl | hrest
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_consAll_of_mem rest hrest)

/-! ## Enumerating the strings

`allStrings` lists one length at a time, which is what the bar argument
needs. Turning a family of choices indexed by strings into one indexed by
`Nat` needs something else: a bijection. This is the bijective base-2
encoding -- a string is read as a numeral whose digits are `1` and `2`, so
every natural is exactly one string and no leading-zero ambiguity arises. -/

/-- Every binary string of a given length, listed. -/
def allStrings : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => consAll false (allStrings n) ++ consAll true (allStrings n)

theorem length_of_mem_allStrings :
    ∀ (n : Nat) (s : List Bool), s ∈ allStrings n → s.length = n
  | 0, s, h => by
    rcases List.mem_cons.mp h with rfl | hc
    · rfl
    · exact absurd hc (fun hx => by cases hx)
  | n + 1, s, h => by
    rcases List.mem_append.mp h with hl | hr
    · obtain ⟨t, ht, rfl⟩ := mem_consAll _ hl
      exact congrArg (· + 1) (length_of_mem_allStrings n t ht)
    · obtain ⟨t, ht, rfl⟩ := mem_consAll _ hr
      exact congrArg (· + 1) (length_of_mem_allStrings n t ht)

theorem mem_allStrings_of_length :
    ∀ (n : Nat) (s : List Bool), s.length = n → s ∈ allStrings n
  | 0, [], _ => List.mem_cons_self
  | 0, _ :: _, h => absurd h (fun hc => by cases hc)
  | n + 1, [], h => absurd h.symm (Nat.succ_ne_zero n)
  | n + 1, b :: s, h => by
    have hs : s.length = n := Nat.succ.inj h
    have hmem := mem_allStrings_of_length n s hs
    cases b with
    | false =>
      exact List.mem_append.mpr (Or.inl (mem_consAll_of_mem _ hmem))
    | true =>
      exact List.mem_append.mpr (Or.inr (mem_consAll_of_mem _ hmem))

#print axioms fired_below_or_not
#print axioms llpoTree_decidable
#print axioms llpoTree_isTree
#print axioms llpoTree_infinite
#print axioms llpo_of_llpoTree_path
#print axioms llpo_of_wkl
#print axioms not_pathsDieOut_llpoTree
#print axioms llpo_of_pathSelection
#print axioms not_isBounded_of_isInfiniteTree
#print axioms mem_of_unbounded
#print axioms take_pathAt
#print axioms hasPath_of_readout
#print axioms readoutSeq
#print axioms readoutSeq_mem
#print axioms llpo_of_wlpo
#print axioms lpo_of_wlpo_of_mp
#print axioms mp_of_lpo
#print axioms zero_mem_ternary_iff
#print axioms lpo_of_ternary_decidable
#print axioms ternary_decidable_of_lpo
#print axioms ternary_eq_zero_iff
#print axioms wlpo_of_ternary_zero_decidable
#print axioms length_take
#print axioms take_extend
#print axioms isBounded_of_fanΔ
#print axioms ternary_zero_decidable_of_wlpo
#print axioms llpo_of_ternary_llpo
#print axioms ternary_llpo_of_llpo

/-! ## The other half of the contraposition, and what it costs

Constructively the contraposition is not free, and the whole cost is one step.
"No path" gives the NEGATION of `IsInfiniteTree`, which is the negation of a
universal statement, while the fan theorem needs a witnessing depth. Turning
the first into the second over a decidable matrix is precisely Markov's
principle -- and the matrix is decidable, because `levelHit` already computes
"some string of this length is in the tree" as a `Bool`.

So the two halves of the classical contraposition are priced differently here:
the fan theorem gives Koenig's given a selection, and Koenig's gives the fan
theorem given `MP`.
-/

/-- Some prefix of `s`, itself included, has met the bar. A scan over the
finitely many prefixes, so a `Bool`. -/
def barredBelow (B : List Bool → Bool) (s : List Bool) : Bool :=
  (List.range (s.length + 1)).any (fun k => B (s.take k))

/-- The unbarred tree: the strings no prefix of which has met the bar. -/
def unbarred (B : List Bool → Bool) (s : List Bool) : Bool := !(barredBelow B s)

/-! ## Subtrees, and boundedness as a bit

The pieces below the `LLPO` step, for deriving `WKLBool` from `LLPO` and
`BinaryDC` -- the theorem is not here yet, so it is described and not named:
a name in prose is checked against the tree, and one for a declaration that
does not exist would be a claim rather than a plan. The step
itself is: if both children of a node are bounded, so is the node, so
`¬ IsBounded s` gives `¬ (bounded left ∧ bounded right)` -- and that is
`LLPO`'s own shape, once boundedness is a `Nat → Bool`. `allStrings` is what
makes it one: the quantifier over strings of a length is finite.
-/

/-- The tree below a node: `t` is in it exactly when `s ++ t` is in `T`. -/
def subTree (T : List Bool → Prop) (s : List Bool) : List Bool → Prop :=
  fun t => T (s ++ t)

/-- A subtree is a tree, by associativity of append. -/
theorem isTree_subTree {T : List Bool → Prop} (hT : IsTree T) (s : List Bool) :
    IsTree (subTree T s) := by
  intro t b h
  have h' : T (s ++ (t ++ [b])) := h
  exact hT (s ++ t) b (by rw [List.append_assoc]; exact h')

/-- Boundedness is monotone in the level. A tree empty at level `N` is
empty at every level above it, because a string whose prefix left the tree
left it too -- `not_mem_of_prefix`, which is the contrapositive of `IsTree`. -/
theorem isBounded_at_above {T : List Bool → Prop} (hT : IsTree T) {N : Nat}
    (hN : ∀ s : List Bool, s.length = N → ¬ T s) :
    ∀ M : Nat, N ≤ M → ∀ s : List Bool, s.length = M → ¬ T s := by
  intro M hNM s hs
  refine not_mem_of_prefix hT s N (by omega) (hN _ ?_)
  rw [List.length_take]
  omega

/-- Both children bounded makes the node bounded.

A string of length `N + 1` below `s` begins with a bit, and the rest sits at
length `N` below `s ++ [b]`. Taking the larger of the two levels and adding
one covers both children at once; `isBounded_at_above` is what lets one level
serve where each child supplies its own. -/
theorem isBounded_of_children {T : List Bool → Prop} (hT : IsTree T)
    (s : List Bool) (h0 : IsBounded (subTree T (s ++ [false])))
    (h1 : IsBounded (subTree T (s ++ [true]))) :
    IsBounded (subTree T s) := by
  obtain ⟨N₀, hN₀⟩ := h0
  obtain ⟨N₁, hN₁⟩ := h1
  refine ⟨max N₀ N₁ + 1, ?_⟩
  intro t ht
  match t with
  -- No `simp` and no `omega` on the length equations: both route through
  -- `Classical.em` here and the budget is a hard ratchet.
  -- `List.length_cons` and `Nat.succ.inj` say the same thing at two axioms.
  | [] => exact absurd ht.symm (Nat.succ_ne_zero (max N₀ N₁))
  | b :: rest =>
    have hrest : rest.length = max N₀ N₁ := by
      have h := ht
      rw [List.length_cons] at h
      exact Nat.succ.inj h
    have hsub : ∀ u : List Bool, T (s ++ [b] ++ u) → subTree T (s ++ [b]) u :=
      fun _ h => h
    -- the rest sits below `s ++ [b]`, at a level both children reach
    have hb : ¬ subTree T (s ++ [b]) rest := by
      cases b with
      | false =>
        exact isBounded_at_above (isTree_subTree hT _) hN₀ _
          (Nat.le_max_left N₀ N₁) rest hrest
      | true =>
        exact isBounded_at_above (isTree_subTree hT _) hN₁ _
          (Nat.le_max_right N₀ N₁) rest hrest
    intro hmem
    exact hb (hsub rest (by
      show T (s ++ [b] ++ rest)
      rw [List.append_assoc]
      exact hmem))

/-! ### Boundedness as a bit

`LLPO` consumes `Nat → Bool`, so the boundedness of a subtree has to BE a bit
rather than merely be decidable. `allStrings` is what makes that possible: the
quantifier every string of length `n` has left the tree ranges over a finite
list, so `List.all` decides it with no principle and no `Decidable` instance --
so the `Bool` carrier is the one to work over.
-/

/-- The bit that fires when the tree below `s` is empty at level `n`. -/
def boundedBit (T : List Bool → Bool) (s : List Bool) (n : Nat) : Bool :=
  (allStrings n).all (fun t => !(T (s ++ t)))

/-- The bit fires exactly when the level is empty. -/
theorem boundedBit_eq_true_iff (T : List Bool → Bool) (s : List Bool) (n : Nat) :
    boundedBit T s n = true ↔
      ∀ u : List Bool, u.length = n → T (s ++ u) = false := by
  constructor
  · intro h u hu
    have hmem := mem_allStrings_of_length n u hu
    have := List.all_eq_true.mp h u hmem
    cases hb : T (s ++ u)
    · rfl
    · rw [hb] at this; exact absurd this (by simp)
  · intro h
    refine List.all_eq_true.mpr (fun t ht => ?_)
    rw [h t (length_of_mem_allStrings n t ht)]
    rfl

/-- Boundedness is exactly the bit firing somewhere. -/
theorem isBounded_iff_exists_boundedBit (T : List Bool → Bool) (s : List Bool) :
    IsBounded (subTree (fun v => T v = true) s) ↔ ∃ n, boundedBit T s n = true := by
  constructor
  · intro ⟨N, hN⟩
    refine ⟨N, (boundedBit_eq_true_iff T s N).mpr (fun u hu => ?_)⟩
    cases hb : T (s ++ u)
    · rfl
    · exact absurd hb (hN u hu)
  · intro ⟨n, hn⟩
    refine ⟨n, fun u hu hmem => ?_⟩
    -- `hmem : subTree _ s u` is only DEFEQ to the equation; the rewrite needs
    -- it stated, since `rw` matches syntactically through no definitions.
    have hmem' : T (s ++ u) = true := hmem
    rw [(boundedBit_eq_true_iff T s n).mp hn u hu] at hmem'
    exact Bool.noConfusion hmem'

/-- The `LLPO` step: an unbounded node has an unbounded child.

`isBounded_of_children` says both children bounded makes the node bounded, so
an unbounded node cannot have both bounded -- and cannot have both is exactly
the hypothesis `LLPO` takes, once boundedness is the bit `boundedBit` makes it.

This is the half of the open converse that is NOT open: the step costs `LLPO`
and nothing more. What remains is iterating it `omega` times, which is the
`BinaryDC` half. -/
theorem exists_unbounded_child_of_llpo (hllpo : LLPO) {T : List Bool → Bool}
    (hT : IsTree (fun v => T v = true)) (s : List Bool)
    (hs : ¬ IsBounded (subTree (fun v => T v = true) s)) :
    ¬ IsBounded (subTree (fun v => T v = true) (s ++ [false])) ∨
      ¬ IsBounded (subTree (fun v => T v = true) (s ++ [true])) := by
  have hnot : ¬ ((∃ n, boundedBit T (s ++ [false]) n = true) ∧
      (∃ n, boundedBit T (s ++ [true]) n = true)) := by
    intro ⟨h0, h1⟩
    exact hs (isBounded_of_children hT s
      ((isBounded_iff_exists_boundedBit T _).mpr h0)
      ((isBounded_iff_exists_boundedBit T _).mpr h1))
  rcases hllpo _ _ hnot with h | h
  · exact Or.inl (fun hb => by
      obtain ⟨n, hn⟩ := (isBounded_iff_exists_boundedBit T _).mp hb
      rw [h n] at hn
      exact Bool.noConfusion hn)
  · exact Or.inr (fun hb => by
      obtain ⟨n, hn⟩ := (isBounded_iff_exists_boundedBit T _).mp hb
      rw [h n] at hn
      exact Bool.noConfusion hn)

/-! ### Iterating the step into a path

`BinaryDC` is dependent choice down a binary tree, but it indexes its
predicates by `tnum c n` -- the TERNARY numeral of `Ternary.lean`'s walk -- and
nothing decodes that back to a node. `TreeDC` below is the same
principle with the path itself as the index, which is a change of coordinates
and not of strength: no new lattice node is claimed, and showing the two
forms interderivable is what a base-three decoder would be for.

Restricted to the nodes a predicate holds at, as `DCOn` is to a set: the step
`exists_unbounded_child_of_llpo` is total on the UNBOUNDED nodes and nowhere
else, so a principle demanding totality everywhere could not consume it.
-/

/-- Dependent choice down a binary tree, with the path as the index and
totality asked only where the predicate holds.

This is DC∨, unrestricted in the assertion class. Berger, Ishihara and
Schuster, *The Weak Kőnig Lemma, Brouwer's Fan Theorem, De Morgan's Law, and
Dependent Choice*, Reports on Mathematical Logic 47 (2012) 63--86, §2,
verbatim:

    DC∨   ∀u (A₀(u) ∨ A₁(u)) ⇒ ∃α ∀n A_{α(n)}(ᾱn)

with `u` over `{0,1}*` and `ᾱn` the length-`n` prefix; `Γ-DC∨` is DC∨ for
assertions `A₀`, `A₁` in a class `Γ`. The notation is Ishihara's,
Constructive reverse mathematics: compactness properties, Oxford Logic
Guides 48 (2005) 245--267, §16.5.

Take `Aᵢ u := P (u ++ [i])`. Their `A_{α(n)}(ᾱn)` is then `P (ᾱn ++ [α n])`,
which is `P (ᾱ(n+1))`, and `P []` supplies the base --- so the conclusions
coincide. TWO DIFFERENCES REMAIN, and both make this the stronger statement:

    CLASS        theirs is used at `Γ = Π⁰₁`, the simply universal assertions.
                 `P : List Bool → Prop` here carries no restriction at all,
                 so `Π⁰₁-DC∨` is an instance of this and not the other way
                 round.
    RELATIVISED  theirs demands the disjunction at EVERY `u`; this asks it
                 only where `P` already holds, so it applies under a weaker
                 premise. The shape is not an invention --- the proof of their
                 Theorem 26 passes through `∀u (u ∈ S ⇒ u0 ∈ S ∨ u1 ∈ S)`.

Their Corollary 28 is `WKL ⇔ LLPO + Π⁰₁-DC∨`. `wklBool_of_llpo_treeDC` below
is Theorem 27, the direction that builds `WKL`; Theorem 26, `WKL ⇒ Π⁰₁-DC∨`,
is not in this tree and is what would close the equivalence. -/
def TreeDC : Prop :=
  ∀ P : List Bool → Prop, P [] →
    (∀ s, P s → P (s ++ [false]) ∨ P (s ++ [true])) →
    ∃ α : Nat → Bool, ∀ n, P (take α n)

/-- An unbounded subtree sits at a node of the tree. At level zero the only
string is the empty one, so a node outside the tree has an empty subtree. -/
theorem mem_of_not_isBounded_subTree {T : List Bool → Bool} {s : List Bool}
    (h : ¬ IsBounded (subTree (fun v => T v = true) s)) : T s = true := by
  cases hb : T s
  · exact absurd ⟨0, fun u hu hmem => by
      have : u = [] := List.eq_nil_of_length_eq_zero hu
      subst this
      have h' : T (s ++ []) = true := hmem
      rw [List.append_nil, hb] at h'
      exact Bool.noConfusion h'⟩ h
  · rfl

/-- Weak König's lemma over a `Bool`-given tree, from `LLPO` and a tree-shaped
dependent choice.

The two halves are exactly two gaps: `LLPO` supplies the STEP -- an unbounded
node has an unbounded child -- and `TreeDC` supplies the ITERATION. Neither is
about trees; the step needs the tree given as bits and the choice needs the
branch given as data. -/
theorem wklBool_of_llpo_treeDC (hllpo : LLPO) (htdc : TreeDC) : WKLBool := by
  intro T htree hinf
  obtain ⟨α, hα⟩ := htdc (fun s => ¬ IsBounded (subTree (fun v => T v = true) s))
    (not_isBounded_of_isInfiniteTree hinf)
    (fun s hs => exists_unbounded_child_of_llpo hllpo htree s hs)
  exact ⟨α, fun n => mem_of_not_isBounded_subTree (hα n)⟩


/-! ## `N∞`, and a set that is omniscient with no principle at all

`LPO` above is exactly `Nat` is omniscient: every `Bool` predicate on it
either fires somewhere or never does. That is a taboo. Pradic and Brown
(arXiv:1904.09193, §3) observe that a DIFFERENT infinite set is omniscient
outright, with no principle --- the non-increasing binary sequences --- and
that `CantorBernstein → EM` follows from it without smuggling `LPO` in. Their
§3 is reproduced here; the construction is Escardó's.
-/

/-- Two distinct equal-length bit strings first differ somewhere, explicitly.

The separation lemma is stated at a differing index; this produces the index,
along with the shared prefix and the two heads.

THE SIMP TACTICS ARE AVOIDED HERE. They close the head comparison and the
length contradictions, and the axiom print then comes back with
`Classical.choice`. Splitting on the two bits directly is choice-free, and it
keeps the recursion visibly decidable.

The conclusion is a DISJUNCTION over which side carries the true bit, because
the separation is directional: it bounds the false-headed value below the
true-headed one, and the hypotheses do not say which is which. -/
theorem exists_first_diff : ∀ u v : List Bool, u.length = v.length → u ≠ v →
    ∃ k, List.take k u = List.take k v ∧
      ((List.drop k u = false :: (List.drop k u).tail ∧
        List.drop k v = true :: (List.drop k v).tail) ∨
       (List.drop k u = true :: (List.drop k u).tail ∧
        List.drop k v = false :: (List.drop k v).tail))
  | [], [], _, hne => absurd rfl hne
  | [], _ :: _, hlen, _ => Nat.noConfusion hlen
  | _ :: _, [], hlen, _ => Nat.noConfusion hlen
  | a :: u', b :: v', hlen, hne => by
      have hlen' : u'.length = v'.length := Nat.succ.inj hlen
      cases a
      · cases b
        · -- both false: the heads agree, recurse
          have hne' : u' ≠ v' := fun h => hne (by rw [h])
          obtain ⟨k, hpre, hheads⟩ := exists_first_diff u' v' hlen' hne'
          exact ⟨k + 1, by
            show false :: List.take k u' = false :: List.take k v'
            rw [hpre], hheads⟩
        · exact ⟨0, rfl, Or.inl ⟨rfl, rfl⟩⟩
      · cases b
        · exact ⟨0, rfl, Or.inr ⟨rfl, rfl⟩⟩
        · have hne' : u' ≠ v' := fun h => hne (by rw [h])
          obtain ⟨k, hpre, hheads⟩ := exists_first_diff u' v' hlen' hne'
          exact ⟨k + 1, by
            show true :: List.take k u' = true :: List.take k v'
            rw [hpre], hheads⟩

#print axioms Constructive.exists_first_diff


/-! ### The row is collection minus a bound

NOT REGISTERED AS LATTICE NODES. `CollectionNat` is a `Prop` and could be one;
it would carry one outgoing edge and nothing incoming, so what implies this
would move rather than close. `UnitLowerBound`'s registry entry names that
failure in its own words. -/

#print axioms not_exists_true
#print axioms boolDigit_le_one
#print axioms boolDigit_eq_one_iff
#print axioms tnum_pos_iff
#print axioms tnum_eq_zero
#print axioms not_mem_of_prefix
#print axioms llpoTree_nil
#print axioms length_repeatBit
#print axioms head_repeatBit
#print axioms head_take
#print axioms pathAt_unbounded
#print axioms mem_consAll
#print axioms mem_consAll_of_mem
/-- The BD-N flag construction: `hat a n` marks the start of the `n`-th block,
once every earlier index has been given room `a i + 1`. -/
def hat (a : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => hat a n + 1 + a n

#print axioms hat

end Constructive
#print axioms Constructive.mem_allStrings_of_length
#print axioms Constructive.length_of_mem_allStrings
#print axioms Constructive.ubar_of_mem
#print axioms Constructive.ubar_of_children
#print axioms Constructive.take_fanSeq
#print axioms Constructive.not_ubar_fanBit
#print axioms Constructive.not_ubar_fanWalk
#print axioms Constructive.fanStable_of_decider
#print axioms Constructive.fanΔ_of_decider
#print axioms Constructive.subTree
#print axioms Constructive.isTree_subTree
#print axioms Constructive.isBounded_at_above
#print axioms Constructive.isBounded_of_children
#print axioms Constructive.boundedBit
#print axioms Constructive.boundedBit_eq_true_iff
#print axioms Constructive.isBounded_iff_exists_boundedBit
#print axioms Constructive.exists_unbounded_child_of_llpo
#print axioms Constructive.TreeDC
#print axioms Constructive.mem_of_not_isBounded_subTree
#print axioms Constructive.wklBool_of_llpo_treeDC
#print axioms Constructive.FANstable
#print axioms Constructive.fanΔ_of_fanStable

#print axioms Constructive.not_not_lpo_pointwise

namespace ZFSet
export Constructive (Extendable FANBool FANstable FANΔ HasPath IsBar IsBounded IsInfiniteTree IsTree IsUniformBar LLPO LPO MP PathSelection PathsDieOut Pseudobounded TernaryDecidable TernaryLLPO TernaryZeroDecidable TreeDC TreeReadout Ubar Unbounded WKL WKLBool WLPO allStrings barredBelow boolDigit boolDigit_eq_one_iff boolDigit_le_one boundedBit boundedBit_eq_true_iff consAll exists_unbounded_child_of_llpo extend fanBit fanSeq fanStable_of_decider fanStable_of_ubarDecider fanWalk fanΔ_of_decider fanΔ_of_fanStable fanΔ_of_ubarDecider fired_below_or_not forall_length_of_isUniformBar hasPath_of_readout head_repeatBit head_take isBounded_at_above isBounded_iff_exists_boundedBit isBounded_of_children isBounded_of_fanΔ isTree_subTree length_of_mem_allStrings length_repeatBit length_take llpoTree llpoTree_decidable llpoTree_infinite llpoTree_isTree llpoTree_nil llpo_of_llpoTree_path llpo_of_pathSelection llpo_of_ternary_llpo llpo_of_wkl llpo_of_wlpo lpo_of_ternary_decidable lpo_of_wlpo_of_mp mem_allStrings_of_length mem_consAll mem_consAll_of_mem mem_of_not_isBounded_subTree mem_of_unbounded mp_iff_sigma01_stable mp_of_lpo nnStable_forall not_exists_true not_isBounded_of_isInfiniteTree not_mem_of_prefix not_not_lpo_pointwise not_pathsDieOut_llpoTree not_ubar_fanBit not_ubar_fanWalk pathAt pathAt_unbounded repeatBit subTree take take_extend take_fanSeq take_pathAt ternary_decidable_of_lpo ternary_eq_zero_iff ternary_llpo_of_llpo ternary_zero_decidable_of_wlpo tnum_eq_zero tnum_pos_iff ubar_of_children ubar_of_mem unbarred wklBool_of_llpo_treeDC wlpo_of_lpo wlpo_of_ternary_zero_decidable zero_mem_ternary_iff)
end ZFSet
