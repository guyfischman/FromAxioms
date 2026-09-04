/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Gödel's first incompleteness theorem

The theorem, with its two arithmetical prerequisites carried as hypotheses
rather than built first: a provability predicate adequate for
the theory, and a fixed point -- a sentence the theory proves equivalent to
its own unprovability. Everything else is proved here.

Both halves are constructive, and they are constructive for different reasons.

`G` is not provable is pure syntax. If the theory proves `G` then adequacy
makes it prove that it proves `G`, and the fixed point makes it prove the negation of
that, so it proves `⊥`. Three uses of implication elimination; the audit line is
empty.

`¬G` is not provable goes through the model. The theory's theorems are true
in `ω`, and `G` is unprovable by the first half, so -- given that `ω` reads the
predicate correctly -- `ω` satisfies `G`. A theory that proved `¬G` would make `ω`
satisfy `¬G` too. No excluded middle appears: the negation is used, never
eliminated, which is exactly why the ω-consistency argument of the textbook
proof is not needed for this direction.

The theorem here is conditional; the instance for Q is not. What this file
proves is the argument, from a provability predicate that is adequate and read
correctly, and a fixed point. `Provability.lean` discharges all three for Q and
states `godel_first_Q_unconditional`.

Keeping the conditional form is not vestigial. `provability_defines` below shows
that `Adequate` and `ReadsProvability` together force `P` to define `T`'s own
theorem set inside `ω`, which is what says the hypotheses are the work rather
than a way around it -- and the argument applies to any theory meeting them, not
only to Q.

The calculus is intuitionistic. `DerivesFO` has `fls_elim` and no
double-negation elimination, so "incomplete" here means incomplete for
intuitionistic first-order logic. The diagonal argument does not care, but a
reader who assumes the classical calculus is assuming something this development
does not yet provide.
-/

import FromAxioms.Metamath.Godel
import FromAxioms.Metamath.Robinson

universe u

namespace Metamath

/-- Naming a formula inside the language: its code, as a numeral. -/
def quote (φ : Formula) : Term := numeral (encode φ)

/-- Applying a one-variable formula to a name. -/
def atName (P : Formula) (φ : Formula) : Formula := subst (single (quote φ)) P

/-- A provability predicate adequate for `T`: whenever `T` proves `φ`, it
proves that it proves `φ`.

This is the first of the two hypotheses. Discharging it means exhibiting a
formula whose satisfaction in `ω` tracks the existence of a derivation, which is
what arithmetising `DerivesFO` would give. -/
def Adequate (T : List Formula) (P : Formula) : Prop :=
  ∀ φ, DerivesFO T φ → DerivesFO T (atName P φ)

/-- A fixed point for `P`: a sentence the theory proves equivalent to its
own `P`-unprovability. The second hypothesis, and the one representability
supplies.

Stated as two implications rather than as `Iff`, because the object language has
no biconditional and the two directions are used separately -- the first half of
the theorem needs only `forward`. -/
structure FixedPoint (T : List Formula) (P : Formula) where
  sentence : Formula
  forward : DerivesFO T (.imp sentence (fnot (atName P sentence)))
  backward : DerivesFO T (.imp (fnot (atName P sentence)) sentence)

/-! ## Q is one of the theories the theorem speaks about

Only the soundness hypothesis is discharged here, and it is the one the model
work already paid for. `Adequate` and `FixedPoint` remain open, and what they
need is representability. -/

/-- The Hilbert-Bernays-Löb derivability conditions. What a provability
predicate must satisfy for the second incompleteness theorem, as against the
first, which needs only the first condition and a fixed point.

Each is a claim that the object theory proves something, so none mentions a
model -- and none is available for `QCtx`, which has no induction and so cannot
prove a universally quantified statement about codes. They are
hypotheses for the same reason `Adequate` is: the argument is worth having
separately from any theory that discharges them. -/
structure Derivability (T : List Formula) (P : Formula) : Prop where
  /-- What `Adequate` says: the theory proves what it proves. -/
  d1 : ∀ φ, DerivesFO T φ → DerivesFO T (atName P φ)
  /-- Formalised Sigma-1 completeness: the theory proves `d1` of itself. -/
  d2 : ∀ φ, DerivesFO T (.imp (atName P φ) (atName P (atName P φ)))
  /-- The theory proves its own provability closed under modus ponens. -/
  d3 : ∀ φ ψ, DerivesFO T
    (.imp (atName P (.imp φ ψ)) (.imp (atName P φ) (atName P ψ)))

end Metamath

namespace ZFSet
export Metamath (Adequate Derivability FixedPoint atName quote)
end ZFSet
