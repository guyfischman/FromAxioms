/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Phase 1 root: logic from nothing.

`prelude`, so this development imports nothing at all. It reconstructs the
propositional connectives, equality, and the quantifiers from inductive types
and the dependent arrow, then declares the classical axioms explicitly.

This module is a separate root from the rest of the library, and nothing
imports both. They cannot coexist: it declares `And`, `Or`, `Eq` and friends at
top level, and so does Lean's `Init`, so importing it from a non-`prelude`
module fails outright with

  environment already contains 'And.rec' from Init.Prelude

So no theorem can mention both, and the correspondence between them is not
proved anywhere: it cannot be stated. The two agree in shape -- a single
constructor taking a proof of each side -- and differ in presentation, Lean's
`And` being a structure with `left` and `right` projections where this one is
an inductive with only its recursor.

What is established here is that the connectives cost nothing. They are
inductive types and the dependent arrow, and the audit reports no axioms for
any of them. Lean's are the same constructions and are likewise axiom-free,
so the rest of the library uses those and inherits the result rather than
assuming it -- along with `simp`, `rw` and `omega`, which are built on
`Init`'s own `Eq` and `Nat` and which nothing in this development uses.
-/
prelude
import FromAxioms.Logic.Connectives
import FromAxioms.Logic.Equality
import FromAxioms.Logic.Quantifiers
import FromAxioms.Logic.Classical
import FromAxioms.Logic.Reverse
