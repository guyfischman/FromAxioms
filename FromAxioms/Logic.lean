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
imports both. They cannot coexist: this file declares `And`, `Or`, `Eq` and
friends at top level, and so does Lean's `Init`, so importing it from a
non-`prelude` module fails outright with

  environment already contains 'And.rec' from Init.Prelude

This development shows what is under the notation; the rest of the library
uses Lean's identical copies of the same definitions.
-/
prelude
import FromAxioms.Logic.Connectives
import FromAxioms.Logic.Equality
import FromAxioms.Logic.Quantifiers
import FromAxioms.Logic.Classical
import FromAxioms.Logic.Reverse
