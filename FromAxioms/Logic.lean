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

This module and `FromAxioms.Foundations` are deliberately separate roots, and
nothing imports both. They cannot coexist: Phase 1 declares `And`, `Or`, `Eq`
and friends at top level, and so does Lean's `Init`, so importing this from a
non-`prelude` module fails outright with

  environment already contains 'And.rec' from Init.Prelude

That is not a defect. Phase 1 exists to show what is under the notation; Phase 2
uses Lean's identical-but-better-equipped copies of the very same definitions.
-/
prelude
import FromAxioms.Logic.Connectives
import FromAxioms.Logic.Equality
import FromAxioms.Logic.Quantifiers
