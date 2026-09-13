/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Hilbert's axioms, as a second presentation.

`GeomPlane.lean` and `GeomIncidence.lean` build one geometry: points are pairs
of located reals and every statement is an equation between coordinates. This
file states the axioms over primitives -- a set of points, a set of lines, an
incidence relation -- so that the coordinate plane becomes a model rather
than the subject, and the two presentations can be priced against each other.

The groups are kept separate, as Hilbert wrote them, because that separation is
what makes the pricing possible: a theorem provable from incidence alone costs
whatever incidence costs, and the continuity axioms -- the ones Euclid needed
and the coordinate plane gets free from `RealL` -- are the ones a reversal will
find.

Distinctness is a parameter. Hilbert says "two distinct points"; read
classically that is `A ≠ B`, and read constructively it is apartness. The
axioms below take the relation as an argument rather than choosing, because the
choice has a price: the plane satisfies the apartness reading for free and the
not-equal reading at the cost of `MP`.
-/

import FromAxioms.SetTheory.ZFSet

universe u

namespace Geometry

/-! ## The axioms, over primitives -/

/-- Hilbert's first group, incidence, over a set of points, a set of lines,
an incidence relation and a reading of "distinct".

This is where axiomatic geometry enters the development: the group is stated
over primitives rather than over the coordinate plane, so a model has to be
supplied and the axioms are not true by construction. -/
structure HilbertIncidence (Pt Ln : ZFSet.{u}) (On : ZFSet.{u} → ZFSet.{u} → Prop)
    (Apart : ZFSet.{u} → ZFSet.{u} → Prop) : Prop where
  /-- I.1: two distinct points lie on a line. -/
  line_of_apart : ∀ A, A ∈ Pt → ∀ B, B ∈ Pt → Apart A B →
    ∃ l, l ∈ Ln ∧ On A l ∧ On B l
  /-- I.2: and on at most one. -/
  unique_line : ∀ A, A ∈ Pt → ∀ B, B ∈ Pt → Apart A B →
    ∀ l, l ∈ Ln → ∀ m, m ∈ Ln → On A l → On B l → On A m → On B m → l = m
  /-- I.3a: every line carries two distinct points. -/
  two_on_line : ∀ l, l ∈ Ln → ∃ A, A ∈ Pt ∧ ∃ B, B ∈ Pt ∧ Apart A B ∧ On A l ∧ On B l
  /-- I.3b: and not everything is on one line. -/
  three_off_line : ∃ A, A ∈ Pt ∧ ∃ B, B ∈ Pt ∧ ∃ C, C ∈ Pt ∧
    ∀ l, l ∈ Ln → ¬ (On A l ∧ On B l ∧ On C l)

end Geometry

#print axioms Geometry.HilbertIncidence
namespace ZFSet
export Geometry (HilbertIncidence)
end ZFSet
