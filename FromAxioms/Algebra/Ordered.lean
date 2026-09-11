/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Ordered domains, and the order their fractions inherit

An order on a ring is given by its positive cone: a subset closed under
addition and multiplication, missing zero, and meeting every element or its
negation. That presentation is chosen because it is the one that transports
-- the cone of a fraction field is determined by the cone below it, and the
whole of this file is that transport plus its consequences.

The point of arriving here is that `NumberTheory.Rat` and `Real` are the library's only
ordered fields so far and both are archimedean, so nothing yet distinguishes
"ordered" from "archimedean". `RatFunc.lean` supplies a field that is
orderable and is not, and this file is what lets that be said.
-/

import FromAxioms.Constructive.Vanishing

set_option autoImplicit false

universe u

open Analysis NumberTheory SetTheory
namespace Algebra

/-! ## The positive cone -/

/-- A positive cone: the data of an order on a ring, as a subset. `total`
is the only clause with content -- the others say the cone is a
sub-semiring-without-zero, and `total` is what makes it an order rather
than a distinguished subset.

`total` is conditioned on `a ≠ zero`, and that is load-bearing. The
unconditional form -- `a ∈ pos ∨ a = zero ∨ -a ∈ pos` -- reaches a
decision that `a` is zero, and for a real that decision is `LPO` even in
the located encoding (`eq_zero_or_apart_of_lpo`). Conditioning it turns the
clause into the negative form, which is what a located real supplies. `NumberTheory.Int`
and `NumberTheory.Rat` satisfy either version, so the weaker one costs their instances
nothing and is the only one `Real` could ever meet. -/
structure IsPosCone (R add mul zero pos : ZFSet.{u}) : Prop where
  subset : pos ⊆ R
  ne_zero : ∀ a, a ∈ pos → a ≠ zero
  add_mem : ∀ a, a ∈ pos → ∀ b, b ∈ pos → opAt add a b ∈ pos
  mul_mem : ∀ a, a ∈ pos → ∀ b, b ∈ pos → opAt mul a b ∈ pos
  total : ∀ a, a ∈ R → a ≠ zero → a ∈ pos ∨ ringNeg R add zero a ∈ pos

/-! ## The located reals, ordered -- and what the order costs

What the order costs on each encoding. `Real` (Dedekind cuts) and `RealL`
(located pairs) are the same reals in two encodings, and they differ on
arithmetic: `x + (-x) = 0` and multiplication are classical for cuts and free
for located pairs.

The order splits too, and further apart. A cut has to decide the sign of a
nonzero real outright. A located pair needs only that a real distinct from zero
is apart from it -- the negative-to-disjunctive step, which is `MP` and sits
strictly below `em` in the lattice. So this is stated over the apartness
hypothesis rather than over a choice axiom, and the located cone audits at the
ambient two. -/

/-- A located real distinct from zero is apart from it. Exactly the
cone's `total` clause, and exactly the negative-to-disjunctive step: it is
`MP`, not `em`. Taken as a hypothesis so the theorems using it audit at the
ambient two. The geometry track proved the same step yields `MP` and is
having it registered as a lattice node; if that node's statement turns out
to be this one, this definition should take its name. -/
def NeApartZero : Prop :=
  ∀ x, x ∈ RealL.{u} → x ≠ realLZero.{u} → realLApart x realLZero.{u}

end Algebra
namespace ZFSet
export Algebra (IsPosCone NeApartZero)
end ZFSet
