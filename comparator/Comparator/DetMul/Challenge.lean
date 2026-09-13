/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The challenge: multiplicativity of the determinant, in MATHLIB's vocabulary

`Matrix`, `Matrix.det`, the `CommRing` class and the matrix `*` are all
Mathlib's. Every declaration below uses Mathlib's vocabulary alone, so a reader
who trusts only Mathlib can read `challenge` and know what is claimed, with no
translation of ours to check.

## The statement, transcribed from source and not from documentation

`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean:134`, in the pinned
checkout:

    @[simp]
    theorem det_mul (M N : Matrix n n R) : det (M * N) = det M * det N :=

with the file's `variable` lines supplying `{n : Type*} [DecidableEq n]
[Fintype n]` and `{R : Type v} [CommRing R]`.

READ FROM `.compare/mathlib4`, NOT FETCHED, for the reason `IvtExact/Challenge`
records at length: the fetch tool answers with a summarising model rather than
returning source, and gave three different readings of one theorem there.

## Why the index type is `Fin m` and the ring stays a variable

Mathlib's `n` is any `Fintype` with decidable equality. A comparator has to be
a CLOSED statement to be discharged, and the tower indexes matrices by `Nat`
below a bound, so `Fin m` is the instance it actually speaks about;
instantiating chooses which case is asserted rather than weakening the claim
being matched.

THE RING IS NOT INSTANTIATED, and that is the load-bearing choice. The
shape is `∀ (R : Type) [CommRing R]`, and the pair turns on it: the tower's
`Algebra.detN_mul` holds over an ARBITRARY `IsRing`, so pinning `R` to `ℤ` here
would test a special case of a general theorem and report it as parity. The
`TypeTransfer` encoding carries an arbitrary `R` across.

## The one gap, stated here rather than hidden

The tower's `detN_mul` carries `0 < n`; mathlib's `det_mul` holds at every size
including zero. `Solution.lean` discharges `m = 0` separately from
`Matrix.det_fin_zero`, where both determinants are `1` and the identity is
`1 = 1 * 1`. That is a case split, not a weakening: the challenge below is
discharged at mathlib's own generality.
-/

namespace Comparator.DetMul

/-- The challenge. Mathlib's `Matrix.det_mul` at `Fin m` over an arbitrary
commutative ring, in Mathlib's own vocabulary.

`Solution.lean` must close this using the `FromAxioms` tower. Nothing in this
file may be changed to make that easier: the whole value of the pair is that
this half is not ours. -/
def challenge : Prop :=
  ∀ (R : Type) [CommRing R] (m : Nat) (M N : Matrix (Fin m) (Fin m) R),
    (M * N).det = M.det * N.det

/-- The challenge is not vacuous, and Mathlib itself is the witness.

A `Prop` nobody has shown inhabited says nothing, and an axiom print cannot see
an empty statement. It is proved from Mathlib, which certifies that the
statement above is the theorem being matched. The comparison itself is
`Solution.lean`. -/
theorem challenge_is_mathlibs : challenge :=
  fun _R _ _m M N => Matrix.det_mul M N

end Comparator.DetMul
