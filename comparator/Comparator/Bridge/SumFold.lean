/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
A FINITE SUM, AS A FOLD ON THE ENCODED CARRIER.

The bottom rung under the Eisenstein Solution's last obligation. To use
`eisenstein_irreducibleI` on a factorisation, the transport has to be
MULTIPLICATIVE --- `polyOf (p * q)` must be the tower's `polyMul` of the two
transports --- and the tower computes a product coefficient as

    convCoeff R add mul zero f g k
      = foldF add zero (fun i => f_i · g_{k-i}) (k + 1)

while mathlib computes it as a `Finset` sum. So before any polynomial statement
there is an arithmetic one: an encoded finite sum IS a fold.

IT IS THE SAME RECURSION ON BOTH SIDES, so this is short:

    foldF op e F 0        = e                     Finset.sum_range_zero
    foldF op e F (k + 1)  = opAt op (fold k) (F k) Finset.sum_range_succ

so the induction is one step with `opAt_opSet` turning the ZFSet operation back
into `α`'s own. Nothing here mentions polynomials, ideals or Eisenstein --- it is
a fact about `encode` and addition, and it is stated for an arbitrary
`F : Nat → α` so that the product case is an instance rather than a repetition.

WHY THE GENERAL FORM RATHER THAN THE ONE USE. The convolution needs it at
`fun i => p.coeff i * q.coeff (k - i)`, but the same lemma is what any future
row transporting a sum will want, and specialising it to the convolution would
hide that behind a name mentioning polynomials.
-/
import Comparator.Bridge.RingTransfer
import Mathlib.Algebra.BigOperators.Intervals

open SetTheory NumberTheory Algebra Comparator.TypeTransfer Comparator.RingTransfer
open scoped Classical

namespace Comparator.SumFold

variable {α : Type} [CommRing α]

/-- An encoded finite sum is a fold on the encoded carrier. One induction;
each step is `opAt_opSet`. -/
theorem encode_sum_eq_foldF (F : Nat → α) :
    ∀ n : Nat,
      encode (∑ i ∈ Finset.range n, F i)
        = foldF (opSet (α := α) (· + ·)) (encode (0 : α))
            (fun i => encode (F i)) n
  | 0 => by rw [Finset.sum_range_zero]; rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, show
      foldF (opSet (α := α) (· + ·)) (encode (0 : α)) (fun i => encode (F i)) (n + 1)
        = opAt (opSet (α := α) (· + ·))
            (foldF (opSet (α := α) (· + ·)) (encode (0 : α))
              (fun i => encode (F i)) n)
            (encode (F n)) from rfl,
      ← encode_sum_eq_foldF F n, opAt_opSet]

/-- The form the convolution uses: the fold the tower computes agrees with the
sum mathlib computes, at every length. -/
theorem foldF_eq_encode_sum (F : Nat → α) (n : Nat) :
    foldF (opSet (α := α) (· + ·)) (encode (0 : α)) (fun i => encode (F i)) n
      = encode (∑ i ∈ Finset.range n, F i) :=
  (encode_sum_eq_foldF F n).symm

#print axioms encode_sum_eq_foldF
#print axioms foldF_eq_encode_sum

end Comparator.SumFold
