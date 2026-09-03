/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Arithmetising syntax

Incompleteness needs a theory to talk about its own sentences, and the first
step is the one Gödel had to invent: a formula is a number. `FirstOrder.lean`
gives the syntax as an ordinary inductive type, so the numbering is a pairing
function and an induction -- and `NatPair.lean` already has the pairing, built
for the anti-diagonal walk and reused here without change.

What matters here is injectivity: distinct formulas have distinct codes, so
a number is a formula. It follows from injectivity of the pairing and an
induction over the syntax, with the tag separating the constructors.

A decoder -- reading an arbitrary number back as a formula -- is the next
step and a different kind of work: the recursion is on the code rather than on
a term, so it needs `natUnpair`'s components to be provably smaller than what
they came from. That bound is not in `NatPair.lean` yet.

The tags are the shape of the term rather than an arbitrary assignment. A
formula is `tag :: payload` and the payload is whatever that tag needs, so the
decoder is a case split on the tag, so the proof is an induction rather than an
arithmetic argument.
-/

import FromAxioms.Core.NatPair
import FromAxioms.Core.NatSearch
import FromAxioms.Metamath.FirstOrder

universe u

open Core
namespace Metamath

/-! ### Terms

Two syntactic categories now, so every operation comes in three parts: a term,
a list of terms, and a formula. The shapes are identical -- tag, payload, `+ 1`
-- so the proofs stay uniform. -/

mutual

/-- A term as a number: `0` tags a variable, `1` a function symbol applied to a
coded list. -/
def encodeTerm : Term → Nat
  | .var n => natPair 0 n + 1
  | .func f ts => natPair 1 (natPair f (encodeTermList ts)) + 1

def encodeTermList : List Term → Nat
  | [] => 0
  | t :: ts => natPair (encodeTerm t) (encodeTermList ts) + 1

end

/-- The eight shapes of a formula, tagged by the shape and paired with whatever
that shape carries. The tag is what makes the injectivity proof a case split
rather than an arithmetic argument.

Every code is a successor, and that is not decoration: `natPair 0 1 = 1`, so
without the `+ 1` a formula's code could equal its own payload and a decoder
recursing on the code would not terminate. Shifting by one makes every part
strictly smaller than the whole. -/
def encode : Formula → Nat
  | .rel r ts => natPair 0 (natPair r (encodeTermList ts)) + 1
  | .eq a b => natPair 1 (natPair (encodeTerm a) (encodeTerm b)) + 1
  | .fls => natPair 2 0 + 1
  | .imp φ ψ => natPair 3 (natPair (encode φ) (encode ψ)) + 1
  | .conj φ ψ => natPair 4 (natPair (encode φ) (encode ψ)) + 1
  | .disj φ ψ => natPair 5 (natPair (encode φ) (encode ψ)) + 1
  | .all φ => natPair 6 (encode φ) + 1
  | .ex φ => natPair 7 (encode φ) + 1

end Metamath
namespace ZFSet
export Metamath (encode)
end ZFSet
