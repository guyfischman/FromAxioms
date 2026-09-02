/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Congruences, and the Chinese remainder theorem

The first step of the arithmetic that discharges the incompleteness hypotheses
(QUEUE: representability). Gödel's β-function codes a finite sequence as a pair
of numbers, and it works because the moduli it uses are pairwise coprime and the
remainder theorem then recovers each entry.

`Prime.lean` has Bézout in its Nat form -- a disjunction, because which side
carries the coefficient flips with each Euclidean step -- and everything here is
built from it. Nothing is decided that is not computed: `%` is a function, and
congruence is an equation between its values.

The Nat-only presentation costs one thing and buys another. It costs the
inverse: `a·m ≡ 1 (mod n)` has to be extracted from both branches of Bézout, and
the second branch gives `-1` where the first gives `1`, which in `Nat` means
multiplying by `n - 1` rather than negating. It buys freedom from a subtraction
that would have to be justified, and from the integers entirely -- `Integer.lean`
exists, but the β-function is about `Nat`, and moving through `ℤ` would mean
transporting every statement back.
-/


namespace NumberTheory

/-! ## The β-function's moduli

Gödel codes a finite sequence by a pair `(a, b)`, reading entry `i` as
`a % (1 + (i+1)·b)`. The construction works because those moduli are pairwise
coprime whenever `b` is divisible by every difference of indices -- which a
factorial supplies -- and because the remainder theorem then solves all the
congruences at once. -/

def betaMod (b i : Nat) : Nat := 1 + (i + 1) * b

/-! ## Gödel's β-function

A pair of numbers codes any finite sequence, so a theory with only `+` and `×`
can talk about recursion: a primitive recursive definition is a statement about
a sequence, and a sequence is a pair.

Two conditions have to hold at once, and the factorial supplies both. The gaps
between indices must divide `b`, which makes the moduli coprime; and every entry
must be smaller than its modulus, so that reducing it changes nothing. Taking
`b = fact m` for an `m` bounding both the length and every entry does it. -/

def beta (a b i : Nat) : Nat := a % betaMod b i

end NumberTheory

namespace ZFSet
export NumberTheory (beta betaMod)
end ZFSet
