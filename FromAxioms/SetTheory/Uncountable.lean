/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# ℝ is uncountable.

The diagonal is geometric rather than digitwise: walk down the thirds of `[0,1]`
so that stage `n` steps clear of the `n`-th real. The digit sequence of
`Ternary.lean` is exactly the record of which way each step went, and the real
it names is inside every interval, hence outside every `L n`.

The split this development keeps finding shows up here in its
sharpest form. Which third to take is a genuine decision, and locatedness
supplies it only as a disjunction:

    p < q  →  p ∈ L n  ∨  q ∈ U n

Reading that disjunction as a digit is defining data by cases, so it costs
`Classical.choice`. Everything else -- the walk, the interval, the proof that
the limit misses every `L n` -- is choice-free, and is stated here against a
locator: a digit sequence together with the promise that each digit steps
clear. `exists_missed` then buys the locator classically, once, and nothing
downstream pays again.

So the honest statement of the result is two-part: the diagonal is constructive
given the decisions, and the decisions are what excluded middle is for.
-/

import FromAxioms.Analysis.Ternary

universe u

open Analysis
namespace SetTheory

/-! ## What the decisions are worth

The locator is a dependent binary choice: the disjunction at stage `n` is
about the interval reached by the digits already taken. Naming that as a
principle turns the whole diagonal choice-free -- `exists_missed_of_binaryDC`
uses no axiom -- and leaves the classical content in one theorem, `binaryDC`,
which is a single `if`. -/

/-- Binary dependent choice: at each stage, a decision that may depend on the
digits already taken. -/
def BinaryDC : Prop := ∀ A B : Nat → Nat → Prop, (∀ k n, A k n ∨ B k n) →
  ∃ c : Nat → Nat, (∀ n, c n ≤ 1) ∧
    ∀ n, (c n = 0 ∧ A (tnum c n) n) ∨ (c n = 1 ∧ B (tnum c n) n)

end SetTheory

namespace ZFSet
export SetTheory (BinaryDC)
end ZFSet
