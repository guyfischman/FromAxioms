/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

import Mathlib.Topology.Order.IntermediateValue
-- `Topology.Order.IntermediateValue` states the theorem but does not define the
-- reals. The module path is version-dependent: at mathlib v4.24.0
-- `Topology/Instances/Real` is a directory whose only leaf is `Lemmas`, so
-- `import Mathlib.Topology.Instances.Real` is `bad import`.
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The challenge: the intermediate value theorem, in Mathlib's vocabulary

The statement below is Mathlib's, not ours: the typeclasses, `Set.Icc`,
`ContinuousOn`, the image, and the subset relation. A reader who trusts Mathlib
can read `challenge` and see what is claimed, without taking our word for any
translation.

## The statement, transcribed from source

`Mathlib/Topology/Order/IntermediateValue.lean:527`, in the resolved checkout at
`comparator/.lake/packages/mathlib`:

    /-- Intermediate Value Theorem for continuous functions on closed
        intervals, case `f a ≤ t ≤ f b`. -/
    theorem intermediate_value_Icc {a b : α} (hab : a ≤ b) {f : α → δ}
        (hf : ContinuousOn f (Icc a b)) :
        Icc (f a) (f b) ⊆ f '' Icc a b :=
      isPreconnected_Icc.intermediate_value (left_mem_Icc.2 hab)
        (right_mem_Icc.2 hab) hf

with the `variable` lines in scope at that point --- the section opened at 60
carrying `{X}` closes at 217, so those are not in scope:

    219  variable {α : Type u} [ConditionallyCompleteLinearOrder α]
                              [TopologicalSpace α] [OrderTopology α]
    348  variable [DenselyOrdered α] {a b : α}
    523  variable {δ : Type*} [LinearOrder δ] [TopologicalSpace δ]
                              [OrderClosedTopology δ]

## What `challenge` asks for, and why it is stated at `ℝ`

`intermediate_value_Icc` is polymorphic. A comparator has to be a closed
statement to be discharged, so this instantiates it at the concrete case our
tower actually proves something about: real-valued functions of a real variable.
`ℝ` satisfies every instance the theorem needs, and instantiating is not
weakening the claim being matched --- it is choosing which instance of it we
assert we can reach.

The tower's own form fixes `[0,1]` and demands a strict straddle;
`Solution.lean` closes both gaps, by an affine reparametrisation and a split on
`c`.
-/

namespace Comparator.IvtExact

/-- The challenge. Mathlib's intermediate value theorem at `ℝ`, in Mathlib's
own vocabulary.

`Solution.lean` must close this using the `FromAxioms` tower. Nothing in this
file may be changed to make that easier: the whole value of the pair is that this
half is not ours. -/
def challenge : Prop :=
  ∀ (a b : ℝ) (f : ℝ → ℝ), a ≤ b → ContinuousOn f (Set.Icc a b) →
    Set.Icc (f a) (f b) ⊆ f '' Set.Icc a b

/-- The challenge is not vacuous, and Mathlib itself is the witness.

A `Prop` nobody has shown inhabited says nothing. Proved by Mathlib, this
certifies that the statement above is the theorem being matched; it is not the
comparator. The comparator is `Solution.lean`, which must reach the same
statement from `FromAxioms` alone. -/
theorem challenge_is_mathlibs : challenge :=
  fun _ _ _ hab hf => intermediate_value_Icc hab hf

end Comparator.IvtExact
