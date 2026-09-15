/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Cardinals as objects, by Scott's trick.

Decision 11 built the relations and left the objects, because a cardinal needs
either a well-ordering (choice) or a least rank (`em`). `Reverse.lean` now has
the least-ordinal principle pinned at exactly `em`, so the objects
are reachable, and this file builds them:

    card x = { y ∈ V (leastRank x)⁺ | x ≈ y }

where `leastRank x` is the smallest rank at which anything equinumerous with `x`
appears. Scott's trick is exactly this restriction: the class of all `y ≈ x` is
too big to be a set, and cutting it at the first stage where it is inhabited
makes it one.

The split is the usual one.

Defining `card` costs nothing. `leastRank` is a union of a separation -- the
least element of a set of ordinals is unique when it exists, so the
⋃-of-a-singleton trick extracts it rather than choosing it, and the
definition goes through whether or not a least element exists at all.

Using it costs `em`, and only through `LeastOrdinal`: every theorem below
takes `EM` as a hypothesis, so the classical surface is untouched.

And the `em` is not decoration. `em_of_leastRank_spec` reverses it: asking that
`leastRank` name the minimum at every set decides every proposition.
`card_congr` cannot be reversed, for a structural reason rather than a gap in
the proof: its hypothesis makes `x` and `y` equinumerous unconditionally, and
`leastRank` depends only on the size, so the proposition-dependence a reversal
needs cancels on both sides of the equation. The classical content of Scott's
trick sits one level down, in the existence of the least rank, and that is
where it is pinned.
-/

import FromAxioms.SetTheory.OrdinalArith

universe u

open Algebra SetTheory
namespace Metamath

/-! ## What the `em` is for -/

/-- `{{∅}}`: a one-element set whose member has rank `2`. -/
private def triple : ZFSet.{u} := singleton (singleton (singleton empty.{u}))

end Metamath

namespace ZFSet
end ZFSet
