/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Polynomials over a domain.

`R[x]` is an integral domain when `R` is one, its vanishing is decided when
`R`'s is, and it cancels.  These are facts about `R[x]`, not about
`Frac(R[x])`, and they live here rather than in `RatFunc.lean` because two
files need them and those two cannot see each other: `IsIntegralDomain` and
`IsCancellative` are declared in `Fraction.lean`, which is absent from
`PolyRing.lean`'s import closure but present in both `Integral.lean`'s and
`RatFunc.lean`'s -- and Integral and RatFunc are incomparable.

So this file is exactly `PolyRing.lean` together with `Fraction.lean`, and it
sits below both consumers.  It was carved out of `RatFunc.lean` once the
rational function field and the Gauss descent turned out to want the same
lemmas from opposite sides of that gap.
-/

import FromAxioms.Algebra.PolyRing

universe u

open NumberTheory SetTheory
namespace Algebra

/-! ## Polynomials over a domain

`isField_frac` wants `R[x]` to be a cancellative integral domain. Both
properties route through the degree, and extracting a degree is
equivalent to `DecidableVanishing R` -- `exists_deg_iff` proves both
directions -- so the rational function field costs a decidability the
fraction field of `R` does not. That cost is pinned, not
assumed, and it is why a decidability hypothesis appears below and not
in `Fraction.lean`.

Note what that decidability is not spent on. The product of two nonzero leading
coefficients is nonzero by the negative form alone, which the domain
already supplies; the decidability is spent one step earlier, on locating
the leading coefficient at all. -/

/-- A polynomial that is not the zero polynomial has a top index, once
vanishing is decided. -/
theorem exists_top_of_ne_polyZero {R add mul zero one p : ZFSet.{u}}
    (hR : IsRing R add mul zero one) (hdec : DecidableVanishing R zero)
    (hp : IsPolyOver R zero p) (hne : p ≠ polyZero R zero) :
    ∃ d : Nat, app p (ofNat.{u} d) ≠ zero
      ∧ ∀ i : Nat, d < i → app p (ofNat.{u} i) = zero := by
  obtain ⟨N, hN⟩ := hp.right.right.right
  rcases exists_lead hR hdec hp N hN with h | ⟨d, -, hdne, hdz⟩
  · exact absurd h hne
  · exact ⟨d, hdne, hdz⟩

end Algebra

#print axioms Algebra.exists_top_of_ne_polyZero
namespace ZFSet
export Algebra (exists_top_of_ne_polyZero)
end ZFSet
