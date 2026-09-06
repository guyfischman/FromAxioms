/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Power-basis independence mod `p` in `Z[zeta_p]`

    A in (natIn p)  ==>  every coordinate of A is divisible by p

THE QUOTIENT RING IS NOT NEEDED. Conrad reaches the independence by
exhibiting `Z[zeta]/(p)` as `(Z/(p))[X]/(X-1)^(p-1)` and reading it off the
presentation. That is how he SEES it, not what it requires. This tree already
had coordinate UNIQUENESS --- `cycCoord_inj_below` (`Integral.lean`),
which IS independence over `Z` --- so the only missing ingredient was LINEARITY,
and only for a CONSTANT multiple.

WHY A CONSTANT AND NOT A GENERAL PRODUCT. `cycCoord` reads the unique
BELOW-DEGREE representative (`cycRep_spec`). Multiplying by a constant scales
coefficients and cannot raise the degree, so the scaled representative is still
below degree and `rep_below_unique` pins it --- no reduction mod `cycShiftPoly`
happens. For a general product the reduction DOES happen and the coefficients
do not survive. That asymmetry makes this a step rather than a subtower, and it
is why nothing here generalises to multiplicativity.

Three rungs, bottom-up: coefficient scaling, coordinate scaling, then the
independence at `c = natIn p` via `cycConst_natIn`.

WHICH BASIS `cycCoord` IS ABOUT, AND IT IS NOT THE ONE THE NAME SUGGESTS.
`cycRep_cycZetaPow` (`Cyclotomic.lean`) says the representative of
`zeta^j` is `(X + 1)^j`, not `X^j` --- this presentation has `zeta = X + 1`,
because `cycShiftPoly` is the SHIFTED cyclotomic polynomial. So `cycCoord p A i`
is `A`'s coordinate against `1, X, X^2, ..., X^(p-2)`, which is the
`(zeta - 1)`-power basis, i.e. the `lambda`-adic one up to sign --- NOT the
`zeta`-power basis `1, zeta, ..., zeta^(p-2)` that Conrad's independence names.

That does not weaken the theorem: divisibility of all coordinates by `p` is
basis-independent whenever the change of basis is integral both ways, and here
it is triangular with unit diagonal. But a caller refuting a congruence written
in POWERS OF ZETA has to convert, and reading `cycCoord` as a zeta-coordinate
is a live way to get a wrong lemma past every check.
-/
import FromAxioms.SetTheory.ZFSet

namespace Analysis

universe u

/-! ## FEEDING THE GENERAL FORM AN EXPLICIT SUM

THE `foldF` HAS A LEADING IDENTITY: `foldF op e f 0` is `e`, so `foldF f 4`
is `(((e + f 0) + f 1) + f 2) + f 3` and not the four-term nest. Stripping it is
one `left_id`, and it is the only content in the adapter.
-/

/-- The coefficient family for four explicit terms. -/
noncomputable def four (c0 c1 c2 c3 : ZFSet.{u}) : Nat → ZFSet.{u} :=
  fun k => if k = 0 then c0 else if k = 1 then c1 else if k = 2 then c2 else c3

#print axioms four
end Analysis
