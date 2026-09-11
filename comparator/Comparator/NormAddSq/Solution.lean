/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`.

THIS ROW IS WHY THE PAIR EXISTS. Its parity claim was `audited` on
`Analysis.innerProduct_add_self`, over `IsInnerProduct`, whose every argument is
a `ZFSet` -- so it could not be applied to `F : Type*` at all, and the row was
recorded as at-parity for weeks. Writing this file is what moved it to
`narrower`; landing `Analysis.isInnerFormT_add_self` is what closes it.

WHAT COMES FROM THE TOWER:

    Analysis.isInnerFormT_add_self :
      IsInnerFormT vadd add form →
        form (vadd x y) (vadd x y)
          = add (add (form x x) (form x y)) (add (form x y) (form y y))

over ARBITRARY Lean types `V` and `R`, with `add` a bare binary operation --- no
ring, no module, no order, and no axioms at all (`#print axioms` reports none).

WHAT MATHLIB SUPPLIES: `real_inner_comm` and `inner_add_left` to satisfy the two
hypotheses, `real_inner_self_eq_norm_sq` to turn norms into inner products, and
`ring` to regroup four terms into `a + 2b + c`. The tower's statement keeps the
four-term shape because a scalar `2` needs a ring it does not assume.
-/
import Comparator.NormAddSq.Challenge
import FromAxioms

namespace Comparator.NormAddSq

open Analysis

theorem solution : challenge := by
  intro F _ _ x y
  -- The two clauses, at mathlib's carrier.
  have hI : IsInnerFormT (fun a b : F => a + b) (fun r s : ℝ => r + s)
      (fun a b : F => inner ℝ a b) :=
    -- `real_inner_comm u w : inner R w u = inner R u w`, the other orientation,
    -- so it is applied swapped rather than `.symm`-ed. `inner_add_left` takes
    -- THREE vectors and no field argument (`Defs.lean:233`); passing `R` made
    -- Lean read `u` as the implicit type.
    { symm := fun u w => real_inner_comm w u
      add_left := fun u u' w => inner_add_left u u' w }
  have hexp := isInnerFormT_add_self hI x y
  simp only at hexp
  -- Norms to inner products, both sides.
  have hx : ‖x‖ ^ 2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
  have hy : ‖y‖ ^ 2 = inner ℝ y y := (real_inner_self_eq_norm_sq y).symm
  have hxy : ‖x + y‖ ^ 2 = inner ℝ (x + y) (x + y) :=
    (real_inner_self_eq_norm_sq (x + y)).symm
  rw [hxy, hx, hy, hexp]
  ring

end Comparator.NormAddSq
