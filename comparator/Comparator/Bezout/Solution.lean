/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`.

    NumberTheory.bezout_int (x y : Nat) :
      ∃ u v : Int, (Nat.gcd x y : Int) = (x : Int) * u + (y : Int) * v

is the challenge, verbatim. Both sides are over Lean's `Nat` and `Int` and both
use core's `Nat.gcd`, so there is nothing to bridge and nothing to transfer ---
the same objects, named the same way.

`Nat.gcd_eq_gcd_ab` is not cited.
-/
import Comparator.Bezout.Challenge
import FromAxioms

namespace Comparator.Bezout

theorem solution : challenge :=
  fun x y => NumberTheory.bezout_int x y

end Comparator.Bezout
