/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
CHALLENGE: the recursion equation for addition on the naturals.

Mathlib's vocabulary only. `Nat.add_succ` is Lean core's

    theorem Nat.add_succ (n m : ℕ) : n + succ m = succ (n + m)

and mathlib inherits it rather than defining its own naturals.

THIS PAIR IS UNUSUAL. Mathlib's side is true by `rfl` on an inductive type, so
the challenge is trivially discharged there, and a Solution that also said
`rfl` would prove nothing about this tower.

WHAT MAKES THE PAIR REAL IS THE SOLUTION'S ROUTE, not the statement. The tower
defines addition on the von Neumann ordinals and proves
`add x (succ y) = succ (add x y)` by EXTENSIONALITY, for arbitrary `ZFSet`s and
not only on `omega`; `add_ofNat` then says that operation agrees with Lean's
through `ofNat`. The Solution goes that way round --- into the ordinals,
through the set-theoretic recursion, and back by injectivity of `ofNat` --- so
what is checked is that the tower's construction DISCHARGES Lean's arithmetic.

A reader who wants to confirm the Solution does not cheat should look for
`rfl` in it: there is none, and `ofNat_injective` is what closes it.
-/

namespace Comparator.NatAddSucc

/-- Lean core's recursion equation, as a closed proposition. -/
def challenge : Prop :=
  ∀ n m : Nat, n + (m + 1) = (n + m) + 1

/-- `challenge` is Lean's own equation, checked by discharging it there. -/
theorem challenge_is_mathlibs : challenge :=
  fun n m => Nat.add_succ n m

end Comparator.NatAddSucc
