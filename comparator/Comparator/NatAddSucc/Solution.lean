/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`, without citing Lean's `rfl`.

THE STATEMENT IS FREE IN LEAN, SO THE ROUTE IS WHAT IS BEING CHECKED.
`Nat.add_succ` holds by `rfl` on an inductive type; this Solution instead:

  * embeds both naturals as von Neumann ordinals with `ofNat`;
  * uses `Arith.add_succ` --- `add x (succ y) = succ (add x y)` for ARBITRARY
    `ZFSet`s, proved by extensionality over the ordinals, not by computation;
  * comes back with `add_ofNat`, which says the tower's addition agrees with
    Lean's through the embedding;
  * and concludes by `ofNat_injective`.

So the pair checks that this tower's set-theoretic recursion is strong enough
to yield Lean's arithmetic equation, rather than that Lean can prove its own
definitional identity. No `rfl` appears below, which is what separates a real
Solution here from a vacuous one.
-/
import Comparator.NatAddSucc.Challenge
import FromAxioms.NumberTheory.Arith

open Comparator.NatAddSucc

open SetTheory NumberTheory

namespace Comparator.NatAddSucc

/-- The challenge, from `FromAxioms` --- through the ordinals. -/
theorem solution : challenge := by
  intro n m
  refine ofNat_injective (m := n + (m + 1)) (n := n + m + 1) ?_
  -- Into the ordinals, through the set-theoretic recursion, and back.
  rw [← add_ofNat.{0} n (m + 1), ofNat_succ m, add_succ, add_ofNat.{0} n m,
    ← ofNat_succ (n + m)]

#print axioms solution

end Comparator.NatAddSucc
