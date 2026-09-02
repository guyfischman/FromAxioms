/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Pairing `Nat` with itself

Lean core has no `Nat.pair`, so the anti-diagonal enumeration is built here.
`natPair k n` walks the diagonals `k + n = d` in order, taking
`(0, d), (1, d-1), …, (d, 0)` within each, and `natUnpair` steps the same walk
one place at a time.

It exists because countable choice at one index reaches two indices only
through an injection `Nat × Nat -> Nat`.
-/

namespace Core

/-- The triangular numbers: how many pairs come before diagonal `n`. -/
def natTri : Nat → Nat
  | 0 => 0
  | n + 1 => natTri n + (n + 1)

def natPair (k n : Nat) : Nat := natTri (k + n) + k

end Core

namespace ZFSet
export Core (natPair natTri)
end ZFSet
