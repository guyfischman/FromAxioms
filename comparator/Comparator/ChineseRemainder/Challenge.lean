/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
CHALLENGE: the Chinese remainder theorem, two coprime moduli.

Mathlib's vocabulary only. `Mathlib/Data/Nat/ModEq.lean:353`:

    def Nat.chineseRemainder (co : n.Coprime m) (a b : ℕ) :
      { k // k ≡ a [MOD n] ∧ k ≡ b [MOD m] }

That is a subtype rather than a theorem, so the challenge states the
proposition it carries. NO POSITIVITY ON EITHER MODULUS: mathlib asks only
coprimality, and the degenerate cases (`n = 0` forces `m = 1`, and conversely)
are inside what it claims.

The row's other mathlib counterpart, `ZMod.chineseRemainder`, is the ring
ISOMORPHISM. It is a `def` and not comparator-shaped; this pair matches the
existence statement, and the row's `at_parity` records the isomorphism axis
separately.
-/
import Mathlib.Data.Nat.ModEq

namespace Comparator.ChineseRemainder

/-- The two-modulus Chinese remainder theorem as a closed proposition. -/
def challenge : Prop :=
  ∀ (n m : ℕ), Nat.Coprime n m → ∀ a b : ℕ,
    ∃ k : ℕ, k ≡ a [MOD n] ∧ k ≡ b [MOD m]

/-- `challenge` is Mathlib's statement, checked by reading it off
`Nat.chineseRemainder`'s subtype. -/
theorem challenge_is_mathlibs : challenge :=
  fun _ _ co a b => ⟨(Nat.chineseRemainder co a b).1,
    (Nat.chineseRemainder co a b).2⟩

end Comparator.ChineseRemainder
