/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
SOLUTION: `challenge` discharged from `FromAxioms`.

    NumberTheory.crt {m n : Nat} (hco : Nat.gcd m n = 1) (hn : 0 < n) (r s : Nat) :
      ∃ x, Cong m x r ∧ Cong n x s

THE CONGRUENCE RELATIONS ARE THE SAME DEFINITION. Ours is
`Cong n a b := a % n = b % n` (`Congruence.lean:31`) and mathlib's is
`Nat.ModEq n a b := a % n = b % n`, so `k ≡ a [MOD n]` and `Cong n k a` are
definitionally equal and no bridge lemma is needed at all.

OURS CARRIES A HYPOTHESIS MATHLIB'S DOES NOT, and writing this file is what made
that visible. `crt` demands `0 < n`; `Nat.chineseRemainder` demands only
coprimality. The gap is exactly the degenerate case, and it is not vacuous:
`Coprime n 0` says `gcd n 0 = n = 1`, so the missing case is real and has to be
discharged here rather than assumed away. It is discharged directly --- with
`m = 0` the second congruence pins `k = b`, and the first is modulo 1 --- so the
tower's theorem plus one case split covers mathlib's statement.

`Nat.chineseRemainder` is not cited.
-/
import Comparator.ChineseRemainder.Challenge
import FromAxioms

namespace Comparator.ChineseRemainder

theorem solution : challenge := by
  intro n m co a b
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `Coprime n 0` forces `n = 1`, so everything is congruent mod `n`.
    have hn1 : n = 1 := by simpa [Nat.Coprime] using co
    subst hn1
    exact ⟨b, Nat.modEq_one, rfl⟩
  · -- The positive case is `crt` verbatim, with the moduli in its order.
    obtain ⟨x, hx1, hx2⟩ := NumberTheory.crt (m := n) (n := m) co hm a b
    exact ⟨x, hx1, hx2⟩

end Comparator.ChineseRemainder
