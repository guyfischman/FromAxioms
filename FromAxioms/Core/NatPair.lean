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

/-! ## Fast twins

The pairing's definitions recurse unarily, linear in the value, which is slow
to execute. Each function gets a closed-form twin and an agreement
theorem; demonstrations run the twin, and the kernel certifies it is the same
function. -/

/-- Integer square root, by quartering: core has none, as with
`Nat.find`. Well-founded on the argument, so the recursion depth is
logarithmic and the compiled form runs. -/
def isqrt (n : Nat) : Nat :=
  if h : n = 0 then 0
  else
    let r := 2 * isqrt (n / 4)
    if (r + 1) * (r + 1) ≤ n then r + 1 else r
  decreasing_by
    exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega)

/-- The defining bracket: `isqrt n` squares below `n`, its successor
above. -/
theorem isqrt_spec : ∀ n, isqrt n * isqrt n ≤ n
    ∧ n < (isqrt n + 1) * (isqrt n + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match hn : n with
    | 0 => 
      rw [show isqrt 0 = 0 from by rw [isqrt]; rfl]
      exact ⟨Nat.le_refl 0, Nat.zero_lt_one⟩
    | m + 1 =>
      have hlt : (m + 1) / 4 < m + 1 :=
        Nat.div_lt_self (Nat.succ_pos m) (by omega)
      obtain ⟨hlo, hhi⟩ := ih ((m + 1) / 4) hlt
      have hdiv1 : 4 * ((m + 1) / 4) ≤ m + 1 := by omega
      have hdiv2 : m + 1 < 4 * ((m + 1) / 4) + 4 := by omega
      rw [show isqrt (m + 1) = (let r := 2 * isqrt ((m + 1) / 4);
          if (r + 1) * (r + 1) ≤ m + 1 then r + 1 else r) from by
        rw [isqrt]; rfl]
      show (let r := 2 * isqrt ((m + 1) / 4);
        if (r + 1) * (r + 1) ≤ m + 1 then r + 1 else r) * _ ≤ m + 1
        ∧ m + 1 < _
      generalize hq : isqrt ((m + 1) / 4) = q at hlo hhi
      have hsq_lo : 2 * q * (2 * q) ≤ m + 1 := by
        have h4 : 2 * q * (2 * q) = 4 * (q * q) := by
          rw [Nat.mul_assoc, Nat.mul_comm q (2 * q), Nat.mul_assoc,
            ← Nat.mul_assoc]
        omega
      have hsq_hi : m + 1 < (2 * q + 2) * (2 * q + 2) := by
        have h4 : (2 * q + 2) * (2 * q + 2)
            = 4 * ((q + 1) * (q + 1)) := by
          have e1 : (2 * q + 2) * (2 * q + 2)
              = 4 * (q * q) + 8 * q + 4 := by
            rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
            have : 2 * q * (2 * q) = 4 * (q * q) := by
              rw [Nat.mul_assoc, Nat.mul_comm q (2 * q), Nat.mul_assoc,
                ← Nat.mul_assoc]
            omega
          have e2 : 4 * ((q + 1) * (q + 1))
              = 4 * (q * q) + 8 * q + 4 := by
            have : (q + 1) * (q + 1) = q * q + 2 * q + 1 := by
              rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
              omega
            omega
          omega
        omega
      rcases Nat.lt_or_ge (m + 1) ((2 * q + 1) * (2 * q + 1))
        with hc' | hc
      · rw [show (let r := 2 * q;
            if (r + 1) * (r + 1) ≤ m + 1 then r + 1 else r)
            = 2 * q from if_neg (by omega)]
        exact ⟨hsq_lo, by omega⟩
      · rw [show (let r := 2 * q;
            if (r + 1) * (r + 1) ≤ m + 1 then r + 1 else r)
            = 2 * q + 1 from if_pos hc]
        exact ⟨hc, hsq_hi⟩

#print axioms isqrt_spec

end Core

namespace ZFSet
export Core (isqrt isqrt_spec natPair natTri)
end ZFSet
