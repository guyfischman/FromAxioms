/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
THE CHALLENGE: Brouwer's fan theorem for decidable bars.

WHY THIS ROW'S COST IS ON THE CHALLENGE SIDE, WHICH IS UNUSUAL HERE. Every other
pair on this track states something mathlib already proves and asks whether the
tower can match it. The row `Brouwer's fan theorem` records mathlib's counterpart
as unnamed --- derivable classically from compactness, and that is accurate:
searching the pinned Mathlib (v4.24.0) for `koenig`, `konig` and `König` returns
only `SetTheory/Cardinal/*`, which is König's THEOREM on cardinal arithmetic and
has nothing to do with binary trees. There is no König's LEMMA to cite.

So the classical argument is written out below. It is the whole content of this
file, and `Solution.lean` is four lines by comparison --- the tower states the
fan theorem as a named principle and derives it from a decider.

THE ARGUMENT. Suppose the bar is not uniform. Then for every `N` some path
avoids `B` for its first `N` steps, so the tree of nodes NO PREFIX OF WHICH IS
BARRED has arbitrarily long members. An infinitely-extendible node has an
infinitely-extendible child --- classically, since if both children failed, the
larger of the two bounds would contradict the parent. Iterating builds a path
all of whose prefixes are unbarred, contradicting barhood.

THE BOOKKEEPING IS ONE LEMMA. Proving prefix closure for an abstract tree ---
`PrefixClosed T → T (s ++ (t ++ u)) → T (s ++ t)` --- takes a left induction
with the prefix generalised, since `List.reverseRecOn` is not core. None of
that is needed here: `Unbarred` is a CONCRETE predicate quantified over
`List.take`, so `unbarred_append` falls out of `List.take_append_of_le_length`
with no induction at all.
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic.ByContra

namespace Comparator.FanTheorem

/-- The first `n` values of a sequence, as a path. The tower's
`Constructive.take` is this recursion character for character; `Solution.lean`
proves them equal rather than assuming it. -/
def take (α : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => take α n ++ [α n]

theorem length_take (α : Nat → Bool) : ∀ n, (take α n).length = n
  | 0 => rfl
  | n + 1 => by simp [take, length_take α n]

/-- `B` is met by every infinite path. -/
def IsBar (B : List Bool → Prop) : Prop :=
  ∀ α : Nat → Bool, ∃ n, B (take α n)

/-- `B` is met by every infinite path at a bounded depth. -/
def IsUniformBar (B : List Bool → Prop) : Prop :=
  ∃ N, ∀ α : Nat → Bool, ∃ n, n ≤ N ∧ B (take α n)

/-- The challenge. Brouwer's fan theorem for decidable bars: a decidable bar
is uniform.

Decidability is part of the statement and not a convenience --- without it the
principle is stronger than Brouwer's. Mathlib's proof below has excluded middle
anyway and does not need the hypothesis; the tower's does.

`Solution.lean` must close this using the `FromAxioms` tower. Nothing in this
file may be changed to make that easier. -/
def challenge : Prop :=
  ∀ B : List Bool → Prop, (∀ s, B s ∨ ¬ B s) → IsBar B → IsUniformBar B

/-! ### König's lemma for the binary tree, classically -/

/-- `s` has no barred prefix --- the tree the argument searches. -/
def Unbarred (B : List Bool → Prop) (s : List Bool) : Prop :=
  ∀ k, k ≤ s.length → ¬ B (List.take k s)

/-- Prefix closure. A prefix of an unbarred node is unbarred, because `List.take k` cannot see past `u` once
`k ≤ u.length`. -/
theorem unbarred_append {B : List Bool → Prop} {u v : List Bool}
    (h : Unbarred B (u ++ v)) : Unbarred B u := by
  intro k hk
  have hlen : k ≤ (u ++ v).length := by
    refine Nat.le_trans hk ?_
    simp
  have : List.take k (u ++ v) = List.take k u := List.take_append_of_le_length hk
  exact this ▸ h k hlen

/-- `s` has unbarred extensions of every length. -/
def Ext (B : List Bool → Prop) (s : List Bool) : Prop :=
  ∀ N, ∃ t : List Bool, t.length = N ∧ Unbarred B (s ++ t)

/-- THE CLASSICAL STEP. A node with unbarred extensions of every length has
a child with the same property.

If both children failed there would be bounds `N₁` and `N₂` past which no
extension survives; an extension of the parent of length `max N₁ N₂ + 1` starts
with some bit, and truncating what follows to the relevant bound contradicts it.
`unbarred_append` is what makes the truncation free. -/
theorem ext_child {B : List Bool → Prop} {s : List Bool} (hs : Ext B s) :
    Ext B (s ++ [true]) ∨ Ext B (s ++ [false]) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Ext] at h1 h2
  push_neg at h1 h2
  obtain ⟨N1, hN1⟩ := h1
  obtain ⟨N2, hN2⟩ := h2
  obtain ⟨t, hlen, hUt⟩ := hs (max N1 N2 + 1)
  cases t with
  | nil => simp at hlen
  | cons b rest =>
    have hrest : rest.length = max N1 N2 := by simpa using hlen
    have hsplit : Unbarred B ((s ++ [b]) ++ rest) := by
      simpa using hUt
    -- `push_neg` leaves the failures as `∀ t, t.length = Nᵢ → ¬ Unbarred …`,
    -- so each branch SUPPLIES the truncation and its length rather than
    -- building a pair for `absurd`.
    cases b with
    | true =>
      refine hN1 (List.take N1 rest) ?_ ?_
      · rw [List.length_take, hrest]
        exact Nat.min_eq_left (Nat.le_max_left _ _)
      · -- stated in this direction so `List.append_assoc` fires on the SPLIT
        -- side; the other orientation rewrites `s ++ ([true] ++ rest)` instead
        -- and `take_append_drop` then has no occurrence to match.
        have hsplit' : ((s ++ [true]) ++ List.take N1 rest) ++ List.drop N1 rest
            = (s ++ [true]) ++ rest := by
          rw [List.append_assoc, List.take_append_drop]
        refine unbarred_append (u := (s ++ [true]) ++ List.take N1 rest)
          (v := List.drop N1 rest) ?_
        rw [hsplit']
        exact hsplit
    | false =>
      refine hN2 (List.take N2 rest) ?_ ?_
      · rw [List.length_take, hrest]
        exact Nat.min_eq_left (Nat.le_max_right _ _)
      · have hsplit' : ((s ++ [false]) ++ List.take N2 rest) ++ List.drop N2 rest
            = (s ++ [false]) ++ rest := by
          rw [List.append_assoc, List.take_append_drop]
        refine unbarred_append (u := (s ++ [false]) ++ List.take N2 rest)
          (v := List.drop N2 rest) ?_
        rw [hsplit']
        exact hsplit

open Classical in
/-- The path built by always stepping to a child that still has extensions. -/
noncomputable def node (B : List Bool → Prop) : Nat → List Bool
  | 0 => []
  | n + 1 =>
    if Ext B (node B n ++ [true]) then node B n ++ [true] else node B n ++ [false]

open Classical in
/-- Its bits, as a sequence. -/
noncomputable def bit (B : List Bool → Prop) (n : Nat) : Bool :=
  if Ext B (node B n ++ [true]) then true else false

theorem node_succ (B : List Bool → Prop) (n : Nat) :
    node B (n + 1) = node B n ++ [bit B n] := by
  rw [node, bit]
  split <;> rfl

theorem take_bit (B : List Bool → Prop) : ∀ n, take (bit B) n = node B n
  | 0 => rfl
  | n + 1 => by rw [take, take_bit B n, node_succ]

/-- Every node on the path still has extensions, by `ext_child` at each
step. -/
theorem ext_node {B : List Bool → Prop} (h0 : Ext B []) : ∀ n, Ext B (node B n)
  | 0 => h0
  | n + 1 => by
    rw [node_succ]
    by_cases hc : Ext B (node B n ++ [true])
    · rw [bit, if_pos hc]; exact hc
    · rw [bit, if_neg hc]
      rcases ext_child (ext_node h0 n) with h | h
      · exact absurd h hc
      · exact h

/-- A node with extensions is itself unbarred: take the extension of length
zero. -/
theorem unbarred_of_ext {B : List Bool → Prop} {s : List Bool} (h : Ext B s) :
    Unbarred B s := by
  obtain ⟨t, hlen, hU⟩ := h 0
  have : t = [] := List.eq_nil_of_length_eq_zero hlen
  subst this
  simpa using hU

/-- The challenge is not vacuous, and the classical König argument is the
witness.

`hdec` is discarded: with excluded middle in the foundation the decidability
hypothesis carries nothing, which is the measurement this pair exists to make.
The tower's Solution cannot discard it. -/
theorem challenge_is_mathlibs : challenge := by
  intro B _hdec hbar
  by_contra hcon
  rw [IsUniformBar] at hcon
  push_neg at hcon
  -- the unbarred tree has arbitrarily long members
  have h0 : Ext B [] := by
    intro N
    obtain ⟨α, hα⟩ := hcon N
    refine ⟨take α N, length_take α N, ?_⟩
    rw [List.nil_append]
    intro k hk
    have hkN : k ≤ N := by rw [length_take α N] at hk; exact hk
    have hre : List.take k (take α N) = take α k := by
      clear hk hα
      induction N with
      | zero =>
        have : k = 0 := Nat.le_zero.mp hkN
        subst this; rfl
      | succ p ih =>
        rcases Nat.lt_or_ge k (p + 1) with hlt | hge
        · have hkp : k ≤ p := Nat.lt_succ_iff.mp hlt
          rw [take, List.take_append_of_le_length (by rw [length_take]; exact hkp)]
          exact ih hkp
        · have : k = p + 1 := Nat.le_antisymm hkN hge
          subst this
          rw [List.take_of_length_le (by rw [length_take])]
    rw [hre]
    exact hα k hkN
  -- the path it builds meets the bar, and cannot
  obtain ⟨n, hn⟩ := hbar (bit B)
  rw [take_bit] at hn
  have hU : Unbarred B (node B n) := unbarred_of_ext (ext_node h0 n)
  refine hU (node B n).length (Nat.le_refl _) ?_
  rw [List.take_of_length_le (Nat.le_refl _)]
  exact hn

#print axioms challenge_is_mathlibs

end Comparator.FanTheorem
