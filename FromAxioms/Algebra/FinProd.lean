/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Folding a commutative operation over a finite set.

`gpow` iterates one element; nothing so far can combine all the elements of a
set. The obstruction is that a set has no order, so a fold has to be taken along
an enumeration and then shown not to depend on which enumeration was used.

The enumerations here are Lean-level functions `Nat → ZFSet` together with a
bound, not set functions. That is deliberate: the reindexing that the proof
needs -- skip the index carrying a given element -- is `fun i => if i < j then
G i else G (i + 1)`, which is a branch on `Nat`, decidable and free. Written
with set functions the same step would be `graphOn` surgery. Nothing is lost:
`Enum` is a `Prop` about a set, and a finite set has an enumeration in this
sense exactly when it has a bijection from a numeral.

Invariance is `enum_fold_unique`, and its two halves come out of one induction: two
enumerations of the same set have the same length and the same fold. The fold
is then named by extracting the unique value from a singleton,
so `setFold` is a definition rather than a choice.
-/

import FromAxioms.Algebra.Group
import FromAxioms.Analysis.Located
import FromAxioms.Core.CoreShim
import FromAxioms.SetTheory.Cantor

universe u

open NumberTheory SetTheory
namespace Algebra

/-! ## Commutative monoids

A fold needs associativity, commutativity, and a unit; it does not need
inverses. -/

structure IsCommMonoid (M op e : ZFSet.{u}) : Prop where
  isFun : IsFunction op
  dom : domain op = prod M M
  ran : range op ⊆ M
  mem_e : e ∈ M
  assoc : ∀ a, a ∈ M → ∀ b, b ∈ M → ∀ c, c ∈ M →
    opAt op (opAt op a b) c = opAt op a (opAt op b c)
  left_id : ∀ a, a ∈ M → opAt op e a = a
  comm : ∀ a, a ∈ M → ∀ b, b ∈ M → opAt op a b = opAt op b a

/-- A commutative monoid is a monoid. `right_id` is `comm` then
`left_id`, and that is the ONLY use of
commutativity in the order-arithmetic family `Group.lean` states over
`IsMonoid`. A hypothesis whose entire contribution is one derivation of a weaker
field is a hypothesis that development did not need.

The two structures are incomparable rather than nested -- `IsGroup` has
`right_id` as a field and no `comm`, `IsCommMonoid` has `comm` and no
`right_id` -- so `IsMonoid` is their meet, and both directions cost nothing. -/
theorem IsCommMonoid.toMonoid {M op e : ZFSet.{u}} (h : IsCommMonoid M op e) :
    IsMonoid M op e :=
  { isFun := h.isFun, dom := h.dom, ran := h.ran, mem_e := h.mem_e,
    assoc := h.assoc, left_id := h.left_id,
    right_id := fun a ha => by rw [h.comm a ha e h.mem_e, h.left_id a ha] }

/-- One conclusion, reached through both structures: the group and commutative
monoid families are INSTANCES of the monoid one rather than cousins of each
other. -/
theorem gpow_add_of_commMonoid {M op e a : ZFSet.{u}} (h : IsCommMonoid M op e)
    (ha : a ∈ M) (j k : Nat) :
    gpow op e a (j + k) = opAt op (gpow op e a j) (gpow op e a k) :=
  gpow_add_bare h.toMonoid ha j k

theorem opAt_mem_monoid {M op e a b : ZFSet.{u}} (h : IsCommMonoid M op e)
    (ha : a ∈ M) (hb : b ∈ M) : opAt op a b ∈ M :=
  h.ran _ (app_mem_range h.isFun (by rw [h.dom]; exact opair_mem_prod ha hb))

theorem right_id_monoid {M op e a : ZFSet.{u}} (h : IsCommMonoid M op e) (ha : a ∈ M) :
    opAt op a e = a := by
  rw [h.comm a ha e h.mem_e]
  exact h.left_id a ha

/-- `a + (b + c) = b + (a + c)` on a commutative monoid.

`ringAdd_left_comm` is this for a ring's additive part, and its proof is the
same three rewrites --- associativity and commutativity, both of which
`IsCommMonoid` states outright. The ring version existed first only because
every fold in this tree was over a ring until `omega` became a semiring. -/
theorem left_comm_monoid {M op e a b c : ZFSet.{u}} (h : IsCommMonoid M op e)
    (ha : a ∈ M) (hb : b ∈ M) (hc : c ∈ M) :
    opAt op a (opAt op b c) = opAt op b (opAt op a c) := by
  rw [← h.assoc a ha b hb c hc, h.comm a ha b hb, h.assoc b hb a ha c hc]

#print axioms left_comm_monoid

/-- An abelian group is a commutative monoid. -/
theorem isCommMonoid_of_isGroup {G op e : ZFSet.{u}} (hG : IsGroup G op e)
    (hab : IsAbelian G op) : IsCommMonoid G op e :=
  ⟨hG.isFun, hG.dom, hG.ran, hG.mem_e, hG.assoc, hG.left_id, hab⟩

/-! ## Enumerations

`Enum F n S` says `F` restricted to `{0, ..., n-1}` is a bijection onto `S`. -/

/-- Reindex to omit position `j`. -/
def skipAt (j : Nat) (F : Nat → ZFSet.{u}) : Nat → ZFSet.{u} :=
  fun i => if i < j then F i else F (i + 1)

theorem skipAt_lt {j : Nat} {F : Nat → ZFSet.{u}} {i : Nat} (h : i < j) :
    skipAt j F i = F i := if_pos h

theorem skipAt_ge {j : Nat} {F : Nat → ZFSet.{u}} {i : Nat} (h : j ≤ i) :
    skipAt j F i = F (i + 1) := if_neg (by omega)

/-! ## The fold along an enumeration -/

def foldF (op e : ZFSet.{u}) (F : Nat → ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => e
  | k + 1 => opAt op (foldF op e F k) (F k)

/-- The involution, transported past a skip at `j`: an index `i` of the
survivors is `orig j i` in the original. -/
def origAt (j i : Nat) : Nat := if i < j then i else i + 1

/-- Its inverse on the survivors: an original index other than `j` comes back. -/
def survAt (j i : Nat) : Nat := if i < j then i else i - 1

theorem origAt_ne (j i : Nat) : origAt j i ≠ j := by
  unfold origAt
  rcases Nat.lt_or_ge i j with h | h
  · rw [if_pos h]; omega
  · rw [if_neg (by omega)]; omega

theorem survAt_origAt (j i : Nat) : survAt j (origAt j i) = i := by
  unfold survAt origAt
  rcases Nat.lt_or_ge i j with h | h
  · rw [if_pos h, if_pos h]
  · rw [if_neg (show ¬ i < j by omega), if_neg (show ¬ i + 1 < j by omega)]
    omega

theorem origAt_survAt {j i : Nat} (h : i ≠ j) : origAt j (survAt j i) = i := by
  unfold origAt survAt
  rcases Nat.lt_or_ge i j with h1 | h1
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg (show ¬ i < j by omega), if_neg (show ¬ i - 1 < j by omega)]
    omega

/-- `skipAt` is the transport, pointwise. Not `rfl` -- `skipAt` puts the
`if` outside `F` and `origAt` puts it inside -- but two cases and no new
machinery. -/
theorem skipAt_origAt (j : Nat) (F : Nat → ZFSet.{u}) (i : Nat) :
    skipAt j F i = F (origAt j i) := by
  rcases Nat.lt_or_ge i j with h | h
  · rw [skipAt_lt h]
    show _ = F (if i < j then i else i + 1)
    rw [if_pos h]
  · rw [skipAt_ge h]
    show _ = F (if i < j then i else i + 1)
    rw [if_neg (show ¬ i < j by omega)]

/-- A fold stays inside a set closed under the operation. No ring, no
monoid, no commutativity -- the zero and the two-argument closure are the whole
hypothesis, so a SUBRING uses it without first exhibiting its restricted ring
structure.

Stated over the AMBIENT operation rather than a restricted one: a subring's
`IsRing` instance carries `restrictOp add S`, and bridging that back to `add`
at every step is work this avoids by never leaving the ambient operation. -/
theorem foldF_mem_closed {S add zero : ZFSet.{u}} (hz : zero ∈ S)
    (hadd : ∀ a, a ∈ S → ∀ b, b ∈ S → opAt add a b ∈ S)
    (F : Nat → ZFSet.{u}) (hF : ∀ i, F i ∈ S) :
    ∀ n : Nat, foldF add zero F n ∈ S
  | 0 => hz
  | n + 1 => hadd _ (foldF_mem_closed hz hadd F hF n) _ (hF n)

#print axioms foldF_mem_closed


theorem foldF_congr {op e : ZFSet.{u}} {F G : Nat → ZFSet.{u}} :
    ∀ k : Nat, (∀ i, i < k → F i = G i) → foldF op e F k = foldF op e G k
  | 0, _ => rfl
  | k + 1, h => by
    rw [foldF, foldF, foldF_congr k (fun i hi => h i (by omega)), h k (by omega)]

theorem foldF_mem {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e) {F : Nat → ZFSet.{u}} :
    ∀ k : Nat, (∀ i, i < k → F i ∈ M) → foldF op e F k ∈ M
  | 0, _ => hM.mem_e
  | k + 1, h =>
    opAt_mem_monoid hM (foldF_mem hM k (fun i hi => h i (by omega))) (h k (by omega))

/-- Any one factor can be moved to the end: folding `G` over `k+1` places is
folding the other `k` and multiplying by `G j`. -/
theorem foldF_skip {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e) {G : Nat → ZFSet.{u}} :
    ∀ k j : Nat, j ≤ k → (∀ i, i < k + 1 → G i ∈ M) →
      foldF op e G (k + 1) = opAt op (foldF op e (skipAt j G) k) (G j)
  | 0, j, hj, _ => by
    obtain rfl : j = 0 := by omega
    rfl
  | k + 1, j, hj, hmem => by
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · -- `G j` is not the last factor: recurse, then swap the last two
      have hstep := foldF_skip hM k j (by omega) (fun i hi => hmem i (by omega))
      have hlast : skipAt j G (k + 1) = G (k + 2) := skipAt_ge (by omega)
      have hX : foldF op e (skipAt j G) (k + 1) ∈ M := by
        refine foldF_mem hM (k + 1) (fun i hi => ?_)
        rcases Nat.lt_or_ge i j with h | h
        · rw [skipAt_lt h]
          exact hmem i (by omega)
        · rw [skipAt_ge h]
          exact hmem (i + 1) (by omega)
      have hXk : foldF op e (skipAt j G) k ∈ M := by
        refine foldF_mem hM k (fun i hi => ?_)
        rcases Nat.lt_or_ge i j with h | h
        · rw [skipAt_lt h]
          exact hmem i (by omega)
        · rw [skipAt_ge h]
          exact hmem (i + 1) (by omega)
      have ha : G j ∈ M := hmem j (by omega)
      have hb : G (k + 1) ∈ M := hmem (k + 1) (by omega)
      show opAt op (foldF op e G (k + 1)) (G (k + 1))
        = opAt op (opAt op (foldF op e (skipAt j G) k) (skipAt j G k)) (G j)
      rw [hstep, skipAt_ge (show j ≤ k by omega), hM.assoc _ hXk _ ha _ hb,
        hM.comm _ ha _ hb, ← hM.assoc _ hXk _ hb _ ha]
    · -- `G j` is the last factor, and the skip changes nothing below it
      obtain rfl : j = k + 1 := by omega
      exact congrArg (fun t => opAt op t (G (k + 1)))
        (foldF_congr (k + 1) (fun i hi => (skipAt_lt hi).symm))

/-- A flattened index is below the product of its two bounds. -/
theorem flat_lt {n m a b : Nat} (ha : a < n) (hb : b < m) : a * m + b < n * m :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hb (a * m))
    (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right m ha)

#print axioms flat_lt

/-- Decoding is inverse to coding, below the bound. -/
theorem flat_div_mod {m j k : Nat} (hk : k < m) :
    (j * m + k) / m = j ∧ (j * m + k) % m = k := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  refine ⟨?_, ?_⟩
  · rw [show j * m + k = k + m * j by rw [Nat.mul_comm, Nat.add_comm],
      Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hk, Nat.zero_add]
  · rw [show j * m + k = k + m * j by rw [Nat.mul_comm, Nat.add_comm],
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

#print axioms flat_div_mod

/-- A fold over `a + b` splits at `a`. -/
theorem foldF_split {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e)
    {F : Nat → ZFSet.{u}} (a : Nat) :
    ∀ b : Nat, (∀ i, i < a + b → F i ∈ M) → foldF op e F (a + b)
      = opAt op (foldF op e F a) (foldF op e (fun i => F (a + i)) b)
  | 0, hmem => (right_id_monoid hM (foldF_mem hM a (fun i hi => hmem i hi))).symm
  | b + 1, hmem => by
    show opAt op (foldF op e F (a + b)) (F (a + b))
      = opAt op (foldF op e F a)
          (opAt op (foldF op e (fun i => F (a + i)) b) (F (a + b)))
    rw [foldF_split hM a b (fun i hi => hmem i (by omega)),
      hM.assoc _ (foldF_mem hM a (fun i hi => hmem i (by omega)))
        _ (foldF_mem hM b (fun i hi => hmem _ (by omega)))
        _ (hmem (a + b) (by omega))]

#print axioms foldF_split

/-- A double fold is a single fold over the flattened index.

`t` runs over `0..n*m-1` and carries the pair `(t / m, t % m)`. The `m = 0`
case needs no side condition: the inner folds are empty on both sides, so the
congruence step is vacuous and supplies `0 < m` from `i < m` where it is
needed. -/
theorem foldF_flatten {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e)
    {G : Nat → Nat → ZFSet.{u}} (hmem : ∀ i j, G i j ∈ M) (m : Nat) :
    ∀ n : Nat, foldF op e (fun i => foldF op e (G i) m) n
      = foldF op e (fun t => G (t / m) (t % m)) (n * m)
  | 0 => by rw [Nat.zero_mul]; rfl
  | n + 1 => by
    show opAt op (foldF op e (fun i => foldF op e (G i) m) n)
        (foldF op e (G n) m) = _
    rw [foldF_flatten hM hmem m n,
      show (n + 1) * m = n * m + m from Nat.succ_mul n m,
      foldF_split hM (n * m) m (fun t _ => hmem (t / m) (t % m))]
    refine congrArg _ (foldF_congr m (fun i hi => ?_))
    obtain ⟨hd, hr⟩ := flat_div_mod (m := m) (j := n) hi
    show G n i = G ((n * m + i) / m) ((n * m + i) % m)
    rw [hd, hr]

#print axioms foldF_flatten

theorem foldF_map {M₁ op₁ e₁ op₂ e₂ : ZFSet.{u}} {g : ZFSet.{u} → ZFSet.{u}}
    (h₁ : IsCommMonoid M₁ op₁ e₁) (hunit : g e₁ = e₂)
    (hmul : ∀ a, a ∈ M₁ → ∀ b, b ∈ M₁ → g (opAt op₁ a b) = opAt op₂ (g a) (g b))
    {F : Nat → ZFSet.{u}} (hF : ∀ i, F i ∈ M₁) :
    ∀ n : Nat, g (foldF op₁ e₁ F n) = foldF op₂ e₂ (fun i => g (F i)) n
  | 0 => hunit
  | n + 1 => by
    show g (opAt op₁ (foldF op₁ e₁ F n) (F n))
      = opAt op₂ (foldF op₂ e₂ (fun i => g (F i)) n) _
    rw [hmul _ (foldF_mem h₁ n (fun i _ => hF i)) _ (hF n),
      foldF_map h₁ hunit hmul hF n]

#print axioms foldF_map

/-! ## Peeling, reversing, adding

Three identities about `foldF` over an index range, used wherever a sum has to
be reindexed. -/

theorem opAt_shuffle4 {M op e a b c d : ZFSet.{u}} (hM : IsCommMonoid M op e)
    (ha : a ∈ M) (hb : b ∈ M) (hc : c ∈ M) (hd : d ∈ M) :
    opAt op (opAt op a b) (opAt op c d) = opAt op (opAt op a c) (opAt op b d) := by
  rw [hM.assoc _ ha _ hb _ (opAt_mem_monoid hM hc hd),
    ← hM.assoc _ hb _ hc _ hd, hM.comm _ hb _ hc, hM.assoc _ hc _ hb _ hd,
    ← hM.assoc _ ha _ hc _ (opAt_mem_monoid hM hb hd)]

/-- Out through both skips lands below `n + 2`. Extracted from
`survPair_maps`, where it was a `have`: the conditioned clauses all need it. -/
theorem origAt_pair_lt {p n i : Nat} (hi : i < n) :
    origAt p (origAt 0 i) < n + 2 := by
  unfold origAt
  rw [if_neg (show ¬ i < 0 by omega)]
  rcases Nat.lt_or_ge (i + 1) p with h | h
  · rw [if_pos h]; omega
  · rw [if_neg (by omega)]; omega

#print axioms origAt_pair_lt

/-- `sigma_survives`, with the two involutivity instances it actually uses
taken directly rather than through a universally quantified clause. -/
theorem sigma_survives {sigma : Nat → Nat} {p i : Nat}
    (hinvol0 : sigma (sigma 0) = 0) (hinvoli : sigma (sigma i) = i)
    (h0 : sigma 0 = p) (hi0 : i ≠ 0) (hip : i ≠ p) :
    And (sigma i ≠ 0) (sigma i ≠ p) := by
  have hp0 : sigma p = 0 := by rw [← h0, hinvol0]
  constructor
  · intro h
    exact hip (by rw [← hinvoli, h, h0])
  · intro h
    exact hi0 (by rw [← hinvoli, h, hp0])


/-- The involution carried to the survivors of skipping `p` then `0`: out
through both skips, apply the permutation, back through both. -/
def survPair (sigma : Nat → Nat) (p i : Nat) : Nat :=
  survAt 0 (survAt p (sigma (origAt p (origAt 0 i))))

/-- The two peels compose into one index map, in the order the peel applies
them: `skipAt 0 (skipAt p F)` at `i` is `F` at `origAt p (origAt 0 i)`. -/
theorem skipAt_skipAt_origAt (p : Nat) (F : Nat → ZFSet.{u}) (i : Nat) :
    skipAt 0 (skipAt p F) i = F (origAt p (origAt 0 i)) := by
  rw [skipAt_origAt, skipAt_origAt]

/-- A survivor's original index is neither `0` nor `p`. -/
theorem origAt_pair_ne (p i : Nat) :
    And (origAt p (origAt 0 i) ≠ 0) (origAt p (origAt 0 i) ≠ p) := by
  refine ⟨?_, origAt_ne p _⟩
  have h0 : origAt 0 i = i + 1 := by
    unfold origAt; rw [if_neg (by omega)]
  rw [h0]
  unfold origAt
  rcases Nat.lt_or_ge (i + 1) p with h | h
  · rw [if_pos h]; omega
  · rw [if_neg (by omega)]; omega

/-- Peeling `p` and then `0` puts `F 0` and `F p` at the outside of the fold. -/
theorem foldF_peel_pair {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e)
    {F : Nat → ZFSet.{u}} (n p : Nat) (hp : 0 < p) (hpn : p < n + 2)
    (hmem : ∀ i, i < n + 2 → F i ∈ M) :
    foldF op e F (n + 2)
      = opAt op (opAt op (foldF op e (skipAt 0 (skipAt p F)) n) (F 0)) (F p) := by
  have horig : ∀ i, i < n + 1 → origAt p i < n + 2 := by
    intro i hi
    unfold origAt
    rcases Nat.lt_or_ge i p with h | h
    · rw [if_pos h]; omega
    · rw [if_neg (by omega)]; omega
  have hskip : ∀ i, i < n + 1 → skipAt p F i ∈ M := by
    intro i hi
    rw [skipAt_origAt]
    exact hmem _ (horig i hi)
  rw [foldF_skip hM (n + 1) p (by omega) hmem,
    foldF_skip hM n 0 (by omega) hskip, skipAt_lt hp]

/-- Peel off the first term instead of the last. -/
theorem foldF_cons {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e) {F : Nat → ZFSet.{u}} :
    ∀ n : Nat, (∀ i, i < n + 1 → F i ∈ M) →
      foldF op e F (n + 1) = opAt op (F 0) (foldF op e (fun i => F (i + 1)) n)
  | 0, hmem => by
    show opAt op e (F 0) = opAt op (F 0) e
    rw [hM.left_id _ (hmem 0 (by omega)), right_id_monoid hM (hmem 0 (by omega))]
  | n + 1, hmem => by
    have hrest : ∀ i, i < n + 1 → F i ∈ M := fun i hi => hmem i (by omega)
    have hfold : foldF op e (fun i => F (i + 1)) n ∈ M :=
      foldF_mem hM n (fun i hi => hmem (i + 1) (by omega))
    show opAt op (foldF op e F (n + 1)) (F (n + 1))
      = opAt op (F 0) (opAt op (foldF op e (fun i => F (i + 1)) n) (F (n + 1)))
    rw [foldF_cons hM n hrest,
      hM.assoc _ (hmem 0 (by omega)) _ hfold _ (hmem (n + 1) (by omega))]

/-- A fold over an index range does not depend on the direction. -/
theorem foldF_reverse {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e) {F : Nat → ZFSet.{u}} :
    ∀ n : Nat, (∀ i, i < n → F i ∈ M) →
      foldF op e F n = foldF op e (fun i => F (n - 1 - i)) n
  | 0, _ => rfl
  | n + 1, hmem => by
    have hrev : foldF op e (fun i => F (n - 1 - i)) n ∈ M :=
      foldF_mem hM n (fun i hi => hmem _ (by omega))
    have hstep := foldF_cons (M := M) hM (F := fun i => F (n - i)) n
      (fun i hi => hmem _ (by omega))
    show opAt op (foldF op e F n) (F n) = foldF op e (fun i => F (n + 1 - 1 - i)) (n + 1)
    rw [show (fun i => F (n + 1 - 1 - i)) = (fun i => F (n - i)) from rfl, hstep,
      show (fun i => F (n - (i + 1))) = (fun i => F (n - 1 - i)) by
        exact funext (fun i => congrArg F (by omega)),
      ← foldF_reverse hM n (fun i hi => hmem i (by omega))]
    show opAt op (foldF op e F n) (F n) = opAt op (F (n - 0)) (foldF op e F n)
    rw [show n - 0 = n from rfl,
      hM.comm _ (hmem n (by omega)) _ (foldF_mem hM n (fun i hi => hmem i (by omega)))]

/-- Folds add termwise. -/
theorem foldF_add {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e) {F G : Nat → ZFSet.{u}} :
    ∀ n : Nat, (∀ i, i < n → F i ∈ M) → (∀ i, i < n → G i ∈ M) →
      foldF op e (fun i => opAt op (F i) (G i)) n
        = opAt op (foldF op e F n) (foldF op e G n)
  | 0, _, _ => (hM.left_id e hM.mem_e).symm
  | n + 1, hF, hG => by
    show opAt op (foldF op e (fun i => opAt op (F i) (G i)) n) (opAt op (F n) (G n))
      = opAt op (opAt op (foldF op e F n) (F n)) (opAt op (foldF op e G n) (G n))
    rw [foldF_add hM n (fun i hi => hF i (by omega)) (fun i hi => hG i (by omega)),
      opAt_shuffle4 hM (foldF_mem hM n (fun i hi => hF i (by omega)))
        (foldF_mem hM n (fun i hi => hG i (by omega))) (hF n (by omega)) (hG n (by omega))]

/-- Two folds combine into a third when their terms do. -/
theorem foldF_pointwise_add {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e)
    {F G H : Nat → ZFSet.{u}} (n : Nat) (hF : ∀ i, i < n → F i ∈ M)
    (hG : ∀ i, i < n → G i ∈ M) (h : ∀ i, i < n → opAt op (F i) (G i) = H i) :
    opAt op (foldF op e F n) (foldF op e G n) = foldF op e H n := by
  rw [← foldF_add hM n hF hG]
  exact foldF_congr n h

/-- Double sums may be swapped -- Fubini's theorem for finite sums, over an
arbitrary commutative monoid. `foldF_triangle` below is its diagonal form and
says the name; this one is the rectangular exchange and did not. -/
theorem foldF_swap {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e) {G : Nat → Nat → ZFSet.{u}}
    (p : Nat) :
    ∀ n : Nat, (∀ i j, i < n → j < p → G i j ∈ M) →
      foldF op e (fun i => foldF op e (fun j => G i j) p) n
        = foldF op e (fun j => foldF op e (fun i => G i j) n) p
  | 0, hG => by
    show e = foldF op e (fun _ => e) p
    clear hG
    induction p with
    | zero => rfl
    | succ k ih =>
      show e = opAt op (foldF op e (fun _ => e) k) e
      rw [← ih, hM.left_id e hM.mem_e]
  | n + 1, hG => by
    show opAt op (foldF op e (fun i => foldF op e (fun j => G i j) p) n)
        (foldF op e (fun j => G n j) p)
      = foldF op e (fun j => foldF op e (fun i => G i j) (n + 1)) p
    rw [foldF_swap hM p n (fun i j hi hj => hG i j (by omega) hj)]
    exact foldF_pointwise_add hM p
      (fun j hj => foldF_mem hM n (fun i hi => hG i j (by omega) hj))
      (fun j hj => hG n j (by omega) hj) (fun j _ => rfl)

/-- A last term equal to the unit can be dropped. -/
theorem foldF_drop_last {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e)
    {F : Nat → ZFSet.{u}} {n : Nat} (hmem : ∀ i, i < n → F i ∈ M) (hlast : F n = e) :
    foldF op e F (n + 1) = foldF op e F n := by
  show opAt op (foldF op e F n) (F n) = foldF op e F n
  rw [hlast]
  exact right_id_monoid hM (foldF_mem hM n hmem)

/-- Trailing units do not change a fold, so a bound can be raised at will. -/
theorem foldF_trunc {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e) {F : Nat → ZFSet.{u}}
    {n : Nat} (hmem : ∀ i, i < n → F i ∈ M) (hz : ∀ i, n ≤ i → F i = e) :
    ∀ m : Nat, n ≤ m → foldF op e F m = foldF op e F n
  | 0, hnm => by
    obtain rfl : n = 0 := by omega
    rfl
  | m + 1, hnm => by
    rcases Nat.eq_or_lt_of_le hnm with heq | hlt
    · rw [← heq]
    · show opAt op (foldF op e F m) (F m) = foldF op e F n
      rw [foldF_trunc hM hmem hz m (by omega), hz m (by omega),
        right_id_monoid hM (foldF_mem hM n hmem)]

/-- Triangular Fubini. Summing over `a + b ≤ k` by the diagonal `a + b = i`
or by rows `a` fixed gives the same answer. -/
theorem foldF_triangle {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e)
    {S : Nat → Nat → ZFSet.{u}} (hS : ∀ a b, S a b ∈ M) :
    ∀ k : Nat, foldF op e (fun i => foldF op e (fun a => S a (i - a)) (i + 1)) (k + 1)
      = foldF op e (fun a => foldF op e (fun b => S a b) (k - a + 1)) (k + 1) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hinner : ∀ a : Nat, foldF op e (fun b => S a b) (k - a + 1) ∈ M :=
      fun a => foldF_mem hM _ (fun b _ => hS a b)
    have hdiag : ∀ a : Nat, S a (k + 1 - a) ∈ M := fun a => hS _ _
    have hleft : foldF op e (fun i => foldF op e (fun a => S a (i - a)) (i + 1)) (k + 1) ∈ M :=
      foldF_mem hM _ (fun i _ => foldF_mem hM _ (fun a _ => hS a _))
    have hD : foldF op e (fun a => S a (k + 1 - a)) (k + 1) ∈ M :=
      foldF_mem hM _ (fun a _ => hdiag a)
    have hstep : foldF op e (fun a => foldF op e (fun b => S a b) (k + 1 - a + 1)) (k + 1)
        = foldF op e (fun a => opAt op (foldF op e (fun b => S a b) (k - a + 1))
            (S a (k + 1 - a))) (k + 1) := by
      refine foldF_congr (k + 1) (fun a ha => ?_)
      show foldF op e (fun b => S a b) (k + 1 - a + 1)
        = opAt op (foldF op e (fun b => S a b) (k - a + 1)) (S a (k + 1 - a))
      rw [show k + 1 - a = (k - a) + 1 by omega]
      rfl
    show opAt op (foldF op e (fun i => foldF op e (fun a => S a (i - a)) (i + 1)) (k + 1))
        (foldF op e (fun a => S a (k + 1 - a)) (k + 1 + 1))
      = opAt op (foldF op e (fun a => foldF op e (fun b => S a b) (k + 1 - a + 1)) (k + 1))
        (foldF op e (fun b => S (k + 1) b) (k + 1 - (k + 1) + 1))
    have hE : foldF op e (fun b => S (k + 1) b) (k + 1 - (k + 1) + 1) = S (k + 1) 0 := by
      rw [show k + 1 - (k + 1) = 0 by omega]
      show opAt op e (S (k + 1) 0) = S (k + 1) 0
      exact hM.left_id _ (hS (k + 1) 0)
    have hD2 : foldF op e (fun a => S a (k + 1 - a)) (k + 1 + 1)
        = opAt op (foldF op e (fun a => S a (k + 1 - a)) (k + 1)) (S (k + 1) 0) := by
      show opAt op (foldF op e (fun a => S a (k + 1 - a)) (k + 1))
        (S (k + 1) (k + 1 - (k + 1))) = _
      rw [show k + 1 - (k + 1) = 0 by omega]
    rw [hstep, foldF_add hM (k + 1) (fun a _ => hinner a) (fun a _ => hdiag a), ← ih,
      hE, hD2, hM.assoc _ hleft _ hD _ (hS (k + 1) 0)]

/-! ## The fold of a set

`IsFoldMapOf g S v` is a `Prop` with at most one witness, so the value can be
named by taking the union of the set of witnesses. The map `g` is applied to
each element as it is folded; `setFold` is the case where it is the identity,
and everything summing a function over a set goes through the general form. -/

/-- Folding a constant is iterating it. `foldF` and `gpow` have the same
recursion -- one more `op` against the same element at each step -- so with the
index ignored they are the same function. -/
theorem foldF_const (op e a : ZFSet.{u}) :
    ∀ n : Nat, foldF op e (fun _ => a) n = gpow op e a n
  | 0 => rfl
  | n + 1 => by
    show opAt op (foldF op e (fun _ => a) n) a = opAt op (gpow op e a n) a
    rw [foldF_const op e a n]

#print axioms foldF_const
/-- A fold of the unit is the unit. -/
theorem foldF_unit {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e) :
    ∀ n : Nat, foldF op e (fun _ => e) n = e
  | 0 => rfl
  | n + 1 => by
    show opAt op (foldF op e (fun _ => e) n) e = e
    rw [foldF_unit hM n]
    exact hM.left_id e hM.mem_e

/-- A map carried through a fold, at the monoid level.

`hom_foldF` and `hom_foldF_mul` are this at a ring's two operations. Neither
proof touches distributivity or negation -- they project `hom_add'`/`hom_mul`
and `hom_zero`/`hom_one`, which is multiplicativity over ONE operation and its
unit. So the two `IsRing`s are the ambient structure rather than the
requirement.

Stated with the two clauses inline rather than through a homomorphism
structure: this tower has `IsRingHom` and no `IsMonoidHom`. Its consumers are
its own ring instances, so they do not argue for one -- a structure is earned by
unrelated callers needing the same interface, and these were absorbed rather
than found. -/
theorem hom_foldF_monoid {M₁ op₁ e₁ M₂ op₂ e₂ h : ZFSet.{u}}
    (h₁ : IsCommMonoid M₁ op₁ e₁) (_h₂ : IsCommMonoid M₂ op₂ e₂)
    (hunit : app h e₁ = e₂)
    (hmul : ∀ a, a ∈ M₁ → ∀ b, b ∈ M₁ →
      app h (opAt op₁ a b) = opAt op₂ (app h a) (app h b))
    {F : Nat → ZFSet.{u}} (hF : ∀ i, F i ∈ M₁) :
    ∀ n : Nat, app h (foldF op₁ e₁ F n)
      = foldF op₂ e₂ (fun i => app h (F i)) n :=
  foldF_map (g := fun x => app h x) h₁ hunit hmul hF

/-! ## Pairing off inverses

In an abelian group, a subset closed under inversion and containing no element
that is its own inverse folds to the identity: the elements come in pairs
`{x, x⁻¹}`, and each pair contributes `e`. The induction removes one pair at a
time. -/

def ginv (G op e a : ZFSet.{u}) : ZFSet.{u} := app (invMap G op e) a

theorem ginv_mem {G op e a : ZFSet.{u}} (h : IsGroup G op e) (ha : a ∈ G) :
    ginv G op e a ∈ G := (app_invMap h ha).left

theorem opAt_ginv {G op e a : ZFSet.{u}} (h : IsGroup G op e) (ha : a ∈ G) :
    opAt op (ginv G op e a) a = e := (app_invMap h ha).right.right

theorem ginv_ginv {G op e a : ZFSet.{u}} (h : IsGroup G op e) (ha : a ∈ G) :
    ginv G op e (ginv G op e a) = a :=
  inv_unique h (ginv_mem h ha) (ginv_mem h (ginv_mem h ha)) ha
    (app_invMap h (ginv_mem h ha)).right.left (app_invMap h ha).right.left

/-! ## Audit

The fold is choice-free: the enumeration is quantified over rather than chosen,
and the value is extracted from a singleton. -/

#print axioms foldF_skip
#print axioms foldF_peel_pair
#print axioms survPair
#print axioms skipAt_skipAt_origAt
#print axioms origAt_pair_ne
#print axioms sigma_survives
#print axioms origAt
#print axioms survAt
#print axioms origAt_ne
#print axioms survAt_origAt
#print axioms origAt_survAt
#print axioms skipAt_origAt
#print axioms foldF_reverse
#print axioms foldF_add
#print axioms foldF_pointwise_add
#print axioms foldF_drop_last
#print axioms foldF_trunc
#print axioms foldF_triangle
#print axioms foldF_swap

/-- A fold of zeros is zero, over a COMMUTATIVE MONOID.

`foldF_zeros` (`PolyRing` 961) says this over a RING -- and a module sum has
no multiplication -- `(V, vadd, vzero)` is a group -- so the ring hypothesis was
never doing work. Named `_monoid` rather than shadowing, following
`NumberTheory.matTrace_mem_closed_below`: the family name plus the mark saying which
hypothesis was dropped. -/
theorem foldF_zeros_monoid {M op e : ZFSet.{u}} (hM : IsCommMonoid M op e)
    {T : Nat → ZFSet.{u}} :
    ∀ n : Nat, (∀ i, i < n → T i = e) → foldF op e T n = e
  | 0, _ => rfl
  | n + 1, hz => by
    show opAt op (foldF op e T n) (T n) = e
    rw [foldF_zeros_monoid hM n (fun i hi => hz i (by omega)),
      hz n (by omega), hM.left_id _ hM.mem_e]

#print axioms foldF_zeros_monoid

/-- A fold supported at ONE index is that index's value, over a commutative
monoid -- `foldF_single_below` (`PolyRing` 1121) without the ring. This turns the
identity matrix's column into the basis vector it selects.

`IsCommMonoid` carries `left_id` only; the RIGHT identity is that plus
`comm`. -/
theorem foldF_single_below_monoid {M op e : ZFSet.{u}}
    (hM : IsCommMonoid M op e) {T : Nat → ZFSet.{u}} {k : Nat} (hTk : T k ∈ M) :
    ∀ n : Nat, k < n → (∀ i, i < n → i ≠ k → T i = e) →
      foldF op e T n = T k
  | 0, hk, _ => absurd hk (by omega)
  | n + 1, hk, hz => by
    show opAt op (foldF op e T n) (T n) = T k
    rcases Nat.eq_or_lt_of_le (show k + 1 ≤ n + 1 from hk) with heq | hlt
    · -- `obtain rfl` ELIMINATES one of the two names, so the bound is left to
      -- inference rather than written out
      obtain rfl : k = n := by omega
      rw [foldF_zeros_monoid hM _ (fun i hi => hz i (by omega) (by omega)),
        hM.left_id _ hTk]
    · have hfold : foldF op e T n ∈ M :=
        foldF_mem hM n (fun i hi => by
          -- `Nat` equality is DECIDABLE, so this `by_cases` is choice-free
          by_cases hik : i = k
          · rw [hik]; exact hTk
          · rw [hz i (by omega) hik]; exact hM.mem_e)
      -- `IsCommMonoid` carries `left_id` only; the right one is that plus `comm`
      rw [hz n (by omega) (by omega), hM.comm _ hfold _ hM.mem_e,
        hM.left_id _ hfold,
        foldF_single_below_monoid hM hTk n (by omega)
          (fun i hi hne => hz i (by omega) hne)]

#print axioms foldF_single_below_monoid
#print axioms foldF_unit
#print axioms hom_foldF_monoid

/-- A fold whose outermost pair is inverse reduces to the rest. -/
theorem foldF_peel_pair_collapse {G op e : ZFSet.{u}} (hG : IsGroup G op e)
    (hab : IsAbelian G op) {F : Nat → ZFSet.{u}} (n p : Nat)
    (hp : 0 < p) (hpn : p < n + 2) (hmem : ∀ i, F i ∈ G)
    (hpair : F p = ginv G op e (F 0)) :
    foldF op e F (n + 2) = foldF op e (skipAt 0 (skipAt p F)) n := by
  have hM := isCommMonoid_of_isGroup hG hab
  have h0 := hmem 0
  have hrest : foldF op e (skipAt 0 (skipAt p F)) n ∈ G := by
    refine foldF_mem hM n (fun i _ => ?_)
    rw [skipAt_skipAt_origAt]
    exact hmem _
  rw [foldF_peel_pair hM n p hp hpn (fun i _ => hmem i), hpair,
    hM.assoc _ hrest _ h0 _ (ginv_mem hG h0),
    hab _ h0 _ (ginv_mem hG h0), opAt_ginv hG h0,
    right_id_monoid hM hrest]

#print axioms foldF_peel_pair_collapse

/-- Out and back is the identity on survivor indices. -/
theorem survAt_pair_origAt (p i : Nat) :
    survAt 0 (survAt p (origAt p (origAt 0 i))) = i := by
  rw [survAt_origAt, survAt_origAt]

/-- Back and out is the identity on original indices avoiding `0` and `p`. -/
theorem origAt_pair_survAt {p x : Nat} (hp : 0 < p) (h0 : x ≠ 0) (hx : x ≠ p) :
    origAt p (origAt 0 (survAt 0 (survAt p x))) = x := by
  have hne : survAt p x ≠ 0 := by
    unfold survAt
    rcases Nat.lt_or_ge x p with h | h
    · rw [if_pos h]; exact h0
    · rw [if_neg (by omega)]; omega
  rw [origAt_survAt hne, origAt_survAt hx]

theorem survPair_nofix {sigma : Nat → Nat} {p n : Nat} (hp : 0 < p)
    (hinvol : ∀ i, i < n + 2 → sigma (sigma i) = i) (h0p : sigma 0 = p)
    (hnofix : ∀ i, i < n + 2 → sigma i ≠ i) {i : Nat} (hi : i < n) :
    survPair sigma p i ≠ i := by
  intro h
  have hx := origAt_pair_ne p i
  have hX : origAt p (origAt 0 i) < n + 2 := origAt_pair_lt hi
  have hs := sigma_survives (hinvol 0 (by omega)) (hinvol _ hX) h0p
    hx.left hx.right
  apply hnofix (origAt p (origAt 0 i)) hX
  have hout := congrArg (fun z => origAt p (origAt 0 z)) h
  show sigma (origAt p (origAt 0 i)) = origAt p (origAt 0 i)
  unfold survPair at hout
  simp only at hout
  rwa [origAt_pair_survAt hp hs.left hs.right] at hout

#print axioms survAt_pair_origAt
#print axioms origAt_pair_survAt
#print axioms survPair_nofix

/-- Coming back through both skips drops an index by two, when it avoids the
peeled pair. -/
theorem survAt_pair_lt {p x n : Nat} (hp : 0 < p) (hpn : p < n + 2)
    (hx : x < n + 2) (h0 : x ≠ 0) (hxp : x ≠ p) :
    survAt 0 (survAt p x) < n := by
  unfold survAt
  rcases Nat.lt_or_ge x p with h | h
  · rw [if_pos h]
    have : x ≠ 0 := h0
    rw [if_neg (show ¬ x < 0 by omega)]
    omega
  · rw [if_neg (by omega)]
    rcases Nat.lt_or_ge (x - 1) 0 with h1 | h1
    · omega
    · rw [if_neg (by omega)]
      omega

theorem survPair_maps {sigma : Nat → Nat} {p n : Nat} (hp : 0 < p)
    (hpn : p < n + 2) (hmaps : ∀ i, i < n + 2 → sigma i < n + 2)
    (hinvol : ∀ i, i < n + 2 → sigma (sigma i) = i) (h0p : sigma 0 = p)
    {i : Nat} (hi : i < n) : survPair sigma p i < n := by
  have hx := origAt_pair_ne p i
  have hX : origAt p (origAt 0 i) < n + 2 := origAt_pair_lt hi
  have hs := sigma_survives (hinvol 0 (by omega)) (hinvol _ hX) h0p
    hx.left hx.right
  exact survAt_pair_lt hp hpn (hmaps _ hX) hs.left hs.right

#print axioms survAt_pair_lt
#print axioms survPair_maps

theorem survPair_invol {sigma : Nat → Nat} {p n : Nat} (hp : 0 < p)
    (hinvol : ∀ i, i < n + 2 → sigma (sigma i) = i) (h0p : sigma 0 = p)
    {i : Nat} (hi : i < n) : survPair sigma p (survPair sigma p i) = i := by
  have hx := origAt_pair_ne p i
  have hX : origAt p (origAt 0 i) < n + 2 := origAt_pair_lt hi
  have hs := sigma_survives (hinvol 0 (by omega)) (hinvol _ hX) h0p
    hx.left hx.right
  show survAt 0 (survAt p (sigma (origAt p (origAt 0 (survPair sigma p i))))) = i
  unfold survPair
  rw [origAt_pair_survAt hp hs.left hs.right, hinvol _ hX, survAt_pair_origAt]


theorem survPair_pairs {G op e : ZFSet.{u}} {F : Nat → ZFSet.{u}}
    {sigma : Nat → Nat} {p n : Nat} (hp : 0 < p)
    (hinvol : ∀ i, i < n + 2 → sigma (sigma i) = i) (h0p : sigma 0 = p)
    (hpairs : ∀ j, j < n + 2 → F (sigma j) = ginv G op e (F j))
    {i : Nat} (hi : i < n) :
    skipAt 0 (skipAt p F) (survPair sigma p i)
      = ginv G op e (skipAt 0 (skipAt p F) i) := by
  have hx := origAt_pair_ne p i
  have hX : origAt p (origAt 0 i) < n + 2 := origAt_pair_lt hi
  have hs := sigma_survives (hinvol 0 (by omega)) (hinvol _ hX) h0p
    hx.left hx.right
  rw [skipAt_skipAt_origAt, skipAt_skipAt_origAt]
  show F (origAt p (origAt 0 (survPair sigma p i)))
    = ginv G op e (F (origAt p (origAt 0 i)))
  unfold survPair
  rw [origAt_pair_survAt hp hs.left hs.right, hpairs _ hX]

#print axioms survPair_invol
#print axioms survPair_pairs

/-- The conditioned recursion: the involution's clauses are asked for on
`{0..n-1}` only, which is what a partial involution can supply. -/
theorem foldF_involution {G op e : ZFSet.{u}} (hG : IsGroup G op e)
    (hab : IsAbelian G op) :
    ∀ n : Nat, ∀ F : Nat → ZFSet.{u}, ∀ sigma : Nat → Nat,
      (∀ i, F i ∈ G) →
      (∀ i, i < n → sigma (sigma i) = i) → (∀ i, i < n → sigma i ≠ i) →
      (∀ i, i < n → sigma i < n) →
      (∀ i, i < n → F (sigma i) = ginv G op e (F i)) →
      foldF op e F n = e := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => intro _ _ _ _ _ _ _; rfl
    | 1 =>
      intro _ sigma _ _ hnofix hmaps _
      exact absurd (show sigma 0 = 0 by have := hmaps 0 (by omega); omega)
        (hnofix 0 (by omega))
    | m + 2 =>
      intro F sigma hmem hinvol hnofix hmaps hpairs
      have h0 : (0 : Nat) < m + 2 := by omega
      have hppos : 0 < sigma 0 := by
        rcases Nat.eq_zero_or_pos (sigma 0) with h | h
        · exact absurd h (hnofix 0 h0)
        · exact h
      rw [foldF_peel_pair_collapse hG hab m (sigma 0) hppos (hmaps 0 h0) hmem
        (hpairs 0 h0)]
      exact ih m (by omega) _ (survPair sigma (sigma 0))
        (fun i => by rw [skipAt_skipAt_origAt]; exact hmem _)
        (fun i hi => survPair_invol hppos hinvol rfl hi)
        (fun i hi => survPair_nofix hppos hinvol rfl hnofix hi)
        (fun i hi => survPair_maps hppos (hmaps 0 h0) hmaps hinvol rfl hi)
        (fun i hi => survPair_pairs hppos hinvol rfl hpairs hi)

#print axioms foldF_involution

/-- The bounded twin of `foldF_mem_closed`. A fold over `0..n-1` only ever
evaluates `F` below `n`, so requiring membership at EVERY index is stronger than
the fold needs -- and the difference bites whenever `F` is defined by cases that
fail at the boundary. -/
theorem foldF_mem_closed_below {S add zero : ZFSet.{u}} (hz : zero ∈ S)
    (hadd : ∀ a, a ∈ S → ∀ b, b ∈ S → opAt add a b ∈ S)
    (F : Nat → ZFSet.{u}) :
    ∀ n : Nat, (∀ i, i < n → F i ∈ S) → foldF add zero F n ∈ S
  | 0, _ => hz
  | n + 1, hF =>
    hadd _ (foldF_mem_closed_below hz hadd F n (fun i hi => hF i (by omega)))
      _ (hF n (Nat.lt_succ_self n))

#print axioms foldF_mem_closed_below

#print axioms IsCommMonoid.toMonoid
#print axioms gpow_add_of_commMonoid
end Algebra

namespace ZFSet
export Algebra (IsCommMonoid flat_div_mod flat_lt foldF foldF_add foldF_congr foldF_cons foldF_const foldF_drop_last foldF_flatten foldF_involution foldF_map foldF_mem foldF_mem_closed foldF_mem_closed_below foldF_peel_pair foldF_peel_pair_collapse foldF_pointwise_add foldF_reverse foldF_single_below_monoid foldF_skip foldF_split foldF_swap foldF_triangle foldF_trunc foldF_unit foldF_zeros_monoid ginv ginv_ginv ginv_mem gpow_add_of_commMonoid hom_foldF_monoid isCommMonoid_of_isGroup left_comm_monoid opAt_ginv opAt_mem_monoid opAt_shuffle4 origAt origAt_ne origAt_pair_lt origAt_pair_ne origAt_pair_survAt origAt_survAt right_id_monoid sigma_survives skipAt skipAt_ge skipAt_lt skipAt_origAt skipAt_skipAt_origAt survAt survAt_origAt survAt_pair_lt survAt_pair_origAt survPair survPair_invol survPair_maps survPair_nofix survPair_pairs)
end ZFSet
