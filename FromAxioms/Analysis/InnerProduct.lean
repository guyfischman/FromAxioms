/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

import FromAxioms.Algebra.TowerLaw

open Algebra SetTheory
namespace Analysis

universe u

/-! ## Symmetry -/

/-- The dot product of two lists over a ring is symmetric. The lists need not
have equal length. -/
theorem dot_comm {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one) :
    ∀ (xs ys : List ZFSet.{u}), (∀ a, a ∈ xs → a ∈ R) → (∀ b, b ∈ ys → b ∈ R) →
      lincomb add mul zero xs ys = lincomb add mul zero ys xs
  | [], ys, _, _ => by
    rw [lincomb_nil_left, lincomb_nil_right]
  | x :: xs, [], _, _ => by
    rw [lincomb_nil_left, lincomb_nil_right]
  | x :: xs, y :: ys, hxs, hys => by
    rw [lincomb_cons, lincomb_cons,
      hR.mulComm _ (hxs x List.mem_cons_self) _ (hys y List.mem_cons_self),
      dot_comm hR xs ys (fun a ha => hxs a (List.mem_cons_of_mem _ ha))
        (fun b hb => hys b (List.mem_cons_of_mem _ hb))]

/-- The dot product is additive in its left argument. -/
theorem dot_vec_add_left {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) {n : Nat} {x x' y : ZFSet.{u}}
    (hx : x ∈ powSet R n) (hx' : x' ∈ powSet R n) (hy : y ∈ powSet R n) :
    lincomb add mul zero (tupleToList (vecAdd add n x x') n) (tupleToList y n)
      = opAt add (lincomb add mul zero (tupleToList x n) (tupleToList y n))
          (lincomb add mul zero (tupleToList x' n) (tupleToList y n)) := by
  rw [tupleToList_vecAdd]
  exact lincomb_zipWith_add (isModule_self hR) _ _ _
    (by rw [tupleToList_length, tupleToList_length])
    (tupleToList_mem hx) (tupleToList_mem hx') (tupleToList_mem hy)

/-- Additivity in the second argument, by symmetry rather than by a second
induction. Bilinearity is one law and a commutation, so `dot_comm` carries the
second half, and it is stated without a length hypothesis. -/
theorem dot_vec_add_right {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) {n : Nat} {x y y' : ZFSet.{u}}
    (hx : x ∈ powSet R n) (hy : y ∈ powSet R n) (hy' : y' ∈ powSet R n) :
    lincomb add mul zero (tupleToList x n) (tupleToList (vecAdd add n y y') n)
      = opAt add (lincomb add mul zero (tupleToList x n) (tupleToList y n))
          (lincomb add mul zero (tupleToList x n) (tupleToList y' n)) := by
  rw [dot_comm hR _ _ (tupleToList_mem hx)
        (tupleToList_mem (vecAdd_mem hR hy hy')),
    dot_vec_add_left hR hy hy' hx,
    dot_comm hR _ _ (tupleToList_mem hy) (tupleToList_mem hx),
    dot_comm hR _ _ (tupleToList_mem hy') (tupleToList_mem hx)]

/-! ## The bridge to the two-coordinate form -/

/-- Pythagoras in `R ^ n` over any ring: if `<x, y> = 0`, then `<x + y, x + y> =
<x, x> + <y, y>`. -/
theorem dot_vec_add_self_of_orth {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) {n : Nat} {x y : ZFSet.{u}}
    (hx : x ∈ powSet R n) (hy : y ∈ powSet R n)
    (horth : lincomb add mul zero (tupleToList x n) (tupleToList y n) = zero) :
    lincomb add mul zero (tupleToList (vecAdd add n x y) n)
        (tupleToList (vecAdd add n x y) n)
      = opAt add (lincomb add mul zero (tupleToList x n) (tupleToList x n))
          (lincomb add mul zero (tupleToList y n) (tupleToList y n)) := by
  have hxy : vecAdd add n x y ∈ powSet R n := vecAdd_mem hR hx hy
  rw [dot_vec_add_left hR hx hy hxy, dot_vec_add_right hR hx hx hy,
    dot_vec_add_right hR hy hx hy, horth]
  have hyx : lincomb add mul zero (tupleToList y n) (tupleToList x n) = zero := by
    rw [dot_comm hR _ _ (tupleToList_mem hy) (tupleToList_mem hx)]
    exact horth
  rw [hyx]
  -- what is left is zero-elimination in the ring: the two cross terms are the
  -- ring's zero, and `lincomb` folds onto that zero at each end.
  -- `isModule_self` makes the ring a module over itself, which is what
  -- `lincomb_mem` needs and what `dot_vec_add_left` already used.
  have hxx : lincomb add mul zero (tupleToList x n) (tupleToList x n) ∈ R :=
    lincomb_mem (isModule_self hR) _ _ (tupleToList_mem hx) (tupleToList_mem hx)
  have hyy : lincomb add mul zero (tupleToList y n) (tupleToList y n) ∈ R :=
    lincomb_mem (isModule_self hR) _ _ (tupleToList_mem hy) (tupleToList_mem hy)
  rw [ringAdd_zero hR hxx, ringZero_add hR hyy]

/-- `<x + y, x + y> = (<x, x> + <x, y>) + (<x, y> + <y, y>)` in `R ^ n` over any
ring. -/
theorem dot_vec_add_self {R add mul zero one : ZFSet.{u}}
    (hR : IsRing R add mul zero one) {n : Nat} {x y : ZFSet.{u}}
    (hx : x ∈ powSet R n) (hy : y ∈ powSet R n) :
    lincomb add mul zero (tupleToList (vecAdd add n x y) n)
        (tupleToList (vecAdd add n x y) n)
      = opAt add
          (opAt add (lincomb add mul zero (tupleToList x n) (tupleToList x n))
            (lincomb add mul zero (tupleToList x n) (tupleToList y n)))
          (opAt add (lincomb add mul zero (tupleToList x n) (tupleToList y n))
            (lincomb add mul zero (tupleToList y n) (tupleToList y n))) := by
  have hxy : vecAdd add n x y ∈ powSet R n := vecAdd_mem hR hx hy
  rw [dot_vec_add_left hR hx hy hxy, dot_vec_add_right hR hx hx hy,
    dot_vec_add_right hR hy hx hy,
    dot_comm hR _ _ (tupleToList_mem hy) (tupleToList_mem hx)]

#print axioms Analysis.dot_vec_add_self

#print axioms Analysis.dot_vec_add_self_of_orth

#print axioms Analysis.dot_comm
#print axioms Analysis.dot_vec_add_left
#print axioms Analysis.dot_vec_add_right
end Analysis
namespace ZFSet
export Analysis (dot_comm dot_vec_add_left dot_vec_add_right dot_vec_add_self dot_vec_add_self_of_orth)
end ZFSet
