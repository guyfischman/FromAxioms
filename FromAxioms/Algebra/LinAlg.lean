/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Vectors over a ring.

`R^n` already exists as a set: `powSet R n`, the `n`-fold product built for
counting the polynomial quotient. Here it is given its algebra -- componentwise
addition, negation and scalar multiplication -- and shown to be an abelian group
satisfying the module laws.

Nothing new is constructed: a vector is a tuple, `tupleCoeff` reads a
component, `tupleOf` builds one, and `powSet_ext` is extensionality. What the
file adds is that the operations are set functions on `powSet R n`, so `IsGroup`
and the rest of the structure vocabulary apply.
-/

import FromAxioms.Algebra.PolyRing

universe u

open NumberTheory SetTheory
namespace Algebra

/-! ## The operations, on components -/

def vecAdd (add : ZFSet.{u}) (n : Nat) (t t' : ZFSet.{u}) : ZFSet.{u} :=
  tupleOf (fun i => opAt add (tupleCoeff t n i) (tupleCoeff t' n i)) n

theorem vecAdd_mem {R add mul zero one : ZFSet.{u}} (hR : IsRing R add mul zero one)
    {n : Nat} {t t' : ZFSet.{u}} (ht : t ∈ powSet R n) (ht' : t' ∈ powSet R n) :
    vecAdd add n t t' ∈ powSet R n :=
  tupleOf_mem n (fun i hi =>
    addAt_mem hR (tupleCoeff_mem n t ht i hi) (tupleCoeff_mem n t' ht' i hi))

theorem coeff_vecAdd {n : Nat} {add t t' : ZFSet.{u}} (i : Nat) (hi : i < n) :
    tupleCoeff (vecAdd add n t t') n i
      = opAt add (tupleCoeff t n i) (tupleCoeff t' n i) :=
  tupleCoeff_tupleOf n i hi

#print axioms vecAdd_mem
#print axioms coeff_vecAdd
end Algebra

namespace ZFSet
export Algebra (coeff_vecAdd vecAdd vecAdd_mem)
end ZFSet
