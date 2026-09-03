/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Robinson arithmetic in the object language

`FirstOrder.lean` gives a language with function symbols and a semantics that
reads a formula into `Prop` relative to a domain, an interpretation of the
function symbols, and one of the relation symbols. This file uses all three
parameters at once for the first time: the domain is `ω`, the function symbols
are zero, successor, addition and multiplication, and there are no relation
symbols at all.

Q is the weakest theory that still proves every true `Σ₁` sentence, and the one
Gödel's argument actually needs -- induction is not required for incompleteness,
only enough arithmetic to compute with numerals. Writing it here is the step
that lets a provability predicate be a formula rather than a metatheoretic
notion.

Every axiom of Q is verified against `ω` by unfolding the interpretation and
appealing to the recursion equations already proved in `Arith.lean`. The only
one with content is Q3 -- every non-zero element is a successor -- and it is
choice-free because `mem_omega_iff` names the numeral rather than asserting one
exists.

This file is Q itself and what Q derives about numerals. The arithmetic carried
out inside Q -- the order, bounded quantification, the pairing graph, the
least witness, the β-function, and representability with them -- is
`QArith.lean`; the bounded fragment and Sigma-1 completeness are
`Bounded.lean`; the representability of each primitive recursive constructor is
`Representable.lean`. All three depend on this one and none is depended on by
it.
-/

import FromAxioms.Analysis.Ternary
import FromAxioms.Metamath.FirstOrder
import FromAxioms.NumberTheory.Prime

universe u

open NumberTheory SetTheory
namespace Metamath

/-! ## The signature

Four function symbols, indexed by the arity they are meant to have. A symbol
applied to the wrong number of arguments evaluates to `∅`: the interpretation is
total, as `Term` places no arity constraint, and no axiom of Q writes such a
term. -/

def arithInterp : Nat → List ZFSet.{u} → ZFSet.{u}
  | 0, _ => empty.{u}
  | 1, [a] => succ a
  | 2, [a, b] => add a b
  | 3, [a, b] => mul a b
  | _, _ => empty.{u}

def tZero : Term := .func 0 []

def tSucc (t : Term) : Term := .func 1 [t]

def tAdd (s t : Term) : Term := .func 2 [s, t]

def tMul (s t : Term) : Term := .func 3 [s, t]

/-- The numeral naming `n`: `n` applications of the successor symbol to zero.
This is the bridge every representability argument runs over -- a `Nat` of the
metatheory becomes a closed term of the object language. -/
def numeral : Nat → Term
  | 0 => tZero
  | n + 1 => tSucc (numeral n)

@[simp] theorem evalT_tZero (env : Nat → ZFSet.{u}) :
    evalT arithInterp.{u} env tZero = empty.{u} := rfl

@[simp] theorem evalT_tSucc (env : Nat → ZFSet.{u}) (t : Term) :
    evalT arithInterp.{u} env (tSucc t) = succ (evalT arithInterp.{u} env t) := rfl

@[simp] theorem evalT_tAdd (env : Nat → ZFSet.{u}) (s t : Term) :
    evalT arithInterp.{u} env (tAdd s t)
      = add (evalT arithInterp.{u} env s) (evalT arithInterp.{u} env t) := rfl

@[simp] theorem evalT_tMul (env : Nat → ZFSet.{u}) (s t : Term) :
    evalT arithInterp.{u} env (tMul s t)
      = mul (evalT arithInterp.{u} env s) (evalT arithInterp.{u} env t) := rfl

/-- A numeral denotes its number. The clause the whole development rests on:
what the object language says about `numeral n` is what the metatheory says
about `ofNat n`. -/
@[simp] theorem evalT_numeral (env : Nat → ZFSet.{u}) :
    ∀ n : Nat, evalT arithInterp.{u} env (numeral n) = ofNat.{u} n
  | 0 => rfl
  | n + 1 => by rw [numeral, evalT_tSucc, evalT_numeral env n, ofNat_succ]

/-! ## The axioms

Seven, in de Bruijn indices: under `.all (.all φ)` the outer variable is index
`1` and the inner is index `0`. -/

/-- `∀x ∀y (Sx = Sy → x = y)`. -/
def qSuccInj : Formula :=
  .all (.all (.imp (.eq (tSucc (.var 1)) (tSucc (.var 0))) (.eq (.var 1) (.var 0))))

/-- `∀x (Sx ≠ 0)`. -/
def qSuccNeZero : Formula :=
  .all (.imp (.eq (tSucc (.var 0)) tZero) .fls)

/-- `∀x (x = 0 ∨ ∃y (x = Sy))`. The axiom that replaces induction: the domain has
no elements beyond the numerals, one step at a time.

A disjunction, not the textbook implication `x ≠ 0 → ∃y (x = Sy)`. The two are
classically interderivable and intuitionistically are not, and `DerivesFO` is
intuitionistic, so the implication form cannot be used the way the standard
proofs use it. -/
def qPred : Formula :=
  .all (.disj (.eq (.var 0) tZero) (.ex (.eq (.var 1) (tSucc (.var 0)))))

/-- `∀x (x + 0 = x)`. -/
def qAddZero : Formula := .all (.eq (tAdd (.var 0) tZero) (.var 0))

/-- `∀x ∀y (x + Sy = S(x + y))`. -/
def qAddSucc : Formula :=
  .all (.all (.eq (tAdd (.var 1) (tSucc (.var 0))) (tSucc (tAdd (.var 1) (.var 0)))))

/-- `∀x (x · 0 = 0)`. -/
def qMulZero : Formula := .all (.eq (tMul (.var 0) tZero) tZero)

/-- `∀x ∀y (x · Sy = x · y + x)`. -/
def qMulSucc : Formula :=
  .all (.all (.eq (tMul (.var 1) (tSucc (.var 0)))
    (tAdd (tMul (.var 1) (.var 0)) (.var 1))))

/-! ## What Q derives

Every term here is closed, and that is the property the equality rules need:
`eq_subst` replaces one term by another inside a formula, so the surrounding
terms must survive the substitution untouched. -/

def QCtx : List Formula :=
  [qSuccInj, qSuccNeZero, qPred, qAddZero, qAddSucc, qMulZero, qMulSucc]

#print axioms arithInterp
#print axioms evalT_numeral
end Metamath

namespace ZFSet
export Metamath (QCtx arithInterp evalT_numeral evalT_tAdd evalT_tMul evalT_tSucc evalT_tZero numeral qAddSucc qAddZero qMulSucc qMulZero qPred qSuccInj qSuccNeZero tAdd tMul tSucc tZero)
end ZFSet
