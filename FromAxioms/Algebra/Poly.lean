/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Polynomials over a ring, and the bound on roots.

A polynomial is a Lean-level list of coefficients, lowest first, evaluated into
a ring by Horner's rule. It is not a set: nothing here needs `R[x]` as an
object, and the theorem that is wanted -- a polynomial with a non-zero
coefficient has fewer roots than it has coefficients -- quantifies over roots,
which are sets. `Prime.lean` already makes the same choice for `List Nat`.

`polyDiv a cs` is synthetic division by `x - a`, and `polyDiv_spec` is the
identity `p(x) = (x - a)·q(x) + p(a)`, with `q` one coefficient shorter. Over a
field that gives the bound by induction on the number of coefficients: a root
`a` splits off, every other root is a root of `q` because a field has no zero
divisors, and `q` is shorter.

The statement proved is the contrapositive -- too many roots forces every
coefficient to zero -- because "non-zero polynomial" has to mean non-zero
coefficients, not a non-zero function: over a finite field `x^p - x` vanishes
everywhere.
-/

import FromAxioms.Algebra.Ring

universe u

open NumberTheory SetTheory
namespace Algebra

/-! ## Evaluation -/

def polyEval (add mul zero : ZFSet.{u}) : List ZFSet.{u} → ZFSet.{u} → ZFSet.{u}
  | [], _ => zero
  | c :: cs, x => opAt add c (opAt mul x (polyEval add mul zero cs x))

theorem polyEval_mem {R add mul zero one : ZFSet.{u}} (h : IsRing R add mul zero one)
    {x : ZFSet.{u}} (hx : x ∈ R) :
    ∀ cs : List ZFSet.{u}, (∀ c, c ∈ cs → c ∈ R) → polyEval add mul zero cs x ∈ R
  | [], _ => h.addGroup.mem_e
  | c :: cs, hcs =>
    addAt_mem h (hcs c (List.mem_cons_self))
      (mulAt_mem h hx (polyEval_mem h hx cs
        (fun d hd => hcs d (List.mem_cons_of_mem _ hd))))

end Algebra

namespace ZFSet
export Algebra (polyEval polyEval_mem)
end ZFSet
