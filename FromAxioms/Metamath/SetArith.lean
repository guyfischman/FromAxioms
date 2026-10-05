/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# ω-arithmetic in the ∈-language

The domain formula -- "x is a natural number", said without infinity
-- and the graphs of Q's four function symbols, all in the purely relational
set language whose one atom is `memF`.

The domain is not bare ordinal-ness. It is "x is an ordinal and every member
of `x ∪ {x}` is empty or a successor" -- the induction-free characterisation
of the naturals, chosen so that Q's predecessor axiom is derivable from the
definition of the domain rather than from an induction the object theory
does not have.
-/

import FromAxioms.Metamath.FirstOrder

namespace Metamath

/-- "Index `a` is empty": `∀z, z ∉ x`. -/
def emptyF (a : Nat) : Formula := .all (fnot (memF 0 (a + 1)))

/-- "Index `b` is the successor of index `a`": `∀z (z ∈ b ↔ z ∈ a ∨ z = a)`,
the biconditional split as a conjunction of implications. -/
def succIsF (b a : Nat) : Formula :=
  .all (.conj
    (.imp (memF 0 (b + 1))
      (.disj (memF 0 (a + 1)) (.eq (.var 0) (.var (a + 1)))))
    (.imp (.disj (memF 0 (a + 1)) (.eq (.var 0) (.var (a + 1))))
      (memF 0 (b + 1))))

/-- "Index `a` is transitive": `∀y ∀z (y ∈ a ∧ z ∈ y → z ∈ a)`. -/
def memTransF (a : Nat) : Formula :=
  .all (.all (.imp (.conj (memF 1 (a + 2)) (memF 0 1)) (memF 0 (a + 2))))

/-- "Membership is linear on index `a`". -/
def linF (a : Nat) : Formula :=
  .all (.all (.imp (.conj (memF 1 (a + 2)) (memF 0 (a + 2)))
    (.disj (memF 1 0) (.disj (.eq (.var 1) (.var 0)) (memF 0 1)))))

/-- "Every member of index `a` is transitive". -/
def membersTransF (a : Nat) : Formula :=
  .all (.imp (memF 0 (a + 1)) (memTransF 0))

/-- "Index `a` is an ordinal", von Neumann style: transitive, members
transitive, and ∈-linear. Foundation is not assumed; linearity is stated
outright. -/
def ordF (a : Nat) : Formula :=
  .conj (memTransF a) (.conj (membersTransF a) (linF a))

/-- "Index `a` is empty or a successor of one of its members". -/
def succOrZeroF (a : Nat) : Formula :=
  .disj (emptyF a) (.ex (.conj (memF 0 (a + 1)) (succIsF (a + 1) 0)))

/-- The domain: "index `a` is a natural number." An ordinal, every member
of whose `x ∪ {x}` is empty or a successor. The second conjunct quantifies
over `z ∈ a ∨ z = a` and asserts `succOrZeroF` of the bound variable. -/
def natF (a : Nat) : Formula :=
  .conj (ordF a)
    (.all (.imp (.disj (memF 0 (a + 1)) (.eq (.var 0) (.var (a + 1))))
      (succOrZeroF 0)))

/-! ## Pairs and applications

The add and mul graphs say "there is a finite course-of-values function",
and the set language has no function symbols -- so pairs, membership of a
pair, and application are all formulas, indices threaded by hand. -/

/-- "Index `p` is the unordered pair of indices `u` and `v`". -/
def pairIsF (p u v : Nat) : Formula :=
  .all (.conj
    (.imp (memF 0 (p + 1))
      (.disj (.eq (.var 0) (.var (u + 1))) (.eq (.var 0) (.var (v + 1)))))
    (.imp (.disj (.eq (.var 0) (.var (u + 1))) (.eq (.var 0) (.var (v + 1))))
      (memF 0 (p + 1))))

/-- "Index `p` is the Kuratowski pair `⟨u, v⟩`": there are `a = {u}` and
`b = {u, v}` with `p = {a, b}`. -/
def opIsF (p u v : Nat) : Formula :=
  .ex (.ex (.conj (pairIsF 1 (u + 2) (u + 2))
    (.conj (pairIsF 0 (u + 2) (v + 2)) (pairIsF (p + 2) 1 0))))

/-- "`⟨u, v⟩` is a member of index `f`". -/
def memOpF (f u v : Nat) : Formula :=
  .ex (.conj (memF 0 (f + 1)) (opIsF 0 (u + 1) (v + 1)))

/-! ## The addition graph

"`c = a + b`", by a course-of-values function on `b ∪ {b}`: `f(∅) = a`,
`f(w ∪ {w}) = f(w) ∪ {f(w)}`, and `c = f(b)`. The witness `f` is bound
first, so inside the body the parameters sit one deeper; each clause's
local binders shift them further, and every index below is the result of
that hand computation. -/

/-- Clause: `f ⊆ (b ∪ {b}) × V` -- every member of `f` is a pair whose
first component is in the recursion's domain. -/
def addDomF (b : Nat) : Formula :=
  .all (.imp (memF 0 1)
    (.ex (.ex (.conj (opIsF 2 1 0)
      (.disj (memF 1 (b + 4)) (.eq (.var 1) (.var (b + 4))))))))


/-- Clause: `f` is single-valued. -/
def addFunF : Formula :=
  .all (.all (.all (.imp
    (.conj (memOpF 3 2 1) (memOpF 3 2 0)) (.eq (.var 1) (.var 0)))))

/-- Clause: `f` is defined on all of `b ∪ {b}`. -/
def addTotF (b : Nat) : Formula :=
  .all (.imp (.disj (memF 0 (b + 2)) (.eq (.var 0) (.var (b + 2))))
    (.ex (memOpF 2 1 0)))

/-- Clause: the base -- `f(∅) = a`, where `a` is the parameter and the referent
is ambient slot `a+1`. The equation sits under the clause's two binders, so it
is written `.var (a+3)`. -/
def addBaseF (a : Nat) : Formula :=
  .all (.all (.imp (.conj (emptyF 1) (memOpF 2 1 0))
    (.eq (.var 0) (.var (a + 3)))))

/-- Clause: the step -- `f(w ∪ {w})` is the successor of `f(w)`. -/
def addStepF : Formula :=
  .all (.all (.all (.all (.imp
    (.conj (succIsF 2 3) (.conj (memOpF 4 3 1) (memOpF 4 2 0)))
    (succIsF 0 1)))))

/-- The graph of addition: `c = a + b`, with the recursion's witness
existentially bound. Args at `a`, `b`; value at `c`. -/
def addRelF (a b c : Nat) : Formula :=
  .ex (.conj (addDomF b)
    (.conj addFunF
      (.conj (addTotF b)
        (.conj (addBaseF a)
          (.conj addStepF (memOpF 0 (b + 1) (c + 1)))))))

/-- The graph of addition over the wide relation: the domain bound is
dropped, so any graph carrying the recursion relates the arguments to the
value. Uniqueness clauses quantify over this relation: a
value read off a larger graph then descends without being restricted
first. `addRelF` implies it by dropping a conjunct. -/
def addRelW (a b c : Nat) : Formula :=
  .ex (.conj addFunF
    (.conj (addTotF b)
      (.conj (addBaseF a)
        (.conj addStepF (memOpF 0 (b + 1) (c + 1))))))

/-! ## The multiplication graph

The same witness skeleton with the base sent to zero and the step adding
the first argument -- the one place a graph mentions another graph. -/

/-- Clause: the base -- `f(∅) = ∅`. -/
def mulBaseF : Formula :=
  .all (.all (.imp (.conj (emptyF 1) (memOpF 2 1 0)) (emptyF 0)))

/-- Clause: the step -- `f(w ∪ {w}) = f(w) + a`, through the addition
graph. -/
def mulStepF (a : Nat) : Formula :=
  .all (.all (.all (.all (.imp
    (.conj (succIsF 2 3) (.conj (memOpF 4 3 1) (memOpF 4 2 0)))
    (addRelF 1 (a + 5) 0)))))

/-- The graph of multiplication: `c = a · b`. Args at `a`, `b`; value
at `c`. -/
def mulRelF (a b c : Nat) : Formula :=
  .ex (.conj (addDomF b)
    (.conj addFunF
      (.conj (addTotF b)
        (.conj mulBaseF
          (.conj (mulStepF a) (memOpF 0 (b + 1) (c + 1)))))))

/-- The multiplication graph over the wide relation. -/
def mulRelW (a b c : Nat) : Formula :=
  .ex (.conj addFunF
    (.conj (addTotF b)
      (.conj mulBaseF
        (.conj (mulStepF a) (memOpF 0 (b + 1) (c + 1))))))

/-! ## The Solovay cut

The domain carries its own arithmetic closure. Each layer says "for every good
argument, the recursion witness up to me exists, is a natural, and is unique"
-- existence for the relativised totality, uniqueness for functionality,
naturality so the witness stays in the domain. Multiplication's layer guards
its arguments with the addition layer, so its successor-closure step can use
addition. -/

/-- The addition-closure clause at index `c`: every natural argument has a
unique natural sum with `c`. -/
def cutAddF (c : Nat) : Formula :=
  .all (.imp (natF 0)
    (.conj
      (.ex (.conj (natF 0) (addRelF 1 (c + 2) 0)))
      (.all (.all (.imp (addRelW 2 (c + 3) 1)
        (.imp (addRelW 2 (c + 3) 0) (.eq (.var 1) (.var 0))))))))

/-- The certificate layer at index `c`: for every natural
argument, a named witness graph whose value carries an exhaustion certificate
-- every member of the sum is in the argument or among the graph's values. -/
def cutAddCertF (c : Nat) : Formula :=
  .all (.imp (natF 0)
    (.ex (.ex (.conj (natF 1)
      (.conj (addDomF (c + 2))
      (.conj addFunF
        (.conj (addTotF (c + 2))
          (.conj (addBaseF 1)
            (.conj addStepF
              (.conj (memOpF 0 (c + 3) 1)
                (.conj
                  (.all (.imp (memF 0 2)
                    (.disj (memF 0 3) (.ex (memOpF 2 0 1)))))
                  (.all (.imp (.ex (memOpF 2 0 1))
                    (.disj (memF 0 2) (.eq (.var 0) (.var 2))))))))))))))))

/-- The first layer: a natural, closed under addition from natural
arguments, with the certificate. -/
def deltaAddF (c : Nat) : Formula :=
  .conj (natF c) (.conj (cutAddF c) (cutAddCertF c))

/-- The multiplication-closure clause, guarded by the first layer. -/
def cutMulF (c : Nat) : Formula :=
  .all (.imp (deltaAddF 0)
    (.conj
      (.ex (.conj (deltaAddF 0) (mulRelF 1 (c + 2) 0)))
      (.all (.all (.imp (mulRelW 2 (c + 3) 1)
        (.imp (mulRelW 2 (c + 3) 0) (.eq (.var 1) (.var 0))))))))

/-- The domain: both layers. -/
def deltaF (c : Nat) : Formula := .conj (deltaAddF c) (cutMulF c)

end Metamath

namespace ZFSet
export Metamath (addBaseF addDomF addFunF addRelF addRelW addStepF addTotF cutAddCertF cutAddF cutMulF deltaAddF deltaF emptyF linF memOpF memTransF membersTransF mulBaseF mulRelF mulRelW mulStepF natF opIsF ordF pairIsF succIsF succOrZeroF)
end ZFSet
