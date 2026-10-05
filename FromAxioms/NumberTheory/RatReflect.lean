/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# Reflection for the rational fragment

The tree's rational algebra spends more text on membership than on arithmetic:
every application of `ratAdd`/`ratMul`/`ratNeg` carries a `_mem_Rat` witness.
`RatExpr.eval_mem` discharges the membership obligation once, by induction over
a syntax tree, for every expression at once, where a hand proof pays it per
subterm per rewrite. `flat` then turns an additive expression into a list of
signed atoms, so association and the placement of negations stop being rewrite
steps; `insertAtom`/`cancelAll` cancel matched pairs; and `evalSum_perm` says
the normal form may be reordered freely. The additive fragment carries
multiplication as an atom; the multiplicative fragment below expands it.

Nothing in this file reifies a goal. That is `RatRing.lean`, a `syntax`/`elab`
layer.
-/

import FromAxioms.NumberTheory.Rational

namespace NumberTheory

/-- Syntax of a commutative-ring expression over the rationals. `DecidableEq` is
derived, so it is structural and choice-free; an absent instance is exactly the
state in which instance search reaches for `Classical.propDecidable`. -/
inductive RatExpr where
  | var (i : Nat)
  | zero
  | one
  | add (a b : RatExpr)
  | mul (a b : RatExpr)
  | neg (a : RatExpr)
  deriving DecidableEq

/-- The denotation of a piece of syntax under an environment. -/
def RatExpr.eval (env : Nat → ZFSet.{u}) : RatExpr → ZFSet.{u}
  | .var i => env i
  | .zero => ratZero.{u}
  | .one => ratOne.{u}
  | .add a b => ratAdd (a.eval env) (b.eval env)
  | .mul a b => ratMul (a.eval env) (b.eval env)
  | .neg a => ratNeg (a.eval env)

/-- If every variable denotes a rational then so does every expression. -/
theorem RatExpr.eval_mem {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ e : RatExpr, e.eval env ∈ Rat.{u}
  | .var i => henv i
  | .zero => ratZero_mem_Rat
  | .one => ratOne_mem_Rat
  | .add a b => ratAdd_mem_Rat (RatExpr.eval_mem henv a) (RatExpr.eval_mem henv b)
  | .mul a b => ratMul_mem_Rat (RatExpr.eval_mem henv a) (RatExpr.eval_mem henv b)
  | .neg a => ratNeg_mem_Rat (RatExpr.eval_mem henv a)

/-- A signed atom: `(true, e)` denotes `-e`. Matching on the `Bool` rather than
testing it with `if` keeps the denotation reducing definitionally. -/
def evalAtom (env : Nat → ZFSet.{u}) : Bool × RatExpr → ZFSet.{u}
  | (true, e) => ratNeg (e.eval env)
  | (false, e) => e.eval env

/-- Flip an atom's sign. -/
def negAtom : Bool × RatExpr → Bool × RatExpr
  | (b, e) => (!b, e)

/-- The denotation of a normal form: a right-nested sum of signed atoms. -/
def evalSum (env : Nat → ZFSet.{u}) : List (Bool × RatExpr) → ZFSet.{u}
  | [] => ratZero.{u}
  | p :: t => ratAdd (evalAtom env p) (evalSum env t)

/-- An atom of a rational environment denotes a rational. -/
theorem evalAtom_mem {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ p : Bool × RatExpr, evalAtom env p ∈ Rat.{u}
  | (true, e) => ratNeg_mem_Rat (RatExpr.eval_mem henv e)
  | (false, e) => RatExpr.eval_mem henv e

/-- And so does a whole normal form. -/
theorem evalSum_mem {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ l : List (Bool × RatExpr), evalSum env l ∈ Rat.{u}
  | [] => ratZero_mem_Rat
  | p :: t => ratAdd_mem_Rat (evalAtom_mem henv p) (evalSum_mem henv t)

/-- Association becomes concatenation. Every `ratAdd_assoc` step a hand
proof would chain is paid here once, in the induction. -/
theorem evalSum_append {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ l1 l2 : List (Bool × RatExpr),
      evalSum env (l1 ++ l2) = ratAdd (evalSum env l1) (evalSum env l2)
  | [], l2 => (ratZero_add (evalSum_mem henv l2)).symm
  | p :: t, l2 => by
    show ratAdd (evalAtom env p) (evalSum env (t ++ l2))
      = ratAdd (ratAdd (evalAtom env p) (evalSum env t)) (evalSum env l2)
    rw [evalSum_append henv t l2,
      ratAdd_assoc (evalAtom_mem henv p) (evalSum_mem henv t) (evalSum_mem henv l2)]

/-- Negating an atom negates its denotation. The `true` case is where
`ratNeg_ratNeg` is spent. -/
theorem evalAtom_negAtom {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ p : Bool × RatExpr, evalAtom env (negAtom p) = ratNeg (evalAtom env p)
  | (false, _) => rfl
  | (true, e) => by
    show RatExpr.eval env e = ratNeg (ratNeg (RatExpr.eval env e))
    rw [ratNeg_ratNeg (RatExpr.eval_mem henv e)]

/-- Negation becomes a sign flip. `ratNeg_add` is spent once per cons here
and never at a call site. -/
theorem evalSum_map_neg {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ l : List (Bool × RatExpr),
      evalSum env (l.map negAtom) = ratNeg (evalSum env l)
  | [] => ratNeg_zero.symm
  | p :: t => by
    show ratAdd (evalAtom env (negAtom p)) (evalSum env (t.map negAtom))
      = ratNeg (ratAdd (evalAtom env p) (evalSum env t))
    rw [evalAtom_negAtom henv p, evalSum_map_neg henv t,
      ratNeg_add (evalAtom_mem henv p) (evalSum_mem henv t)]

/-- The additive normal form: a flat list of signed atoms. A `mul` is an atom,
which is what confines this file to the additive fragment. -/
def RatExpr.flat : RatExpr → List (Bool × RatExpr)
  | .zero => []
  | .add a b => a.flat ++ b.flat
  | .neg a => a.flat.map negAtom
  | .var i => [(false, .var i)]
  | .one => [(false, .one)]
  | .mul a b => [(false, .mul a b)]

/-- Soundness: the normal form denotes what the expression does. -/
theorem RatExpr.flat_sound {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ e : RatExpr, evalSum env e.flat = e.eval env
  | .zero => rfl
  | .var i => ratAdd_zero (henv i)
  | .one => ratAdd_zero ratOne_mem_Rat
  | .mul a b =>
    ratAdd_zero (ratMul_mem_Rat (RatExpr.eval_mem henv a) (RatExpr.eval_mem henv b))
  | .add a b => by
    show evalSum env (a.flat ++ b.flat) = ratAdd (a.eval env) (b.eval env)
    rw [evalSum_append henv a.flat b.flat, RatExpr.flat_sound henv a,
      RatExpr.flat_sound henv b]
  | .neg a => by
    show evalSum env (a.flat.map negAtom) = ratNeg (a.eval env)
    rw [evalSum_map_neg henv a.flat, RatExpr.flat_sound henv a]

/-- Adjacent transposition. One `ratAdd_comm` and two associativities. -/
theorem evalSum_swap {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u})
    (p q : Bool × RatExpr) (l : List (Bool × RatExpr)) :
    evalSum env (p :: q :: l) = evalSum env (q :: p :: l) := by
  show ratAdd (evalAtom env p) (ratAdd (evalAtom env q) (evalSum env l))
    = ratAdd (evalAtom env q) (ratAdd (evalAtom env p) (evalSum env l))
  rw [← ratAdd_assoc (evalAtom_mem henv p) (evalAtom_mem henv q) (evalSum_mem henv l),
    ← ratAdd_assoc (evalAtom_mem henv q) (evalAtom_mem henv p) (evalSum_mem henv l),
    ratAdd_comm (evalAtom_mem henv p) (evalAtom_mem henv q)]

/-- Reordering is free once transposition is proved: `List.Perm`'s four
constructors are reflexivity, congruence, transposition and transitivity, and
`evalSum_swap` supplies the `swap` case. -/
theorem evalSum_perm {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u})
    {l1 l2 : List (Bool × RatExpr)} (h : l1.Perm l2) :
    evalSum env l1 = evalSum env l2 := by
  induction h with
  | nil => rfl
  | cons p _ ih =>
    show ratAdd (evalAtom env p) (evalSum env _) = ratAdd (evalAtom env p) (evalSum env _)
    rw [ih]
  | swap a b l => exact evalSum_swap henv b a l
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- `a + (-a + s) = s`, a cancellation once the pair is adjacent. Distinct from
`ratAdd_sub_cancel`, `q + (p + -q) = p`, by one `ratAdd_comm`; this spelling is
the one `evalSum_cancel` and `insertAtom_sound` consume, because the normaliser
puts the negation on the left. -/
theorem ratAdd_neg_cancel_left {a s : ZFSet.{u}} (ha : a ∈ Rat.{u})
    (hs : s ∈ Rat.{u}) : ratAdd a (ratAdd (ratNeg a) s) = s := by
  rw [← ratAdd_assoc ha (ratNeg_mem_Rat ha) hs, ratAdd_neg ha, ratZero_add hs]

/-- An adjacent inverse pair at the head of a normal form cancels. -/
theorem evalSum_cancel {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u})
    (e : RatExpr) (l : List (Bool × RatExpr)) :
    evalSum env ((false, e) :: (true, e) :: l) = evalSum env l := by
  show ratAdd (e.eval env) (ratAdd (ratNeg (e.eval env)) (evalSum env l))
    = evalSum env l
  exact ratAdd_neg_cancel_left (RatExpr.eval_mem henv e) (evalSum_mem henv l)

/-- Cancellation anywhere, not only at the head, given a permutation that
brings the pair to the front. -/
theorem evalSum_cancel_perm {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u})
    (e : RatExpr) (l rest : List (Bool × RatExpr))
    (h : l.Perm ((false, e) :: (true, e) :: rest)) :
    evalSum env l = evalSum env rest :=
  (evalSum_perm henv h).trans (evalSum_cancel henv e rest)

/-- The search. Add an atom to an already-cancelled list: if its opposite is
present, both disappear. -/
def insertAtom (p : Bool × RatExpr) : List (Bool × RatExpr) → List (Bool × RatExpr)
  | [] => [p]
  | q :: t => if q = negAtom p then t else q :: insertAtom p t

/-- Inserting an atom adds its denotation, cancelling or not. -/
theorem insertAtom_sound {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u})
    (p : Bool × RatExpr) :
    ∀ l : List (Bool × RatExpr),
      evalSum env (insertAtom p l) = ratAdd (evalAtom env p) (evalSum env l)
  | [] => rfl
  | q :: t => by
    by_cases h : q = negAtom p
    · show evalSum env (if q = negAtom p then t else q :: insertAtom p t)
        = ratAdd (evalAtom env p) (evalSum env (q :: t))
      rw [if_pos h, h]
      show evalSum env t
        = ratAdd (evalAtom env p) (ratAdd (evalAtom env (negAtom p)) (evalSum env t))
      rw [evalAtom_negAtom henv p,
        ratAdd_neg_cancel_left (evalAtom_mem henv p) (evalSum_mem henv t)]
    · show evalSum env (if q = negAtom p then t else q :: insertAtom p t)
        = ratAdd (evalAtom env p) (evalSum env (q :: t))
      rw [if_neg h]
      show ratAdd (evalAtom env q) (evalSum env (insertAtom p t))
        = ratAdd (evalAtom env p) (evalSum env (q :: t))
      rw [insertAtom_sound henv p t]
      exact evalSum_swap henv q p t

/-- Cancel every matched pair in a flattened sum. -/
def cancelAll : List (Bool × RatExpr) → List (Bool × RatExpr)
  | [] => []
  | p :: t => insertAtom p (cancelAll t)

/-- And the cancelled form denotes the same rational. -/
theorem cancelAll_sound {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ l : List (Bool × RatExpr), evalSum env (cancelAll l) = evalSum env l
  | [] => rfl
  | p :: t => by
    show evalSum env (insertAtom p (cancelAll t))
      = ratAdd (evalAtom env p) (evalSum env t)
    rw [insertAtom_sound henv p (cancelAll t), cancelAll_sound henv t]


#print axioms NumberTheory.RatExpr
#print axioms NumberTheory.RatExpr.eval
#print axioms NumberTheory.RatExpr.eval_mem
#print axioms NumberTheory.evalAtom
#print axioms NumberTheory.negAtom
#print axioms NumberTheory.evalSum
#print axioms NumberTheory.evalAtom_mem
#print axioms NumberTheory.evalSum_mem
#print axioms NumberTheory.evalSum_append
#print axioms NumberTheory.evalAtom_negAtom
#print axioms NumberTheory.evalSum_map_neg
#print axioms NumberTheory.RatExpr.flat
#print axioms NumberTheory.RatExpr.flat_sound
#print axioms NumberTheory.evalSum_swap
#print axioms NumberTheory.evalSum_perm
#print axioms NumberTheory.ratAdd_neg_cancel_left
#print axioms NumberTheory.evalSum_cancel
#print axioms NumberTheory.evalSum_cancel_perm
#print axioms NumberTheory.insertAtom
#print axioms NumberTheory.insertAtom_sound
#print axioms NumberTheory.cancelAll
#print axioms NumberTheory.cancelAll_sound

/-! ## The multiplicative fragment

Everything above treats `ratMul` as an atom: `flat` splits a sum and `cancelAll`
matches opposites, and a product is an opaque leaf. Below, a product is
structure. The normal form becomes a sum of signed monomials ---
`List (Bool × List Nat)`, a sign and a list of variable indices --- and the
three operations the additive layer could not see through become `normMul`,
concatenation and a sign flip.

The additive parallel holds almost everywhere. `evalMon_append` is
`evalSum_append` with `ratOne_mul`/`ratMul_assoc` in place of
`ratZero_add`/`ratAdd_assoc`; `evalPoly_swap` is `evalSum_swap`; `evalMon_perm`
and `evalPoly_perm` get reordering from `List.Perm`'s four constructors exactly
as `evalSum_perm` does. The one exception is `evalSMon_smonMul`: signs multiply,
and there is no additive twin of that.

The `norm*` prefix keeps clear of `Algebra.polyMul` and `Algebra.polyNeg`, which
act on a polynomial as a `ZFSet`; these act on the reflected representation.

The sort is hand-written because `List.mergeSort` is defined by well-founded
recursion, so the kernel will not evaluate it, and a reflective proof needs the
normal forms to reduce so that `decide` can compare them. A structurally
recursive insertion sort reduces, and its permutation proof is four lines each
way. `isortMon_perm` and `isortPoly_perm` depend on no axioms at all.
-/

/-- A monomial is a list of variable indices; its value is their product. -/
def evalMon (env : Nat → ZFSet.{u}) : List Nat → ZFSet.{u}
  | [] => ratOne.{u}
  | i :: t => ratMul (env i) (evalMon env t)

theorem evalMon_mem {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ m : List Nat, evalMon env m ∈ Rat.{u}
  | [] => ratOne_mem_Rat
  | i :: t => ratMul_mem_Rat (henv i) (evalMon_mem henv t)

/-- Concatenating monomials multiplies them --- the multiplicative twin of
`evalSum_append`, with `ratOne_mul` and `ratMul_assoc` where that one spends
`ratZero_add` and `ratAdd_assoc`. -/
theorem evalMon_append {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ m n : List Nat,
      evalMon env (m ++ n) = ratMul (evalMon env m) (evalMon env n)
  | [], n => (ratOne_mul (evalMon_mem henv n)).symm
  | i :: t, n => by
    show ratMul (env i) (evalMon env (t ++ n))
      = ratMul (ratMul (env i) (evalMon env t)) (evalMon env n)
    rw [evalMon_append henv t n,
      ratMul_assoc (henv i) (evalMon_mem henv t) (evalMon_mem henv n)]

/-- A signed monomial: `true` is negated. -/
def evalSMon (env : Nat → ZFSet.{u}) : Bool × List Nat → ZFSet.{u}
  | (true, m) => ratNeg (evalMon env m)
  | (false, m) => evalMon env m

theorem evalSMon_mem {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ p : Bool × List Nat, evalSMon env p ∈ Rat.{u}
  | (true, m) => ratNeg_mem_Rat (evalMon_mem henv m)
  | (false, m) => evalMon_mem henv m

/-- A polynomial is a list of signed monomials; its value is their sum. -/
def evalPoly (env : Nat → ZFSet.{u}) : List (Bool × List Nat) → ZFSet.{u}
  | [] => ratZero.{u}
  | p :: t => ratAdd (evalSMon env p) (evalPoly env t)

theorem evalPoly_mem {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ l : List (Bool × List Nat), evalPoly env l ∈ Rat.{u}
  | [] => ratZero_mem_Rat
  | p :: t => ratAdd_mem_Rat (evalSMon_mem henv p) (evalPoly_mem henv t)

theorem evalPoly_append {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ l1 l2 : List (Bool × List Nat),
      evalPoly env (l1 ++ l2) = ratAdd (evalPoly env l1) (evalPoly env l2)
  | [], l2 => (ratZero_add (evalPoly_mem henv l2)).symm
  | p :: t, l2 => by
    show ratAdd (evalSMon env p) (evalPoly env (t ++ l2))
      = ratAdd (ratAdd (evalSMon env p) (evalPoly env t)) (evalPoly env l2)
    rw [evalPoly_append henv t l2,
      ratAdd_assoc (evalSMon_mem henv p) (evalPoly_mem henv t)
        (evalPoly_mem henv l2)]

/-- The product of two signed monomials: xor the signs, concatenate the
variables. -/
def smonMul : Bool × List Nat → Bool × List Nat → Bool × List Nat
  | (b, m), (c, n) => (xor b c, m ++ n)

/-- The sign rule: signs multiply, the one place the additive parallel has no
twin. Four cases: `ratMul_neg_neg` for two negatives, `ratNeg_mul` and
`ratMul_neg` for the mixed pairs, `evalMon_append` throughout. -/
theorem evalSMon_smonMul {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ p q : Bool × List Nat,
      evalSMon env (smonMul p q) = ratMul (evalSMon env p) (evalSMon env q)
  | (false, m), (false, n) => evalMon_append henv m n
  | (false, m), (true, n) => by
    show ratNeg (evalMon env (m ++ n))
      = ratMul (evalMon env m) (ratNeg (evalMon env n))
    rw [ratMul_neg (evalMon_mem henv m) (evalMon_mem henv n),
      evalMon_append henv m n]
  | (true, m), (false, n) => by
    show ratNeg (evalMon env (m ++ n))
      = ratMul (ratNeg (evalMon env m)) (evalMon env n)
    rw [ratNeg_mul (evalMon_mem henv m) (evalMon_mem henv n),
      evalMon_append henv m n]
  | (true, m), (true, n) => by
    show evalMon env (m ++ n)
      = ratMul (ratNeg (evalMon env m)) (ratNeg (evalMon env n))
    rw [ratMul_neg_neg (evalMon_mem henv m) (evalMon_mem henv n),
      evalMon_append henv m n]

/-- One signed monomial against a whole polynomial. -/
def normMulSMon (p : Bool × List Nat) :
    List (Bool × List Nat) → List (Bool × List Nat)
  | [] => []
  | q :: t => smonMul p q :: normMulSMon p t

/-- Distribution, paid once. This is the induction a hand proof re-runs at
every product of sums. -/
theorem evalPoly_normMulSMon {env : Nat → ZFSet.{u}}
    (henv : ∀ i, env i ∈ Rat.{u}) (p : Bool × List Nat) :
    ∀ l : List (Bool × List Nat),
      evalPoly env (normMulSMon p l) = ratMul (evalSMon env p) (evalPoly env l)
  | [] => (ratMul_zero (evalSMon_mem henv p)).symm
  | q :: t => by
    show ratAdd (evalSMon env (smonMul p q)) (evalPoly env (normMulSMon p t))
      = ratMul (evalSMon env p) (ratAdd (evalSMon env q) (evalPoly env t))
    rw [ratMul_add (evalSMon_mem henv p) (evalSMon_mem henv q)
        (evalPoly_mem henv t),
      evalSMon_smonMul henv p q, evalPoly_normMulSMon henv p t]

/-- The product of two normal forms: quadratic in the summands, where the
additive layer's join was concatenation. -/
def normMul : List (Bool × List Nat) → List (Bool × List Nat) →
    List (Bool × List Nat)
  | [], _ => []
  | p :: t, l => normMulSMon p l ++ normMul t l

theorem evalPoly_normMul {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ l1 l2 : List (Bool × List Nat),
      evalPoly env (normMul l1 l2)
        = ratMul (evalPoly env l1) (evalPoly env l2)
  | [], l2 => (ratZero_mul (evalPoly_mem henv l2)).symm
  | p :: t, l2 => by
    rw [show normMul (p :: t) l2 = normMulSMon p l2 ++ normMul t l2 from rfl,
      evalPoly_append henv (normMulSMon p l2) (normMul t l2),
      evalPoly_normMulSMon henv p l2, evalPoly_normMul henv t l2]
    exact (ratAdd_mul (evalSMon_mem henv p) (evalPoly_mem henv t)
      (evalPoly_mem henv l2)).symm

/-- Negate a normal form: flip every sign. -/
def normNeg : List (Bool × List Nat) → List (Bool × List Nat)
  | [] => []
  | (b, m) :: t => (!b, m) :: normNeg t

theorem evalPoly_normNeg {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ l : List (Bool × List Nat),
      evalPoly env (normNeg l) = ratNeg (evalPoly env l)
  | [] => (ratNeg_zero).symm
  | (false, m) :: t => by
    show ratAdd (ratNeg (evalMon env m)) (evalPoly env (normNeg t))
      = ratNeg (ratAdd (evalMon env m) (evalPoly env t))
    rw [ratNeg_add (evalMon_mem henv m) (evalPoly_mem henv t),
      evalPoly_normNeg henv t]
  | (true, m) :: t => by
    show ratAdd (evalMon env m) (evalPoly env (normNeg t))
      = ratNeg (ratAdd (ratNeg (evalMon env m)) (evalPoly env t))
    rw [ratNeg_add (ratNeg_mem_Rat (evalMon_mem henv m))
        (evalPoly_mem henv t),
      ratNeg_ratNeg (evalMon_mem henv m), evalPoly_normNeg henv t]

/-- Every `RatExpr` to a sum of signed monomials. `add` is concatenation, `mul`
is `normMul`, `neg` is a sign flip --- the three operations `RatExpr.flat` above
can only treat as atoms. -/
def RatExpr.norm : RatExpr → List (Bool × List Nat)
  | .var i => [(false, [i])]
  | .zero => []
  | .one => [(false, [])]
  | .add a b => a.norm ++ b.norm
  | .mul a b => normMul a.norm b.norm
  | .neg a => normNeg a.norm

/-- Soundness of the whole normaliser. Six cases for six constructors, every
one discharged by a lemma above rather than by an algebraic step written here. -/
theorem RatExpr.norm_sound {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ e : RatExpr, evalPoly env e.norm = e.eval env
  | .var i => by
    show ratAdd (ratMul (env i) ratOne.{u}) ratZero.{u} = env i
    rw [ratMul_one (henv i), ratAdd_zero (henv i)]
  | .zero => rfl
  | .one => by
    show ratAdd ratOne.{u} ratZero.{u} = ratOne.{u}
    rw [ratAdd_zero ratOne_mem_Rat]
  | .add a b => by
    show evalPoly env (a.norm ++ b.norm) = ratAdd (a.eval env) (b.eval env)
    rw [evalPoly_append henv a.norm b.norm, RatExpr.norm_sound henv a,
      RatExpr.norm_sound henv b]
  | .mul a b => by
    show evalPoly env (normMul a.norm b.norm) = ratMul (a.eval env) (b.eval env)
    rw [evalPoly_normMul henv a.norm b.norm, RatExpr.norm_sound henv a,
      RatExpr.norm_sound henv b]
  | .neg a => by
    show evalPoly env (normNeg a.norm) = ratNeg (a.eval env)
    rw [evalPoly_normNeg henv a.norm, RatExpr.norm_sound henv a]

/-- Transposition inside a monomial: `ratMul_comm` where `evalSum_swap` spends
`ratAdd_comm`. -/
theorem evalMon_swap {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u})
    (i j : Nat) (m : List Nat) :
    evalMon env (i :: j :: m) = evalMon env (j :: i :: m) := by
  show ratMul (env i) (ratMul (env j) (evalMon env m))
    = ratMul (env j) (ratMul (env i) (evalMon env m))
  rw [← ratMul_assoc (henv i) (henv j) (evalMon_mem henv m),
    ← ratMul_assoc (henv j) (henv i) (evalMon_mem henv m),
    ratMul_comm (henv i) (henv j)]

/-- Reordering a monomial is free once transposition is proved, by the same
argument `evalSum_perm` makes one level up: `List.Perm`'s four constructors are
reflexivity, congruence, transposition and transitivity, and only `swap` needs
an argument. -/
theorem evalMon_perm {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u})
    {m n : List Nat} (h : m.Perm n) : evalMon env m = evalMon env n := by
  induction h with
  | nil => rfl
  | cons i _ ih =>
    show ratMul (env i) (evalMon env _) = ratMul (env i) (evalMon env _)
    rw [ih]
  | swap i j m => exact evalMon_swap henv j i m
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- A signed monomial is invariant under reordering its variables. -/
theorem evalSMon_perm {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ (b : Bool) {m n : List Nat}, m.Perm n →
      evalSMon env (b, m) = evalSMon env (b, n)
  | false, _, _, h => evalMon_perm henv h
  | true, _, _, h => by
    show ratNeg (evalMon env _) = ratNeg (evalMon env _)
    rw [evalMon_perm henv h]

/-- Transposition at the polynomial level, the twin of `evalSum_swap`. -/
theorem evalPoly_swap {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u})
    (p q : Bool × List Nat) (l : List (Bool × List Nat)) :
    evalPoly env (p :: q :: l) = evalPoly env (q :: p :: l) := by
  show ratAdd (evalSMon env p) (ratAdd (evalSMon env q) (evalPoly env l))
    = ratAdd (evalSMon env q) (ratAdd (evalSMon env p) (evalPoly env l))
  rw [← ratAdd_assoc (evalSMon_mem henv p) (evalSMon_mem henv q)
      (evalPoly_mem henv l),
    ← ratAdd_assoc (evalSMon_mem henv q) (evalSMon_mem henv p)
      (evalPoly_mem henv l),
    ratAdd_comm (evalSMon_mem henv p) (evalSMon_mem henv q)]

theorem evalPoly_perm {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u})
    {l1 l2 : List (Bool × List Nat)} (h : l1.Perm l2) :
    evalPoly env l1 = evalPoly env l2 := by
  induction h with
  | nil => rfl
  | cons p _ ih =>
    show ratAdd (evalSMon env p) (evalPoly env _)
      = ratAdd (evalSMon env p) (evalPoly env _)
    rw [ih]
  | swap a b l => exact evalPoly_swap henv b a l
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Insert into a sorted monomial. Structural, so the kernel reduces it --- see
the header on why core's `mergeSort` cannot be used here. -/
def insMon (i : Nat) : List Nat → List Nat
  | [] => [i]
  | j :: t => if Nat.ble i j then i :: j :: t else j :: insMon i t

theorem insMon_perm (i : Nat) : ∀ m : List Nat, (insMon i m).Perm (i :: m)
  | [] => List.Perm.refl _
  | j :: t => by
    show (if Nat.ble i j then i :: j :: t else j :: insMon i t).Perm (i :: j :: t)
    cases Nat.ble i j with
    | true => exact List.Perm.refl _
    | false => exact ((insMon_perm i t).cons j).trans (List.Perm.swap i j t)

/-- Insertion sort of a monomial. -/
def isortMon : List Nat → List Nat
  | [] => []
  | i :: t => insMon i (isortMon t)

theorem isortMon_perm : ∀ m : List Nat, (isortMon m).Perm m
  | [] => List.Perm.refl _
  | i :: t => (insMon_perm i (isortMon t)).trans ((isortMon_perm t).cons i)

/-- An order on signed monomials. Nothing below depends on it being a total
order: soundness goes through the permutation lemmas alone, and sortedness would
be needed only to prove the decision complete, which is a different claim and is
not made here. -/
def smonGo : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | i :: s, j :: t => if i == j then smonGo s t else Nat.ble i j

def smonLe (p q : Bool × List Nat) : Bool :=
  if p.2.length == q.2.length then smonGo p.2 q.2
  else Nat.ble p.2.length q.2.length

/-- The same insertion, one level up, over signed monomials. -/
def insSMon (p : Bool × List Nat) :
    List (Bool × List Nat) → List (Bool × List Nat)
  | [] => [p]
  | q :: t => if smonLe p q then p :: q :: t else q :: insSMon p t

theorem insSMon_perm (p : Bool × List Nat) :
    ∀ l : List (Bool × List Nat), (insSMon p l).Perm (p :: l)
  | [] => List.Perm.refl _
  | q :: t => by
    show (if smonLe p q then p :: q :: t else q :: insSMon p t).Perm (p :: q :: t)
    cases smonLe p q with
    | true => exact List.Perm.refl _
    | false => exact ((insSMon_perm p t).cons q).trans (List.Perm.swap p q t)

def isortPoly : List (Bool × List Nat) → List (Bool × List Nat)
  | [] => []
  | p :: t => insSMon p (isortPoly t)

theorem isortPoly_perm : ∀ l : List (Bool × List Nat), (isortPoly l).Perm l
  | [] => List.Perm.refl _
  | p :: t => (insSMon_perm p (isortPoly t)).trans ((isortPoly_perm t).cons p)

/-- Canonicalise every monomial, leaving the sum's order alone. -/
def normCanonMons : List (Bool × List Nat) → List (Bool × List Nat)
  | [] => []
  | (b, m) :: t => (b, isortMon m) :: normCanonMons t

theorem evalPoly_normCanonMons {env : Nat → ZFSet.{u}}
    (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ l : List (Bool × List Nat), evalPoly env (normCanonMons l) = evalPoly env l
  | [] => rfl
  | (b, m) :: t => by
    show ratAdd (evalSMon env (b, isortMon m)) (evalPoly env (normCanonMons t))
      = ratAdd (evalSMon env (b, m)) (evalPoly env t)
    rw [show evalSMon env (b, isortMon m) = evalSMon env (b, m) from
        evalSMon_perm henv b (isortMon_perm m),
      evalPoly_normCanonMons henv t]

/-- Negate one signed monomial. -/
def smonNeg : Bool × List Nat → Bool × List Nat
  | (b, m) => (!b, m)

theorem evalSMon_smonNeg {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ p : Bool × List Nat, evalSMon env (smonNeg p) = ratNeg (evalSMon env p)
  | (false, _) => rfl
  | (true, m) => (ratNeg_ratNeg (evalMon_mem henv m)).symm

/-- The cancellation search, and why sorting alone is not a normal form:
`isortPoly` brings equal monomials together but never annihilates a pair, so
`x + -x` canonicalises to a two-element list while `0` canonicalises to the
empty one. This is `insertAtom` one layer down, over signed monomials rather than
over `RatExpr` atoms, and its one algebraic step is `ratAdd_neg_cancel_left`. -/
def insCancelSMon (p : Bool × List Nat) :
    List (Bool × List Nat) → List (Bool × List Nat)
  | [] => [p]
  | q :: t => if q = smonNeg p then t else q :: insCancelSMon p t

theorem evalPoly_insCancelSMon {env : Nat → ZFSet.{u}}
    (henv : ∀ i, env i ∈ Rat.{u}) (p : Bool × List Nat) :
    ∀ l : List (Bool × List Nat),
      evalPoly env (insCancelSMon p l) = ratAdd (evalSMon env p) (evalPoly env l)
  | [] => rfl
  | q :: t => by
    by_cases h : q = smonNeg p
    · show evalPoly env (if q = smonNeg p then t else q :: insCancelSMon p t)
        = ratAdd (evalSMon env p) (evalPoly env (q :: t))
      rw [if_pos h, h]
      show evalPoly env t
        = ratAdd (evalSMon env p)
            (ratAdd (evalSMon env (smonNeg p)) (evalPoly env t))
      rw [evalSMon_smonNeg henv p,
        ratAdd_neg_cancel_left (evalSMon_mem henv p) (evalPoly_mem henv t)]
    · show evalPoly env (if q = smonNeg p then t else q :: insCancelSMon p t)
        = ratAdd (evalSMon env p) (evalPoly env (q :: t))
      rw [if_neg h]
      show ratAdd (evalSMon env q) (evalPoly env (insCancelSMon p t))
        = ratAdd (evalSMon env p) (evalPoly env (q :: t))
      rw [evalPoly_insCancelSMon henv p t]
      exact evalPoly_swap henv q p t

/-- Cancel every matched pair of signed monomials. -/
def normCancel : List (Bool × List Nat) → List (Bool × List Nat)
  | [] => []
  | p :: t => insCancelSMon p (normCancel t)

theorem evalPoly_normCancel {env : Nat → ZFSet.{u}}
    (henv : ∀ i, env i ∈ Rat.{u}) :
    ∀ l : List (Bool × List Nat), evalPoly env (normCancel l) = evalPoly env l
  | [] => rfl
  | p :: t => by
    show evalPoly env (insCancelSMon p (normCancel t))
      = ratAdd (evalSMon env p) (evalPoly env t)
    rw [evalPoly_insCancelSMon henv p (normCancel t), evalPoly_normCancel henv t]

/-- The canonical form the kernel can run: every monomial sorted, then
opposite pairs annihilated, then the sum sorted.

All three passes are load-bearing and each closes identities the others cannot.
Sorting the monomials makes `x*y` and `y*x` the same monomial; cancelling makes
`x + -x` and `0` the same polynomial; sorting the sum makes `x + y` and `y + x`
the same. Cancellation sits between the two sorts because it matches monomials
by equality, so their variables must already be in order --- `x*y + -(y*x)`
cancels only if `normCanonMons` has run first. -/
def normCanon (l : List (Bool × List Nat)) : List (Bool × List Nat) :=
  isortPoly (normCancel (normCanonMons l))

theorem evalPoly_normCanon {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u})
    (l : List (Bool × List Nat)) :
    evalPoly env (normCanon l) = evalPoly env l := by
  rw [show normCanon l = isortPoly (normCancel (normCanonMons l)) from rfl,
    evalPoly_perm henv (isortPoly_perm (normCancel (normCanonMons l))),
    evalPoly_normCancel henv (normCanonMons l),
    evalPoly_normCanonMons henv l]

/-- The bridge a tactic spends once. Two expressions with the same canonical
form denote the same rational --- and `normCanon` reduces, so `h` is closed by
`rfl` or `decide` at the call site rather than by an algebraic argument. -/
theorem rat_by_ring {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u})
    (a b : RatExpr) (h : normCanon a.norm = normCanon b.norm) :
    a.eval env = b.eval env := by
  rw [← RatExpr.norm_sound henv a, ← RatExpr.norm_sound henv b,
    ← evalPoly_normCanon henv a.norm, ← evalPoly_normCanon henv b.norm, h]


#print axioms NumberTheory.evalMon
#print axioms NumberTheory.evalMon_mem
#print axioms NumberTheory.evalMon_append
#print axioms NumberTheory.evalSMon
#print axioms NumberTheory.evalSMon_mem
#print axioms NumberTheory.evalPoly
#print axioms NumberTheory.evalPoly_mem
#print axioms NumberTheory.evalPoly_append
#print axioms NumberTheory.smonMul
#print axioms NumberTheory.evalSMon_smonMul
#print axioms NumberTheory.normMulSMon
#print axioms NumberTheory.evalPoly_normMulSMon
#print axioms NumberTheory.normMul
#print axioms NumberTheory.evalPoly_normMul
#print axioms NumberTheory.normNeg
#print axioms NumberTheory.evalPoly_normNeg
#print axioms NumberTheory.RatExpr.norm
#print axioms NumberTheory.RatExpr.norm_sound
#print axioms NumberTheory.evalMon_swap
#print axioms NumberTheory.evalMon_perm
#print axioms NumberTheory.evalSMon_perm
#print axioms NumberTheory.evalPoly_swap
#print axioms NumberTheory.evalPoly_perm
#print axioms NumberTheory.insMon
#print axioms NumberTheory.insMon_perm
#print axioms NumberTheory.isortMon
#print axioms NumberTheory.isortMon_perm
#print axioms NumberTheory.smonGo
#print axioms NumberTheory.smonLe
#print axioms NumberTheory.insSMon
#print axioms NumberTheory.insSMon_perm
#print axioms NumberTheory.isortPoly
#print axioms NumberTheory.isortPoly_perm
#print axioms NumberTheory.normCanonMons
#print axioms NumberTheory.evalPoly_normCanonMons
#print axioms NumberTheory.smonNeg
#print axioms NumberTheory.evalSMon_smonNeg
#print axioms NumberTheory.insCancelSMon
#print axioms NumberTheory.evalPoly_insCancelSMon
#print axioms NumberTheory.normCancel
#print axioms NumberTheory.evalPoly_normCancel
#print axioms NumberTheory.normCanon
#print axioms NumberTheory.evalPoly_normCanon
#print axioms NumberTheory.rat_by_ring

end NumberTheory
