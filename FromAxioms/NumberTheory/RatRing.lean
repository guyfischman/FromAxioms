/-
Copyright (c) 2026 Guy Fischman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guy Fischman
-/

/-
# A reflective tactic for rational ring identities

`RatReflect.lean` proves the normalisers correct; this file reads a goal and
builds the syntax, so an identity between rational expressions closes in one
line. `rat_by_reflection` spends `flat_sound` and `cancelAll_sound` once rather
than per call site; `reifyRatExpr` reads a goal `lhs = rhs` and reifies both
sides into `RatExpr`, collecting atoms; `rat_ring` and `rat_ring!` are the
elaborators that put them together.

The first `import Lean` under `FromAxioms/`. The audit is `#print axioms` on the
produced term, per declaration; a tactic is a metaprogram and never appears in a
proof term, and every theorem below prints `[propext, Quot.sound]`, the same as
the hand proof it replaces. The reifier itself is a declaration too, so it is
written without a monad: a definition in `MetaM` prints `Classical.choice`
whatever its body, while `reifyRatExpr` threads its `Array Expr` state by hand,
recurses on fuel and returns `Option`. It prints `[propext]`. What that costs
is the atom test: atoms are compared by structural `Expr` equality, so two
definitionally equal but structurally different spellings of one subterm
receive two indices and the goal is not closed.

`rat_ring` takes one atom per goal and refuses with a count when it finds more;
`rat_ring!` takes any number, owing the caller one membership fact per atom,
which `ratAll_nil` and `ratAll_cons` discharge.
-/
import Lean
import FromAxioms.NumberTheory.RatReflect

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic

namespace NumberTheory

/-- The bridge the tactic applies: two expressions whose cancelled normal forms
agree denote the same rational. `flat_sound` and `cancelAll_sound` are spent
here, once per side, for every goal `rat_ring` closes. -/
theorem rat_by_reflection {env : Nat → ZFSet.{u}} (henv : ∀ i, env i ∈ Rat.{u})
    (a b : RatExpr) (h : cancelAll a.flat = cancelAll b.flat) :
    a.eval env = b.eval env := by
  rw [← RatExpr.flat_sound henv a, ← RatExpr.flat_sound henv b,
    ← cancelAll_sound henv a.flat, ← cancelAll_sound henv b.flat, h]

/-- The atom scan. `findRatAtomScan atoms e n` checks the last `n` entries of
`atoms`, oldest first, for one structurally equal to `e` and returns its index.
A top-level declaration rather than a `let rec` so that it carries its own
`#print axioms` line; it prints none. -/
def findRatAtomScan (atoms : Array Expr) (e : Expr) : Nat → Option Nat
  | 0 => none
  | n + 1 => if atoms[atoms.size - (n + 1)]! == e then some (atoms.size - (n + 1))
      else findRatAtomScan atoms e n

/-- Find `e` among the collected atoms, by structural `Expr` equality.
Anything that is not one of the five operations is an atom, and a repeated
subterm gets one index, so that `cancelAll` can cancel it. `ratMul` is
reified as an operation but never flattened, matching `RatExpr.flat`.

The reifier has no monad, because a definition in `MetaM` prints
`Classical.choice`. Its only monadic needs would be an atom test and an
`Array Expr` state, and the state threads by hand; it recurses on fuel rather
than `partial` and returns `Option` rather than calling `throwError`. The
structural test is what this costs: a subterm under two definitionally equal
but structurally different spellings receives two indices and `decide` refuses.
`tactic_repeated_atom` below checks the case that does hold, that repeated
occurrences of one spelling share an index.

The `elab` bodies below run in `MetaM`; an `elab` produces no named
declaration, so the reifier's body is kept out of them. -/
def findRatAtom (atoms : Array Expr) (e : Expr) : Option Nat :=
  findRatAtomScan atoms e atoms.size

/-- The reifier, with no monad. The fuel bound is the `throwError` the monadic
version would have: it refuses at exhaustion rather than returning something
that would still typecheck. -/
def reifyRatExpr : Nat → Expr → Array Expr → Option (Expr × Array Expr)
  | 0, _, _ => none
  | n + 1, e, atoms =>
      match e.getAppFnArgs with
      | (``NumberTheory.ratAdd, #[a, b]) => do
          let (ea, atoms) ← reifyRatExpr n a atoms
          let (eb, atoms) ← reifyRatExpr n b atoms
          return (mkApp2 (mkConst ``RatExpr.add) ea eb, atoms)
      | (``NumberTheory.ratMul, #[a, b]) => do
          let (ea, atoms) ← reifyRatExpr n a atoms
          let (eb, atoms) ← reifyRatExpr n b atoms
          return (mkApp2 (mkConst ``RatExpr.mul) ea eb, atoms)
      | (``NumberTheory.ratNeg, #[a]) => do
          let (ea, atoms) ← reifyRatExpr n a atoms
          return (mkApp (mkConst ``RatExpr.neg) ea, atoms)
      | (``NumberTheory.ratZero, _) => some (mkConst ``RatExpr.zero, atoms)
      | (``NumberTheory.ratOne, _) => some (mkConst ``RatExpr.one, atoms)
      | _ =>
          match findRatAtom atoms e with
          | some i => some (mkApp (mkConst ``RatExpr.var) (mkNatLit i), atoms)
          | none =>
              some (mkApp (mkConst ``RatExpr.var) (mkNatLit atoms.size), atoms.push e)

/-- Close a rational ring identity by reflection. Reads the goal, reifies both
sides, and discharges the normal-form equality by `decide` through the derived
`DecidableEq RatExpr`. One goal is left: that the atom is a rational, which
belongs to the caller, since nothing about the goal's syntax establishes it.

It refuses rather than guesses when the goal is not an equation or carries more
than one atom; whatever a tactic produced at the second atom would still
typecheck.

The goal is instantiated before it is read. A goal produced by `refine f ?_ ?_`
has the type `?a = ?a'` with both metavariables already assigned, and `whnfR`
of an `Eq` application hands back the arguments still wrapped in their mvars;
`reifyRatExpr` would then find no `ratAdd` at the head and file each whole side
as one atom. -/
elab "rat_ring" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.Meta.whnfR (← Lean.instantiateMVars (← g.getType))
  let some (_, lhs, rhs) := ty.eq?
    | throwError "rat_ring: the goal is not an equation"
  let some (ea, atoms) := reifyRatExpr 1000 lhs #[]
    | throwError "rat_ring: out of fuel on the left side"
  let some (eb, atoms) := reifyRatExpr 1000 rhs atoms
    | throwError "rat_ring: out of fuel on the right side"
  unless atoms.size == 1 do
    throwError "rat_ring: this build reifies exactly one atom, found {atoms.size}"
  let env := Lean.Expr.lam `i (mkConst ``Nat) atoms[0]! Lean.BinderInfo.default
  let envS ← Lean.Elab.Term.exprToSyntax env
  let eaS ← Lean.Elab.Term.exprToSyntax ea
  let ebS ← Lean.Elab.Term.exprToSyntax eb
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    refine rat_by_reflection (env := $envS) ?_ $eaS $ebS (by decide)))

theorem reflected_one_sub_succ {x : ZFSet.{u}} (hx : x ∈ Rat.{u}) :
    ratAdd ratOne.{u} (ratNeg (ratAdd x ratOne.{u})) = ratNeg x := by
  rat_ring
  exact fun _ => hx

theorem tactic_neg_add_cancel {x : ZFSet.{u}} (hx : x ∈ Rat.{u}) :
    ratAdd (ratNeg x) (ratAdd x ratOne.{u}) = ratOne.{u} := by
  rat_ring
  exact fun _ => hx

/-- The atom occurs four times and the expression nests three deep. -/
theorem tactic_deep {x : ZFSet.{u}} (hx : x ∈ Rat.{u}) :
    ratAdd (ratAdd x x) (ratNeg (ratAdd (ratAdd x ratOne.{u}) (ratAdd x ratOne.{u})))
      = ratNeg (ratAdd ratOne.{u} ratOne.{u}) := by
  rat_ring
  exact fun _ => hx

/-! ### Any number of atoms

`rat_ring` above carries exactly one atom. What follows removes the cap. -/

/-- An environment built from a list of atoms, with `ratZero` past the end. The
default is what makes `envOf_mem` hold with no side condition on the index. -/
def envOf : List ZFSet.{u} → Nat → ZFSet.{u}
  | [], _ => ratZero.{u}
  | a :: _, 0 => a
  | _ :: t, (n+1) => envOf t n

theorem envOf_mem : ∀ (l : List ZFSet.{u}), (∀ x ∈ l, x ∈ Rat.{u}) →
    ∀ i, envOf l i ∈ Rat.{u}
  | [], _, _ => ratZero_mem_Rat
  | a :: _, h, 0 => h a (List.Mem.head _)
  | _ :: t, h, (n+1) => envOf_mem t (fun x hx => h x (List.Mem.tail _ hx)) n

/-- The empty atom list is trivially rational. -/
theorem ratAll_nil : ∀ x ∈ ([] : List ZFSet.{u}), x ∈ Rat.{u} := fun _ h => nomatch h

/-- One membership fact per atom, and no case analysis at the call site: the
consumer's second line grows by one citation per atom. -/
theorem ratAll_cons {a : ZFSet.{u}} {l : List ZFSet.{u}} (ha : a ∈ Rat.{u})
    (hl : ∀ x ∈ l, x ∈ Rat.{u}) : ∀ x ∈ (a :: l), x ∈ Rat.{u}
  | _, List.Mem.head _ => ha
  | x, List.Mem.tail _ h => hl x h

/-- The bridge at a list environment: the caller owes one membership fact per
atom rather than one per index. `rat_by_reflection` does the work; this only
supplies the environment, so nothing about the reflection is proved twice. -/
theorem rat_by_reflection_list {l : List ZFSet.{u}} (hl : ∀ x ∈ l, x ∈ Rat.{u})
    (a b : RatExpr) (h : cancelAll a.flat = cancelAll b.flat) :
    a.eval (envOf l) = b.eval (envOf l) :=
  rat_by_reflection (envOf_mem l hl) a b h

/-- The same bridge through the multiplicative normal form. `rat_by_ring` does
the work; this only supplies the environment, as `rat_by_reflection_list` does
for the additive one.

`cancelAll ∘ flat` treats `ratMul` as an atom: it cancels `x + -x` and reorders
a sum, and cannot see inside a product, so `x*y = y*x` is beyond it.
`normCanon ∘ norm` expands products into monomials, sorts each monomial, cancels
opposite pairs and sorts the sum, so it closes everything the additive bridge
closes and the products it cannot. `rat_ring!` below goes through this one. -/
theorem rat_by_ring_list {l : List ZFSet.{u}} (hl : ∀ x ∈ l, x ∈ Rat.{u})
    (a b : RatExpr) (h : normCanon a.norm = normCanon b.norm) :
    a.eval (envOf l) = b.eval (envOf l) :=
  rat_by_ring (envOf_mem l hl) a b h

/-- `rat_ring` with no cap on the number of atoms. Identical to it through
reification, and differing in what it builds from the collected atoms: a
`List ZFSet` rather than a constant function, so it needs no count and cannot
refuse on one. -/
elab "rat_ring!" : tactic => do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.Meta.whnfR (← Lean.instantiateMVars (← g.getType))
  let some (_, lhs, rhs) := ty.eq?
    | throwError "rat_ring!: the goal is not an equation"
  let some (ea, atoms) := reifyRatExpr 1000 lhs #[]
    | throwError "rat_ring!: out of fuel on the left side"
  let some (eb, atoms) := reifyRatExpr 1000 rhs atoms
    | throwError "rat_ring!: out of fuel on the right side"
  let zf ← Lean.Meta.inferType lhs
  let mut lst ← Lean.Meta.mkAppOptM ``List.nil #[zf]
  for a in atoms.reverse do
    lst ← Lean.Meta.mkAppOptM ``List.cons #[zf, a, lst]
  let lstS ← Lean.Elab.Term.exprToSyntax lst
  let eaS ← Lean.Elab.Term.exprToSyntax ea
  let ebS ← Lean.Elab.Term.exprToSyntax eb
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    refine rat_by_ring_list (l := $lstS) ?_ $eaS $ebS (by decide)))

/-- Two atoms. -/
theorem tactic_two_atoms {x y : ZFSet.{u}} (hx : x ∈ Rat.{u}) (hy : y ∈ Rat.{u}) :
    ratAdd (ratAdd x y) (ratNeg (ratAdd y x)) = ratZero.{u} := by
  rat_ring!
  exact ratAll_cons hx (ratAll_cons hy ratAll_nil)

/-- Three atoms and a nested negation. -/
theorem tactic_three_atoms {x y z : ZFSet.{u}} (hx : x ∈ Rat.{u}) (hy : y ∈ Rat.{u})
    (hz : z ∈ Rat.{u}) :
    ratAdd (ratAdd x (ratAdd y z)) (ratNeg (ratAdd z (ratAdd y x))) = ratZero.{u} := by
  rat_ring!
  exact ratAll_cons hx (ratAll_cons hy (ratAll_cons hz ratAll_nil))

/-- The same atom appears on both sides in interleaved positions, and closes:
reification gives repeated occurrences of one spelling a shared index. A
definitionally equal but structurally different pair would not close. -/
theorem tactic_repeated_atom {x y : ZFSet.{u}} (hx : x ∈ Rat.{u}) (hy : y ∈ Rat.{u}) :
    ratAdd (ratAdd x (ratAdd y x)) (ratNeg (ratAdd x (ratAdd x y))) = ratZero.{u} := by
  rat_ring!
  exact ratAll_cons hx (ratAll_cons hy ratAll_nil)

/-- What the multiplicative bridge buys: `(x + y) * z = z*y + z*x` needs the
product expanded and then both the monomials and the sum reordered, so
`cancelAll ∘ flat`, which sees `ratMul` as an atom, cannot close it. Not
`ratAdd_mul` restated: that one concludes `x*z + y*z`. -/
theorem tactic_mul_distrib_swapped {x y z : ZFSet.{u}}
    (hx : x ∈ Rat.{u}) (hy : y ∈ Rat.{u}) (hz : z ∈ Rat.{u}) :
    ratMul (ratAdd x y) z = ratAdd (ratMul z y) (ratMul z x) := by
  rat_ring!
  exact ratAll_cons hx (ratAll_cons hy (ratAll_cons hz ratAll_nil))

#print axioms NumberTheory.rat_by_reflection
#print axioms NumberTheory.findRatAtomScan
#print axioms NumberTheory.findRatAtom
#print axioms NumberTheory.reifyRatExpr
#print axioms NumberTheory.reflected_one_sub_succ
#print axioms NumberTheory.tactic_neg_add_cancel
#print axioms NumberTheory.tactic_deep
#print axioms NumberTheory.envOf
#print axioms NumberTheory.envOf_mem
#print axioms NumberTheory.ratAll_nil
#print axioms NumberTheory.ratAll_cons
#print axioms NumberTheory.rat_by_reflection_list
#print axioms NumberTheory.rat_by_ring_list
#print axioms NumberTheory.tactic_mul_distrib_swapped
#print axioms NumberTheory.tactic_two_atoms
#print axioms NumberTheory.tactic_three_atoms
#print axioms NumberTheory.tactic_repeated_atom

end NumberTheory
