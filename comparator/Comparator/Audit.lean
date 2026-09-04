/-
THE AUDIT: is each `solution` really this tower's proof of Mathlib's statement?

A pair claims two things, and prose can assert either. This file asks Lean for
both, because every compiled proof term carries its constant dependencies and
every constant knows which module declared it. `open`, helper indirection,
notation and elaboration are all resolved by the time the term exists, so there
is nothing left for a grep to miss.

  THE PROOF USES THIS TOWER. A `solution` must reach a PROPOSITION declared
  under `FromAxioms/`. Reaching tower DATA is not enough and was the first
  version's mistake: `ZFSet`, `SetTheory.sep` and `Analysis.IsCut` are reached
  through the types of encoded terms, so a Solution that pushed everything
  through the encoding and then argued about it in Mathlib would show exactly
  those, having derived none of it.

  THE PROOF IS NOT MATHLIB'S. `challenge_is_mathlibs` discharges the challenge
  FROM Mathlib, so the Mathlib theorems it reaches are the ones Mathlib itself
  uses to prove this statement. A `solution` reaching any of them is using
  Mathlib's proof of the very theorem it claims to have matched.

WHY THE SECOND IS AN INTERSECTION AND NOT A BAN. A pair stated over `ℝ` must
reach Mathlib propositions to relate `ℝ` to this tower's reals at all, and a
transfer is not a proof of the theorem. So every Mathlib theorem a solution
reaches is REPORTED, and only the ones Mathlib's own proof uses are a finding.

WHAT IT STILL CANNOT SEE, said plainly so the next reader does not overtrust
it: whether the tower constant is LOAD-BEARING rather than incidental. A proof
could depend on a tower lemma in a step some Mathlib lemma would also close.
Only removing the citation and rebuilding settles that, one pair at a time.
-/
-- `import Lean` IS NOT INCIDENTAL. This file asks the environment about
-- constants, and nothing under `FromAxioms/` imports Lean's meta library: the
-- tower is `prelude` at the root and pulls in as little as it can. A pair that
-- happened to import Mathlib would drag `Lean` in behind it and hide the need.
import Lean
import Comparator.NatAddSucc.Solution

open Lean

namespace Comparator.Audit

/-- The module that declared this constant.

DEFINED HERE RATHER THAN IMPORTED. `Environment.getModuleFor?` is Mathlib's,
and an audit that reached for it would be asking Mathlib to help check whether
Mathlib was used. Core gives the index and the header gives the names. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

/-- Was this constant declared in a module under `FromAxioms`? -/
def isTowerConst (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => (`FromAxioms).isPrefixOf m
  | none => false

/-- Was it declared in Mathlib? -/
def isMathlibConst (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => (`Mathlib).isPrefixOf m
  | none => false

/-- The constants of one kind a proof term reaches, not descending past one
found.

Bounded by `fuel`, and the bound is reported when it is hit: a silent cap would
turn *no such dependency* and *ran out of budget* into the same answer. -/
partial def depsOf (env : Environment) (stop : Environment → Name → Bool)
    (start : Name) : StateM (Array Name × NameSet × Nat) Unit := do
  let (found, seen, fuel) ← get
  if fuel == 0 || seen.contains start then return
  set (found, seen.insert start, fuel - 1)
  if stop env start then
    let (found, seen, fuel) ← get
    set (found.push start, seen, fuel)
    return
  match env.find? start with
  | some ci => match ci.value? with
    | some v => for c in v.getUsedConstants do depsOf env stop c
    | none => return
  | none => return

/-- A constant carrying PROOF CONTENT rather than statement vocabulary.

A THEOREM IS PROOF; A DEFINITION IS VOCABULARY. Both halves of a pair elaborate
the same statement, so both reach the instances and class fields of whatever
the statement mentions.

THE TRAP IS THE `Prop`-CLASS. `Archimedean`, `IsWellFounded` and
`IsOrderedAddMonoid` are all `Prop`, so `Real.instArchimedean` is stored as a
THEOREM and passes a theorem test while being nothing more than the statement
being able to mention `ℝ`. Counting those accused 18 of 60 solutions of resting
on Mathlib's proof, and a check that reports the unavoidable trains its reader
to skip it. Excluding instances, class fields and tactic internals leaves the
theorems that argue: `exists_rat_btwn` is the density of the rationals. -/
def isProofContent (env : Environment) (n : Name) : MetaM Bool := do
  match env.find? n with
  | some (.thmInfo _) =>
    if ← Meta.isInstance n then return false
    if (env.getProjectionFnInfo? n).isSome then return false
    if (`Mathlib.Tactic).isPrefixOf ((moduleOf env n).getD Name.anonymous) then
      return false
    return true
  | _ => return false

/-- Is this the name of a Solution MODULE, `Comparator.<Pair>.Solution`? -/
def isSolutionModule (m : Name) : Bool :=
  m.getRoot == `Comparator && m.getString! == "Solution"

/-- Every pair's `solution`, found BY DECLARING MODULE rather than by name, so
a pair whose theorem is spelled differently cannot go silently unaudited. -/
def solutionNames (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    match moduleOf env n with
    | some m =>
      if isSolutionModule m && "solution".isPrefixOf n.getString!.toLower then
        acc.push n
      else acc
    | none => acc

/-- The `challenge_is_mathlibs` belonging to the same pair as this solution. -/
def witnessFor (env : Environment) (solution : Name) : Option Name :=
  match moduleOf env solution with
  | some m =>
    let pair := m.getPrefix
    env.constants.fold (init := none) fun acc n _ =>
      match acc with
      | some _ => acc
      | none =>
        match moduleOf env n with
        | some m' =>
          if m'.getPrefix == pair && m'.getString! == "Challenge"
              && "challenge_is".isPrefixOf n.getString! then some n else none
        | none => none
  | none => none

def mathlibTheorems (env : Environment) (n : Name) : MetaM (Array Name × Bool) := do
  let ((), (found, _, fuel)) := (depsOf env isMathlibConst n).run (#[], {}, 400000)
  let mut out : Array Name := #[]
  for c in found do
    if ← isProofContent env c then out := out.push c
  return (out, fuel == 0)

/-- **The audit.** Both halves, per pair, with the witnesses named so the
output reads as evidence rather than as a verdict. -/
def report : MetaM Unit := do
  let env ← getEnv
  let names := (solutionNames env).qsort (fun a b => a.toString < b.toString)
  let mut noProp := 0
  let mut onMathlib := 0
  for n in names do
    let ((), (tower, _, fuel)) := (depsOf env isTowerConst n).run (#[], {}, 400000)
    let mut props : Array Name := #[]
    let mut data : Array Name := #[]
    for c in tower do
      match env.find? c with
      | some ci =>
        if ← Meta.isProp ci.type then props := props.push c else data := data.push c
      | none => pure ()
    if props.isEmpty then
      noProp := noProp + 1
      IO.println s!"NO TOWER PROPOSITION  {n}   (tower data reached: {data.size})"
      if fuel == 0 then IO.println "    (fuel exhausted -- inconclusive, not a verdict)"
    else
      IO.println s!"ok  {n}   tower props={props.size} data={data.size}"
      for c in props.toList.take 3 do IO.println s!"      {c}"
    let (mine, _) ← mathlibTheorems env n
    match witnessFor env n with
    | none => IO.println s!"    NO WITNESS -- no `challenge_is_*` certifies this statement"
    | some w =>
      let (theirs, _) ← mathlibTheorems env w
      let wset := theirs.foldl (init := ({} : NameSet)) fun s x => s.insert x
      let shared := mine.filter wset.contains
      if !shared.isEmpty then
        onMathlib := onMathlib + 1
        IO.println s!"    RESTS ON MATHLIB'S OWN PROOF ({shared.size})"
        for c in shared.toList.take 5 do
          IO.println s!"      {c}   [{(moduleOf env c).getD Name.anonymous}]"
      else if !mine.isEmpty then
        IO.println s!"    mathlib theorems reached: {mine.size}, none of Mathlib's own proof"
  IO.println s!"--- solutions: {names.size} | with no tower proposition: {noProp} \
| resting on Mathlib's own proof: {onMathlib}"
  if noProp != 0 || onMathlib != 0 then
    throwError "the audit found {noProp + onMathlib} pair(s) to answer for"

#eval report

end Comparator.Audit
