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
import Comparator.DetMul.Solution
import Comparator.PairEncoding.Solution
import Comparator.IrrationalSqrtPrime.Solution
import Comparator.NormAddSq.Solution
import Comparator.Bezout.Solution
import Comparator.ChineseRemainder.Solution
import Comparator.InfinitudePrimes.Solution
import Comparator.UniqueFactorisation.Solution
import Comparator.IntNoZeroDiv.Solution

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

/-- The Mathlib theorem each pair claims to match, keyed by the pair's module
prefix. Generated from `formalization.yaml`'s `mathlib:` field by the emitter,
so the audit checks the registry's claim rather than restating it. -/
def matched : List (Name × Name) := [(`Comparator.NatAddSucc, `Nat.add_succ),
  (`Comparator.DetMul, `Matrix.det_mul),
  (`Comparator.PairEncoding, `none),
  (`Comparator.IrrationalSqrtPrime, `Nat.Prime.irrational_sqrt),
  (`Comparator.NormAddSq, `norm_add_sq_real),
  (`Comparator.Bezout, `Nat.gcd_eq_gcd_ab),
  (`Comparator.ChineseRemainder, `Nat.chineseRemainder),
  (`Comparator.InfinitudePrimes, `Nat.exists_infinite_primes),
  (`Comparator.UniqueFactorisation, `Nat.primeFactorsList_unique),
  (`Comparator.IntNoZeroDiv, `mul_eq_zero)]

/-- Does `start`'s proof term reach `target`, DESCENDING INTO MATHLIB?

The other walks stop at the first Mathlib constant, which is right for asking
what a proof leans on and wrong here: a solution that calls some Mathlib lemma
whose own proof uses the matched theorem has used it, one step removed. So this
one follows every edge until it finds the target or runs out of fuel, and the
caller reports exhaustion rather than reading it as a pass. -/
partial def reaches (env : Environment) (target : Name) (start : Name) :
    StateM (Bool × NameSet × Nat) Unit := do
  let (found, seen, fuel) ← get
  if found || fuel == 0 || seen.contains start then return
  set (found, seen.insert start, fuel - 1)
  if start == target then
    let (_, seen, fuel) ← get
    set (true, seen, fuel)
    return
  match env.find? start with
  | some ci => match ci.value? with
    | some v => for c in v.getUsedConstants do reaches env target c
    | none => return
  | none => return

/-- **The audit.** Both halves, per pair, with the witnesses named so the
output reads as evidence rather than as a verdict. -/
def report : MetaM Unit := do
  let env ← getEnv
  let names := (solutionNames env).qsort (fun a b => a.toString < b.toString)
  let mut noProp := 0
  let mut onMathlib := 0
  let mut calls := 0
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
    -- THE CHECK THAT FAILS THE BUILD. A pair is void if its solution reaches
    -- the theorem it claims to match. Sharing `one_mul` with Mathlib's proof is
    -- not that: any proof of a ring identity over Mathlib's `R` has to use
    -- Mathlib's lemmas about `R`, so the intersection below reports and does
    -- not fail. It accused four pairs of ring plumbing before this split.
    let pair := (moduleOf env n).map Name.getPrefix
    match pair.bind (fun p => (matched.find? (·.1 == p)).map (·.2)) with
    | none =>
      calls := calls + 1
      IO.println s!"    NO MATCHED THEOREM registered for this pair"
    | some tgt =>
      -- A PAIR CAN HAVE NO COUNTERPART. `pair-encoding` matches a definitional
      -- convention rather than a theorem, and its registry says `mathlib:
      -- none`, so there is nothing to reach and nothing to check. Reported,
      -- because a pair nothing can check should say so, and not failed.
      if tgt == `none || tgt == `«n/a» then
        IO.println s!"    NO MATHLIB COUNTERPART -- unchecked by this rule"
      else if !env.contains tgt then
        calls := calls + 1
        IO.println s!"    MATCHED THEOREM `{tgt}` DOES NOT EXIST in this Mathlib"
      else
        let ((), (hit, _, left)) := (reaches env tgt n).run (false, {}, 2000000)
        if hit then
          calls := calls + 1
          IO.println s!"    CALLS THE THEOREM IT MATCHES: `{tgt}`"
        else if left == 0 then
          calls := calls + 1
          IO.println s!"    INCONCLUSIVE -- fuel exhausted before `{tgt}` was ruled out"
        else
          IO.println s!"    does not reach `{tgt}`"
    let (mine, _) ← mathlibTheorems env n
    match witnessFor env n with
    | none => IO.println s!"    NO WITNESS -- no `challenge_is_*` certifies this statement"
    | some w =>
      let (theirs, _) ← mathlibTheorems env w
      let wset := theirs.foldl (init := ({} : NameSet)) fun s x => s.insert x
      let shared := mine.filter wset.contains
      if !shared.isEmpty then
        onMathlib := onMathlib + 1
        IO.println s!"    shares {shared.size} Mathlib theorem(s) with Mathlib's own proof"
        for c in shared.toList.take 5 do
          IO.println s!"      {c}   [{(moduleOf env c).getD Name.anonymous}]"
      else if !mine.isEmpty then
        IO.println s!"    mathlib theorems reached: {mine.size}, none of Mathlib's own proof"
  IO.println s!"--- solutions: {names.size} | with no tower proposition: {noProp} \
| calling the theorem they match: {calls} | sharing a lemma with Mathlib's \
proof (reported, not failed): {onMathlib}"
  if noProp != 0 || calls != 0 then
    throwError "the audit found {noProp + calls} pair(s) to answer for"

#eval report

/-- **The per-pair verdict, written to `PAIRS.md`.**

WHAT A READER WANTS FROM A PAIR is three things at once: that the proof is
correct, that it is as general as the theorem it matches, and what it costs in
axioms. The evidence for those is scattered -- the build settles the first, the
challenge's binders carry the second, and the axiom lines are per declaration --
so this assembles what the kernel can answer into one table.

TWO OF THE THREE ARE MECHANICAL AND THE THIRD IS NOT. Correctness and cost are
computed here. GENERALITY IS NOT: whether `∀ (R : Type) [CommRing R] (m : Nat)`
matches a Mathlib statement quantified over `[Fintype n] [DecidableEq n]` is a
reading of two binder lists, and a table that guessed at it would be the
confident-and-wrong kind. `formalization.yaml` carries that per pair, in prose,
where it can be qualified.

THE COST COLUMN IS THE ONE THAT NEEDS ITS BASELINE STATED. A pair whose Mathlib
statement mentions `Matrix.det` cannot print without `Classical.choice`, because
`Matrix.det` carries it: no route avoids it, and the pair is not paying for its
own construction. So the surcharge is measured against BOTH what the tower
theorems need AND what Mathlib's own proof of the challenge costs, and it is the
part that says whether the pair spent anything of its own. -/
def writePairs : MetaM Unit := do
  let env ← getEnv
  let names := (solutionNames env).qsort (fun a b => a.toString < b.toString)
  let mut rows := #[]
  for n in names do
    let paid ← collectAxioms n
    let ((), (tower, _, _)) := (depsOf env isTowerConst n).run (#[], {}, 400000)
    let mut props := #[]
    let mut owed : NameSet := {}
    for c in tower do
      match env.find? c with
      | some ci =>
        if ← Meta.isProp ci.type then
          props := props.push c
          for a in ← collectAxioms c do owed := owed.insert a
      | none => pure ()
    let mut certified := "NO"
    let mut mathlibs : NameSet := {}
    let mut applied := #[]
    match witnessFor env n with
    | some w =>
      certified := "yes"
      for a in ← collectAxioms w do mathlibs := mathlibs.insert a
      applied := (← mathlibTheorems env w).1
    | none => pure ()
    let extra := paid.filter (fun a => !owed.contains a && !mathlibs.contains a)
    rows := rows.push (n, certified, paid, props, owed, applied, extra)
  let mut out := "# The pairs, and what each one establishes\n\n"
  out := out ++ "Generated by `Comparator/Audit.lean` on every `lake build` in `comparator/`.\nEach row is what the kernel answers about one pair.\n\nA PAIR IS CERTIFIED AS MATHLIB'S AND CARRIES NO SURCHARGE UNLESS ITS ROW SAYS\nOTHERWISE. `challenge_is_mathlibs` proves the challenge FROM Mathlib, so the\nproposition is Mathlib's rather than ours; a pair without that witness is\nmarked `NOT CERTIFIED`, and one paying beyond both sides carries a\n`surcharge` line.\n\n`rests on` counts the propositions proved under `FromAxioms/` that the proof\nactually reaches; a pair reaching none has not used this library.\n\nA surcharge is what a pair pays beyond both the tower theorems it uses and\nMathlib's own proof of the same statement. A statement whose vocabulary carries\n`Classical.choice` costs it whoever proves it, so that is charged to neither\nside.\n\nGenerality is NOT here. Comparing two binder lists is a reading rather than a\ncomputation, so `formalization.yaml` carries it per pair, where it can say that\na pair is narrower than what it matches.\n\n"
  for (n, cert, paid, props, owed, applied, extra) in rows do
    out := out ++ s!"## `{n}`\n\n"
    if cert != "yes" then
      out := out ++ "- NOT CERTIFIED: no `challenge_is_mathlibs` proves this\n"
    out := out ++ s!"- this pair costs: `{paid.toList}`\n"
    out := out ++ s!"- rests on {props.size} tower proposition(s), costing `{owed.toList}`\n"
    for c in props.toList.take 4 do out := out ++ s!"    - `{c}`\n"
    if !applied.isEmpty then
      out := out ++ s!"- Mathlib's own proof applies {applied.size} theorem(s), among them\n"
      for c in applied.toList.take 3 do out := out ++ s!"    - `{c}`\n"
    if !extra.isEmpty then
      out := out ++ s!"- surcharge beyond both: `{extra.toList}`\n"
    out := out ++ "\n"
  IO.FS.writeFile "PAIRS.md" out
  IO.println s!"PAIRS.md written: {rows.size} pair(s)"

#eval writePairs

end Comparator.Audit
