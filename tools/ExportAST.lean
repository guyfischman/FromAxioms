/-
Every Phase 2 declaration, as JSON, from the compiler rather than from a regex.

`tools/lean.py` parses Lean with regexes, and the failures are not hypothetical:
a signature splitter needed a hand-written depth scanner, a probe was aborted by
a keyword, and a declaration's kind was read wrong. This is the ground truth
those tools should be consuming.

    lake env lean tools/ExportAST.lean

prints one JSON object per line: name, module, kind, whether it is private, the
axioms it depends on, structural hashes of its type and value, and the library
constants it refers to. The hashes
are what an allow list should key on -- they change when the elaborated term
changes, even if the source text does not.

**Phase 1 is not exported, and cannot be.** Reading the environment needs
`import Lean`, `Lean` imports `Init`, and `Init` already contains `And`, `Or`
and `Eq` -- the very declarations `FromAxioms/Logic/` defines. That is the same
collision the two-root split exists for, so Phase 1 keeps the text parser.
-/

import FromAxioms
import Lean

open Lean

private def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- UNMANGLE, exactly as the `name` field does. A reference to a private
declaration arrives as `_private.<module>.<hash>.<name>` while the row it points
at is keyed on the user-facing name, so leaving these mangled made 461
references dangle the moment private rows started being emitted -- reported by
`dag.py` as an undercounted graph, and invisible to `figclaims.py`, which
recomputes its totals from this same export so both numbers move together. -/
private def userNames (ns : Array Name) : Array Name :=
  ns.map fun r => (privateToUserName? r).getD r

/-- Declarations the compiler generates for us -- matchers, `brecOn`, equation
lemmas -- are not part of what the library offers, and counting them would swamp
every measurement. `isInternalDetail` is the compiler's own answer to the
question; `isInternal` alone misses `.match_1` and friends, which is 401
declarations here.

**Ask it of the USER-FACING name.** Lean mangles a private declaration to
`_private.<module>.<hash>.<name>`, and `isInternalDetail` is true of any name
whose root component starts with `_` -- so an exclusion written for compiler
detail took the ENTIRE private surface with it. 302 private declarations, zero
private rows in 8304, and every row printing `"private": false`, which reads as
*there are none* rather than *none were emitted*.

Stripping the prefix first is what keeps both halves right: a private lemma
`_private.M.h.foo` has base `foo` and is NOT internal, while a private matcher
`_private.M.h.foo.match_1` has base `foo.match_1` and still is. Testing
`!isPrivateName n` instead would have readmitted the matchers. -/
private def isInternal (n : Name) : Bool :=
  let base := (privateToUserName? n).getD n
  base.isInternalDetail || n.hasMacroScopes

/-- Whether the compiler produced this declaration rather than the library
writing it. `isInternal` catches matchers and macro scopes; this catches the
rest -- constructors and recursors of an `inductive`, the projections of a
`structure`, the auxiliary recursors, and `noConfusion`.

**It must be the compiler's answer and not a name pattern.** A structure
projection is named `Foo.field`, indistinguishable from a theorem named
`Foo.field`, so any exclusion written as a regex over names would be a
hand-maintained list -- and maintained by whoever writes the parser, which means
the declaration form the parser cannot read is the form most likely to be
excluded by hand as "generated". The list and the parser would share a blind
spot by construction.

**A declaration range is NOT the criterion, and that was measured rather than
assumed.** The appealing version asked `findDeclarationRanges?` -- did this come
from source text? -- on the theory that a synthesised declaration has no
position. It has one: generated declarations inherit the position of the syntax
that produced them, so `PSet.rec` and `PSet.casesOn` both report a range and the
miss count went from 245 to 539. The clean single fact was wrong in the
direction that matters, and it looked cleaner than what works.

**`isReservedName` is the compiler's own list**, which is the distinction worth
keeping: a list Lean maintains for its own generated forms is a witness, and the
same list transcribed here would be a mirror. It covers `.rec`, `.casesOn`,
`.brecOn`, `.below`, `.injEq`, `.noConfusion`, `.sizeOf_spec` and the rest,
without this file naming any of them. -/
private def isGenerated (env : Environment) (n : Name) : ConstantInfo → Bool
  | .ctorInfo _ => true
  | .recInfo _ => true
  | _ => isReservedName env n || env.isProjectionFn n
         || isAuxRecursor env n || isNoConfusion env n

private partial def countForall : Expr → Nat
  | .forallE _ _ b _ => 1 + countForall b
  | _ => 0

/-- Which leading parameters the value never mentions, or `none` when the
question cannot be asked.

Lean's `unusedVariables` linter **does not fire on definition parameters** -- a
`def` with four whose body mentions three compiles silently -- so `binders.py`,
which reads the linter, catches an unused binder in a *proof* and is
structurally blind to one in a *definition*.

**Three outcomes, not two, and the third is why this was probed before it was
written.** Analysis warned that a structurally recursive `def` may have a value
that is not lambda-headed, in which case walking the value's binders examines
fewer than the declaration has. Measured: of 1,222 Phase 2 defs with parameters,
1,179 have exactly as many leading lambdas as their type has binders and **43 do
not** -- `ZFSet.Mem` short by two, `sUnion`, `freeC`, `lenCode`, `D0.val` by
one. For those the honest answer is `none`. Reporting them as "no unused
parameters" would be a default dressed as a finding, and it is exactly the case
where the field would be wrong in a way that looks right.

`hasLooseBVar` is what makes the rest exact: it accounts for nested binders, so
a parameter mentioned only under a lambda inside the body counts as used. -/
private def unusedParams (ci : ConstantInfo) : Option (Array Nat) :=
  match ci with
  | .defnInfo di =>
    let want := countForall di.type
    if want == 0 then some #[] else
    let rec go : Nat → Expr → Array Nat → Option (Array Nat)
      | 0, _, acc => some acc
      | n + 1, .lam _ _ b _, acc =>
          go n b (if b.hasLooseBVar 0 then acc else acc.push (want - (n + 1)))
      | _, _, _ => none            -- fewer lambdas than parameters: unknown
    go want di.value #[]
  | _ => none

/-- The library constants a declaration mentions, type and value together.
The type counts: a definition appearing only in a theorem's *statement* is
still the library saying something about it, which is the question
`tools/inert.py` asks. Uses the elaborator's resolved names, so a use written
as dot notation on a variable -- `a.ArithB d`, which no tokeniser can
attribute to a namespace -- is seen like any other. -/
private def usedBy (env : Environment) (self : Name) (ci : ConstantInfo) :
    Array Name :=
  let all := match ci.value? with
    | some v => ci.type.getUsedConstants ++ v.getUsedConstants
    | none => ci.type.getUsedConstants
  userNames <| all.filter fun r =>
    !isInternal r && r != self &&
      (match env.getModuleIdxFor? r with
       | some j => (`FromAxioms).isPrefixOf env.header.moduleNames[j.toNat]!
       | none => false)

/-- The constants a declaration invokes from OUTSIDE `FromAxioms`.

`usedBy` keeps only names whose module is prefixed `FromAxioms`, which is right
for `astcheck.py` -- the regex parser is checked against what the library
WRITES. It makes the export unable to answer a different question: *which core
lemmas does the tower actually invoke, and what do they cost*.

That question has an answer worth having. Measured on a sample: `Nat.sub_lt`,
`Nat.le_antisymm`, `Nat.strongRecOn` and `Decidable.byCases` depend on NO
axioms; `Nat.div_le_self`, `Int.emod_emod_of_dvd` and `List.mem_append` cost
`propext`. Three readings, none classical -- so the sweep distinguishes, and a
roster of offenders alone could not tell *nobody looked* from *somebody looked
and it was clean*.

Recursors and other internals are dropped by `userNames`/`isInternal`, as they
are for `refs`; what remains is what a person wrote. -/
private def coreUsedBy (env : Environment) (self : Name) (ci : ConstantInfo) :
    Array Name :=
  let all := match ci.value? with
    | some v => ci.type.getUsedConstants ++ v.getUsedConstants
    | none => ci.type.getUsedConstants
  userNames <| all.filter fun r =>
    !isInternal r && r != self &&
      (match env.getModuleIdxFor? r with
       | some j => !((`FromAxioms).isPrefixOf env.header.moduleNames[j.toNat]!)
       | none => false)

/-- The constants a declaration's *statement* mentions, without its proof.

`refs` unions the type with the value, so it cannot distinguish a principle a
theorem **states** from one its proof merely invokes. That is why an
implication between principles had to be recognised by its *name* --
`llpo_of_wkl` -- rather than by what it says, which tests the naming
convention instead of the thing. -/
private def usedByType (env : Environment) (self : Name) (ci : ConstantInfo) :
    Array Name :=
  userNames <| ci.type.getUsedConstants.filter fun r =>
    !isInternal r && r != self &&
      (match env.getModuleIdxFor? r with
       | some j => (`FromAxioms).isPrefixOf env.header.moduleNames[j.toNat]!
       | none => false)

/-- The constants a declaration's *proof* mentions, without its statement.

The complement of `usedByType`, and NOT derivable from the fields beside it:
`refs` is the UNION, so a constant appearing in both the type and the value is
indistinguishable from one appearing only in the type. Recovering the term side
needs the term side.

What it buys is the question `refs` cannot ask -- a principle a theorem STATES
and its proof never invokes. A hypothesis carried in the signature and unused by
the argument is exactly that shape, and `binders.py` can only see it through the
compiler's warnings, which a REPLAYED build does not emit. -/
private def usedByValue (env : Environment) (self : Name) (ci : ConstantInfo) :
    Array Name :=
  userNames <| (match ci.value? with
    | some v => v.getUsedConstants
    | none => #[]).filter fun r =>
    !isInternal r && r != self &&
      (match env.getModuleIdxFor? r with
       | some j => (`FromAxioms).isPrefixOf env.header.moduleNames[j.toNat]!
       | none => false)

/-- A nullary `Prop`-valued definition: `def WKL : Prop := ...`.

This is what a principle *is*, stated as a property of the declaration
rather than as a lookup. Both edge detectors ask "is this constant a
**registered** principle?", so neither can see an implication between
principles the registry does not name -- `dc -> acomega` was proved in the
library and invisible to both for exactly that reason. A
detector keyed on this instead consults no registry at all.

Nullary matters and is not a separate test: a definition taking arguments
has a `forallE` type, so `IsTree` and `Extendable` are `Prop`-valued and
excluded here without anything having to say so. -/
private def isPropDef (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => match ci.type with
    | .sort .zero => true
    | _ => false
  | _ => false

/-- A `Prop`-VALUED definition of any arity: `def Close (x y d : ...) : Prop`.

Deliberately NOT `isPropDef`, and the difference is a whole population rather
than an edge case. `isPropDef` is the *principle* detector and excludes an
argument-taking definition on purpose; a tool asking which definitions restate
another wants exactly the ones it excludes. Keying such a tool on `isPropDef`
gives it a population of 67 in which no hit is possible, and a clean sweep over
a set that cannot contain the answer looks identical to a clean tree. -/
private partial def propValuedType : Expr → Bool
  | .forallE _ _ b _ => propValuedType b
  | .letE _ _ _ b _ => propValuedType b
  | .mdata _ e => propValuedType e
  | .sort .zero => true
  | _ => false

/-- Is every argument of the conclusion a FREE, UNRESTRICTED variable?

A witness of a FAMILY concludes `S z` for `z` a bound variable that no
hypothesis mentions. Two things are not that, and only one is visible in the
spine columns:

* `S (f c)` applies the structure to a CONSTRUCTED argument, so it witnesses one
  INSTANCE. The spine shows this -- the argument's head is a constant.
* `∀ x, x ∈ K → S x` concludes on a bound variable that a hypothesis RESTRICTS,
  which is the same restriction as applying a constructor to it. The spine does
  NOT show it: the hypothesis binder's spine comes back empty, so a rule reading
  spines cannot tell it from a free index. The whole content of such a theorem
  is that `K` is where the readout becomes free, so counting it as a family
  witness would be exactly backwards (geometry, who found it).

Computed here rather than approximated in Python, for the reason this tree keeps
relearning: a stand-in agrees with the property on every case anyone checked.

De Bruijn bookkeeping: binder `j` counted from the outside is `bvar (n-1-j)` in
the conclusion and `bvar (k-1-j)` inside binder `k`'s type, so a later binder
mentioning it is exactly a loose bvar at that index. -/
private partial def collectBinders : Expr → Array Expr → (Array Expr × Expr)
  | .forallE _ d b _, acc => collectBinders b (acc.push d)
  | e, acc => (acc, e)

private def conclFreeIndices (type : Expr) : Bool :=
  let (binders, concl) := collectBinders type #[]
  let n := binders.size
  concl.getAppArgs.all fun a =>
    match a with
    | .bvar i =>
      if i < n then
        let j := n - 1 - i
        !((List.range n).any fun k =>
            decide (k > j) && (binders[k]!).hasLooseBVar (k - 1 - j))
      else false
    | _ => false

private def isPropValued (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ => propValuedType ci.type
  | _ => false

/-- The head constant of the statement's conclusion, after the hypotheses and
binders are stripped. With `typeRefs` this is what gives an implication its
direction: the set says which principles appear, the head says which one is
concluded. Empty when the conclusion is not headed by a constant. -/
private partial def conclusionHead : Expr → Name
  | .forallE _ _ b _ => conclusionHead b
  | .letE _ _ _ b _ => conclusionHead b
  | .mdata _ e => conclusionHead e
  | e => (e.getAppFn.constName?).getD Name.anonymous

/-- Every constant CONCLUDED, descending through the connectives.

`head` reads the ROOT of the conclusion, so a producer whose statement is an
`↔` has head `Iff` and its subject is invisible -- `exists_deg_iff` produces
`IsDegOf` and `lattice.py --sources` ranked `IsDegOf` second-worst UNPRODUCED
(analysis, 4 false positives of 17). Unwrapping `Iff` alone is not the repair:
`exists_critical_or_not` concludes a DISJUNCTION, and the family is -- a proxy that reads the root of a term cannot see the term.

So this descends through `Iff`, `And`, `Or`, `Not` and `Exists`, and stops at
anything else. It is deliberately NOT a full traversal of the conclusion: an
argument of a produced predicate is mentioned, not concluded, and collapsing
those two would make the report say nothing. `head` is kept beside this,
unchanged, because the direction of an implication is a different question from
what a theorem establishes. -/
private partial def conclusionHeads : Expr → List Name
  | .forallE _ _ b _ => conclusionHeads b
  | .letE _ _ _ b _ => conclusionHeads b
  | .mdata _ e => conclusionHeads e
  | .lam _ _ b _ => conclusionHeads b
  | e =>
    let args := e.getAppArgs.toList
    match e.getAppFn.constName? with
    | some n =>
      if n == ``Iff || n == ``And || n == ``Or || n == ``Not
          || n == ``Exists then
        args.foldl (fun acc a => acc ++ conclusionHeads a) []
      else [n]
    | none => []

/-- The ENVIRONMENT'S OWN KIND for each conclusion head.

**Distinguishes a structure being CONSTRUCTED from a constant being
REFERENCED**, which is the question two detectors independently needed and
neither could ask (, 1223; scheduling recorded in 2754).

Their obstruction was the same: a rule of the form *the conclusion mentions a
constant the proof never touches, AND the conclusion is not a structure being
constructed* is unsatisfiable from names alone, because excluding conclusion
heads that are defs, Prop-defs or structures returns ZERO -- conclusion heads
are defs and structures essentially by definition.

So the field reports the environment's classification rather than inventing
one: `kindOf` already answers `constructor`, `inductive`, `def`, `theorem`,
`axiom`, and a caller asking *is this head a value being built* now does a
LOOKUP instead of a heuristic.

Parallel to `heads` and deduped the same way, so index i of one names index i
of the other. A head the environment does not know -- which `conclusionHeads`
can yield for a bound variable applied to arguments -- reports `unknown`
rather than being dropped, because dropping it would silently misalign the two
arrays and that is exactly the failure a paired encoding invites.
-/
/-- A hash of the CONCLUSION alone, binders stripped.

**The key a meaning-keyed duplicate sweep needs, and the one the export did not
have.** Measured before adding it: clustering the 10953 public theorems by
`conclSpine` puts 6958 of them in 1336 clusters, largest 155, because a spine is
the head plus each argument's HEAD and drops the arguments themselves. The pair
that motivated the sweep -- `remainder_unique` and `remainder_unique_domain`,
character-identical but for one argument -- lands in a cluster of TWELVE. So the
spine catches the case and buries it.

`typeHash` is the opposite error: it covers the whole type, so two statements
of one theorem under different hypotheses never match, which is exactly the pair
a hypothesis-stripping search exists to find.

This hashes the conclusion after `forallE` binders are stripped, so it is the
same object `concludes.py` renders per query -- but computed once for every
declaration instead of once per Lean invocation, which is what makes a SWEEP
possible at all. 10953 invocations is not a sweep.

Deliberately NOT descending through `Exists`, unlike `conclusionSpine`: that
descent exists so a witness search can see inside an existential, and folding
`∃ g, P g` together with `P g` would merge two genuinely different statements.
-/
private partial def conclusionOf : Expr → Expr
  | .forallE _ _ b _ => conclusionOf b
  | .letE _ _ _ b _ => conclusionOf b
  | .mdata _ e => conclusionOf e
  | e => e

/-- Where `n` first appears in `xs`, or `xs.length` if it does not. -/
private def rankOf (xs : List Nat) (n : Nat) : Nat :=
  let rec go : List Nat → Nat → Nat
    | [],      k => k
    | x :: tl, k => if x == n then k else go tl (k + 1)
  go xs 0

/-- The LOOSE bound variables of `e`, as outer ids, in first-occurrence order.
`d` is the number of binders entered since the conclusion began. -/
private partial def looseIds : Expr → Nat → List Nat → List Nat
  | .bvar i,           d, acc =>
      if i < d then acc
      else if acc.contains (i - d) then acc else acc ++ [i - d]
  | .app f a,          d, acc => looseIds a d (looseIds f d acc)
  | .lam _ t b _,      d, acc => looseIds b (d + 1) (looseIds t d acc)
  | .forallE _ t b _,  d, acc => looseIds b (d + 1) (looseIds t d acc)
  | .letE _ t v b _,   d, acc => looseIds b (d + 1) (looseIds v d (looseIds t d acc))
  | .mdata _ x,        d, acc => looseIds x d acc
  | .proj _ _ x,       d, acc => looseIds x d acc
  | _,                 _, acc => acc

private partial def renumber (m : List Nat) : Expr → Nat → Expr
  | .bvar i,           d => if i < d then .bvar i else .bvar (d + rankOf m (i - d))
  | .app f a,          d => .app (renumber m f d) (renumber m a d)
  | .lam n t b bi,     d => .lam n (renumber m t d) (renumber m b (d + 1)) bi
  | .forallE n t b bi, d => .forallE n (renumber m t d) (renumber m b (d + 1)) bi
  | .letE n t v b nd,  d => .letE n (renumber m t d) (renumber m v d) (renumber m b (d + 1)) nd
  | .mdata _ x,        d => renumber m x d
  | .proj s i x,       d => .proj s i (renumber m x d)
  | e,                 _ => e

/-- A hash of the conclusion with its free variables abstracted POSITIONALLY.

The naive version -- hash the term left after stripping `forallE` -- is keyed
on the NUMBER OF HYPOTHESES, which is the one thing a hypothesis-stripping key
must ignore. A loose de Bruijn index counts binders outward from where it
stands, so `remainder_unique` and `remainder_unique_domain`, whose conclusions
are both `r = polyZero R zero` character for character, hashed differently
purely because the second takes two more hypotheses. Renumbering the loose
variables into first-occurrence order removes the dependence.

`mdata` is dropped rather than descended through, so an annotation the
elaborator happened to leave on one side does not split a pair.

**What this deliberately DOES merge**: two conclusions of the same shape over
unrelated variables. `a = polyZero b c` is one key however the variables were
bound, which is the intended reading of *same conclusion* and is why the
report is a report and not a check. -/
private def conclusionHash (t : Expr) : String :=
  let c := conclusionOf t
  toString (renumber (looseIds c 0 []) c 0).hash

private def conclusionHeadKinds (env : Environment) (t : Expr) : List String :=
  (conclusionHeads t).eraseDups.map fun n =>
    match env.find? n with
    | some ci => kindOf ci
    | none    => "unknown"

/-- The APPLICATION SPINE of a term: its head, then each argument's head, one
level deep, with `_` for anything that is not a constant application.

`head` and a flat `typeRefs` leave every consumer reading roots, which cannot
answer the question the family exists for: *is this predicate ever concluded AT
THE ARGUMENT SHAPE somebody assumes it at*. `close_invApart` took
`WithinOf (realLInvApart x) (realLOf c)` twice with nothing building one, while
`WithinOf` is concluded constantly.

**One level, not the whole tree.** It is the minimum that distinguishes
`P _ (f _)` from `P _ _`, and going deeper multiplies the shapes without
separating more cases -- subsumption (`P _ _` instantiates to `P _ (f _)`) is
what the consumer must credit, and that is cheaper on short spines.

**Elaborated rather than textual, and the gap is measured.** `producers.py`
reads source signatures and cannot tell a BOUND VARIABLE from a constant: 4 of
its 25 rows are headed `A`, `B`, `F`, `G`, which are binder names in the
theorems' own signatures. Here a local is not a `const` and renders as `_` by
construction. It is also blind to implicit arguments, which this is not. -/
private def spineOf (e : Expr) : List String :=
  let arg (a : Expr) : String :=
    match a.getAppFn with
    | .const n _ => n.toString
    | _ => "_"
  match e.getAppFn with
  | .const n _ => n.toString :: (e.getAppArgs.toList.map arg)
  | _ => []

/-- The conclusion's spine, after the binders are stripped.

**Descends through `Exists`**, because `\u2203 g, IsRecApprox A a f n g` is how this
tower states that a structure is inhabited, and stopping at the head reports
`Exists` -- which is true of every existential and says nothing about any of
them. A witness sweep keyed on the head then reads *nothing concludes this
structure* while the file beside it proves exactly that, and the error runs in
the FALSE-ABSENCE direction, which is the one that does not announce itself.

The descent is into the predicate's body, and `Exists` stores it as a lambda,
so the binder is stripped the same way a `forallE` is. Nested existentials
recurse: `exists_finiteGaloisSetup` quantifies seven variables before naming its
structure. -/
private partial def conclusionSpine : Expr → List String
  | .forallE _ _ b _ => conclusionSpine b
  | .letE _ _ _ b _ => conclusionSpine b
  | .mdata _ e => conclusionSpine e
  | e =>
    match e.getAppFn, e.getAppArgs with
    | .const ``Exists _, #[_, .lam _ _ body _] => conclusionSpine body
    | _, _ => spineOf e

/-- **The head of each binder whose type is itself QUANTIFIED**, in order:
`(h : ∀ z, SideReadout z)` contributes `SideReadout`, `(h : SideReadout c)`
contributes nothing.

`binderSpines` cannot make this distinction --- a restricting hypothesis
contributes an EMPTY spine, so an instance and a family look identical there.
The difference matters because for a READOUT the quantified form is the priced
principle and an instance proves nothing, while for a BUNDLE the quantified
form is false and the instance is the only witness a structure can have. One
column, read in opposite directions by two populations.

An ordinary arrow is a `forallE` too, so this also reports the codomain head of
a plain function hypothesis; the consumer filters to the structures it is
asking about. -/
private partial def quantifiedBinderHeads : Expr → List String
  | .forallE _ d b _ =>
    (match d with
     | .forallE _ _ _ _ => [(conclusionHead d).toString]
     | _ => []) ++ quantifiedBinderHeads b
  | .letE _ _ _ b _ => quantifiedBinderHeads b
  | .mdata _ e => quantifiedBinderHeads e
  | _ => []

/-- One spine per hypothesis binder, in order. -/
private partial def binderSpines : Expr → List (List String)
  | .forallE _ d b _ => spineOf d :: binderSpines b
  | .letE _ _ _ b _ => binderSpines b
  | .mdata _ e => binderSpines e
  | _ => []

/-- The type's *shape*: its structure with every library constant's name
erased and core constants kept. Two statements that differ only in which
construction they talk about -- `bisectR_step` and `halveR_step`, before the
first was retired -- have the same shape and different types.

Erasing core constants too would collapse `∈` with `≤` and match everything,
so the line is drawn at the library boundary: what this development names is
what a copied abstraction would have renamed. A shape collision is a
*candidate*, never a verdict; `tools/abstract.py` reports families of them,
because one pair is a coincidence and nine at once is a copied machine. -/
private partial def shapeOf (env : Environment) : Expr → String
  | .const n _ =>
      match env.getModuleIdxFor? n with
      | some j =>
        if (`FromAxioms).isPrefixOf env.header.moduleNames[j.toNat]! then "K"
        else "c" ++ n.toString
      | none => "c" ++ n.toString
  | .app f a => "(" ++ shapeOf env f ++ " " ++ shapeOf env a ++ ")"
  | .lam _ t b _ => "L" ++ shapeOf env t ++ "." ++ shapeOf env b
  | .forallE _ t b _ => "P" ++ shapeOf env t ++ "." ++ shapeOf env b
  | .letE _ t v b _ => "E" ++ shapeOf env t ++ shapeOf env v ++ shapeOf env b
  | .bvar i => "b" ++ toString i
  | .fvar _ => "f"
  | .mvar _ => "m"
  | .sort _ => "S"
  | .lit _ => "l"
  | .mdata _ e => shapeOf env e
  | .proj n i e => "j" ++ n.toString ++ toString i ++ shapeOf env e

/-- The same shape with *binder types* erased as well.

`shapeOf` alone misses the case it was written for. `bisectR_step` quantified
over `G : ZFSet → ZFSet` and `halveR_step` over `P : ZFSet → ZFSet → Prop`;
the two statements are otherwise identical, but a binder type is part of the
expression, so the shapes differed and the pair went unreported. What makes
them the same statement is the *body* -- what is claimed about the payload,
not what the payload is -- so this erases the binder's type and keeps the
body. Coarser on purpose, and the suffix agreement in `tools/abstract.py` is
what keeps it readable. -/
private partial def bodyOf (env : Environment) : Expr → String
  | .const n _ =>
      match env.getModuleIdxFor? n with
      | some j =>
        if (`FromAxioms).isPrefixOf env.header.moduleNames[j.toNat]! then "K"
        else "c" ++ n.toString
      | none => "c" ++ n.toString
  | .app f a => "(" ++ bodyOf env f ++ " " ++ bodyOf env a ++ ")"
  | .lam _ _ b _ => "L T." ++ bodyOf env b
  | .forallE _ _ b _ => "P T." ++ bodyOf env b
  | .letE _ _ v b _ => "E" ++ bodyOf env v ++ bodyOf env b
  | .bvar i => "b" ++ toString i
  | .fvar _ => "f"
  | .mvar _ => "m"
  | .sort _ => "S"
  | .lit _ => "l"
  | .mdata _ e => bodyOf env e
  | .proj n i e => "j" ++ n.toString ++ toString i ++ bodyOf env e

#eval show CoreM Unit from do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    if isInternal name then continue
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`FromAxioms).isPrefixOf mod do continue
    let axs ← collectAxioms name
    let row := Json.mkObj [
      -- The USER-FACING name: `_private.<module>.<hash>.<name>` matches
      -- nothing the parser or the registries know, so a row under the
      -- mangled name would be present and unusable. `private` below
      -- carries the distinction that the prefix was doing.
      ("name", Json.str ((privateToUserName? name).getD name).toString),
      ("module", Json.str mod.toString),
      ("kind", Json.str (kindOf ci)),
      ("private", Json.bool (isPrivateName name)),
      ("generated", Json.bool (isGenerated env name ci)),
      ("unusedParams", match unusedParams ci with
        | some a => Json.arr (a.map (fun i => Json.num (JsonNumber.fromNat i)))
        | none => Json.null),
      ("axioms", Json.arr (axs.map (fun a => Json.str a.toString))),
      ("typeHash", Json.str (toString ci.type.hash)),
      ("shapeHash", Json.str (toString (hash (shapeOf env ci.type)))),
      ("bodyHash", Json.str (toString (hash (bodyOf env ci.type)))),
      ("valueHash", Json.str (match ci.value? with
        | some v => toString v.hash
        | none => "")),
      ("refs", Json.arr (((usedBy env name ci).toList.eraseDups.map
        (fun r => Json.str r.toString)).toArray)),
("coreRefs", Json.arr (((coreUsedBy env name ci).toList.eraseDups.map
        (fun r => Json.str r.toString)).toArray)),
      ("typeRefs", Json.arr (((usedByType env name ci).toList.eraseDups.map
        (fun r => Json.str r.toString)).toArray)),
      ("valueRefs", Json.arr (((usedByValue env name ci).toList.eraseDups.map
        (fun r => Json.str r.toString)).toArray)),
      ("head", Json.str (conclusionHead ci.type).toString),
      ("heads", Json.arr (((conclusionHeads ci.type).eraseDups.map
        (fun r => Json.str r.toString)).toArray)),
      ("conclHeadKinds", Json.arr (((conclusionHeadKinds env ci.type).map
        Json.str).toArray)),
      ("conclHash", Json.str (conclusionHash ci.type)),
      ("conclSpine", Json.arr (((conclusionSpine ci.type).map Json.str).toArray)),
      ("binderSpines", Json.arr (((binderSpines ci.type).map
        (fun s => Json.arr ((s.map Json.str).toArray))).toArray)),
      ("isPropDef", Json.bool (isPropDef ci)),
      ("isPropValued", Json.bool (isPropValued ci)),
      ("quantifiedBinderHeads", Json.arr
        (((quantifiedBinderHeads ci.type).map Json.str).toArray)),
      ("conclFreeIndices", Json.bool (conclFreeIndices ci.type))
    ]
    IO.println row.compress
