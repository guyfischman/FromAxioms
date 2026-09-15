#!/usr/bin/env python3
"""Principle-shaped HYPOTHESES no registry accounts for.

`#print axioms` is the whole-library sweep for AXIOMS: `.audit/Sweep*.lean`
prints every declaration reachable from `FromAxioms.Foundations`, and
`audit.py` refuses any non-constructive result without a `classical.json`
entry. That side is closed.

**A PRINCIPLE CARRIED IN A BINDER AUDITS EXACTLY AS CLEAN AS ONE THAT NEEDS
NOTHING.** `EM` is a `def : Prop`, so `(hem : EM)` is a signature, not a proof
step, and no axiom line can see it. CLAUDE.md says this in its first five lines
and it is the reason this file exists.

Three tools already measure part of it, each with a population chosen for a
DIFFERENT question, and none of them sweeps the library:

    rowbinders.py   what each PARITY ROW's cited declarations take -- row-scoped
    hypnodes.py     NULLARY Prop-defs that are not lattice nodes -- proposal-shaped
    binders.py      binders no proof USES -- the opposite error

This asks the auditor's question: which principle-shaped hypotheses are TAKEN
somewhere and accounted for NOWHERE. It reports the takers, so a reviewer can
read the site rather
than the name.

    python3 tools/hypaudit.py              # report
    python3 tools/hypaudit.py --names      # bare names, one per line
    python3 tools/hypaudit.py --taker NAME # which declarations take one

**REPORT-ONLY.** There is no `--check`, and nothing gates on this. Most
unaccounted names are ordinary predicates stated as hypotheses precisely so
their price is visible, so a count here is a reading rather than a debt.

**EVERY FIGURE IN THIS DOCSTRING HAS BEEN WRONG ONCE**, which is the reason
`_freshness()` and `_population()` now print rather than leaving the reader to
trust a comment. The counts above replaced `62 / 38 / 57`, which came from the
case-sensitivity defect; the debt count replaced `16`, from the SAME defect
written a second time. A number in prose beside a tool that computes it is a
claim nobody re-runs.

**WHAT IT CANNOT SEE, and the first is the one that matters.**

  * PARAMETERISED principles. `DCOn (baireStateOn X)` has type
    `ZFSet -> Prop`, so `isPropDef` is false and it is invisible here. A clean
    report is therefore not a statement that nothing parameterised is
    unaccounted.
  * Strengths arriving as DATA. A readout, a selector or a modulus is a
    function, not a Prop, and `hypcost.json` already holds two such nodes
    (`choice`, `natof`). This population is Props only.
  * Whether a listed name IS a strength. This is a NAME-SHAPE measurement:
    nullary Prop-def, taken in a binder spine, minus two registries. It
    produces candidates for reading, never a verdict.

An empty result means nothing was found IN THAT POPULATION.
"""
import argparse
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
EXPORT = ROOT / ".audit" / "ast-cache.json"
LATTICE = ROOT / "tools" / "lattice.json"
HYPCOST = ROOT / "tools" / "hypcost.json"


def _load(p):
    try:
        return json.loads(p.read_text())
    except (OSError, ValueError):
        return None


def _spine_names(row):
    """Every name appearing in a binder spine, however the export nests it."""
    out = set()
    for sp in (row.get("binderSpines") or []):
        if isinstance(sp, str):
            out.add(sp)
        elif isinstance(sp, list):
            out.update(x for x in sp if isinstance(x, str))
    return out


def collect():
    """`(unaccounted, accounted, takers, mentioned)`, or `None` with no export."""
    ex = _load(EXPORT)
    if not ex or "rows" not in ex:
        return None
    rows = ex["rows"]
    nullary = {r["name"] for r in rows if r.get("isPropDef")}

    lat = _load(LATTICE) or {}
    hyp = _load(HYPCOST) or {}
    # Registries key on BARE names; the export is fully qualified. AND THE
    # COMPARISON IS CASE-INSENSITIVE, which the first version got wrong and
    # which made this tool report a false gap.
    #
    # THE DEBT COUNT SURVIVED THE BUG, because those names are absent from
    # the registries in ANY casing, so the headline figure stayed intact while
    # the comparison was wrong.
    known = {n.split(".")[-1].lower() for n in (lat.get("nodes") or [])}
    known |= {k.lower() for k in hyp if not k.startswith("_")}
    # `_unplaced` IS A REGISTRY. A principle adjudicated there as
    # unplaceable is accounted for, and reporting it as unregistered asks a
    # reader to adjudicate what is already adjudicated.
    #
    # A backlog with an irreducible floor stops being read: the stop hook prints
    # `THIS IS THE PRIORITY` at a number that no correct action can move, and
    # the next session learns to discount it.
    cls = _load(ROOT / "tools" / "classical.json") or {}
    known |= {e.get("principle", "").split(".")[-1].lower()
              for e in (cls.get("_unplaced") or []) if e.get("principle")}
    # AND `hypotheses.json`, WHICH THIS COUNTED AS NO REGISTRY AT ALL --- the
    # registry `ROADMAP-ACCOUNTING`'s criterion 1 is defined against.
    #
    # Two tools, one question, opposite answers, and the report that carries
    # the priority is this one.
    hyps = _load(ROOT / "tools" / "hypotheses.json") or {}
    known |= {k.split(".")[-1].lower() for k in hyps if not k.startswith("_")}
    known.discard("")

    takers = {}
    for r in rows:
        for h in _spine_names(r) & nullary:
            takers.setdefault(h, []).append(r["name"])

    # CONCLUDERS, for the second question this tool answers: is anything even
    # CLAIMING to establish this, or is it only ever assumed?
    #
    # `head` is the conclusion's head after telescoping, so a declaration
    # concluding `EM` has `head == "Constructive.EM"`. CONCLUDED IS NOT
    # DISCHARGED and the distinction is the whole care needed here: `EM` has 35
    # concluders and every one is a REVERSAL (`em_of_subgroupFinite`), deriving
    # it FROM something rather than proving it. So a positive count means only
    # that the name appears on the right of an arrow somewhere, so the report
    # says `some declaration concludes it` and not `it is proved`.
    #
    # The sound half is the NEGATIVE: zero concluders means nothing in the
    # library so much as claims to establish it. Combined with absence from
    # every registry, that is a hypothesis assumed and owed.
    concluders = {}
    for r in rows:
        h = r.get("head")
        if h in nullary:
            concluders.setdefault(h, []).append(r["name"])

    # THIRD TIER, AND IT IS WEAKER EVIDENCE THAN THE OTHER TWO. A landmark row
    # can price a principle in its `principle` field or merely mention it in
    # prose, and this cannot tell those apart: it is a SUBSTRING test over the
    # whole registry. It is reported SEPARATELY rather than folded into
    # `accounted` for that reason -- collapsing them would let a name that
    # appears only inside someone's note read as adjudicated.
    #
    try:
        parity_text = (ROOT / "tools" / "landmark-parity.json").read_text()
    except OSError:
        parity_text = ""

    unacc, mentioned, acc = {}, {}, {}
    for k, v in takers.items():
        bare = k.split(".")[-1]
        if bare.lower() in known:
            acc[k] = v
        elif parity_text and bare in parity_text:
            mentioned[k] = v
        else:
            unacc[k] = v
    # THE SAME CASE BUG AS ABOVE, AND IT SURVIVED THE FIX BECAUSE IT IS WRITTEN
    # TWICE. `known` is lowercased; this comparison was not, so a REGISTERED
    # principle whose name has capitals was reported as a debt.
    #
    # AND THE DOCSTRING ABOVE ASSERTED THE OPPOSITE --- *the debt count survived
    # the bug at 12, because those names are absent from the registries in ANY
    # casing*. That was written when the classification was fixed here and the
    # debt line was not read. A claim about which numbers a defect spared is
    # itself a measurement, and that one was never taken.
    debt = {k: v for k, v in takers.items()
            if not concluders.get(k)
            and k.split(".")[-1].lower() not in known
            and not (parity_text and k.split(".")[-1] in parity_text)}
    return unacc, acc, takers, mentioned, debt


def _freshness():
    """Say so when the export no longer matches the sources.

    An audit tool whose output is a claim about coverage must say when its
    export no longer matches the sources: a stale denominator makes the
    coverage read better than it is.

    A count that cannot announce its own staleness is validation that cannot
    fail.
    """
    try:
        sys.path.insert(0, str(ROOT / "tools"))
        import astexport
        stale, _ = astexport.stale_modules()
    except Exception:
        return
    if not stale:
        return
    print("=" * 74)
    print(f"  ANSWERED FROM AN EXPORT THAT PREDATES THE SOURCES --"
          f" {len(stale)} module(s)")
    print("  have changed since it was written. Every count below is about the")
    print("  tree AS IT WAS. A hypothesis landed since is missing from the")
    print("  population, and one removed since is still counted.")
    print("  Run `python3 tools/regen.py`, then re-run this.")
    print("=" * 74)


def _population():
    """The extent this tool's answers are about, printed rather than assumed.

    A tool that computes a declaration set and reports an ABSENCE must say
    which population the absence is over. These takers come from this tree's
    elaborated export, so every count below is a floor.
    """
    print("  ONE BRANCH, AND EVERY COUNT HERE IS A LOWER BOUND. The takers are")
    print("  read from this tree's export, so a peer's declaration taking an")
    print("  unregistered principle is missing from these lists with no mark.")
    print("  The numbers are a claim about this branch and not about the")
    print("  project, and they rise at a merge without anything here changing.")
    print()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--names", action="store_true",
                    help="bare names of the unaccounted, one per line")
    ap.add_argument("--debt", action="store_true",
                    help="only the assumed-and-never-concluded, unregistered")
    ap.add_argument("--taker", metavar="NAME",
                    help="list the declarations that take NAME")
    args = ap.parse_args()

    got = collect()
    if got is None:
        print(f"  no elaborated export at {EXPORT.relative_to(ROOT)} --")
        print("  run `python3 tools/regen.py` first. This tool reads the")
        print("  ELABORATED binders, so a source scan cannot stand in for it.")
        return 1
    unacc, acc, takers, mentioned, debt = got

    if args.taker:
        sites = takers.get(args.taker)
        if sites is None:
            near = [k for k in takers if k.split(".")[-1] == args.taker]
            if near:
                sites = takers[near[0]]
                print(f"  (matched {near[0]})")
            else:
                print(f"  {args.taker} is taken by nothing, or is not a "
                      f"nullary Prop-def")
                return 0
        for s in sorted(sites):
            print(f"  {s}")
        return 0

    if args.debt:
        _freshness()
        _population()
        for n, sites in sorted(debt.items(), key=lambda kv: (-len(kv[1]), kv[0])):
            print(f"  {len(sites):5d} takers  {n}")
        return 0

    if args.names:
        for n in sorted(unacc):
            print(n)
        return 0

    print("=" * 74)
    print(f"HYPAUDIT  -- {len(unacc)} principle-shaped hypotheses in no registry")
    print("=" * 74)
    _freshness()
    _population()
    print(f"  nullary Prop-defs taken as a binder:   {len(takers)}")
    print(f"    REGISTERED (lattice, hypcost, hypotheses): {len(acc)}")
    print(f"    only MENTIONED in landmark-parity:    {len(mentioned)}")
    print(f"    in no registry at all:                {len(unacc)}")
    print()
    print("  The middle tier is a SUBSTRING test over the parity registry, so")
    print("  it cannot separate a priced `principle` field from a passing")
    print("  mention in someone's note. It is listed apart from REGISTERED")
    print("  because that difference is the whole question.")
    print()
    for n, sites in sorted(unacc.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        print(f"  {len(sites):5d}  {n}")
    print()
    print("  `--taker NAME` lists the declarations taking one, so the SITE can")
    print("  be read rather than the name guessed at.")
    print()
    print("  THIS IS A CANDIDATE LIST, NOT A VERDICT. A nullary Prop-def stated")
    print("  as a hypothesis is usually the discipline working -- the price is")
    print("  in the signature where a reader can see it. What the list is for is")
    print("  that NOBODY HAS RULED on these one way or the other.")
    print()
    print("-" * 74)
    print(f"  ASSUMED AND NEVER CONCLUDED, in no registry: {len(debt)}")
    print("-" * 74)
    for n, sites in sorted(debt.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        print(f"  {len(sites):5d} takers  {n}")
    print()
    print("  These are the ones NOTHING in the library concludes -- not a")
    print("  reversal, not a construction, nothing -- and that no registry")
    print("  prices. A theorem taking one is conditional on something nobody")
    print("  has established or declared a principle.")
    print()
    print("  CONCLUDED IS NOT DISCHARGED. `EM` has 35 concluders and all are")
    print("  reversals deriving it FROM something. So a name being ABSENT from")
    print("  this list is weaker evidence than its being on it.")
    print()
    print("  AND IT CANNOT SEE PARAMETERISED PRINCIPLES. `DCOn (baireStateOn X)`")
    print("  is `ZFSet -> Prop`, so it is absent from this population entirely;")
    print("  An empty report here is not a clean bill for the tree.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
