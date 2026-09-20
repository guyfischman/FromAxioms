#!/usr/bin/env python3
"""Principle-shaped hypotheses no registry accounts for.

`#print axioms` is the whole-library sweep for axioms, and `audit.py` refuses
any non-constructive result without a `classical.json` entry. That side is
closed.

**A principle carried in a binder audits exactly as clean as one that needs
nothing.** `EM` is a `def : Prop`, so `(hem : EM)` is a signature, not a proof
step, and no axiom line can see it, which is the reason this file exists.

So the question here is the auditor's: which principle-shaped hypotheses are
taken somewhere and accounted for nowhere. It reports the takers, so a
reviewer can read the site rather than the name.

    python3 tools/hypaudit.py              # report
    python3 tools/hypaudit.py --names      # bare names, one per line
    python3 tools/hypaudit.py --taker NAME # which declarations take one

**Report-only.** There is no `--check`, and nothing gates on this. Most
unaccounted names are ordinary predicates stated as hypotheses precisely so
their price is visible, so a count here is a reading rather than a debt.

**No figure is quoted here.** `_freshness()` and `_population()` print the
counts instead, because a number in prose beside a tool that computes it is a
claim nobody re-runs.

**What it cannot see, and the first is the one that matters.**

  * Parameterised principles. `DCOn (baireStateOn X)` has type
    `ZFSet -> Prop`, so `isPropDef` is false and it is invisible here. A clean
    report is therefore not a statement that nothing parameterised is
    unaccounted.
  * Strengths arriving as data. A readout, a selector or a modulus is a
    function, not a Prop, and `hypcost.json` already holds two such nodes
    (`choice`, `natof`). This population is Props only.
  * Whether a listed name is a strength. This is a name-shape measurement:
    nullary Prop-def, taken in a binder spine, minus two registries. It
    produces candidates for reading, never a verdict.

An empty result means nothing was found in that population.
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
    # Registries key on bare names; the export is fully qualified. And the
    # comparison is case-insensitive: a registered principle whose name has
    # capitals reads as a debt otherwise.
    known = {n.split(".")[-1].lower() for n in (lat.get("nodes") or [])}
    known |= {k.lower() for k in hyp if not k.startswith("_")}
    # `_unplaced` is a registry. A principle adjudicated there as
    # unplaceable is accounted for, and reporting it as unregistered asks a
    # reader to adjudicate what is already adjudicated. A backlog with an
    # irreducible floor stops being read at all.
    cls = _load(ROOT / "tools" / "classical.json") or {}
    known |= {e.get("principle", "").split(".")[-1].lower()
              for e in (cls.get("_unplaced") or []) if e.get("principle")}
    # And `hypotheses.json` is a registry too, which this counted as none at
    # all: two tools, one question, opposite answers.
    hyps = _load(ROOT / "tools" / "hypotheses.json") or {}
    known |= {k.split(".")[-1].lower() for k in hyps if not k.startswith("_")}
    known.discard("")

    takers = {}
    for r in rows:
        for h in _spine_names(r) & nullary:
            takers.setdefault(h, []).append(r["name"])

    # Concluders, for the second question this tool answers: is anything even
    # claiming to establish this, or is it only ever assumed?
    #
    # `head` is the conclusion's head after telescoping, so a declaration
    # concluding `EM` has `head == "Constructive.EM"`. Concluded is not
    # discharged and the distinction is the whole care needed here: `EM` has 35
    # concluders and every one is a reversal (`em_of_subgroupFinite`), deriving
    # it from something rather than proving it. So a positive count means only
    # that the name appears on the right of an arrow somewhere, so the report
    # says `some declaration concludes it` and not `it is proved`.
    #
    # The sound half is the negative: zero concluders means nothing in the
    # library so much as claims to establish it. Combined with absence from
    # every registry, that is a hypothesis assumed and owed.
    concluders = {}
    for r in rows:
        h = r.get("head")
        if h in nullary:
            concluders.setdefault(h, []).append(r["name"])

    # Third tier, and it is weaker evidence than the other two. A landmark row
    # can price a principle in its `principle` field or merely mention it in
    # prose, and this cannot tell those apart: it is a substring test over the
    # whole registry. It is reported separately rather than folded into
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
    # Cased the same way as above, and it is written twice: `known` is
    # lowercased, so a comparison that is not reports a registered principle
    # as a debt.
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
    print(f"  Answered from an export that predates the sources --"
          f" {len(stale)} module(s)")
    print("  have changed since it was written. Every count below is about the")
    print("  tree as it was. A hypothesis landed since is missing from the")
    print("  population, and one removed since is still counted.")
    print("  Run `python3 tools/regen.py`, then re-run this.")
    print("=" * 74)


def _population():
    """The extent this tool's answers are about, printed rather than assumed.

    A tool that computes a declaration set and reports an absence must say
    which population the absence is over. These takers come from this tree's
    elaborated export, so every count below is a floor.
    """
    print("  One branch, and every count here is a lower bound. The takers are")
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
        print("  elaborated binders, so a source scan cannot stand in for it.")
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
    print(f"    registered (lattice, hypcost, hypotheses): {len(acc)}")
    print(f"    only mentioned in landmark-parity:    {len(mentioned)}")
    print(f"    in no registry at all:                {len(unacc)}")
    print()
    print("  The middle tier is a substring test over the parity registry, so")
    print("  it cannot separate a priced `principle` field from a passing")
    print("  mention in someone's note. It is listed apart from registered")
    print("  because that difference is the whole question.")
    print()
    for n, sites in sorted(unacc.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        print(f"  {len(sites):5d}  {n}")
    print()
    print("  `--taker NAME` lists the declarations taking one, so the site can")
    print("  be read rather than the name guessed at.")
    print()
    print("  This is a candidate list, not a verdict. A nullary Prop-def stated")
    print("  as a hypothesis is usually the discipline working -- the price is")
    print("  in the signature where a reader can see it. What the list is for is")
    print("  that nobody has ruled on these one way or the other.")
    print()
    print("-" * 74)
    print(f"  Assumed and never concluded, in no registry: {len(debt)}")
    print("-" * 74)
    for n, sites in sorted(debt.items(), key=lambda kv: (-len(kv[1]), kv[0])):
        print(f"  {len(sites):5d} takers  {n}")
    print()
    print("  These are the ones nothing in the library concludes -- not a")
    print("  reversal, not a construction, nothing -- and that no registry")
    print("  prices. A theorem taking one is conditional on something nobody")
    print("  has established or declared a principle.")
    print()
    print("  Concluded is not discharged. `EM` has 35 concluders and all are")
    print("  reversals deriving it from something. So a name being absent from")
    print("  this list is weaker evidence than its being on it.")
    print()
    print("  And it cannot see parameterised principles. `DCOn (baireStateOn X)`")
    print("  is `ZFSet -> Prop`, so it is absent from this population entirely;")
    print("  An empty report here is not a clean bill for the tree.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
