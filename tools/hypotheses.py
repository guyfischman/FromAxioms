#!/usr/bin/env python3
"""The hypothesis inventory: principles assumed in binders, not proved.

The axiom audit tracks what proofs *use*; nothing tracked what statements
*assume*. `DC`, the readouts, `EM`-as-hypothesis, `TotalGraphs` -- a
principle threaded through hypotheses is an axiom wearing different clothes,
invisible to `#print axioms` because a conditional theorem is unconditionally
provable. This tool sweeps every Phase 2 declaration signature for the names
registered in `tools/hypotheses.json` and reports, per hypothesis, what
assumes it (binder position) and what concludes in it -- the work-list an
agent discharging hypotheses starts from.

    python3 tools/hypotheses.py            # the inventory
    python3 tools/hypotheses.py --check    # CI: a registered name that no
                                           # longer occurs is stale, an
                                           # entry without a discharge note
                                           # is unadjudicated, and the
                                           # calibration budget must be met
                                           # exactly

Calibration pins each hypothesis to its strength. An entry may carry a
`calibration` block -- `shape` (omniscience / choice / modulus / subject),
`principle` (a lattice node, or `none` for a genuinely new strength),
`forward` (a theorem deriving the hypothesis from the principle), `reverse`
(a theorem recovering the principle from the hypothesis schema) -- with
`open` marking a direction still owed and `n/a` a direction that does not
apply (moduli are data, subject matter has no strength). The number of
entries still owing -- no block, or a direction `open` -- is `_uncalibrated`,
and the check demands exact equality: lowering it records progress, raising
it takes the same two edits as any ratchet.

It also lists, as a NOTE, `Prop`-valued definitions that appear in other
declarations' binders but are not registered -- the discovery mechanism, so
a new principle cannot circulate quietly.
"""

import argparse
import collections
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import lean  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "tools" / "hypotheses.json"
def word(name):
    return re.compile(r"\b" + re.escape(name) + r"\b")


def sweep():
    """Per registered name: (assumes, concludes) lists of (file, decl)."""
    reg = {k: v for k, v in json.loads(REGISTRY.read_text()).items()
           if not k.startswith("_")}
    pats = {k: word(k.split(".")[-1]) for k in reg}
    hits = {k: ([], []) for k in reg}
    prop_defs = {}
    binder_text = []
    for path in sorted(lean.phase2_files(ROOT)):
        lines = lean.stripped_lines(path)
        for decl in lean.parse_file(path):
            bare = decl["name"]
            # one pass per file: slice from the declaration line instead of
            # re-reading the file per name, which was quadratic
            start = decl["line"] - 1
            m = re.search(r"\b" + re.escape(bare) + r"\b",
                          lines[start]) if start < len(lines) else None
            if m is None:
                continue
            rest = lines[start][m.end():] + "\n" \
                + "\n".join(lines[start + 1:start + 80])
            got = lean.split_signature(rest)
            if got is None:
                continue
            binder_list, conclusion, _ = got
            binders = " ".join(binder_list) \
                if isinstance(binder_list, list) else binder_list
            binder_text.append((path.name, bare, binders))
            # `split_signature` has ALREADY eaten the colon, so a pattern
            # requiring one can never match and `prop_defs` stayed empty on
            # every run this detector has ever had. Nothing noticed, because
            # an empty set and a set nothing was found for print the same
            # thing: no NOTE (FINDINGS 2192, again).
            # A PRINCIPLE IS A CLOSED PROP. `def LPO : Prop` takes no
            # parameters; `def Btw (a b c : Point) : Prop` is an ordinary
            # predicate and there are 141 of those, which as a NOTE would be
            # a wall of text nobody reads. Requiring no binders is what
            # separates a strength from a relation.
            if re.match(r"\s*:?\s*Prop\s*$", conclusion or "") \
                    and not (binder_list or []) \
                    and bare[:1].isupper():
                prop_defs.setdefault(bare, path.name)
            for k, pat in pats.items():
                if bare == k.split(".")[-1]:
                    continue
                if pat.search(binders or ""):
                    hits[k][0].append((path.name, bare))
                elif pat.search(conclusion or ""):
                    hits[k][1].append((path.name, bare))
    unregistered = []
    for pname, pfile in sorted(prop_defs.items()):
        if pname in pats or any(pname == k.split(".")[-1] for k in pats):
            continue
        pat = word(pname)
        n = sum(1 for _, b2, binders in binder_text
                if b2 != pname and pat.search(binders or ""))
        if n >= 1:
            unregistered.append((pname, pfile, n))
    return reg, hits, unregistered


# The five kinds `hypotheses.json`'s `_README` declares, and against which it
# says `kind` IS validated. It was not: the field was read in exactly one
# place -- an f-string that prints it -- and never compared, which is how four
# entries drifted to a fifth value nothing defined (FINDINGS 1033).
#
# **The README asserted the check in the past tense while the check did not
# exist.** A reader who verified the claim by reading the registry's own
# documentation found it stated as settled. Argument, mechanism and execution
# are three things (structures); here only the first was present.
KINDS = frozenset({"principle", "readout", "witness", "decider", "structural"})


def bad_kinds(reg):
    """Registered hypotheses whose `kind` is not one of the declared five.

    Returns (name, kind) pairs. An entry with NO `kind` is reported too: a
    missing field and an undeclared value are the same defect for a reader
    who trusts the enum.
    """
    out = []
    for name, v in reg.items():
        if name.startswith("_") or not isinstance(v, dict):
            continue
        k = v.get("kind")
        if k not in KINDS:
            out.append((name, k))
    return sorted(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    # THE FULL LIST, BECAUSE `--check` PRINTS SIX OF EIGHTEEN. That NOTE says
    # `e.g.` and gives a sample, which is right for a report a human reads and
    # useless to anything that wants to ACT on the population --- and criterion 1
    # of `ROADMAP-ACCOUNTING.md`'s end state is exactly about acting on it.
    #
    # It prints the same `unregistered` this file already computes rather than a
    # second derivation, because a caller reimplementing the sweep is how two
    # tools come to disagree about one tree. The filters that remove lattice
    # nodes and `classical.json`-priced entries run below and are applied here
    # too, so this and the NOTE always name the same set.
    ap.add_argument("--unregistered", action="store_true",
                    help="print every closed-Prop hypothesis that circulates "
                         "unregistered, one per line, for a tool to consume")
    args = ap.parse_args()
    reg, hits, unregistered = sweep()
    stale = [k for k, (a, c) in hits.items() if not a and not c]
    unadjudicated = [k for k, v in reg.items()
                     if not v.get("discharge", "").strip()]

    full = json.loads(REGISTRY.read_text())
    budget = full.get("_uncalibrated")
    nodes = set(json.loads(
        (ROOT / "tools" / "lattice.json").read_text())["nodes"]) | {"none"}
    # `relative` IS NOT A FIFTH KIND OF STRENGTH, it is the absence of a
    # single one. A hypothesis carrying a PROMISE about its argument has a
    # strength that varies with the argument, so `principle`, `forward` and
    # `reverse` cannot apply --- and writing `n/a` in all three without saying
    # WHY is the unexplained-n/a that three entries were corrected for on
    # 2026-08-31.
    #
    # `HalveDecider` is the case: `not_halveDecider_forall` refutes the
    # universal form and `sqrtTwoDecider` builds an instance outright, so the
    # strength runs from FREE to FALSE. `Calibrate.lean`'s docstring predicted
    # the shape --- *its calibration must therefore be relative to a P, which
    # is a different kind of registry entry (FINDINGS 889)* --- and the entry
    # sat at `calibration: null` for want of it, counted as OWING, while both
    # ends stood proved in the tree.
    shapes = {"omniscience", "choice", "modulus", "subject", "relative"}
    decls = {d["name"]
             for path in sorted(lean.phase2_files(ROOT))
             for d in lean.parse_file(path)}
    bad_cal = []
    owing = []
    for k, v in reg.items():
        cal = v.get("calibration")
        if cal is None:
            owing.append(k)
            continue
        if cal.get("shape") not in shapes:
            bad_cal.append((k, f"shape {cal.get('shape')!r} not in "
                            f"{sorted(shapes)}"))
        if cal.get("principle") not in nodes:
            bad_cal.append((k, f"principle {cal.get('principle')!r} is not a "
                            "lattice node"))
        open_dir = False
        for side in ("forward", "reverse"):
            w = cal.get(side)
            if w in ("open",):
                open_dir = True
            elif w in ("n/a",):
                pass
            elif isinstance(w, str) and w.split(".")[-1] in decls:
                pass
            else:
                bad_cal.append((k, f"{side} {w!r} is neither open, n/a, nor "
                                "a declaration"))
        # BOTH ENDS OF THE VARIATION, OR IT IS AN OPT-OUT. An entry claiming
        # its strength DEPENDS on its argument must exhibit the dependence;
        # otherwise `relative` is how a hypothesis leaves the register while
        # appearing to be in it.
        if cal.get("shape") == "relative":
            for side, what in (
                    ("refuted", "a theorem refuting the UNIVERSAL form"),
                    ("free_at", "an instance discharged outright")):
                w = cal.get(side)
                if not (isinstance(w, str) and w.split(".")[-1] in decls):
                    bad_cal.append((k, f"shape `relative` needs `{side}` -- "
                                       f"{what}; got {w!r}"))
        if open_dir:
            owing.append(k)
    if not args.check:
        print("=" * 74)
        print(f"HYPOTHESES  -- {len(reg)} registered; what the library assumes")
        print("=" * 74)
        for k in sorted(reg, key=lambda k: -len(hits[k][0])):
            a, c = hits[k]
            v = reg[k]
            print(f"\n  {k}  [{v['kind']}]  "
                  f"assumed by {len(a)}, concluded by {len(c)}")
            print(f"      {v['meaning']}")
            print(f"      discharge: {v['discharge']}")
            cal = v.get("calibration")
            if cal:
                print(f"      calibration: [{cal['shape']}] "
                      f"principle {cal['principle']}, "
                      f"forward {cal['forward']}, reverse {cal['reverse']}")
            files = sorted({f for f, _ in a})
            if files:
                print(f"      assumed in: {', '.join(files)}")
    if stale:
        print("=" * 74)
        print(f"FAIL -- {len(stale)} registered hypothesis(es) occur nowhere")
        print("=" * 74)
        for k in stale:
            print(f"  {k}")
        print()
        print("  The registry is a ratchet: remove the entry, or restore the")
        print("  name -- an entry nothing matches is a claim about nothing.")
        return 1
    if unadjudicated:
        print("=" * 74)
        print(f"FAIL -- {len(unadjudicated)} entries have no discharge note")
        print("=" * 74)
        for k in unadjudicated:
            print(f"  {k}")
        print()
        print("  Say what removing the hypothesis would take, or why it")
        print("  stays. An inventory without adjudications is a list.")
        return 1
    if bad_cal:
        print("=" * 74)
        print(f"FAIL -- {len(bad_cal)} malformed calibration(s)")
        print("=" * 74)
        for k, why in bad_cal:
            print(f"  {k}: {why}")
        print()
        print("  A calibration names a lattice node and two witnesses; a")
        print("  witness is a theorem, `open`, or `n/a`.")
        return 1
    if budget is None or len(owing) != budget:
        print("=" * 74)
        print(f"FAIL -- {len(owing)} entries owe calibration; "
              f"_uncalibrated says {budget}")
        print("=" * 74)
        for k in owing:
            print(f"  {k}")
        print()
        print("  Classify the entry (or prove a direction) and lower the")
        print("  budget, or record the growth on its own line -- raising it")
        print("  is two edits on purpose.")
        return 1
    if unregistered:
        # TWO REGISTRIES, and a principle adjudicated in the other one is not
        # unadjudicated. 15 of the first 29 this reported are LATTICE NODES
        # with a gloss and edges -- reporting them as unregistered overstates
        # the backlog by half and would have sent someone to write entries
        # that already exist elsewhere (2215).
        try:
            # FOLD THE KEYS, because the query side is folded two lines below.
            # `set(...["nodes"])` keeps the registry's own spelling, and
            # `'FANΔ'.lower()` is `'fanδ'` while the key is `'fanΔ'` --- the one
            # node of 86 whose key is not its own lowercase. Comparing a folded
            # name against unfolded keys reported it as UNREGISTERED, which is
            # the same character that produced two contradictory counts across
            # two tracks on 2026-08-28 and a third report in `lattice.py`.
            nodes = {k.lower() for k in json.loads(
                (ROOT / "tools" / "lattice.json").read_text())["nodes"]}
        except (OSError, ValueError, KeyError):
            nodes = None
        if nodes is None:
            print("NOTE: tools/lattice.json is unreadable, so it cannot be "
                  "told which of these\n      are adjudicated there. UNREAD, "
                  "not absent.")
        else:
            placed = [n for n, _, _ in unregistered if n.lower() in nodes]
            unregistered = [x for x in unregistered if x[0].lower() not in nodes]
            if placed:
                print(f"NOTE: {len(placed)} closed-Prop hypotheses are absent "
                      f"from hypotheses.json but ARE\n      lattice nodes "
                      f"({', '.join(placed[:5])}...), so they are adjudicated "
                      f"in the\n      other registry rather than "
                      f"unadjudicated.")
    if unregistered:
        # THREE registries, not two. `_equivalences` prices a statement that no
        # declaration's audit line can reach, which is exactly the shape of a
        # hypothesis, so it is where the sharpest of these live -- five of the
        # thirteen this reported are there, each with a named reversal.
        # AND `_unplaced` IS THE FOURTH, which this missed. A principle
        # adjudicated as UNPLACEABLE --- proved outright, or with an edge whose
        # witness carries an extra hypothesis that is not itself a principle ---
        # has been ruled on deliberately, with a note saying what would close
        # it. Reporting it as *circulating unregistered* asks a reader to
        # adjudicate what is already adjudicated, and the only way to satisfy
        # the report would be to give it a lattice node, which for a PROVED
        # statement is the error `_unplaced` exists to prevent.
        #
        # Measured 2026-08-31: `SplitDecision` appeared in this list while
        # sitting in `_unplaced` with a note recording that `splitDecision`
        # proves it unconditionally. Same defect as `hypaudit.py`'s, fixed there
        # an hour earlier and not looked for here.
        try:
            cls = json.loads((ROOT / "tools" / "classical.json").read_text())
            priced = {
                e["statement"].split(".")[-1].lower()
                for e in cls["_equivalences"]
                if isinstance(e, dict) and "statement" in e}
            priced |= {
                e["principle"].split(".")[-1].lower()
                for e in (cls.get("_unplaced") or [])
                if isinstance(e, dict) and e.get("principle")}
        except (OSError, ValueError, KeyError):
            priced = None
        if priced is None:
            print("NOTE: tools/classical.json is unreadable, so it cannot be "
                  "told which of these\n      are priced there. UNREAD, not "
                  "absent.")
        else:
            equiv = [n for n, _, _ in unregistered if n.lower() in priced]
            unregistered = [x for x in unregistered if x[0].lower() not in priced]
            if equiv:
                print(f"NOTE: {len(equiv)} closed-Prop hypotheses are absent "
                      f"from hypotheses.json but ARE\n      priced in "
                      f"classical.json's `_equivalences` "
                      f"({', '.join(equiv[:5])}), so they carry a\n      "
                      f"principle and a reversal already.")
    if args.unregistered:
        # AFTER both filters above, so this names what the NOTE names.
        for n, f, c in sorted(unregistered):
            print(f"{n}\t{f}\t{c}")
        return 0
    if unregistered:
        names = ", ".join(f"{n} ({f})" for n, f, c in unregistered[:6])
        # The COUNT, not just a sample. Six names with no total reads as six
        # cases; it was twenty-nine (FINDINGS 2195 -- a count without its
        # ceiling is a numerator).
        print(f"NOTE: {len(unregistered)} closed-Prop hypotheses circulate "
              f"unregistered, e.g. {names}."
              f"\n      `_uncalibrated` counts only what the registry holds, "
              f"so it cannot see these.")
    # The one measurement of what a hypothesis COSTS. Reversals price axioms
    # and the costmap prices encodings, and both are cheap because the second
    # artefact is free -- a reversal is a theorem worth having, the second
    # encoding already exists. For a hypothesis the second route is never
    # free, so it is never sought; it only ever arrives when an item is
    # superseded mid-build. Reported so the practice stays visible, and so
    # the count is a fact rather than an impression (2205).
    routes = ROOT / "tools" / "routes.json"
    try:
        priced = len(json.loads(routes.read_text())["entries"])
    except (OSError, ValueError, KeyError):
        priced = None
    if priced is None:
        print("NOTE: tools/routes.json is unreadable, so no hypothesis is "
              "known to be priced.\n      That is UNREAD, not zero.")
    elif priced < 2:
        print(f"NOTE: {priced} hypothesis is priced by a second route. "
              f"Hypotheses in this\n      library are otherwise UNPRICED -- "
              f"`DC`, the readouts and the located\n      families each rest "
              f"on exactly one proof, and an overpriced result looks\n"
              f"      exactly like a correctly priced one. Record a "
              f"supersession in\n      tools/routes.json when the HYPOTHESIS "
              f"SET changes; a tidier proof from\n      the same inputs is "
              f"not one.")
    # THREE NUMBERS, because one was doing work it could not support.
    # `_uncalibrated` counts entries with an `open` direction and reads 2,
    # which invites "34 are pinned down". They are not: only TWO of 36 are
    # clean equivalences. Six are two-way, and four of those have forwards
    # spending BinaryDC and DC on top of LLPO -- a BOUND, not an equivalence,
    # and the entries say so while the number cannot (2221).
    def _real(x):
        return x not in ("n/a", "open", None)

    equiv, bound, unmeasured = 0, 0, 0
    # THE N/A GROUP IS NOT ONE CONDITION, and reporting it as one number told a
    # different story than `undischarged.py`, which selects the same population
    # and then splits it by the adjudicated `verdict`. Two instruments
    # disagreeing about one tree is how a debt gets argued about instead of
    # paid, so the split is reported HERE too.
    verdicts = collections.Counter()
    for _k, _v in reg.items():
        _c = (_v or {}).get("calibration") or {}
        _f, _r = _c.get("forward"), _c.get("reverse")
        if _real(_f) and _real(_r):
            # multi-premise forwards are counted as bounds by the entry's own
            # `discharge` prose, which is where the extra premises are named
            if "spend" in (_v.get("discharge") or "") or \
                    "with BinaryDC" in (_v.get("discharge") or ""):
                bound += 1
            else:
                equiv += 1
        elif _real(_f) or _real(_r):
            bound += 1
        else:
            unmeasured += 1
            verdicts[(_v or {}).get("verdict") or "UNVERDICTED"] += 1
    print(f"NOTE: of {len(reg)} hypotheses, {equiv} are two-way equivalences, "
          f"{bound} are ONE-WAY\n      BOUNDS, and {unmeasured} have neither "
          f"direction proved. `_uncalibrated` counts\n      only entries "
          f"with an `open` direction, so it cannot see the difference "
          f"between\n      *equivalent to LLPO* and *implied by LLPO plus two "
          f"other principles*.")
    print(f"      Of those {unmeasured}: "
          + ", ".join(f"{n} {v}" for v, n in sorted(verdicts.items()))
          + ".\n      Only `open` is debt -- `never` is the measuring stick, "
            "the subject\n      matter, and the universe gap of FINDINGS 28. "
            "`undischarged.py`\n      ratchets the `open` set and refuses an "
            "UNVERDICTED entry.")
    # A FIELD SAYING `n/a` WHILE THE ENTRY'S OWN PROSE SAYS THE DIRECTION IS
    # OWED. `n/a` means *the question does not arise*; `open` means *owed*, and
    # `_uncalibrated` counts only the latter --- so an owed direction spelled
    # `n/a` is invisible to the budget that exists to track it.
    #
    # Found by hand on `MonotoneConvergence` 2026-08-31, whose discharge read
    # *open: the reverse is proved, the forward direction is not* beside
    # `forward: "n/a"`. Two more wore the same spelling that day:
    # `OuterApproached`, where the forward was one `Or.elim`, and the four
    # lattice-node entries whose placement the GRAPH already held. `n/a` is the
    # value that looks like a default and is a claim.
    #
    # DELIBERATELY NARROW: it fires only when the prose NAMES the direction
    # alongside an openness word, because a discharge may say `open` about
    # something else entirely and a check that guessed would be ignored.
    disagree = []
    for _k, _v in reg.items():
        _c = (_v or {}).get("calibration") or {}
        _d = (_v or {}).get("discharge") or ""
        low = _d.lower()
        for _dir in ("forward", "reverse"):
            if _c.get(_dir) != "n/a":
                continue
            if _dir not in low:
                continue
            near = low[max(0, low.find(_dir) - 60):low.find(_dir) + 80]
            # AN ENTRY EXPLAINING WHY `n/a` IS CORRECT MUST NOT FIRE. `DC`
            # says a forward deriving it from itself *is not a thing to
            # write* --- a justification, matched by a rule hunting for
            # `forward` beside a negation. A check that names the entry
            # explaining itself trains its reader to dismiss it, and the true
            # positive goes out with the false one.
            if any(w in near for w in ("not a thing to write", "by construction",
                                       "vacuous", "from itself", "does not "
                                       "arise", "itself is not")):
                continue
            if any(w in near for w in ("open", "not proved", "is not",
                                       "unproved", "owed", "nobody")):
                disagree.append((_k, _dir))
    if disagree:
        print("NOTE: %d entr(y/ies) say `n/a` in a field their own discharge\n"
              "      calls OPEN. `n/a` is *does not arise*; `open` is *owed*,\n"
              "      and `_uncalibrated` counts only the second:"
              % len(disagree))
        for _k, _dir in disagree:
            print("        %-28s %s" % (_k, _dir))

    if args.check:
        bad = bad_kinds(full)
        if bad:
            print('=' * 74)
            print(f'KIND -- {len(bad)} entr(y/ies) with an undeclared kind')
            print('=' * 74)
            for name, k in bad:
                print(f'  {name}  kind={k!r}')
            print('\n  `_README` declares exactly five: '
                  + ', '.join(sorted(KINDS)) + '.')
            print('  Use one, or extend the enum in `_README` AND here --')
            print('  the registry says kind is validated, so it must be.')
            return 1

        print(f"  OK -- {len(reg)} hypotheses adjudicated, none stale, "
              f"{len(owing)} owing calibration (budget met)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
