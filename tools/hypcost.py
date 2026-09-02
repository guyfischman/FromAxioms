#!/usr/bin/env python3
"""Where each principle is SPENT, as opposed to merely carried.

A principle taken as a hypothesis never reaches a `#print axioms` line, so the
axiom surface cannot see the project's own preferred technique.  This reports,
per principle, the declarations that USE their hypothesis rather than passing it
to another declaration that takes one -- the ROOT SET.

The root set is the object.  A count of declarations mentioning a principle is
not: three instruments gave 40, 47 and 57 for `FAN` and none of them counted
uses.
"""

import argparse
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
# WHAT IT CANNOT SEE, stated because the root set reads as exhaustive and is
# not: it matches an EXPLICIT binder `(h : FAN)`. An implicit `{h : FAN}`, an
# instance binder, or a principle reached through a structure field is invisible.
# On this tree that currently costs nothing -- every principle is an explicit
# binder -- but "currently" is the whole reason to write it down.
#
# AND ONE ENTRY WAS MISSING FROM THAT LIST WHILE COSTING 31 ROOTS. A binder
# spelled with a NAMESPACE PREFIX -- `(hdc : Constructive.DCOn.{u} ...)` --
# matched nothing, so a principle read as spent in the files that happen to
# write it bare and nowhere else. Fixed in `scan()`; recorded here because the
# defect was not that the list was wrong but that it was SHORT, and a reader
# checking whether their case is covered gets a definite "not listed" either
# way. 13 principles gained roots, `EM`, `ApartStable` and `FANstable` among
# them, so this was never one principle's problem.
#
# A DECLARATION IS ATTRIBUTED TO ONE PRINCIPLE: `binder.search` takes the FIRST
# match in the signature. `triadicPlacement_of_locatorMap_of_em` takes both
# `HasLocatorMap` and `EM` and is reported under whichever is written first.
# Pre-existing and unchanged here, but the prefix fix can MOVE such a
# declaration between principles by making an earlier binder visible, which is
# what it did to that one. A root leaving a principle is therefore not
# automatically a shrink -- check the other principles and the forwarders
# before reading it as one.
#
# WHAT THIS TOOL STILL CANNOT ANSWER, and the distinction cost `reversal` a
# measurement: a principle that is NOT A LATTICE NODE is not in the alternation
# at all, so it is reported NOWHERE rather than incompletely. `DCOn` is that
# case today. Silence here means "not a registered principle" as readily as it
# means "never spent", and only `lattice.json` separates the two.

# PRIVATE INCLUDED, DELIBERATELY, and the opposite of `compare.py`'s default.
# That tool excludes private because a private lemma is not part of what the
# library OFFERS -- a claim about the SURFACE. This one asks where a principle is
# SPENT, and a private consumer spends it exactly as a public one does. Omitting
# them does not merely miss roots: a public declaration forwarding to a private
# taker is reported as a ROOT, which is a false positive, and analysis measured
# the totals agreeing while four entries were wrong in two directions.
import lean  # noqa: E402  -- the shared parser; a fresh regex reads a docstring
              # line beginning "theorem at all: ..." as a declaration named `at`


def principles(root):
    """Names of the lattice's nodes that are actually declared as `def`s.

    **CASEFOLD ON BOTH SIDES.** This compared `decl.lower()` against the RAW
    keys, which works for every node whose key is already lowercase and fails
    for the one that is not: `fanΔ`. `'FANΔ'.lower()` is `'fanδ'`, because
    Python maps the Greek capital delta to a small delta the registry does not
    use, so `def FANΔ` at Omniscience.lean:483 was never recognised as a
    principle definition. It is the ONLY node in the lattice whose key differs
    from its own lowercase, checked across all 86, so the loss was exactly one
    node and it was silent.

    Reported by `reversal`, who hit the identical transform in a five-line
    lookup of their own the same day: *`x.lower() in set` reads as a comparison
    and is a lossy transform*. The rule this tree already had -- hand-rolled
    parsers drift -- is filed under PARSERS, and this is not a parser.
    """
    nodes = {n.casefold() for n in
             json.load(open(root / "tools" / "lattice.json"))["nodes"]}
    found = {}
    for path in sorted(lean.phase2_files(root)):
        for decl in lean.parse_file(path, include_private=True):
            if decl["kind"] == "def" and decl["name"].casefold() in nodes:
                found[decl["name"]] = decl["file"]
    return found


def spans(path):
    """(decl, signature, body) for each declaration, signature = text up to `:=`."""
    text = path.read_text(encoding="utf-8", errors="replace").split("\n")
    decls = lean.parse_file(path, include_private=True)
    for i, decl in enumerate(decls):
        start = decl["line"] - 1
        end = decls[i + 1]["line"] - 1 if i + 1 < len(decls) else len(text)
        body = "\n".join(text[start:end])
        yield decl, body.split(":=")[0], body


def scan(root):
    princ = principles(root)
    if not princ:
        return {}, {}
    alt = "|".join(sorted(map(re.escape, princ), key=len, reverse=True))
    # A NAMESPACE PREFIX IS PART OF THE SPELLING, NOT PART OF THE NAME.
    # `(hdc : Constructive.DCOn.{u} (baireStateOn X))` was INVISIBLE while the
    # bare `(hdc : DCOn.{u} ...)` twenty lines up matched, so one principle read
    # as spent in half the places it is spent -- and the tool's own list of what
    # it cannot see did not mention it. `(?:\w+\.)*` cannot widen the match to a
    # different name: the prefix must end in a dot, so `(h : XFAN)` still fails
    # exactly as before, and the principle must still be a whole component.
    #
    # THE APPLICATION FORM WAS NEVER THE PROBLEM, and this comment records that
    # because a correct-sounding diagnosis was already acted on once. `reversal`
    # reported that a binder type which is an APPLICATION rather than a name is
    # invisible here; measured, all three of `(h : DCOn)`, `(h : DCOn.{u} s)`
    # and `(h : DCOn.{u} (f X))` match, because `\b` closes the name before the
    # dot. The silence they saw had a different cause -- see `principles()`.
    binder = re.compile(r"\(\s*(\w+)\s*:\s*(?:\w+\.)*(" + alt + r")\b")

    # pass 1: who TAKES a principle, and under which binder name
    takers = {}
    for path in sorted(lean.phase2_files(root)):
        for decl, sig, body in spans(path):
            m = binder.search(sig)
            if m:
                takers[decl["name"]] = (decl, m.group(1), m.group(2), body)

    # pass 2: a taker FORWARDS if it applies its binder to another taker
    roots, forwarders = {}, {}
    for name, (decl, var, principle, body) in takers.items():
        # `foo hfan` and `foo.{u} hfan` both count as an application
        applied = set(re.findall(r"\b(\w+)(?:\.\{[^}]*\})?\s+" + re.escape(var) + r"\b", body))
        applied.discard(name)
        if applied & set(takers):
            forwarders.setdefault(principle, []).append(name)
        else:
            # repo-relative: `lean.py` reports the path it was handed, and an
            # absolute one is unquotable in a finding and differs per seat.
            rel = pathlib.Path(decl["file"])
            try:
                rel = rel.relative_to(root)
            except ValueError:
                pass
            roots.setdefault(principle, []).append((str(rel), decl["line"], name))
    return roots, forwarders


RECORD = pathlib.Path(__file__).resolve().parent / "hypcost.json"


def _rootkey(roots):
    """The recorded shape: principle -> sorted `file::decl`, NO LINE NUMBERS.

    A line-keyed record re-fires on every edit ABOVE a declaration, which is
    ordinary growth -- so the check would report a new root whenever anything
    moved, and a check that fires on the normal case gets ignored. The same
    reason `citeline.py` exists and CLAUDE.md's rule to cite by NAME.
    """
    return {p: sorted(f"{f}::{n}" for f, _ln, n in rows)
            for p, rows in roots.items()}


def compare(roots, recorded):
    """New roots, and recorded roots that have gone.

    A NEW ROOT is the event nothing else reports: a principle spent where it
    was not spent before moves no audit line, trips no ratchet and touches no
    allow list, because a hypothesis-carried principle never reaches a
    `#print axioms` line at all. That silence is the whole reason this tool
    exists, so the new root is the FAILURE and the vanished one is a NOTE --
    spending a principle in one fewer place needs no permission.
    """
    now = _rootkey(roots)
    added, gone = {}, {}
    for pr, keys in now.items():
        was = set(recorded.get(pr, []))
        new = [k for k in keys if k not in was]
        if new:
            added[pr] = new
    for pr, keys in recorded.items():
        missing = [k for k in keys if k not in set(now.get(pr, []))]
        if missing:
            gone[pr] = missing
    return added, gone


def main():
    ap = argparse.ArgumentParser(
        description="Where each principle is SPENT, not merely carried.")
    ap.add_argument("--record", action="store_true",
                    help="write the current root set as the baseline")
    ap.add_argument("--check", action="store_true",
                    help="exit non-zero on a root that is not in the baseline")
    args = ap.parse_args()
    root = pathlib.Path(__file__).resolve().parent.parent
    roots, forwarders = scan(root)

    if args.record:
        RECORD.write_text(json.dumps(_rootkey(roots), indent=1,
                                     ensure_ascii=False, sort_keys=True) + "\n")
        print(f"recorded the root set for {len(roots)} principle(s)")
        return 0

    if args.check:
        if not RECORD.exists():
            print("REFUSING -- no baseline; write one with "
                  "`python3 tools/hypcost.py --record`.\n"
                  "  A check with nothing to compare against reports clean and "
                  "means nothing.")
            return 2
        recorded = json.loads(RECORD.read_text())
        added, gone = compare(roots, recorded)
        if gone:
            print(f"NOTE: {sum(len(v) for v in gone.values())} recorded root(s) "
                  f"are no longer spent there.\n"
                  f"      Spending a principle in fewer places needs no "
                  f"permission; re-record when settled.")
            for pr, ks in sorted(gone.items()):
                for k in ks:
                    print(f"        {pr}  {k}")
        if added:
            print(f"FAIL -- {sum(len(v) for v in added.values())} NEW root(s): a "
                  f"principle is now SPENT where it was not before.")
            for pr, ks in sorted(added.items()):
                for k in ks:
                    print(f"    {pr}  {k}")
            print("\n  This moves no audit line and trips no ratchet, because a\n"
                  "  hypothesis-carried principle never reaches `#print axioms`.\n"
                  "  Read whether the new site should spend it, then\n"
                  "  `python3 tools/hypcost.py --record`.")
            return 1
        if not gone:
            print("OK -- every principle is spent where it was recorded.")
        return 0

    total = 0
    for principle in sorted(roots):
        rows = sorted(roots[principle])
        total += len(rows)
        print("%s -- spent in %d place(s)" % (principle, len(rows)))
        for f, line, name in rows:
            print("    %s:%d  %s" % (f, line, name))
        carried = len(forwarders.get(principle, []))
        if carried:
            print("    (%d further declaration(s) carry it without using it)"
                  % carried)
        print()
    print("%d root(s) across %d principle(s)" % (total, len(roots)))
    # THE EXTENT, in the OUTPUT rather than a docstring, because a comment is
    # not saying (extent.py's own rule, narrowed after a match anywhere in the
    # source granted the tier to a tool that named no extent at all).
    print("  population: the declarations of THIS TREE. A peer branch may spend")
    print("  a principle in a file that has not merged, so a root set is a")
    print("  LOWER BOUND that a merge can only raise;")
    print("  and `spent in 2 places` is a claim about this checkout, not the")
    print("  library. Re-run after a batch merge before quoting one.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
