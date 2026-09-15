#!/usr/bin/env python3
"""No Mathlib under `FromAxioms/`, and no `comparator/` either --- checked.

THE CLAIM THIS EXISTS TO MAKE CHECKABLE. `README.md` says the tower is built on
Lean core with no Mathlib. Once `comparator/` imports Mathlib --- to STATE the
theorems parity is measured against --- that sentence stops being true in letter
unless it is qualified, and a qualified sentence nobody checks is exactly the
kind of assertion this project exists to replace. So:

    no file reachable from `FromAxioms/` imports Mathlib or Batteries
    no file reachable from `FromAxioms.lean` imports `comparator/`

The second is the direction check. Without it the dependence could silently
reverse --- a `FromAxioms/` file citing something under `comparator/` would make
the tower depend on Mathlib transitively while every direct import still looked
clean.

WHY IMPORTING MATHLIB TO CHECK A CLAIM IS THE OPPOSITE OF IMPORTING IT TO MAKE
ONE. A `comparator/` pair states mathlib's theorem in MATHLIB's own vocabulary
and discharges it from ours. Mathlib appears there as the thing being matched,
never as a step in a proof: the `challenge.lean` half imports it to write the
statement, and the `solution.lean` half closes that statement using only this
tree. Nothing in `FromAxioms/` can see either file, which is what this gate
enforces and what makes the README's distinction a fact.

TESTED ON COMMENT-STRIPPED SOURCE. A docstring naming Mathlib is prose, not an
import --- this file's own header would trip a naive grep, and so would every
parity docstring that says what mathlib's version assumes. Skipping that
distinction treats a docstring line reading `instance costs**` as a command.
`lean.strip_comments` is the shared answer and is used here.
"""
import argparse
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import lean  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "FromAxioms"
TOWER_ROOT = ROOT / "FromAxioms.lean"

# An import line, after comments are stripped. Lean writes `import A.B.C`, one
# module per line; the leading anchor is what keeps a mid-line occurrence in a
# `#eval` string or a wide term from counting.
IMPORT = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_.']*)")

# The two forbidden roots under `FromAxioms/`, plus the comparator directory
# whose direction is checked separately.
FOREIGN = ("Mathlib", "Batteries", "Std")
COMPARATOR = "Comparator"


def imports_of(path):
    """Every module this file imports, read from COMMENT-STRIPPED source."""
    raw = path.read_text(errors="replace").split("\n")
    code = lean.strip_comments(raw)
    out = []
    for n, line in enumerate(code, 1):
        m = IMPORT.match(line)
        if m:
            out.append((n, m.group(1)))
    return out


def check():
    if not SRC.is_dir():
        print("nomathlib: FAIL -- no FromAxioms/ directory to check")
        return 1

    files = sorted(SRC.rglob("*.lean"))
    if not files:
        print("nomathlib: FAIL -- FromAxioms/ holds no .lean files, so a clean "
              "result would mean nothing")
        return 1

    bad = []
    for path in files:
        rel = path.relative_to(ROOT)
        for n, mod in imports_of(path):
            root = mod.split(".")[0]
            if root in FOREIGN:
                bad.append((f"{rel}:{n}", f"imports {mod}"))
            elif root == COMPARATOR:
                bad.append((f"{rel}:{n}",
                            f"imports {mod} -- the tower must not depend on "
                            "the comparators"))

    # THE DIRECTION CHECK, stated over the ROOT rather than over every file:
    # `FromAxioms.lean` is the tower's own entry point, so a comparator
    # reachable from it is a comparator the whole tower depends on.
    if TOWER_ROOT.is_file():
        for n, mod in imports_of(TOWER_ROOT):
            if mod.split(".")[0] == COMPARATOR:
                bad.append((f"FromAxioms.lean:{n}",
                            f"imports {mod} -- direction reversed"))

    print("=" * 72)
    print("NOMATHLIB  -- no Mathlib, Batteries or comparator under FromAxioms/")
    print("=" * 72)
    print(f"  {len(files)} file(s) read, comments stripped before matching")

    if bad:
        print(f"\n  FAIL -- {len(bad)} forbidden import(s):")
        for where, why in bad:
            print(f"    {where:52s} {why}")
        print("\n  Mathlib belongs under `comparator/` ONLY, where it states the"
              " theorem being")
        print("  matched. A proof step that needs it is a proof this tree has "
              "not made.")
        return 1

    print("\n  OK -- nothing under FromAxioms/ imports Mathlib, Batteries or a "
          "comparator.")
    print("  The README's claim is a checked fact, not a promise.")
    return 0


def selftest():
    """Prove the checker can FAIL, since a gate that cannot is not a gate.

    The population is real files, so a clean run is consistent with a matcher
    that never matches --- the failure this repository keeps meeting, where
    `0 occurrences` reads as a result. These two cases are the positive
    controls.
    """
    ok = True

    seen = imports_of.__wrapped__ if hasattr(imports_of, "__wrapped__") else None
    del seen

    # a real import is caught
    probe = ["import Mathlib.Analysis.SpecialFunctions.Basic", "theorem t : True := trivial"]
    hits = [m.group(1) for m in (IMPORT.match(l) for l in lean.strip_comments(probe)) if m]
    if hits != ["Mathlib.Analysis.SpecialFunctions.Basic"]:
        print("  SELFTEST FAIL -- a real import was not matched:", hits)
        ok = False

    # a docstring naming Mathlib is NOT an import
    probe = ["/-- mathlib states this as `import Mathlib.Order.Basic`, and we",
             "do not. -/", "theorem t : True := trivial"]
    hits = [m.group(1) for m in (IMPORT.match(l) for l in lean.strip_comments(probe)) if m]
    if hits:
        print("  SELFTEST FAIL -- prose naming an import was counted:", hits)
        ok = False

    # a line comment naming one is not either
    probe = ["-- import Mathlib.Tactic", "theorem t : True := trivial"]
    hits = [m.group(1) for m in (IMPORT.match(l) for l in lean.strip_comments(probe)) if m]
    if hits:
        print("  SELFTEST FAIL -- a commented import was counted:", hits)
        ok = False

    print("  SELFTEST OK -- matcher fires on an import and not on prose"
          if ok else "  SELFTEST FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--selftest", action="store_true",
                    help="show the matcher firing and not firing")
    args = ap.parse_args()
    if args.selftest:
        sys.exit(selftest())
    sys.exit(check())
