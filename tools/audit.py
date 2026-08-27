#!/usr/bin/env python3
"""Ask the kernel what every declaration costs, and hold the answer to a floor.

    python3 tools/audit.py             the table
    python3 tools/audit.py --markdown  regenerate AXIOMS.md
    python3 tools/audit.py --check     CI: fail on an unregistered classical result

A hand-written `#print axioms` line documents one declaration and is only ever
written for the ones somebody remembered. This generates a line for every
declaration in the tree instead, so a result that is classical and unnoticed
cannot hide in the gap between what was proved and what was annotated.

Anything reaching `Classical.choice`, or the `em` and `choice` declared in
`FromAxioms/Logic/`, needs an entry in `tools/classical.json` giving the
reason. The build fails until it has one. Everything else is reported and not
gated.

Two failure modes are guarded explicitly, because both report a CLEAN TREE
while measuring nothing:

  * An empty sweep. "No classical results" and "no results examined" are the
    same output. A directory that matches no files is a failure, not a pass.
  * A chunk that dies. A probe file that fails contributes its error text
    instead of its audit lines, and its declarations simply vanish. So the
    check is on the return code AND on name coverage: every declaration
    submitted must come back with a verdict.
"""

import argparse
import concurrent.futures
import json
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import lean  # noqa: E402

# `Logic` is swept on its own against its own root, because it is `prelude`: it
# declares `And`, `Or` and `Eq` at top level and cannot be imported beside
# anything built on `Init`. Every other area is swept together against
# `FromAxioms`, which imports all of them.
PRELUDE = "Logic"
REGISTRY = ROOT / "tools" / "classical.json"
AXIOMS_MD = ROOT / "AXIOMS.md"
CHUNK = 400

# What counts as a cost needing a justification. `propext` and `Quot.sound` are
# Lean core's quotient and proposition-extensionality axioms; they are ambient
# here and not what this file watches for.
GATED = {"Classical.choice", "em", "choice"}

# Non-greedy, because a primed name puts a quote INSIDE the quotes: Lean prints
# `'contrapose'' depends on ...`, and a `[^']+` class stops at the first inner
# quote and silently reports `contrapose`, a name that does not exist. Eight
# declarations went missing that way and the coverage guard caught them.
LINE = re.compile(r"'(.+?)' (?:depends on axioms: \[([^\]]*)\]"
                  r"|does not depend on any axioms)")


def phases():
    """`[(label, root module, is_prelude, [directories])]`, discovered.

    The area directories are found rather than listed, so a new one joins the
    sweep the moment its first file lands. A hardcoded list is the failure this
    guards against: an area nobody added would go unaudited and the run would
    report clean.
    """
    base = ROOT / "FromAxioms"
    dirs = sorted(d.name for d in base.iterdir()
                  if d.is_dir() and d.name != PRELUDE and any(d.glob("*.lean")))
    out = []
    if (base / PRELUDE).is_dir():
        out.append((PRELUDE, f"FromAxioms.{PRELUDE}", True, [PRELUDE]))
    if dirs:
        out.append(("FromAxioms", "FromAxioms", False, dirs))
    if not out:
        print("FAIL: no area directory under FromAxioms/ holds a .lean file.")
        raise SystemExit(1)
    return out


def declarations():
    """`{label: [full names]}`, refusing any area that matched nothing."""
    out = {}
    for label, _root, _prelude, dirs in phases():
        names = []
        for sub in dirs:
            subdir = ROOT / "FromAxioms" / sub
            found = sorted(subdir.glob("*.lean"))
            if not found:
                deeper = list(subdir.rglob("*.lean")) if subdir.exists() else []
                print(f"FAIL: FromAxioms/{sub}/*.lean matched no files.")
                if deeper:
                    print(f"  {len(deeper)} .lean file(s) exist deeper; the "
                          f"glob is one level and needs widening.")
                print("  An empty sweep audits nothing and would otherwise "
                      "pass.")
                raise SystemExit(1)
            for path in found:
                # PUBLIC declarations only. A private one cannot be named from
                # outside its module, so `#print axioms ZFSet.nat_cancel` is an
                # unknown constant and the whole probe chunk fails -- taking
                # every declaration in that chunk out of the sweep with it.
                #
                # Nothing goes unmeasured by this. `#print axioms` walks the
                # dependency closure regardless of privacy, so a private
                # declaration's cost surfaces in whatever public declaration
                # uses it. One that nothing uses is dead code, and its cost is
                # not a fact about the library.
                names += [d["full"] for d in lean.parse_file(path)]
        out[label] = sorted(set(names))
    return out


def sweep(names_by_phase):
    """Run `#print axioms` over every declaration. Returns `{name: [axioms]}`."""
    env = dict(os.environ)
    env["PATH"] = f"{pathlib.Path.home()}/.elan/bin:" + env.get("PATH", "")
    scratch = ROOT / ".audit"
    scratch.mkdir(exist_ok=True)

    jobs, submitted = [], []
    for label, root_mod, is_prelude, _dirs in phases():
        names = names_by_phase[label]
        submitted += names
        header = ("prelude\n" if is_prelude else "") + f"import {root_mod}\n"
        for i in range(0, len(names), CHUNK):
            body = header + "".join(f"#print axioms {n}\n"
                                    for n in names[i:i + CHUNK])
            f = scratch / f"Sweep{label}{i // CHUNK}.lean"
            f.write_text(body)
            jobs.append(f)

    failures = []

    def run(f):
        r = subprocess.run(["lake", "env", "lean", str(f)], cwd=ROOT, env=env,
                           capture_output=True, text=True, timeout=1800)
        if r.returncode != 0:
            failures.append((f.name, r.returncode, r.stderr[-400:]))
        return r.stdout + r.stderr

    with concurrent.futures.ThreadPoolExecutor(
            max_workers=min(8, os.cpu_count() or 2)) as pool:
        out = "".join(pool.map(run, jobs))

    if failures:
        print(f"FAIL: {len(failures)} probe chunk(s) did not compile; their "
              f"declarations are absent from the sweep, not clean.")
        for name, code, err in failures[:3]:
            print(f"  {name} exited {code}: {err.strip()[:200]}")
        raise SystemExit(1)

    found = {}
    for m in LINE.finditer(out):
        axioms = [a.strip() for a in (m.group(2) or "").split(",") if a.strip()]
        found[m.group(1)] = axioms

    missing = [n for n in submitted if n not in found]
    if missing:
        print(f"FAIL: {len(missing)} declaration(s) submitted but not reported")
        for n in missing[:8]:
            print(f"  {n}")
        raise SystemExit(1)
    return found


def gated(found):
    """`{name: [axioms]}` for results that need a registered justification."""
    return {n: ax for n, ax in found.items() if set(ax) & GATED}


def registry():
    if not REGISTRY.exists():
        return {}
    return {k: v for k, v in json.loads(REGISTRY.read_text()).items()
            if not k.startswith("_")}


def markdown(found, reg):
    tally = {}
    for ax in found.values():
        key = ", ".join(ax) or "none"
        tally[key] = tally.get(key, 0) + 1
    out = ["# Axioms",
           "",
           "<!-- generated by `python3 tools/audit.py --markdown`; "
           "do not edit -->",
           "",
           f"Every one of the {len(found)} declarations in the library, asked "
           "what it depends on.",
           "",
           "| axioms | declarations |",
           "|---|---|"]
    for k, n in sorted(tally.items(), key=lambda kv: (-kv[1], kv[0])):
        out.append(f"| `{k}` | {n} |")
    g = gated(found)
    out += ["", f"## Registered costs ({len(g)})", ""]
    if not g:
        out.append("None. No declaration here reaches `Classical.choice`, "
                   "`em` or `choice`.")
    else:
        out += ["| declaration | axioms | why |", "|---|---|---|"]
        for n in sorted(g):
            out.append(f"| `{n}` | `{', '.join(g[n])}` | "
                       f"{reg.get(n, 'UNREGISTERED')} |")
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--markdown", action="store_true")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()

    found = sweep(declarations())
    reg, g = registry(), gated(found)

    tally = {}
    for ax in found.values():
        key = ", ".join(ax) or "none"
        tally[key] = tally.get(key, 0) + 1
    for k, n in sorted(tally.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"  {n:>5}  {k}")
    print(f"  {len(found):>5}  total")

    unregistered = sorted(set(g) - set(reg))
    stale = sorted(set(reg) - set(g))
    rc = 0
    if unregistered:
        print(f"\nFAIL: {len(unregistered)} classical result(s) with no entry "
              f"in tools/classical.json")
        for n in unregistered:
            print(f"  {n}  [{', '.join(g[n])}]")
        rc = 1
    if stale:
        print(f"\nFAIL: {len(stale)} registry entr(ies) name a declaration "
              f"that is no longer classical or no longer exists")
        for n in stale:
            print(f"  {n}")
        rc = 1

    text = markdown(found, reg)
    if args.markdown:
        AXIOMS_MD.write_text(text)
        print(f"\nwrote {AXIOMS_MD.name}")
    elif args.check:
        current = AXIOMS_MD.read_text() if AXIOMS_MD.exists() else ""
        if current != text:
            print("\nFAIL: AXIOMS.md is stale; run "
                  "`python3 tools/audit.py --markdown`")
            rc = 1
    return rc


if __name__ == "__main__":
    sys.exit(main())
