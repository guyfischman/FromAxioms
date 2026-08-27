#!/usr/bin/env python3
"""Phase 2 declarations as the compiler sees them.

Named `astexport` rather than `ast`: `ast` is a standard-library module, and
shadowing one breaks any tool that imports it indirectly -- which is how
`tools/queue.py` once killed `fuzz.py` through `concurrent.futures`. The check
in `tools/sigcheck.py` caught this one the first time it ran.

`tools/lean.py` reads Lean with regexes. This reads it with Lean: it runs
`tools/ExportAST.lean`, which walks the environment and prints one JSON object
per declaration -- name, module, kind, private, axioms, and structural hashes of
the type and the value.

    python3 tools/astexport.py            # summary
    python3 tools/astexport.py --json     # the rows themselves

Cached on a digest of the sources plus the exporter, the same rule
`tools/audit.py`'s sweep uses: the answer is a function of those, so if none has
changed the previous answer still stands (`tools/cache.py`).

**Phase 2 only.** The exporter needs `import Lean`, which drags in `Init`, whose
`And`/`Or`/`Eq` are exactly what Phase 1 declares -- so Phase 1 cannot be read
this way and keeps the text parser. That is not a gap in the tool; it is the
two-root split doing what it exists to do.
"""

import argparse
import json
import os
import pathlib
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import cache  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
EXPORTER = ROOT / "tools" / "ExportAST.lean"


def source_key(root=None):
    """The digest a stored export must carry to count as current.

    `root` names ANOTHER tree, for a consumer holding a peer's cache --
    `crossmerge.py` reads one per branch. Every path is then taken from that
    tree, INCLUDING its `astexport.py`: the key covers the code that produced
    the answer, so keying a peer's cache on ours would call their export stale
    whenever this tree edited the exporter, and current whenever they did.
    """
    r = ROOT if root is None else pathlib.Path(root)
    covered = list((r / "FromAxioms").rglob("*.lean"))
    if not covered:
        raise SystemExit(
            f"no modules under {r / 'FromAxioms'}: a cache key covering "
            f"nothing never goes stale, which is worse than no cache")
    return cache.cache_key(
        [r / "lean-toolchain", r / "lakefile.toml",
         r / "tools" / "ExportAST.lean",
         # The AGGREGATOR, not just the directory below it. It is the file of
         # `import` lines that decides what gets elaborated, so its content
         # changes what the export CONTAINS -- and adding a file moves the key
         # via the glob while adding its import moved nothing. An export
         # generated between those two edits was then served under a matching
         # key (geometry, who lost three gate runs to it; the failure surfaces
         # in `astcheck.py` as *parsed from X, absent from the environment*,
         # which points at the parser and away from the cache).
         #
         # The HUB is the most exposed seat, not the least: every batch that
         # brings a new file changes the aggregator and nothing else, and the
         # aggregator is a conflict file on most batches.
         # EVERY MODULE, by the tree's own layout. This named
         # `FromAxioms/Foundations.lean` and the directory beside it, which is
         # how the private tree is arranged and not this one: neither path
         # exists here, so the key covered nothing that changes and the cache
         # answered every question with the first export ever taken. It served
         # 147 declarations against a tree holding 225, and the graph drew 7
         # landmarks of 13.
         r / "FromAxioms.lean",
         *sorted((r / "FromAxioms").rglob("*.lean"))],
        str(r / "tools" / "astexport.py"))


def export(use_cache=True, cached_only=False):
    """Every Phase 2 declaration, as a list of dicts.

    `cached_only` returns `None` rather than elaborating when the cache does
    not match. A consumer for whom the export is an *enhancement* -- `inert`
    crediting a use written as dot notation, `dupes` fingerprinting a proof --
    must pass it: regenerating costs a rebuild of every module downstream of
    whatever changed, which is minutes for a file low in the tower, and it is
    paid inside every selftest copy that patches one.
    """
    scratch = ROOT / ".audit"
    scratch.mkdir(exist_ok=True)
    store = scratch / "ast-cache.json"
    key = source_key()
    if use_cache and store.exists():
        try:
            got = json.loads(store.read_text())
            if got.get("key") == key:
                return got["rows"]
        except (ValueError, KeyError):
            pass
    if cached_only:
        return None

    env = dict(os.environ)
    env["PATH"] = f"{pathlib.Path.home()}/.elan/bin:" + env.get("PATH", "")
    # The exporter reads the compiled environment, not the sources the key
    # digests. A window where sources are newer than the build products let a
    # stale answer be cached under a key that kept matching --
    # so make the products current first, and refuse to export if that fails.
    b = subprocess.run(["lake", "build"], cwd=ROOT, env=env,
                       capture_output=True, text=True, timeout=1800)
    if b.returncode != 0:
        raise RuntimeError(
            "refusing to export from a failed build -- the environment would "
            "not match the sources the cache key digests:\n"
            + (b.stdout + b.stderr)[-2000:])
    r = subprocess.run(["lake", "env", "lean", "tools/ExportAST.lean"],
                       cwd=ROOT, env=env, capture_output=True, text=True,
                       timeout=1800)
    rows = []
    for line in r.stdout.splitlines():
        line = line.strip()
        if line.startswith("{"):
            rows.append(json.loads(line))
    if not rows:
        raise RuntimeError(
            "the exporter produced no declarations -- it failed to elaborate:\n"
            + (r.stdout + r.stderr)[-2000:])
    # ATOMIC, because 22 tools read this file `cached_only` and a prefix is
    # indistinguishable to them from an absent cache: `json.loads` raises,
    # the raise is swallowed, and the consumer silently answers from a
    # source-only population instead of refusing. `os.replace` is atomic on
    # POSIX, so a reader sees the old complete file or the new one.
    tmp = store.with_suffix(".json.partial")
    tmp.write_text(json.dumps({"key": key, "rows": rows}))
    os.replace(tmp, store)
    return rows


def public_declarations(rows=None):
    """What the library offers: no internals, no private, no constructors."""
    rows = rows if rows is not None else export()
    return [r for r in rows
            if not r["private"] and r["kind"] in ("theorem", "def", "abbrev",
                                                  "inductive", "axiom")]


def main():
    ap = argparse.ArgumentParser(description="Export Phase 2 declarations.")
    ap.add_argument("--json", action="store_true", help="print the rows")
    ap.add_argument("--no-cache", action="store_true")
    args = ap.parse_args()

    rows = export(use_cache=not args.no_cache)
    if args.json:
        print(json.dumps(rows, indent=1))
        return 0

    pub = public_declarations(rows)
    kinds = {}
    for r in pub:
        kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1

    from lean import parse_file
    written = set()
    for f in sorted((ROOT / "FromAxioms" / "Foundations").glob("*.lean")):
        for d in parse_file(f):
            written.add(d["full"])
    generated = [r for r in pub if r["name"] not in written]

    print("=" * 74)
    print(f"AST  -- {len(pub)} public declarations of {len(rows)} exported")
    print("=" * 74)
    for k, n in sorted(kinds.items()):
        print(f"  {n:5}  {k}")
    # Two numbers get quoted from this project and they are not the same
    # number; saying which is which here is cheaper than reconciling them
    # later.
    print(f"\n  {len(pub) - len(generated):5}  written in source "
          f"(what compare.py and inert.py count)")
    print(f"  {len(generated):5}  generated by the compiler: eliminators, "
          f"projections, instances")
    print(f"\n  OK -- read from the environment, not from the source text.")
    return 0


if __name__ == "__main__":
    sys.exit(main())


def cold_because():
    """The newest source postdating the cache, or None if the export is warm.

    **Lives here because the cache does.** Two generators need it and a third
    will: `dating.py --markdown` wrote a whole table of UNMEASURED verdicts to
    a tracked file from a cold export -- every cost state collapsed to zero,
    the fundamental theorem of calculus lost its SUPPLIED verdict -- and the
    gate then PASSED, because the file matched what the generator produces from
    a cold export. A check comparing a generated file against its own generator
    verifies agreement with the generator rather than with the tree.

    `_free_or_not` was already careful that UNMEASURED and FREE must not print
    alike; the refusal has to reach the WRITER, because a generator does not
    inherit the caution its own logic makes.

    **KEYED ON THE DIGEST, NOT ON MTIME.** This asked a
    different question from `export`, which admits a cache on `key == source_key()`,
    and a merge separates the two answers: git moves timestamps without moving
    bytes, so the cache reads FRESH to `freshness.py` and cold here -- and no
    re-run converges them, because `export` will not rewrite a cache it already
    considers current. The only exit was deleting the cache by hand, and it cost
    two tracks a gate in one hour. 2041 had already ruled for keys over
    timestamps; this was the one reader that had not been brought across.

    It also scanned `Logic/`, which `source_key` correctly omits -- Phase 2's
    export cannot depend on Phase 1, since nothing imports both roots -- so a
    Phase 1 edit reported the Phase 2 export cold.
    """
    # THE STORED KEY, NOT MTIME, and the two are not interchangeable.
    # `source_key()` is this module's own definition of "what the cache was
    # built from", and `freshness.py` already asks with it. This function asked
    # with MTIME instead -- so a MERGE, which rewrites a file's timestamp
    # without changing a byte, made the two disagree permanently: `freshness`
    # reported FRESH, this reported cold, and re-running the export could not
    # clear it because the export correctly declines to rebuild a cache it
    # considers current. The only escape was deleting the cache by hand. It
    # failed gates in two trees from two different triggers before the cause
    # was one thing (structures, and algebra from the other side).
    #
    # ONE SET COMPUTED TWICE is this repository's most expensive defect shape,
    # and two freshness keys for one cache is exactly it. The repair is one
    # definition called by both, not two spellings kept in step by hand.
    cache = ROOT / ".audit" / "ast-cache.json"
    if not cache.exists():
        return "the export cache does not exist"
    try:
        stored = json.loads(cache.read_text()).get("key")
    except (OSError, ValueError):
        return "the export cache cannot be read"
    if stored == source_key():
        return None
    # Naming a file is still the useful report, so say WHICH source is newest
    # by mtime -- but only once the digest has already established staleness.
    # mtime picks the likely culprit; it no longer decides the verdict.
    #
    # FOUNDATIONS ONLY, because that is what `source_key` digests. A Phase 1
    # edit cannot move this key -- nothing imports both roots -- so a `Logic/`
    # file can never be the culprit, and naming one would be a wrong answer to
    # a question the digest has already settled correctly.
    newest, when = None, cache.stat().st_mtime
    for path in (ROOT / "FromAxioms" / "Foundations").glob("*.lean"):
        try:
            m = path.stat().st_mtime
        except OSError:
            continue
        if m > when:
            when, newest = m, path.name
    return newest or "the recorded sources no longer digest to the stored key"

