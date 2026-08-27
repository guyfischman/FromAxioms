#!/usr/bin/env python3
"""Reading Lean source, for the tools that have to.

Four tools parse this library: `compare.py` counts declarations, `find.py`
searches them, `dupes.py` hashes proof blocks, `chains.py` reads projections.
They shared nothing, and each carried its own comment-stripper -- three copies
of the same twenty lines. The copy in `dupes.py` was the one that did not know
about `private theorem`, so a six-line window could span two declarations and
be reported as a repeat.

How many tools still keep their own is not written here, deliberately: a
hand-written count restales the moment one lands, and it restales DOWNWARD, so
a reader deciding whether to write another concludes the problem is smaller
than it is. `parsercopies.py --check` prints the three classes on every gate
run and its allow list holds the reason for each.

Stripping comments is not cosmetic. This library's files are prose-heavy, and
without it the declaration regex matches English: "the axiom budget" parses as
`axiom budget`, "the structure we" as `structure we`.

How to call it, because this docstring explained why the module exists and
never said that, and the omission caused the exact failure the module prevents:
a reader spent four attempts on the signature, wrote a fresh regex instead, and
it could not see `@[simp] theorem` -- a false finding that had to be retracted
. The correct instrument existed and was harder to
call than to rewrite, which is a documentation defect with a proof attached.

    from lean import parse_file, source_files

    for path in source_files(ROOT):          # every .lean in both phases
        for d in parse_file(path):           # -> list of dicts, in file order
            d["name"]   # bare name, e.g. "realLAdd_assoc"
            d["full"]   # namespaced, e.g. "ZFSet.realLAdd_assoc"
            d["kind"]   # theorem | def | abbrev | structure | inductive
            d["line"]   # 1-based line of the declaration
            d["file"]   # str(path)

`parse_file` takes a `pathlib.Path` and strips comments first, so attributes,
`private`, and docstring prose are all handled. Use it rather than a regex: the
tools that wrote their own each omitted something different.

`name` AND `full` ARE DIFFERENT SPELLINGS OF THE SAME DECLARATION, AND SETS
BUILT FROM THEM DO NOT MEET. This is the one thing above that a caller can
read correctly and still get wrong, and it cost a session: `mergedecls.py`
compared a set of `full` names against a set of bare ones, and on `PSet.lean`
that is 40 against 38 with an INTERSECTION OF ONE -- so every declaration read
as both present and absent, a check failed every merge, and its advisory arm
reported 11,173 deletions that had not happened.

The rule is not "prefer one". Both are right for different questions -- `full`
is the identity, `name` is what a human types and what a diff line carries. The
rule is that any comparison must fix one spelling on both sides, and where
one side is outside your control (a diff, an allow list, a peer's registry) the
usual answer is `d["full"].split(".")[-1]`, which is what `find.py` and
`bundle.py` do at every comparison site.
"""

import pathlib
import re

# path -> comment-stripped lines. See `stripped_lines`.
_STRIPPED = {}

# input digest -> times stripped. See `repeated_strips`.
_STRIP_COUNTS = {}

# One spelling of a Lean identifier, exported so the readers that need it do not
# each write their own. `lattice.py`, `signature.py` and `declsize.py` all did,
# and all three omitted the subscript range -- which truncates
# `binaryDC_of_countableBoolChoice₂` to a name that does not exist, so a
# lookup fails while the tool reports a declaration confidently.
ATOM = r"[A-Za-z_][\w'!?₀-₉]*"
IDENT = ATOM + r"(?:\." + ATOM + r")*"
# `ATOM` is one dotted SEGMENT, exported for the same reason `IDENT` is: a
# reader wanting unqualified tokens wrote its own class and lost the trailing
# prime. Never wrap either in a trailing `\b` -- see the note below.
# A Lean name is dotted SEGMENTS, each opening with a letter or underscore.
# Admitting the dot inside the class let `def Foo.{u}` -- legal, since a `def`
# does not auto-bind universes -- parse as `Foo.`, a name no declaration has.
#
# A TRAILING `\b` ON EITHER OF THESE SILENTLY STRIPS A TRAILING PRIME, and the
# corrupted name RESOLVES. After `realLSum_add'` the next character is a space;
# `'` and ` ` are both non-word, so the boundary fails there and the engine
# backtracks to end at `d` -- where `'` does supply one. Internal primes
# survive, so it is specifically Lean's own prime convention that breaks, which
# is not a case anyone thinks to test.
#
# Measured by analysis, in both directions at once, and the failures are worse
# than a miss because a primed lemma nearly always sits beside its unprimed
# twin: `placement.py` reported `realLSum_add declared later Weier:155`, true of
# a declaration that was not the one referenced, and `crossref.py` ATTRIBUTED a
# citation of `foo'` to `foo` while reporting `foo'` uncited. A wrong answer
# carrying a correct line number is not one anybody re-checks.
#
# The class already ends the match at the right place. The `\b` adds nothing and
# costs the prime, so there is no configuration in which it is wanted.

DECL = re.compile(
    r"^[ \t]*"
    r"(?:@\[[^\]]*\][ \t]*)*"
    r"(?:(?:protected|noncomputable|nonrec|partial|unsafe|scoped|local)[ \t]+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure|inductive|class|axiom)[ \t]+"
    rf"(?P<name>{IDENT})"
)

# The same shape with `private` allowed, and captured. `DECL` omits `private`
# on purpose: `compare.py`'s denominator is what the library OFFERS, and a
# file-internal lemma is not part of that.
#
# But that population is wrong for the tools that answer *has this been proved
# already*. A private hit answers "do not write this" exactly as well as a
# public one; it answers only "you cannot call it from elsewhere" differently.
# `realLIoo_inhabited` was reported absent by two tools while sitting four
# lines from where it was about to be rewritten, so the split
# is per-consumer rather than one rule.
DECL_ANY = re.compile(
    r"^[ \t]*"
    r"(?:@\[[^\]]*\][ \t]*)*"
    r"(?P<private>private[ \t]+)?"
    r"(?:(?:protected|noncomputable|nonrec|partial|unsafe|scoped|local)[ \t]+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure|inductive|class|axiom)[ \t]+"
    rf"(?P<name>{IDENT})"
)
NS_OPEN = re.compile(r"^[ \t]*namespace[ \t]+([A-Za-z_][A-Za-z0-9_.']*)")
NS_END = re.compile(r"^[ \t]*end[ \t]+([A-Za-z_][A-Za-z0-9_.']*)[ \t]*$")


def _report_repeats():
    """One NOTE on stderr when a run re-parsed the same text many times.

    STDERR deliberately: several tools emit JSON or a name list on stdout
    that other tools parse, and a diagnostic line there would corrupt them.
    `gates.py` scans stdout AND stderr for `NOTE:`, so the gate still shows
    it.

    The threshold is wasted strips, not repeats: two passes over one file is
    ordinary, and thousands is the quadratic shape that cost 79.9 seconds in
    one check while contention took the blame.
    """
    wasted = sum(n - 1 for n in _STRIP_COUNTS.values() if n > 1)
    if wasted < 500:
        return
    import sys
    worst = max(_STRIP_COUNTS.values())
    print(f"NOTE: this run re-parsed the same text {wasted} times over "
          f"({worst} for one input).\n      That is the shape where a "
          f"function takes a NAME and re-reads the file to\n      find it. "
          f"`lean.stripped_lines(path)` is the cached route.",
          file=sys.stderr)


def repeated_strips():
    """Inputs stripped more than once, as (count, first 40 chars).

    `strip_comments` is the choke point every reader of this library passes
    through, so counting repeats here finds a whole class of waste that no
    single tool can see: a function that takes a NAME and re-reads the file
    to find it looks cheap at its own call site and is quadratic in a loop.

    `signature.structures()` re-read every source file once per declaration
    it was asked about -- 3904 strips, 79.9 seconds, and the check it backed
    took 36s against a 0.1s baseline while contention took the blame
. This makes the next one visible without profiling.
    """
    return sorted(((n, k) for k, n in _STRIP_COUNTS.items() if n > 1),
                  reverse=True)


def strip_comments(lines):
    """Blank out Lean comments, preserving line numbering.

    Necessary, not cosmetic: this library's files are prose-heavy, and without
    stripping, the declaration regex matches English. "the axiom budget" parsed
    as `axiom budget`, "the structure we" as `structure we`, and "Phase 1" as
    `axiom Phase` -- four phantom declarations in one file, inflating our counts
    and polluting SURPLUS.

    Lean block comments nest, so this tracks depth rather than matching pairs.
    `/-- doc -/` and `/-! section -/` are ordinary block comments for our
    purposes.
    """
    key = (len(lines), hash(lines[0]) if lines else 0,
           hash(lines[-1]) if lines else 0)
    _STRIP_COUNTS[key] = _STRIP_COUNTS.get(key, 0) + 1
    # SPANS, not characters. The obvious loop appends one character at a time
    # and re-slices `line[i:i+2]` at every step -- 7.7 MILLION appends over one
    # `dating.py` run, which profiled at 85% of that tool's time and is paid
    # again by `audit`, `compare`, `find`, `dupes` and `chains`. The markers are
    # sparse, so `str.find` jumps between them and whole runs of text are copied
    # in one slice.
    #
    # The scan order below is the original's and must stay: `/-` is tested
    # before `-/`, which is before `--`. `/--` therefore OPENS a block rather
    # than being a line comment, and `---/` closes one from inside.
    out = []
    depth = 0
    for line in lines:
        buf = []
        i = 0
        n = len(line)
        while i < n:
            if depth == 0:
                a = line.find("/-", i)
                b = line.find("--", i)
                if a < 0 and b < 0:
                    buf.append(line[i:])
                    break
                if b >= 0 and (a < 0 or b < a):
                    buf.append(line[i:b])
                    break                      # `--` at depth 0 ends the line
                buf.append(line[i:a])
                depth += 1
                i = a + 2
            else:
                a = line.find("/-", i)
                b = line.find("-/", i)
                if a < 0 and b < 0:
                    break                      # rest of the line is comment
                if a >= 0 and (b < 0 or a < b):
                    depth += 1
                    i = a + 2
                else:
                    depth -= 1
                    i = b + 2
        out.append("".join(buf))
    return out


def parse_lines(lines, include_private=False, source="<lines>"):
    """The same walk, over lines already read and stripped.

    Split out so a tool holding a STRING can use the shared reader. Seven
    tools read `git show <rev>:<file>` and carry a private declaration regex --
    `crossref`, `ledgercheck`, `lost`, `mergedel`, `names`, `precompile`,
    `similar` -- and FIVE of them import this module and rolled their own
    anyway. That is the shape of a rule that could not be followed rather than
    one being ignored: the only entry point took a PATH, so the shared reader
    charged a filesystem round-trip per blob. `mergedel.py` reads 332 blobs per
    run and 498 across a criss-cross base pair.

    `source` is what the records report as their file; a revision reader passes
    `"<rev>:<relpath>"`, which is more informative than a temp file's name.

    STRIPPED IS A PRECONDITION AND ITS FAILURE IS SILENT. `parse_file` is
    `parse_lines(stripped_lines(path))`; calling this one on RAW text does not
    error, it returns MORE declarations -- prose words from `/-- ... -/`
    docstrings parse as names. Geometry got `ZFSet.the`, `ZFSet.was` and
    `ZFSet.rather` that way, out of a tree that exists only in git:

        parse_lines(strip_comments(git_show(rev, path).split("\n")))

    The summary line above said already read and stripped and that was not
    enough, because the reader who needs this entry point is reading the
    paragraph about holding a STRING. A caller who has text rather than a path
    has, by construction, not been through the stripper.
    """
    out = []
    rx = DECL_ANY if include_private else DECL
    stack = []
    path = source
    if not lines:
        return out
    for i, line in enumerate(lines):
        m = NS_OPEN.match(line)
        if m:
            stack.append(m.group(1))
            continue
        m = NS_END.match(line)
        if m:
            if stack and stack[-1] == m.group(1):
                stack.pop()
            continue
        m = rx.match(line)
        if m:
            name = m.group("name")
            full = ".".join(stack + [name]) if stack else name
            rec = {
                "name": name,
                "full": full,
                "kind": m.group("kind"),
                "file": str(path),
                "line": i + 1,
            }
            if include_private:
                rec["private"] = bool(m.group("private"))
            out.append(rec)
    return out


def parse_file(path, include_private=False, fresh=False):
    """Extract namespaced declarations from one Lean file.

    Tracks `namespace`/`end` so that `theorem euc` inside `namespace PSet`
    becomes `PSet.euc`. Without this, `PSet.mem` and `ZFSet.mem` collide and
    coverage is silently double-counted.

    `include_private` adds `private` declarations, each carrying
    `"private": True`. Off by default because the measuring tools must not
    count a file-internal lemma as part of what the library offers; on for the
    tools that answer has this been proved already, where excluding it
    produces a false absence.

    The walk itself is `parse_lines`; this supplies the reading and the
    per-path cache. Callers that already hold text want the other one.
    """
    return parse_lines(stripped_lines(path, fresh=fresh), include_private,
                       str(path))


# --------------------------------------------------------------------------
# Declaration spans
# --------------------------------------------------------------------------

# TRAILERS: lines that sit after a declaration's text and belong to the FILE
# rather than to it. A span computed as "this declaration's line up to the next
# one's" collects all of them, because the parser cannot see them and so cannot
# stop at them.
#
# This has cost three separate defects in one session, in two tools:
#
#   the file's `end ZFSet`   rode into the LAST declaration of every module, so
#                            a generated probe carried a stray namespace close
#                            in its middle and 637 signatures elaborated outside
#                            the namespace
#   `#print axioms` blocks   rode into whichever declaration preceded them
#   the NEXT declaration's   rode into the previous one, so a generated header
#   docstring                printed each audit line under someone else's prose
#
# All three are one shape: a line RANGE ends where the parser's next known thing
# starts, and everything the parser does not model rides along. Centralised here
# so a fourth tool gets it right without rediscovering it.
# `@[...]` IS NOT A TRAILER, it is the NEXT declaration's attribute, and an
# early version listed it here -- which would have deleted every `@[csimp]` in
# the tree from whichever span happened to precede it. An attribute line is
# carried forward with the docstring, for the same reason and by the same code.
TRAILER = re.compile(r"^\s*(?:#print\b|#check\b|#eval\b|#guard\b|end\b)")
LEADER = re.compile(r"^\s*(?:@\[|/--|/-!)")


def decl_span(raw, decls, i, strip_trailing_doc=True):
    """The `i`-th declaration's own lines, with the file's tail removed.

    Returns `(body, carried)`. `carried` is a doc comment that OPENED after this
    declaration's text and therefore belongs to the NEXT one -- the caller
    should prepend it there rather than drop it, since dropping is how a
    generated file loses every docstring in a module.
    """
    start = decls[i]["line"] - 1
    end = decls[i + 1]["line"] - 1 if i + 1 < len(decls) else len(raw)
    span = list(raw[start:end])
    while span and (not span[-1].strip() or TRAILER.match(span[-1])):
        span.pop()
    if not strip_trailing_doc:
        return span, []
    j = len(span)
    while j and not span[j - 1].strip():
        j -= 1
    if not j:
        return span, []
    k = j
    # Walk back over a run of LEADER lines -- a doc comment and/or attributes --
    # that opens after this declaration's own text. Anything in that run belongs
    # to whatever comes next.
    if span[j - 1].rstrip().endswith("-/"):
        k = j - 1
        while k >= 0 and not LEADER.match(span[k]):
            k -= 1
    while k - 1 >= 0 and LEADER.match(span[k - 1]):
        k -= 1
    # k <= 0 means the run opens at the declaration's own first line, so it is
    # this declaration's own docstring or attribute and not a carry.
    if k <= 0 or k >= j:
        return span, []
    body = span[:k]
    while body and not body[-1].strip():
        body.pop()
    return body, span[k:j]


def _lead_start(raw, start, floor):
    """First line of the docstring/attribute run that belongs to `start`.

    `floor` bounds the walk at the previous declaration's own first line.
    Without it, a declaration with no docstring walks back through everything
    above it and swallows its neighbour.
    """
    k = start
    while k - 1 >= floor and not raw[k - 1].strip():
        k -= 1
    if k - 1 >= floor and raw[k - 1].rstrip().endswith("-/"):
        k -= 1
        while k - 1 >= floor and not LEADER.match(raw[k]):
            k -= 1
    while k - 1 >= floor and LEADER.match(raw[k - 1]):
        k -= 1
    return k


def doc_span(raw, decls, i):
    """`(start, end)` covering the i-th declaration WITH its docstring.

    `decl_span` starts at the declaration, so a caller that moves or deletes by
    that span strands the `/-- ... -/` above it -- which then attaches to
    whatever follows, silently, and compiles. The moved declaration arrives
    undocumented and its new neighbour acquires a docstring about something
    else. Every caller was writing that walk-back itself.

    THE END IS CLAMPED to the next declaration's lead start, so two spans
    cannot overlap. The clamp is not belt-and-braces: `decl_span`'s carried-doc
    walk-back is otherwise the only guard, and it is not always right --
    `weaveBits` in `Baire.lean` keeps two lines of `weaveBits_append`'s
    docstring, which is one overlap in 14674 declarations and exactly the
    hand-written case that deleted a line past the end of a range.
    """
    start = decls[i]["line"] - 1
    floor = decls[i - 1]["line"] if i > 0 else 0
    lead = _lead_start(raw, start, floor)
    body, _ = decl_span(raw, decls, i)
    end = start + len(body)
    if i + 1 < len(decls):
        end = min(end, _lead_start(raw, decls[i + 1]["line"] - 1, decls[i]["line"]))
    return lead, max(end, start + 1)


def source_files(root):
    """Every Lean file in the library, in a stable order."""
    return sorted(root.glob("FromAxioms/**/*.lean"))


# --------------------------------------------------------------------------
# Signatures
# --------------------------------------------------------------------------
#
# Splitting `theorem f {a : T} (h : P) : Q := proof` into its binders and its
# conclusion cannot be done with a regex, because binders contain `:` and the
# proof contains `:=`. It needs a depth scanner: the interesting delimiters are
# the ones at depth zero.
#
# This exists so a statement can be transformed rather than only counted --
# turning a theorem into the hypothesis of its own reversal, or rewriting a `≠`
# in a conclusion while leaving binders alone. Both are mechanical on structured
# binders and hopeless on text.

OPENERS = {"(": ")", "{": "}", "[": "]", "⟨": "⟩", "⦃": "⦄"}
CLOSERS = {v: k for k, v in OPENERS.items()}


def split_signature(text):
    """Split a declaration body into (binders, conclusion).

    `text` starts immediately after the declaration's name and runs to the end
    of the file. Returns `(binders, conclusion, end)` where `end` is how much of
    `text` the signature occupies, or `None` when there is no top-level `:`.

    Scanning stops at a top-level `:=` or at a top-level `|` beginning a line --
    a theorem given by pattern-matching equations has a perfectly good
    conclusion and no `:=` at all, and treating the equations as part of the
    statement is how a splitter silently corrupts what it hands on.
    """
    depth = 0
    binders = []
    start = 0
    colon = None
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in OPENERS:
            if depth == 0:
                start = i
            depth += 1
        elif c in CLOSERS:
            depth -= 1
            if depth == 0 and colon is None:
                binders.append(text[start:i + 1])
            elif depth < 0:
                return None
        elif depth == 0:
            # THE EARLIEST OF THREE BOUNDARIES, not `:=` with `|` as a fallback.
            # A structure-style declaration ends its signature at `where` and
            # its field bodies carry their own depth-zero `:=`, so a scanner
            # without this case files a fragment of the PROOF as part of the
            # conclusion. `split_at_assignment` below already takes the earliest
            # of the same three.
            _where = (c in " \n" and text.startswith("where", i + 1)
                      and (i + 6 >= n or text[i + 6] in " \n\t\r"))
            if text.startswith(":=", i) or _where or (
                    c == "|" and (i == 0 or text[:i].rstrip(" \t").endswith("\n"))):
                if colon is None:
                    return None
                return binders, text[colon + 1:i].strip(), i
            if c == ":" and colon is None:
                colon = i
        i += 1
    return None



def split_at_assignment(src):
    """Split a whole declaration into `(signature, proof)` at its `:=`.

    The `:=` must be at bracket depth zero, and a splitter that searches for a
    literal instead gets it wrong in BOTH directions. Measured over
    `FromAxioms/Foundations/*.lean`, 14200 declarations carrying a `:=`:

        13479   agree
             2   landed EARLY -- a bracketed `:=` (a `fun .. => ..` with a
                 local binding, an autoParam, a `let` in a hypothesis type)
                 taken as the split, so the conclusion is cut off the
                 signature
           726   landed LATE -- either no `':= by'` at the real split, so the
                 probe ran on to a `have .. := by` inside a term proof, or an
                 equation-style declaration whose `| ` boundary precedes a
                 depth-zero `:=` buried in one of its branches

    The late case is 99.7% of the damage. Note that 49 declarations have a
    bracketed first `:=` and only 2 of them mis-split, because a `':= by'`
    probe steps over a bare bracketed `:=` by accident -- so "first `:=` is
    bracketed", the shape the defect was reported as, overstates that half by
    twenty-four times while missing the other half entirely.

    A declaration given by EQUATIONS ends its signature at the first `| ` line,
    and that boundary can come BEFORE any depth-zero `:=` -- so the two
    candidates are computed and the EARLIER one wins. Taking the `:=` first and
    the `| ` only as a fallback is wrong on exactly these: `pb_gcd_family`
    (PolyRing.lean) is `| 0 => ..` / `| D + 1 => by obtain ..` and does have a
    depth-zero `:=`, 1451 characters in, inside the second equation's proof.
    Splitting there files most of the proof as signature -- the same failure the
    depth rule exists to prevent, reached by a different route. Found by
    algebra, whose queue item carried the case as a runnable condition.

    Returns `(src, '')` when there is neither, which is the honest answer for a
    `structure` or an `inductive`.
    """
    # THE EARLIER OF THE TWO BOUNDARIES, not `:=` with `|` as a fallback.
    # An equation-style declaration has NO `:=` ending its signature -- the
    # boundary is `| 0 => ...` -- so a `:=` found later is inside an
    # alternative's proof. Reaching the `|` only when no `:=` exists anywhere
    # meant `pb_gcd_family` filed 395 characters of proof, `obtain` included,
    # as signature. Measured: 523 of 16147 declarations move, every one
    # SHORTENING the signature; none lengthens.
    depth = 0
    bar = -1
    whr = -1
    for i, c in enumerate(src):
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif depth == 0 and src.startswith(':=', i):
            seen = [x for x in (bar, whr) if x >= 0]
            j = min(seen) if seen else i
            return src[:j], src[j:]
        elif depth == 0 and bar < 0 and src.startswith('\n  | ', i):
            bar = i
        elif depth == 0 and whr < 0 and src.startswith(' where\n', i):
            # STRUCTURE STYLE. The `where` stays in the signature -- it is part
            # of the statement -- and the FIELDS are the proof half.
            whr = i + len(' where')
    seen = [x for x in (bar, whr) if x >= 0]
    return (src, '') if not seen else (src[:min(seen)], src[min(seen):])


def invalidate(path=None):
    """Drop the cached strip for `path`, or for everything when `path` is None.

    PUBLIC ON PURPOSE. A caller that WRITES a `.lean` file and then re-reads it
    needs this, and the previous answer was to clear a private dict -- which
    only a reader of this source could discover.
    """
    if path is None:
        _STRIPPED.clear()
    else:
        _STRIPPED.pop(str(path), None)


def stripped_lines(path, fresh=False):
    """The file's lines with comments removed, computed once per path.

    `signature()` re-read the file and re-stripped it FOR EVERY DECLARATION
    it was asked about, so a file with two hundred theorems parsed itself two
    hundred times. One call to `redundant.candidates()` on a single file cost
    10.3 seconds; with this it costs 0.4.

    Keyed on the path, and INVALIDATION IS PUBLIC: `fresh=True` here, or
    `lean.invalidate(path)` for a caller that has just written the file.

    A private attribute is not an API. The paragraph above used to end *a
    tool that starts editing files mid-run must not use this*, and the only
    remedy was `_STRIPPED.clear()` on a private name -- so every caller who
    needed it had to read this source. A hazard whose only remedy is
    undocumented is a hazard with no remedy, and three callers hit it: the
    third was a port applier that edits `.lean` files and re-parses to verify
    its own work, which read the PRE-EDIT parse on every verification after the
    first. A rollback appeared not to take, one real duplicate looked permanent,
    and 33 of 36 patches were skipped as though each would duplicate it.

    The warning was correct, adjacent to the code, and MORE specific than most
    -- and prose adjacent to the violation is not an instrument, because the
    person it is addressed to is the person who breaks it.
    """
    key = str(path)
    got = None if fresh else _STRIPPED.get(key)
    if got is None:
        try:
            got = strip_comments(
                path.read_text(encoding="utf-8", errors="replace").splitlines())
        except OSError:
            got = []
        _STRIPPED[key] = got
    return got


# A principle is a `Prop`-valued `def` taking NO PARAMETERS. That single
# distinction separates a strength (`LPO`, `WKL`, `FAN`) from a predicate
# (`IsBar`, `IsTree`, `HasPath`), with no judgement call -- which is what
# makes a check over it mechanical rather than a curated list that drifts.
PRINCIPLE_DEF = re.compile(r"^def\s+([A-Za-z_][\w'])\s(.*?):\s*Prop\s*:=",
                           re.M)


def nullary_prop_defs(path):
    """Principle names defined in one file, by the arity rule.

    The CRITERION lives here and the CORPUS does not: `lattice.py` asks about
    `Omniscience.lean` alone, `hypotheses.py` about every Foundations file,
    and both are right for their question. What must not differ is what
    counts as a principle -- the rule was written twice, independently,
    months apart, and two copies of one definition are free to drift without
    anything noticing.
    """
    src = "\n".join(stripped_lines(path))
    return sorted(m.group(1) for m in PRINCIPLE_DEF.finditer(src)
                  if not m.group(2).strip())


def signature(path, name):
    """Binders and conclusion of one declaration, or `None`."""
    text = "\n".join(stripped_lines(path))
    for m in re.finditer(rf"(?m)^[ \t](?:@\[[^\]]\][ \t])"
                         rf"(?:(?:private|protected|noncomputable|nonrec)[ \t]+)*"
                         rf"(?:theorem|lemma)[ \t]+{re.escape(name)}(?![A-Za-z0-9_.'])",
                         text):
        got = split_signature(text[m.end():])
        if got:
            return got[0], got[1]
    return None


# Registered once, at import: any tool that reads the library through this
# module reports its own waste without having to remember to ask.
import atexit  # noqa: E402
atexit.register(_report_repeats)

# THEOREM STEMS THAT OTHER THEOREMS EXTEND.
#
# Read by `find.py`, `proves.py` and `concludes.py` at SEARCH time. It lives
# beside the parser because it is a fact about the NAME SET the parser produces,
# and because all three already import this module -- a fourth would be a fourth
# thing to import and to forget.
import functools as _functools


def sibling_note(name):
    """A warning that an exact hit on `name` may be the wrong member, or None.

    THE TRAP IS AN EXACT HIT, NOT A NULL. A declaration that is also a
    PREFIX of others answers a name search successfully and returns a member the
    reader did not want. Ranked by how much each outcome prompts a second look:
    a null sends you by another route; several prefix hits prompt a decision,
    which might be got right; an exact hit prompts nothing at all. So a
    plausible count of ONE, on the name you typed, is the worst of the three and
    the only one no tool remarks on.

    THE POPULATION IS THEOREMS PREFIXING THEOREMS, and the narrowing is why
    this is worth printing. Any-name-prefixes-any-name is 2163 here and is
    noise: a definition and its lemmas share a stem BY DESIGN. Restricted to
    theorems it is 893, about 8% of public theorems, so fewer than one exact hit
    in ten carries a note -- rare enough to keep its force.

    A BARE PREFIX, with no word-boundary condition, and that was measured.
    Requiring the sibling to continue with `_` looks like the tidy refinement
    and brings 893 down to 674 -- removing exactly the dangerous half:
    `arityOK_Q` against `arityOK_QCtx`, `app_conjAct` against `app_conjActSub`.
    A name continuing WITHOUT a separator is MORE confusable at a glance, not
    less, because it reads as a different word rather than a longer form of this
    one.
    """
    try:
        sibs = _theorem_siblings().get(name.split(".")[-1])
    except Exception:
        return None                      # a note is never worth an exception
    if not sibs:
        return None
    shown = ", ".join(sorted(sibs)[:4])
    more = f", and {len(sibs) - 4} more" if len(sibs) > 4 else ""
    return (f"NOTE: `{name}` has {len(sibs)} sibling(s) sharing this stem "
            f"({shown}{more}).\n"
            f"      An exact-name hit here may not be the member you want.")


@_functools.cache
def _theorem_siblings():
    """stem -> the theorem names extending it, theorems only."""
    root = pathlib.Path(__file__).resolve().parent.parent
    pool = set()
    for f in sorted((root / "FromAxioms").rglob("*.lean")):
        for d in parse_file(f):
            if d.get("kind") == "theorem":
                pool.add(d["name"])
    pool = sorted(pool)
    out = {}
    for n in pool:
        sibs = [m for m in pool if m != n and m.startswith(n)]
        if sibs:
            out[n] = sibs
    return out
