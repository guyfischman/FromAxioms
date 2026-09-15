#!/usr/bin/env python3
"""Cache keys for the measurement tools.

Its own module rather than a section of `tools/lean.py`, which parses Lean
source and has nothing to do with caching. It went there first because that is
where shared code lived, which is how a utility module becomes a junk drawer --
the tell was that `lean.py`'s docstring would have had to be made vague to cover
both.
"""

import hashlib
import json
import pathlib


def cache_key(inputs, tool):
    """Digest for a cached computation: its inputs, and the code defining it.

    **The rule.** A cache whose output is a function *this tool defines* must
    include the tool in its key: changing which declarations are swept, or how a
    name is normalised, changes the answer while every input stays put. Neither
    failure is visible from the outside, so the rule is written here.

    **The exception.** A tool that runs the *current* comparator over old
    revisions holds the measurement fixed while the library varies. Keying its
    series on the comparator would discard the whole history every time the
    comparator was touched, which is the opposite of its purpose.

    So the question to ask of a new cache is not "should I hash the tool" but
    *is the tool the thing being held fixed, or the thing being measured with*.
    Hash it in the first case; leave it out, with a comment saying so, in the
    second.

    `inputs` is an iterable of paths and/or bytes; `tool` is the file whose code
    defines the computation, normally `__file__`.

    Paths enter the key *relative to the repository root*, so a key computed in
    one checkout is valid in a copy of it. A check run against a copy would
    otherwise miss a warm cache and recompute the whole axiom sweep.

    **Symlinks are not resolved**, and that is the second half of the same
    point. Measuring old revisions in a temp tree with a checkout symlinked in,
    resolving the link puts the *real* path in the key, which no longer sits
    under the temp root, so every revision misses the index cache.
    An input is identified by where the tool looked for it, not by where the
    filesystem kept it.
    """
    # `absolute`, not `resolve`, on both sides: on macOS `/tmp` is a symlink to
    # `/private/var/...`, so resolving the root and not the inputs (or the other
    # way) makes every path fall outside it and the key differ between a tree
    # and its copy.
    root = pathlib.Path(tool).absolute().parent.parent
    h = hashlib.sha256()
    h.update(pathlib.Path(tool).read_bytes())
    for item in inputs:
        if isinstance(item, (bytes, bytearray)):
            h.update(item)
        else:
            p = pathlib.Path(item)
            try:
                rel = p.absolute().relative_to(root)
            except ValueError:
                rel = p
            h.update(str(rel).encode())
            if p.exists():
                h.update(p.read_bytes())
    return h.hexdigest()


# --- verdict caching -------------------------------------------------------
#
# Some checks are pure functions of files on disk and take seconds to say so.
# Re-normalising every proof in the library, or rebuilding and running the
# demonstrations, cannot change its answer while the inputs sit still, and
# together they dominate a warm gate run.
#
# **Only a pass is cached, ever.** Skipping a failure would suppress the
# message that makes a failing check useful, and a check that remembers it
# failed is a check nobody can fix incrementally. So a miss -- or any prior
# failure -- means run it.
#
# The key must name every input the verdict reads. A check whose answer
# depends on something unhashed (the built library, the environment) must
# include a digest of that too, or the cache will hold a stale pass through
# exactly the change that mattered.

VERDICTS = "verdicts.json"


def _verdict_store(tool):
    root = pathlib.Path(tool).absolute().parent.parent
    scratch = root / ".audit"
    scratch.mkdir(exist_ok=True)
    return scratch / VERDICTS


def _load_verdicts(tool):
    store = _verdict_store(tool)
    if not store.exists():
        return {}
    try:
        return json.loads(store.read_text())
    except (ValueError, OSError):
        return {}


def passed_before(name, inputs, tool):
    """True when this exact input set has already been recorded as passing."""
    return _load_verdicts(tool).get(name) == cache_key(inputs, tool)


def record_pass(name, inputs, tool):
    """Remember that this input set passed. Call only on a zero exit."""
    got = _load_verdicts(tool)
    got[name] = cache_key(inputs, tool)
    try:
        _verdict_store(tool).write_text(json.dumps(got, indent=1, sort_keys=True))
    except OSError:
        pass
