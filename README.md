# FromAxioms

Mathematics rebuilt in Lean 4 from the axioms of logic alone, with the
axiomatic cost of every result measured rather than assumed.

No dependencies aside from Lean toolchain.

## The point

Every theorem rests on some collection of principles. The aim here is for each result to answer three questions, all answered mechanically:

1. **What did the proof use?** `#print axioms` is an upper bound, and the kernel
   computes it.
2. **What does the theorem need?** Deriving the principle back from the theorem in a reversal, choice-free.
3. **Can the cost be moved into the statement?** A principle taken as a
   hypothesis is a cost the type signature records and the kernel checks.

The intended result is a map of the terrain rather than a pile of theorems: not
"the intermediate value theorem is constructive" or "is not", but which form is
free, which costs a named principle, and a proof of each.

## What is here

`FromAxioms/Logic/` is complete: the connectives, equality, the quantifiers,
the classical axioms declared explicitly, and the reversals that pin them. It
is `prelude`, importing nothing at all, and is kept a separate root because it
declares `And`, `Or` and `Eq` at top level and so cannot be imported beside
Lean's `Init`. The rest of the library builds on core and has begun.

Seven of the nine ZFC axioms are already theorems about a constructed model of
sets rather than assumptions about a postulated one -- and the kernel reports
that none of them costs anything at all:

```
'PSet.equiv_iff_ext'     does not depend on any axioms   -- EXTENSIONALITY
'PSet.mem_empty_iff'     does not depend on any axioms   -- EMPTY SET
'PSet.mem_pair_iff'      does not depend on any axioms   -- PAIRING
'PSet.mem_sUnion_iff'    does not depend on any axioms   -- UNION
'PSet.mem_powerset_iff'  does not depend on any axioms   -- POWER SET
'PSet.mem_sep_iff'       does not depend on any axioms   -- SEPARATION
'PSet.succ_mem_omega'    does not depend on any axioms   -- INFINITY
```

Reproduce with `lake build 2>&1 | grep axioms`, which prints the cost of every
audited declaration in the tree, the seven above among them.

## The audit

```sh
python3 tools/audit.py
```

This generates a `#print axioms` line for *every* declaration rather than
reading the ones written by hand, so a classical result nobody thought to
annotate cannot hide in the gap. Of the 150 declarations here, 117 depend on no
axioms at all. Anything reaching `Classical.choice`, or the declared `em`
or `choice`, needs an entry in `tools/classical.json` giving the reason, and
naming the reversal where one exists. CI runs `--check` on every push, which
fails on an unregistered result, on an entry whose subject is gone, and on a
stale [AXIOMS.md](AXIOMS.md).

## Building

```sh
lake build
```

Lean 4.24.0, pinned in `lean-toolchain`.

## Status

Early, and released in dependency order: what is here builds, and every commit
builds, but this is the beginning of the development rather than all of it.
Names and statements in published files are stable; the tree above them is not
yet here.

## Licence

Apache 2.0. See [LICENSE](LICENSE).
