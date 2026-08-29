# FromAxioms

Mathematics rebuilt in Lean 4 from the axioms of logic alone, with the
axiomatic cost of every result measured rather than assumed.

No dependencies aside from the Lean toolchain.

## The point

Every theorem rests on some collection of principles. The aim here is for each
result to answer three questions, all answered mechanically:

1. **What did the proof use?** `#print axioms` is an upper bound, and the kernel
   computes it.
2. **What does the theorem need?** Deriving the principle back from the theorem
   in a reversal, choice-free.
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
Lean's `Init`.

Above it, sets are constructed rather than postulated: pre-sets as a `W`-type,
then `ZFSet` as their extensional quotient. Extensionality, the empty set,
union, power set, separation and replacement are theorems about that
construction, and the kernel reports that none of them costs an axiom.
Regularity is here too, at the quotient level, where it costs `propext` and
`Quot.sound`. Arithmetic on omega, the ordered pair, relations and functions
follow; the integers are next.

The cost of every declaration is in [AXIOMS.md](AXIOMS.md), regenerated with
each commit. To check it rather than read it:

```sh
lake build 2>&1 | grep axioms
```

## The graph

[The library from the axioms up](https://guyfischman.github.io/FromAxioms/),
regenerated on every push: each declaration, what it rests on, and where each
axiom first enters beneath it. Dated results are marked.

## The audit

```sh
python3 tools/audit.py
```

This generates a `#print axioms` line for *every* declaration rather than
reading the ones written by hand, so a classical result nobody thought to
annotate cannot hide in the gap. Anything reaching `Classical.choice`, or the
declared `em` or `choice`, needs an entry in `tools/classical.json` giving the
reason and naming the reversal where one exists. CI runs `--check` on every
push, which fails on an unregistered result, on an entry whose subject is
gone, and on a stale [AXIOMS.md](AXIOMS.md).

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
