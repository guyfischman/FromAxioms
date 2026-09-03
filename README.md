# FromAxioms

Mathematics rebuilt in Lean 4 from the axioms of logic alone, with the logical
cost of every result measured rather than assumed.

**[The library from the axioms up](https://guyfischman.github.io/FromAxioms/)**
-- every declaration, what it rests on, and where each axiom and each named
principle first enters beneath it. Regenerated on every push.

No dependencies aside from the Lean toolchain.

## The point

Every theorem rests on some collection of principles. Each result here answers
three questions, all answered mechanically:

1. **What did the proof use?** `#print axioms` is an upper bound, and the
   kernel computes it.
2. **What does the theorem need?** Deriving the principle back from the theorem
   in a reversal, choice-free. That is a lower bound, and the two together pin
   the cost rather than bounding it on one side.
3. **What does the statement assume?** A principle taken as a hypothesis never
   reaches an axiom line -- a conditional theorem is unconditionally true -- so
   the binders are swept too, and each principle is traced to the declarations
   that spend it rather than pass it on.

The intended result is a map of the terrain rather than a pile of theorems: not
"the intermediate value theorem is constructive" or "is not", but which form is
free, which costs a named principle, and a proof of each.

## What is here

`FromAxioms/Logic/` is `prelude` and imports nothing at all. It reconstructs
the connectives, equality and the quantifiers from inductive types and the
dependent arrow, so that none of them is a primitive. It then declares the
classical axioms **separately** -- excluded middle and choice as distinct
axioms, rather than excluded middle derived from choice -- and proves the
reversals that pin each classical theorem to the weakest principle yielding it.
De Morgan's third law needs only weak excluded middle; double negation
elimination needs the full strength; extracting a decision procedure needs
choice even given excluded middle. Those distinctions collapse when both come
from one axiom.

It is a separate root, and nothing imports it: it declares `And`, `Or` and `Eq`
at top level, as Lean's `Init` does, so the two cannot share an environment.
What it establishes carries anyway. The connectives cost no axioms, and Lean's
are the same constructions, so everything above uses those and inherits the
result along with the tactics built on them.

Above that, sets are constructed rather than postulated: pre-sets as a `W`-type,
then `ZFSet` as their extensional quotient. Extensionality, separation,
replacement and the rest are theorems about that construction, and the kernel
reports what each costs. The arithmetic, analysis and algebra built on them
follow the same rule.

## The audit

Three sweeps, all run by CI on every push.

```sh
python3 tools/audit.py --check       # what proofs use
python3 tools/hypotheses.py --check  # what statements assume
python3 tools/hypcost.py --check     # where each principle is spent
```

The first generates a `#print axioms` line for *every* declaration rather than
reading the ones written by hand, so a classical result nobody thought to
annotate cannot hide in the gap. Anything reaching `Classical.choice`, or the
declared `em` or `choice`, needs an entry in `tools/classical.json` giving the
reason and naming the reversal where one exists.

The other two answer what an axiom line cannot. A principle threaded through a
hypothesis is invisible to the kernel's report, so `tools/hypotheses.json`
registers every principle assumed in a binder together with its calibration,
and `tools/hypcost.json` records which declarations spend one rather than
forward it. A new spend site is the event nothing else reports.

Per-declaration costs are in [AXIOMS.md](AXIOMS.md), regenerated with each
commit.

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
