# Formalized mathematics strand — August 2026

> **STATUS 2026-08-15 — this strand has not been started.** It is the only one of
> the three with no landed work: no commits since it was written, and none of its
> five items attempted. That is a deliberate record, not an oversight to hide.
>
> The other two strands moved a long way in the meantime, and two of their
> results change what this one should plan for:
>
> - **The Lean proof-TERM route is unavailable at our scale.** Mathlib's
>   `lrat_proof` peaks at 96.6 GB on a 628 MB certificate; native reflection does
>   the same instance in 8.9 GB. Any plan here that assumes importing or emitting
>   proof terms for large results needs rewriting around reflection. See
>   [`../refactor-2026-08/05-proof-consumption.md`](../refactor-2026-08/05-proof-consumption.md).
> - **The export is now actually tested.** 163 of 163 modules are read by a real
>   Lean 4.30.0, where previously zero were and the suites printed `ok` anyway.
>   Integration claims can now be checked rather than asserted.
>
> Before starting: the `fact` ledger did not exist when this was written, and it
> is the obvious import target — one file per proposition, with `proof_route` and
> `axiom_footprint` already distinguishing what a checker actually established.

The third roadmap strand, parallel to
[engineering](../refactor-2026-08/README.md) and
[mathematics](../mathematics-2026-08/README.md).

Those two ask *where is the code untidy* and *what mathematics can we do*. This
one asks: **the world has already formalized roughly ten million lines of
mathematics. What do we collect, how do we synthesize it, how does it get into
axeyum, and what do we build ourselves instead?**

> **Parallelism.** The ingest path lives in `crates/axeyum-lean-import/` and the
> kernel in `crates/axeyum-lean-kernel/`. The kernel is **owned by another lane**
> — see
> [`refactor-2026-08/00-parallel-work.md`](../refactor-2026-08/00-parallel-work.md).
> The *collection* and *synthesis* phases below touch neither and can start now.

## The universe, measured

| library | system | size |
|---|---|---|
| **Mizar Mathematical Library** | Mizar | **3.7 MLOC** — oldest, arguably largest |
| **Archive of Formal Proofs** | Isabelle/HOL | **4.8 MLOC** (roughly half is algorithm verification rather than mathematics) |
| **Mathlib 4** | Lean 4 | **115,000+ definitions, 232,000 theorems, >1.5 M lines** |
| **Mathematical Components** | Rocq/Coq | ~150,000 lines |

Network analysis of Mathlib alone extracts **308,129 declarations and 8.4 M
edges across 7,563 modules** (arXiv:2604.24797).

These are the corpora we can check ourselves against, and the map of what has
already been formalized. Their size is a *stock* built at human bandwidth over
years; ours is a **rate**, and it is measured below.

## The thesis of this strand

**Build the foundations ourselves, axiom-free, in parallel — and use the world's
libraries to check ourselves against, not to substitute for building.**

Measured on 2026-08-14: one lane produced **73 proved theorems in 11 h 43 min**
— ~149/day/lane — every one reporting **no axioms**, while also writing an ADR
each and updating tests. Ten lanes is ~1,500/day. The construction plan and the
arithmetic are in [`05-throughput.md`](05-throughput.md); the binding constraint
turns out to be a **single-file lock**, not compute or capability.

What makes this ours rather than a re-derivation is the loop the integration
allows: the library gives the solver facts, the solver decides goals the library
needs, reconstruction turns those decisions into kernel-checked terms, and the
DAG says what to prove next. **That cycle was closed end to end once on
2026-08-14.** It has never been automatic. Making it automatic is the strand.

Import stays, in a supporting role we are uniquely placed to fill:

- We have an **independent Lean kernel** (`axeyum-lean-kernel`, 37,987 lines)
  that is not Lean, written in a different language, by different people.
- We have a **fail-closed importer** for the official `lean4export` NDJSON
  format, with 17 genuine v4.30 fixtures and 9 test suites.
- On 2026-08-14 the **reverse** direction closed too: Lean's own kernel accepted
  an axeyum development from an empty environment, with a tamper control.

A library checked by exactly one kernel is a single point of trust. A second,
independent kernel that admits the same declarations is a measurement almost
nobody can produce — and it tells us where our own construction diverges from
the world's. That is worth having *in addition to* building, and it is the
research community's pluralistic-library problem ("QED Reloaded", Rabe et al.),
whose interchange infrastructure we should consume rather than rebuild.

## Where we actually stand

Measured, not assumed:

```
axeyum-lean-import   17 lean4export v4.30 fixtures, 9 test suites, fail-closed
K1 (import)          5/5 — on FIVE PINNED SINGLE-ROOT FIXTURES, not authority
L3                   0/12 — the phase that supplies Z, Dvd, and finite sums
dependency-closed Init/Std/mathlib population   UNSTARTED
references/          lean4 cloned (686 MB); NO mathlib clone
```

So the ingest path works on toy inputs and has never been pointed at a
population. That is the gap this strand exists to close, and the requirements
document already names the next step: *"use the existing `axeyum-lean-import`
reader to ingest a dependency-closed slice."*

## The four phases

1. [`01-collect.md`](01-collect.md) — which corpora, in which formats, under
   which licences, and what it costs to hold them.
2. [`02-synthesize.md`](02-synthesize.md) — the same theorem exists in four
   systems under four names. Alignment, deduplication, and the interchange
   formats that already exist (Dedukti, MMT/OMDoc, OpenTheory) so we do not
   invent a fifth.
3. [`03-integrate.md`](03-integrate.md) — getting it through
   `axeyum-lean-import` into an independently-checked environment, at
   population scale rather than fixture scale.
4. [`04-implement.md`](04-implement.md) — the boundary decision: what we import
   versus what we prove ourselves, and why `nat_prelude` is being built by hand
   while 232,000 theorems sit next door.
5. [`05-throughput.md`](05-throughput.md) — **the construction plan**: the
   measured production rate, the single-file lock that caps it, and the
   self-extension loop only this architecture can run.

## The measure of success

Not how much we ingest, and not theorem count. **Theorems the system proved
without a human writing the proof**, on a zero-axiom base, in the order the DAG
asked for — plus, from the import side, how much foreign mathematics axeyum can
now *use* in a proof, a certificate or a negative control that it could not use
before.

The first number is currently zero. [`05`](05-throughput.md) C2 makes it
positive.
