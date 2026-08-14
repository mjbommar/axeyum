# Formalized mathematics strand — August 2026

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

Against that, axeyum's own library is **106 proved theorems**. The ratio to
Mathlib's theorem count is roughly **1 : 2,200**.

## The thesis of this strand

**We should not race Mathlib. We should become the independent checker of it.**

That is not a consolation prize — it is the position axeyum is uniquely built
for, and almost nobody else occupies:

- We have an **independent Lean kernel** (`axeyum-lean-kernel`, 37,987 lines)
  that is not Lean, written in a different language, by different people.
- We have a **fail-closed importer** for the official `lean4export` NDJSON
  format, with 17 genuine v4.30 fixtures and 9 test suites.
- On 2026-08-14 the **reverse** direction closed too: Lean's own kernel accepted
  an axeyum development from an empty environment, with a tamper control.

A library of 232,000 theorems checked by exactly one kernel is a single point of
trust. A second, independent kernel that admits the same declarations is the
strongest assurance artifact available in this field, and it is a *measurement*
rather than a claim.

The research community already calls this the pluralistic-library problem —
"QED Reloaded: Towards a Pluralistic Formal Library of Mathematical Knowledge"
(Rabe et al.) — and the interchange work below is its infrastructure.

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

## The honest risk

Every phase here is a way to spend unbounded effort on other people's
mathematics while our own ladder
([mathematics strand](../mathematics-2026-08/README.md)) stays at rung two.
Import is only worth it if imported content **carries evidence through our
stack** — otherwise we have a large read-only museum.

The test for this strand is therefore not "how much did we ingest". It is:
**how much imported mathematics can axeyum now use in a proof, a certificate, or
a negative control that it could not use before.**
