# 02 — Synthesize

**The problem.** The same theorem exists in four systems under four names, four
foundations and four proof styles. Ten million lines of formalized mathematics
is not ten million lines of *distinct* mathematics, and nobody knows the overlap.

This phase is about turning a pile of corpora into a **map**: what has been
formalized, where, how often, and under which foundation.

Nothing here touches `crates/`. It is fully parallelisable.

## Do not invent a fifth interchange format

Three serious attempts already exist, and the field has been at this for two
decades:

| format | scope | status |
|---|---|---|
| **OpenTheory** | HOL family — HOL4, HOL Light, ProofPower, Isabelle | **dormant, re-check before planning on it**: the package repository is live but its newest packages date to ~2020, and the `gilith/hol-light` export fork was last pushed 2020-02-12 while mainline HOL Light ships weekly (checked 2026-08-15). Its standard library HAS been translated onward to Dedukti. |
| **Dedukti** | universal proof checker on λΠ-calculus modulo | the most general; used as a backend to verify proofs from multiple provers |
| **MMT / OMDoc** | logical framework in which many systems' logics are represented | the Mizar library has an OMDoc translation |

Point translators also exist — HOL Light → Coq, HOL Light → Isabelle/HOL,
HOL Light → Metamath (Carneiro) — which tells you both that the problem is
tractable and that it is done pairwise because the general case is hard.

**Our position should be a consumer of these, not a competitor.** The one format
we have a working reader for is `lean4export`, and the correct next format is
whichever has a published path *into* it, not whichever is most elegant.

## The alignment problem, stated honestly

Aligning theorems across systems is a research area, not an engineering task.
`add_comm` in Lean, `ADD_SYM` in HOL Light and Mizar's commutativity registration
are the *same mathematics* under different foundations, and no mechanical
procedure gets that right in general. Relevant prior art: alignment-based
translation using interface theories, and **JEFL: Joint Embedding of Formal Proof
Libraries**.

What is tractable, and what this strand should actually do:

1. **Align on statements, not proofs.** Two systems agreeing that a statement is
   a theorem is useful even when their proofs share nothing.
2. **Align a small, high-value core** — arithmetic, order, divisibility,
   elementary number theory. That core is where our library is, and it is where
   overlap is densest.
3. **Publish disagreements as findings.** Where two libraries state what looks
   like the same theorem with different hypotheses, that is either a genuine
   foundational difference or somebody's error. Both are worth knowing, and
   neither is discoverable without the alignment.

## The synthesis nobody has done, which we are unusually placed to do

Three graphs exist and have never been joined:

| graph | nodes | source |
|---|---:|---|
| informal concept DAG | **1,567 concepts, 2,254 prerequisite edges** | `../math-education/graph/` |
| formal dependency graph | **308,129 declarations, 8.4 M edges** | Mathlib, per arXiv:2604.24797 at commit `534cf0b`. NOT the same thing as LeanDojo Benchmark 4, which is proof-state/tactic training data (~122,517 theorems, 259,580 tactics, 167,779 premises) and is not a kernel-level export. No published bulk `lean4export` dump of Mathlib exists (searched 2026-08-15). |
| axeyum's routing table | **23 nodes** with decidability class and executing family | `docs/curriculum/` |

Joining them answers questions none can answer alone:

- **Which of the 1,567 human concepts are formalized at all?** That is the
  coverage map of formal mathematics against a pedagogical account of the
  subject, and it does not exist.
- **Where does pedagogical order disagree with logical order?** The Mathlib
  network analysis predicts substantial divergence — 50.9% coupling across
  namespaces, human taxonomies diverging from logical structure. Our 13 strands
  are exactly such a taxonomy. The disagreements are information.
- **Which formalized theorems fall inside a fragment axeyum decides?** That is
  the mathematics strand's D2 frontier computed against *formal* rather than
  informal content — a far stronger result.

This is the same work as
[`mathematics-2026-08/05-the-mathematics-dag.md`](../mathematics-2026-08/05-the-mathematics-dag.md)
D3, approached from the corpus side. They should be done once, together.

## Deduplication, and why it matters to us specifically

If we ever import from two systems, the same theorem arrives twice under
different names, with different hypotheses, in a kernel that will happily admit
both. That is not unsound, but it makes the library's *content* unmeasurable —
and this project's chosen metric is **assumptions remaining per prelude**, which
depends on knowing what is actually there.

Decide the identity policy **before** the second import, not after. The
importer already computes ADR-0350 canonical identity manifests — structural
content and direct-dependency digests, ignoring wire and arena order. That is
the right primitive to build identity on, and it exists.

## What to do first

1. **Download the LeanDojo Mathlib4 dependency graph.** External, cheap, and it
   is the formal half of the join. Checked 2026-08-15: LeanDojo Benchmark 4 is
   real and mirrored on HuggingFace, but per-mirror licences are unconfirmed and
   it is **tactic/proof-state data, not declarations** — so it supports the join
   on names and statements and nothing beyond that. There is no published
   kernel-level export of Mathlib to substitute for it.
2. **Run the three-way join** on names and statements as far as it goes, and
   publish the coverage map — including how much did *not* match, which is the
   honest half of the result.
3. **Read the alignment literature before writing an aligner** — interface
   theories, JEFL, and the Dedukti/MMT experience reports. This is the area of
   this whole roadmap where reinventing is most likely and least excusable.
4. **Write down the identity policy** for cross-system imports while there is
   still only one importer.
