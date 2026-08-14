# 01 — Collect

**The question.** What do we hold locally, in what format, under what licence,
and at what cost?

Today: `references/` holds a 686 MB shallow clone of **lean4** and several
solvers. **There is no Mathlib clone.** The importer's 17 fixtures are
hand-picked v4.30 exports, not a corpus.

## The corpora, ranked by what they are worth to us

### Tier 1 — Lean 4 / Mathlib. Start here, and possibly finish here.

**Why first:** it is the only corpus we can already read. `axeyum-lean-import`
consumes official `lean4export` NDJSON 3.1.0 fail-closed; nothing else in the
universe has a working path into our kernel.

- **115,000+ definitions, 232,000 theorems, >1.5 M lines**; 308,129 declarations
  and 8.4 M dependency edges when the full module graph is counted.
- Apache-2.0, so redistribution and derived artifacts are unproblematic.
- Export is a *generated* artifact: `lean4export` must be run against a built
  Mathlib, which means a Lean toolchain and a full build — hours of CPU and tens
  of GB, not a `git clone`.

**Collect:** a pinned Mathlib revision, its `lean4export` NDJSON, and the
toolchain manifest that produced it. Pin all three together; an export without
its producing revision is unreproducible, which is the same defect class the
claim ledger's `instance-pin` exists to prevent.

### Tier 2 — the HOL family, via OpenTheory

**Isabelle/HOL's Archive of Formal Proofs: 4.8 MLOC**, though roughly half is
algorithm and system verification rather than mathematics — a fact worth
respecting before quoting the headline number.

**OpenTheory** is the interchange format for the HOL family (HOL4, HOL Light,
ProofPower, Isabelle), and its standard library has already been translated to
Dedukti by others. So there is a path, and it is not ours to build.

**Collect:** the OpenTheory standard library package set. Small, well-defined,
and it is the natural second system precisely because its logic (simple type
theory) is *further* from Lean's dependent type theory than anything else we
would try — a harder and therefore more informative second data point.

### Tier 3 — Mizar and Rocq, for reference not ingestion

- **Mizar Mathematical Library, 3.7 MLOC** — the oldest and among the largest,
  with an existing OMDoc translation. Its set-theoretic foundation (Tarski–
  Grothendieck) is far from our kernel; treat it as a *coverage map* of what
  mathematics has been formalized, not as an import target.
- **Rocq/Coq Mathematical Components, ~150,000 lines** — small, high quality,
  and its dependent type theory is closest to Lean's. A plausible third target
  and a poor second one, because it would teach us less than the HOL detour.

### Tier 4 — not libraries, but corpora we should hold anyway

- **TPTP** derivation format — ATP traces, and the closest thing to a standard
  for machine-generated first-order proofs. Relevant to the *certificate* side
  of our stack rather than the library side.
- **SMT-LIB** benchmarks — already partially held under `corpus/`.
- **OEIS** — 380,000+ integer sequences with provenance. Not formal, but it is
  the best available index of *computed* mathematics, and the mathematics
  strand's D4 work queue (706 `computed`/`proved` concepts) has an obvious join
  against it.

## What collection actually costs

Three costs that are routinely under-counted, and one that bit this project
already today:

1. **Building to export.** Mathlib's NDJSON does not exist until Mathlib is
   built. Budget a Lean toolchain, hours of CPU, and tens of GB.
2. **Storage and the checkout.** `references/` is gitignored and repopulated by
   `scripts/fetch-references.sh` — the right pattern, and any corpus we add
   should follow it rather than entering git.
3. **Memory, which is the one we keep rediscovering.** Every large artifact this
   project has handled has hit a materialisation limit: a proof checker at 8×
   the proof size (since reduced to 1.5×), a reconstruction arena at 24.6 GB for
   4.6 M hints, a formatting gate blind to 44% of files because it walked the
   wrong structure. **An 8.4 M-edge import will hit the same class of wall**, and
   the useful question to ask up front is what the streaming story is, not what
   the peak memory is.
4. **Licence hygiene.** Apache-2.0 (Mathlib) and the AFP's BSD-style terms are
   permissive; Mizar's are more restrictive. Record the licence *with* the pin,
   because a derived artifact in our ledger inherits it.

## What to do first

1. **Add Mathlib to `scripts/fetch-references.sh`** at a pinned revision. Cheap,
   reversible, and it makes every later measurement possible.
2. **Produce one `lean4export` NDJSON of a dependency-closed slice** — not all
   of Mathlib. `Init` plus the transitive closure of one interesting theorem is
   the right first artifact, and it is exactly what the requirements document
   asks for.
3. **Pin revision + toolchain + export together**, hashed, following the
   `instance-pin` discipline the claim ledger already uses.
4. **Measure before ingesting**: declaration count, edge count, wire size, and
   the depth of the dependency closure. Those four numbers decide whether
   [`03-integrate.md`](03-integrate.md) is a week or a quarter.
