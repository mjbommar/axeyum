# ADR-0379: A claim ledger joining the knowledge graph to machine-checked evidence

- Status: proposed
- Date: 2026-08-12
- Deciders: (pending review)

## Context

Axeyum has two mature but disjoint artifact systems:

1. **The pile** — machine-checked results: solver evidence
   (`EvidenceReport`), pack checks (`artifacts/examples/math/*/expected.json`),
   benchmark baselines, DRAT/Farkas/Alethe certificates, Lean
   reconstructions. Rich in assurance vocabulary, but with no notion of what
   a result *means* mathematically: no concept anchors, no prerequisite
   structure, no representation of open problems.
2. **The map** — the sibling `math-education` knowledge graph: 1,565
   concepts with a six-value epistemic vocabulary (`axiom / proved /
   computed / empirical / conjectured / open`), per-encounter prerequisite
   edges with written reasons, 148 first-class misconceptions, and a strict
   target-resolution policy (pending vs resolved references). Rich in
   meaning, but its `computed` status is a claim about mathematics with no
   field naming the program, the range checked, or the certificate.

Neither system can represent the thing an agentic mathematics loop works
on: *a claim whose truth status can move* — from `open` through
`conjectured` to `computed`, each transition justified by a checkable
artifact. `math-education/PLAN.md` commitment 4 ("Verified content … the
algebra shown is checked, not asserted") has no implementing schema; the
axeyum pack `check` record has assurance labels but no epistemics and no
frontier representation.

## Decision

Introduce a **claim ledger** under `artifacts/claims/` (schema:
`artifacts/ontology/claim.schema.json`). One claim = one directory =
`claim.json` plus its evidence artifacts. Key commitments:

1. **The epistemic vocabulary is imported verbatim from the map.** A
   claim's `epistemic_status` uses `math-education`'s six values with their
   meanings, so both corpora share one epistemics and a claim's status can
   be projected into the graph without translation.
2. **Evidence rows are per-sub-statement, with per-row assurance**
   (`checked / replay-only / not-checked`), mirroring the repo's existing
   assurance-separation discipline. `computed` requires at least one
   `checked` row; `bound-citation` rows can never be `checked` (a citation
   is not a machine check).
3. **Concept references follow the map's resolution policy.** A ref may be
   `pending` (target not yet written) — that is an honest work-list marker.
   A ref marked `resolved` must name a 40-hex `graph_pin` and resolve in
   that graph; a false `resolved` is a validation error. This mirrors
   `math-education`'s `pending()` single-policy helper.
4. **Open problems are first-class.** `conjectured`/`open` claims must
   carry a `frontier` record: current known bounds (with evidence ids or
   citations) and the concrete artifact that would settle the claim. This
   is the field that makes the ledger a *worklist for discovery* rather
   than a museum of results.
5. **Untrusted search, trusted checking — recorded, not implied.**
   Provenance separates `conjectured_by` (which may be an LLM: the
   "conjectured-by" metadata anticipated in
   `docs/research/03-architecture/llm-integration-points.md`),
   `searched_by` (untrusted tools), and `checked_by` (trusted disposers).
   `scripts/check-claim-certificates.py` re-derives every `checked` row
   from the artifact using an independent in-file implementation, fails
   closed on families it does not understand, and for UNSAT certificates
   additionally requires the stored CNF to regenerate byte-identically
   from the claim parameters so a certificate cannot be laundered against
   the wrong instance.

## First population

The family `rado-colouring-a(x-y)=bz`
(`artifacts/claims/rado/`, semantics in
`artifacts/claims/rado/SEMANTICS.md`): 34 published Rado numbers
(Chang–De Loera–Wesley, arXiv:2210.03262) replicated with independently
replayed witnesses and drat-trim-verified DRAT certificates, plus the open
entry `R_4(2(x-y)=3z)` carried as a frontier claim with new
machine-verified lower-bound witnesses.

## Gates

- `scripts/validate-claims.py` — structural + referential + epistemic
  discipline; nonzero exit on any error.
- `scripts/check-claim-certificates.py` — semantic replay of every
  `checked` evidence row.
- `scripts/check-claim-negative-fixtures.py` — the validator must reject
  the three committed invalid fixtures with their expected diagnostics
  (`artifacts/fixtures/claims-invalid/`).

None of these is wired into `just check` yet; wiring is a follow-up once
the ledger design survives review.

## Consequences

- A future `math-education` surface can consume the ledger read-only (the
  `RC:mathematical-nexus` external-collection pattern: pinned commit,
  license status, per-resource concept anchor) without solver capability
  leaking into curricular scope.
- Scenario families, pack checks, and curriculum nodes gain a place to
  point when a learning artifact corresponds to a real frontier problem.
- The ledger is deliberately file-per-claim and append-preferred so
  parallel agent lanes can add claims without index contention; a
  generated dashboard can follow later.

## Alternatives considered

- **Extending the pack `check` record** — rejected: packs are pedagogical
  fixtures keyed to validation handlers; claims need epistemic status,
  frontier records, and cross-repo anchors that would bloat every pack.
- **New fields inside `math-education` concepts** — rejected: violates
  that repo's "solver capability stays separate from curricular scope"
  constraint and its authored/derived discipline.
- **A single ledger JSON file** — rejected: multi-agent write contention
  and unreviewable diffs; the repo's one-file-per-artifact convention wins.
