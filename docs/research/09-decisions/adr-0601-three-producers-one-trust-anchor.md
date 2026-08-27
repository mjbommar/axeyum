# ADR-0601: Autogenesis, the CAS, and the import pipeline are producers behind one trust anchor

Status: accepted
Date: 2026-08-27
Index-summary: The kernel is the sole trust anchor; CAS certificates must reconstruct through it, imports are labeled scaffolding that never enter the headline, and autogenesis operations declare which producer route discharges them.
Index-status: accepted

## Context

Three capability stacks grew independently and each works in isolation:

- **Kernel lanes** prove theorems through `Kernel::add_declaration`; 505 ledger
  facts ride `kernel-lean`, all axiom-free.
- **The CAS** (`axeyum-cas`, G0–G18) computes over a decidable fragment, but its
  23 `cas-certificate` facts rest on the CAS's *own* normal form —
  `curriculum-gaps.md`: "the CAS-witness → Alethe/Lean bridge is undesigned;
  `equal` is a self-contained `MultiPoly` normal form, never lowers to the
  solver." The search half of "untrusted fast search, trusted small checking"
  currently ships without the checking half.
- **The import pipeline** (`axeyum-lean-import`, ADR-0350) is a fail-closed
  lean4export importer with staging and identity manifests. Five facts ride
  `imported-kernel-lean`; the validator counts a 164-item backlog of results
  settled elsewhere but not here. There is no systematic flow from that backlog
  to anything.
- **Autogenesis selection** is jammed in a way that shows the missing
  integration exactly: `fact-frontier.py` reports 141 dependency-ready facts and
  zero admissible, because operations exist only for already-settled kernel-lane
  work. The selector has no concept of a producer other than a kernel lane.

Measured 2026-08-27: 1,332 distinct kernel theorems, all axiom-free;
776 ledger facts, 0 validator errors.

## Decision

1. **One trust anchor.** A fact's evidence is *reconstructed* only when an
   independent checker with fail-on-absence semantics re-derives it, and for
   mathematical content that checker is `Kernel::add_declaration` (directly, or
   via a checker that consults the kernel environment). The CAS, the solver
   stack, and the importer are producers of *candidates and hints*, never of
   trust.

2. **CAS certificates reconstruct or say so.** The `cas-certificate` route
   splits observably: evidence that reconstructs through the kernel (the bridge,
   starting with the polynomial-identity slice landing against
   `Complex.polyEval`/`polyMul`) versus evidence that terminates in the CAS's
   own normal form. The validator must distinguish these; a fact of the second
   kind is honest but is not `checked` in the sense the headline uses, and the
   ledger must not let the two read identically. Existing facts are not
   deleted; they are re-labeled as the bridge reaches their class.

3. **Imports are scaffolding, labeled, never headline.** The importer's roles
   are: (a) trusted *statements* — targets the constructive library aims at;
   (b) reference proofs for study; (c) dependency scaffolding for search. An
   imported fact keeps `imported-kernel-lean`, keeps its (typically classical)
   axiom footprint visible, and is excluded from every axiom-free and
   originated count — which the validator already does structurally; this ADR
   makes it a stated invariant rather than an accident. The 164-item backlog
   becomes a produced artifact: external-proved × epistemically-open ×
   curriculum-reachable, ordered by the curriculum DAG, consumable by the
   selector as import candidates.

4. **Autogenesis operations declare their route.** An operation names the
   producer that discharges it — `kernel-lane`, `cas-bridge`, or `import` — and
   admissibility is dependency-readiness × a registered operation × that
   route's capability actually existing. This is what makes the CAS and the
   importer first-class citizens of the flywheel instead of side channels, and
   it is the structural fix for a selector that could only ever see one kind of
   work.

5. **Capability docs state what ships.** The decidability map and CAS docs must
   distinguish shipped routes from planned ones; the two known overstatements
   (`real_algebraic.rs`, which does not exist, cited as the algebraic-number
   route; primality tagged ECPP/Pratt over a deterministic Miller–Rabin
   implementation) are corrected alongside this ADR.

## Consequences

- The Pareto position against classical libraries becomes stateable: on every
  fact we ship, the kernel checked it; certified-CAS artifacts and
  self-extension are axes with no counterpart; breadth is conceded and covered
  by labeled imports.
- The bridge inherits a measured risk: one concrete degree-2 kernel check cost
  ~356 s today. Route 2's viability at scale is an open measurement, and the
  bridge work is required to report its cost curve, not just its correctness.
- `fact-frontier.py`, the operation schema, and `validate-facts.py` each need
  a bounded change; none is speculative — each closes a gap this ADR names.
