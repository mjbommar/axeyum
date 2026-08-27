# ADR-0604: Lean is the surface syntax; axeyum builds no parser

Status: accepted
Date: 2026-08-27
Index-summary: Axeyum never grows its own mathematical surface language or elaborator; statements are authored in Lean and arrive via a statement-only mode of the existing importer, producer contracts serve as the tactic layer, and results export back through lean_pp — Mathlib becomes an interface, not a competitor.
Index-status: accepted

## Context

Compared as SYSTEMS, Lean/Mathlib is five layers: surface language,
elaborator, tactic layer, kernel, retrieval. Axeyum's kernel layer is at
parity or stronger (independent re-validation, evidence artifacts, the
two-axis ledger); every layer above it is currently absent or ad hoc:
theorems are constructed by Rust code calling `IntDev` combinators, engines
(`ring_law_proof`, Farkas/SOS, the CAS, Sturm) have no uniform goal→engine
dispatch, and discovery is grep. The cost shows up as hundreds of lines of
Rust per stated theorem and 3,000-word lane briefs compensating by hand.

Meanwhile both halves of a Lean interface already exist: `axeyum-lean-import`
is a fail-closed lean4export importer (ADR-0350 identity manifests, staging
kernel, atomic publication) that today imports only complete proof streams;
and `lean_pp`/`render_lean` already render kernel declarations as Lean.

## Decision

1. **Axeyum never builds a mathematical surface language, parser, or
   elaborator.** Lean is the authoring surface. This is a permanent scope
   exclusion, not a deferral.
2. **The front door for mathematics is STATEMENT-ONLY IMPORT**: a mode of
   `axeyum-lean-import` that translates a declaration's TYPE through the same
   fail-closed path, admits nothing, and registers the result as an open goal
   (a ledger fact whose `formal.statement` is the kernel's own rendering of
   the imported type). Proof streams are discarded in this mode by
   construction. This turns the import backlog artifact (ADR-0601 §3) from a
   list into a work queue, and gives external users a way to pose goals
   without writing Rust.
3. **Producer contracts (ADR-0602) are the tactic layer.** A contract —
   "goals of this shape are dischargeable via route R" — is what a tactic is,
   with the difference that discharge produces checkable artifacts and a
   ledger receipt rather than ephemeral elaboration state.
4. **Results round-trip.** Anything admitted here is exportable via
   `lean_pp` with its identity manifest, so axeyum-verified, axiom-free,
   executable results are consumable FROM Lean. Mathlib is thereby an
   interface on both ends — statement source and result consumer — not a
   competitor to out-build.
5. **Constructivization is explicit, per ADR-0603**: an imported classical
   statement that is constructively unavailable is not silently weakened; it
   becomes the family's labeled import row plus, where proved, the boundary
   refutation and the strongest constructive form.

## Consequences

- "Properly using axeyum" acquires a definition: Lean statement in →
  contract dispatch → engine → kernel admission → ledger fact → Lean export.
  The missing segments are exactly (2) here and the running ADR-0602
  implementation; everything else exists at least in first-slice form.
- The importer needs one new mode, not a redesign; its fail-closed staging
  discipline applies unchanged (a malformed statement imports nothing).
- The congruence-deriver producer and environment retrieval are the two
  quality-of-life layers after that, in that order.
