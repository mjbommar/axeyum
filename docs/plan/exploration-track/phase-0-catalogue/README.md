# Phase 0 — the bridge catalogue as data

Verdict from review: **needs revision.** The idea is sound and well-precedented;
three of its premises were factually wrong. See
[`00-review-synthesis.md`](../00-review-synthesis.md) corrections 1 and 2.

## Goal

Turn the composition space that is currently compiled into
`crates/axeyum-solver/src/auto.rs` into a validated, machine-readable artifact,
**generated from Rust and golden-tested** — never hand-transcribed.

## What the reviews corrected

1. **Edge identity is the route attempt, not `fragment → fragment`.** Dispatch is
   conditioned on the 10-flag `Features` vector (`auto.rs:7171-7191`), opaque
   Rust shape probes returning `Option`, config flags, and a *runtime* cost
   measurement (`reduction_shrinks_encoding`, `auto.rs:1519-1550`). The
   `bv2nat-blast` guard (`auto.rs:3026-3031`) describes roughly QF_BVLIA, which
   has no atlas row. Atlas fragment ids are advisory annotations, not keys.
2. **There are no RouteTrace logs to replay.** `RouteTrace` has no serde, is never
   persisted by `axeyum-bench`, and does not cover the quantifier pipeline in
   `solve()`. Validation must be re-run based.
3. **The 14 `TrustId`s are neither necessary nor sufficient.** 45 route labels
   exist; a dozen reductions carry no `TrustId`; four `TrustId`s
   (`SatRefutation`, `Farkas`, `Sos`, `Diophantine`) are terminal certificates,
   not edges. `trust_ids` is a cross-reference field.

## Design

**Single source of truth: a Rust route registry.** New
`crates/axeyum-solver/src/route_registry.rs` holding `RouteMeta` records with
`label`, `phase`, `kind`, `order_index`, `requires`/`forbids` feature masks,
named opaque `probes`, `config_gates`, `dynamic_gates`, `verdicts`,
`sat_transfer`, `unsat_transfer`, `walk_back`, `trust_ids`, `source_fragments`,
`target`, and `reference`.

The coupling trick that makes extraction complete: **recorder call sites take
their label from the registry const** (`ROUTE_QF_BV.label`), so a route cannot
exist in dispatch without a registry entry — the compiler enforces coverage. In
the interim, a unit test asserts every literal passed to `record_*` in `auto.rs`
appears in `ALL_ROUTES`.

**The artifact:** `artifacts/ontology/bridge-catalogue.json` +
`bridge-catalogue.schema.json`, rendered deterministically by
`bridge_catalogue_json()`.

Key vocabulary decision: `soundness` splits **per verdict direction** —
`{sat_transfer, unsat_transfer}` — which is the machine-readable
over/under-approximation label phase 1 formalizes. An unsat-only refuter is
`{sat: none, unsat: exact}`; a sound relaxation is
`{sat: replay-checked, unsat: sound-relaxation}`.

Do **not** build a guard DSL rich enough to express `blast_bv2nat_linear` or
`reduction_shrinks_encoding`. Named opaque probe references only; a re-encoded
guard is a second implementation with its own soundness surface and it will drift.

## Validation, three layers

1. **Structural (Python)** — `scripts/validate-bridge-catalogue.py`,
   dependency-free, mirroring `scripts/validate-smt-fragment-atlas.py`: schema
   keys, closed enums, unique ids, `order_index` unique per phase,
   `source_fragments ⊆` atlas row ids, `trust_ids ⊆` the 14 ledger labels, local
   `sources` paths exist, and soundness-consistency rules. Wire into
   `just foundational-resources`.
2. **Golden (Rust)** — `tests/bridge_catalogue.rs` asserts
   `bridge_catalogue_json() == committed file`. The artifact cannot drift from
   the code. This is the `trust_ledger_markdown` pattern (`trust.rs:343-387`).
3. **Behavioral replay (Rust)** — re-run `check_auto_explained` over the LCG
   corpus builders in `tests/route_trace.rs` plus the committed corpus; check
   that every attempted label is in the catalogue, that attempt order is a
   **subsequence** of `(phase, order_index)`, that every `Decided` verdict is
   permitted by the edge's `verdicts`, and that attempted routes' guards held.
   Plus a mutation fixture: perturbing one `order_index`/`forbids` bit must make
   the validator fail.

## What replay validation can and cannot claim

**Can:** the catalogue's order, guards, and verdict capabilities are consistent
with observed dispatch on the exercised corpus.

**Cannot:** routes the corpus never exercises (report edge-coverage %), and
over-strong `forbids` (invisible under subsequence semantics — mitigated by
generating guards from the same registry the code uses, plus per-route fixture
pins in the style of `tests/route_trace.rs:299-504`).

Two additive changes are prerequisites for teeth: a JSON rendering of
`RouteTrace`, and a `depth`/`context` marker on attempts recorded inside
`dispatch_reduced`'s re-entry (`auto.rs:1566`) so reduced-query attempts are not
misattributed to the original query's guard check.

## Prior art worth reading before starting

- **Why3 transformations + drivers** — the closest analogue: named transformation
  registry in code, composition as *data* referencing names, `why3 show
  transformations` introspection. <https://why3.org/doc/technical.html>
- **Z3 tactics/probes/`check-sat-using`** — the probe/tactic split maps onto
  `Features::scan_within` vs route. Cautionary: no soundness-direction metadata,
  implicit model conversion. <https://microsoft.github.io/z3guide/docs/strategies/tactics/>
- **cvc5 preprocessing pass classification** (normalization / simplification /
  reduction). `trust.rs` already mirrors cvc5's `TrustId`.
- **Lean Aesop** — rule sets as data with `safe`/`unsafe`/`norm` labels and
  success probabilities driving search. <https://github.com/leanprover-community/aesop>
- **FastSMT** — proof that a searched policy over a tactic space works and yields
  an interpretable artifact; it needed the space enumerable first, which is
  exactly this phase. <https://github.com/eth-sri/fastsmt>

## Tasks

| id | title | size |
|---|---|---|
| [T0.1](T0.1-route-trace-json-export.md) | RouteTrace JSON export + bench persistence | S |
| [T0.2](T0.2-route-registry.md) | Route registry (`ALL_ROUTES`) + coverage test | M |
| [T0.3](T0.3-catalogue-artifact.md) | Catalogue artifact, schema, structural + golden validators | M |
| [T0.4](T0.4-behavioral-replay-validator.md) | Behavioral replay validator | M–L |
| [T0.5](T0.5-soundness-direction-audit.md) | Per-edge soundness-direction audit + ADR | M |
| [T0.6](T0.6-coverage-expansion.md) | Trace coverage for `solve()` preamble + quantifier routes, plus a `solve_explained` entry point — **prerequisite of T0.1's bench half** | L |
| [T0.7](T0.7-measured-cost-model.md) | Measured cost model from bench artifacts | M |

## Exit criteria for the phase

`just foundational-resources` validates the catalogue; the golden test pins it to
the registry; the replay validator passes on the LCG and committed corpora with
edge coverage reported; the mutation fixture proves the validator has teeth.

## Scope discipline

**This phase is descriptive.** Making `check_auto` *read* the catalogue changes a
soundness-critical component's control flow and is phase 3, behind its own ADR
with a byte-identical-`RouteTrace` gate.
