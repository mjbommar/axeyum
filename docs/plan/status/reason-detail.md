# Lane: reason-detail — the 44 free-string DeclineReason detail sites got the ADR-2060 treatment

<!-- plan-section: lane-status -->

**Lane reason-detail (`DONE`, reason-detail, 2026-09-15).** Phase 3 dependency
named by [ADR-2101](../../research/09-decisions/adr-2101-the-trace-is-the-api.md)
("this ADR did not typify [the 44 free-string sites]... typifying the detail is
a compiler-enumerated refactor... which is a lane rather than a slice of one"),
closed by [ADR-2104](../../research/09-decisions/adr-2104-typed-decline-detail.md).
`DeclineReason::{UnsupportedDetail,Budget,VerifierRejected}` now carry closed,
named enums instead of a free `String`. Also closed the two other Item 2
targets: registered the three orphan control suites
`check-control-registration.sh` had flagged.

Branch base: `git merge-base main HEAD` is `7d922fe58` (ROUTE-OWNERSHIP,
ADR-2100), local `main`'s HEAD when this lane's worktree merged it.

## What changed

Three new enums in `route_trace.rs`: `UnsupportedDetail`
(`Backend`/`IngestRefusal`/`OwnershipInconsistency`), `Budget`
(`NiaRelaxationSliceExpired`/`NiaRefinementRoundCapReached`/
`SquareCoefficientGuardExceeded`/`IntBoxEnumerationCapExceeded`/`Other`),
`VerifierRejected` (ten named producers plus `Backend`). Each has an exhaustive
`name()` (no wildcard arm) and a `Display` copied byte-for-byte from the site
it replaces. The three `String`-accepting `DeclineReason` constructors are
gone; `cargo check` names every production construction site.

`crates/axeyum-bench/examples/diagnose_evidence.rs`'s `decline_detail` helper
changed `Option<&str>` → `Option<String>` (the three variants no longer share
a borrowable `String` field); every caller shadow-binds `.as_str()` so its own
logic is unchanged.

New `crates/axeyum-solver/tests/decline_detail_typed.rs`: five tests drive a
real query to a specific typed variant; an exhaustive accounting match names
the technical reason for each of the other 14 (mostly trust-anchor branches
where driving the decline means constructing the decider bug it exists to
report).

New `SUITES["typed-decline-detail"]` in `scripts/tests/mutation_controls.py`;
fixed one pre-existing anchor (`route-ownership-marker`) this lane's own edit
to `record_route_refusal` went stale.

`scripts/check.sh` gained three `step` lines: `holdout-price-controls`,
`parity-nonverdict-classifier`, `producer-channel-controls`.

## Numbers

| | |
|---|---|
| ADR-2101's claimed free-string producer sites | 44 (`UnsupportedDetail` 11, `Budget` 16, `VerifierRejected` 17) |
| rustc-enumerated production construction sites, this lane | **25** (13 `auto.rs`, 4 `nia_linearize.rs`, 2 `nia_square.rs`, 1 `int_real_relax.rs`, 1 `smtlib.rs`, 4 `span_log.rs` consumer) |
| gap explained by | shared helpers (`unsupported_decline` 16 callers, `DeclineReason::from_unknown` ~30 callers) whose signature did not change, plus an apparent overcount in ADR-2101's `Budget` figure (13 raw occurrences in this tree, not 16) |
| declared typed-detail variants | 19 (3 `UnsupportedDetail` + 5 `Budget` + 11 `VerifierRejected`) |
| driven by a constructed query | **5** |
| undriven, named with a reason | **14** (10 trust-anchor, 2 adversarial-instance, 1 three-stage internal chain, 1 concurrent lane's surface) |
| `to_json` schema version | unchanged, **2** |
| byte-stability tests (`route_trace.rs`) | green, unchanged assertions |
| `route_trace_reader.py` control suite | 12/12, unchanged |
| `dispatch/reason:` suites (`hooks/pre-push`, read not retyped) | **19/19** green |
| mutation: `typed-decline-detail` | kills exactly 1 named test |
| mutation anchors, `--check-anchors` | stale=0 |
| orphan control suites (`check-control-registration.sh`) | 3 → **0** |

## What this lane did not do

- Did not force the sixteen `unsupported_decline` callers or the ~30
  `DeclineReason::from_unknown` callers through individually-typed
  constructors — they share one classification each and forcing per-site
  distinctions would inflate the compiler count without adding information
  the trail carries (see ADR-2104 §"Alternatives rejected").
- Did not attempt to drive the ten trust-anchor `VerifierRejected` branches
  from a query: doing so means constructing the underlying decider bug each
  branch exists to report, a differential/fuzzing project of its own.
- Did not touch `auto.rs`'s ownership table or the `q:*` rung dispatch beyond
  the `DeclineReason` constructor call sites rustc named (QUANT-LADDER-OWNERSHIP's
  surface).
- Did not investigate the pre-existing duplicate ADR numbers `0166`/`0167`
  surfaced by `gen-adr-index.py`'s `duplicate_numbers=` field — unrelated to
  this lane's diff, present on the merge base already.
