# ADR-2104: the classification axis was typed, the detail was three free strings, and the compiler names 25 of the counted 44

Status: accepted
Index-summary: ADR-2101 counted 44 producer sites putting a free-form `String` into a `DeclineReason` detail (`UnsupportedDetail` 11, `Budget` 16, `VerifierRejected` 17) and deliberately did not typify them. This lane does. `UnsupportedDetail`, `Budget` and `VerifierRejected` are now closed enums (`UnsupportedDetail::{Backend,IngestRefusal,OwnershipInconsistency}`, `Budget::{NiaRelaxationSliceExpired,NiaRefinementRoundCapReached,SquareCoefficientGuardExceeded,IntBoxEnumerationCapExceeded,Other}`, `VerifierRejected::{MbqiCandidateUnchecked,CoercionRelaxCouplingFailed,Backend,MbqiQuickReplayFailed,CasNormalFormDisagreement,CasDivisibilityCertificateFailed,CasIdealCombinationFailed,NiaRelaxationReplayFailed,NiaRefinementNoNewLemma,SquareWitnessReplayFailed,RealRelaxationSatDoesNotTransfer}`), each with an exhaustive `name()` (no wildcard arm) and a `Display` copied byte-for-byte from the site it replaces. Removing the `String`-accepting `DeclineReason` constructors and retyping the three variants' payload made rustc enumerate every production construction site: **25**, not 44 — the gap and why it differs is measured below, not asserted. `to_json`'s `"detail"` field renders identically (schema stays **2**); the route-trace byte-stability tests and `scripts/route_trace_reader.py`'s 12-test control suite pass unchanged. A new driven-producer suite, `tests/decline_detail_typed.rs`, constructs a real query for **5 of the 19** declared variants and asserts the *specific* variant the trail carries; the other 14 are named individually, by an exhaustive accounting match, with the technical reason they are not driven from a query — most are trust-anchor branches (a CAS refuter's or replay-checker's own two derivations disagreeing), the same shape ADR-2060 found undriveable for two of its six `SimplexDecline` producers. One mutation (`SUITES["typed-decline-detail"]`) makes `nia-square`'s coefficient-guard decline report the wrong `Budget` variant and kills exactly one named test. Fixed one anchor this lane's own edit went stale (`route-ownership-marker`, ADR-2100's suite, unrelated to this ADR's subject but broken by touching the same call site) — `--check-anchors` is `stale=0`.
Index-status: accepted
Date: 2026-09-15

## Context

[ADR-2101](adr-2101-the-trace-is-the-api.md) closed the completeness field, the
route-label vocabulary, and the reader — and named, without fixing, a fourth
gap: `DeclineReason::UnsupportedDetail`, `Budget` and `VerifierRejected` each
carry a free `String`. The *classification* axis (`reason` token, and `kind`
for `Incomplete`) is typed and survives to every consumer; the *detail* — which
sentence, from which of several distinct causes sharing one reason token — does
not. ADR-2101's own table:

| variant | free string? | src sites |
|---|---|---:|
| `Unsupported` | no | 14 |
| `NotApplicable` | no | 30 |
| `UnsupportedDetail(String)` | **yes** | 11 |
| `Budget(String)` | **yes** | 16 |
| `VerifierRejected(String)` | **yes** | 17 |
| `Incomplete(UnknownReason)` | kind typed, detail free | 15 |

44 = 11 + 16 + 17. ADR-2101 explicitly deferred this: "typifying the detail is
a compiler-enumerated refactor across the solver of the same size as ADR-2060's
own, which is a lane rather than a slice of one." This is that lane.

The method is ADR-2060's own, stated there as the reason a name-scan
under-reports: "the compiler is the only method that cannot under-report at
that level." Applied here: retype the payload, delete the `String`-accepting
path, and let every resulting compile error name a site.

## Decision

### 1. Three closed enums, one per detail

`UnsupportedDetail`, `Budget`, `VerifierRejected` — named to match the
`DeclineReason` variant they fill, the same convention `Decision::GaveUp(GaveUp)`
uses in `lra.rs`. Each has:

- an exhaustive `name()` (`&'static str`, **no wildcard arm** — a new variant
  fails to compile here until it is named);
- a `Display` whose text is the *exact* string the site used to construct,
  copied rather than retyped (rustfmt's `\`-continuation indentation bug
  ADR-2060 found is a reason to copy carefully, not a reason to skip it);
- a `String`-carrying catch-all **only** where the site's message is genuinely
  free text from a producer this crate does not compose sentences for — the
  same rule ADR-2060 used to keep `Incomplete`/`OutOfMemory` stringly ("these
  interpolate measured numbers... a closed set is what lets a test assert that
  every producer has a reason of its own without carrying a literal list to go
  stale against" — and conversely, where it does *not* interpolate, close it).

What each catch-all actually is:

- `UnsupportedDetail::Backend(String)` — a decider/backend's own
  `SolverError::Unsupported` message (the eleven-now-sixteen `auto.rs` sites
  behind `unsupported_decline`), plus `check_auto_explained`'s own terminal
  dispatch-error `Display` and MILP's own error — every one an external
  `Display`, not a sentence this crate composes.
- `UnsupportedDetail::IngestRefusal(String)` — the SMT-LIB front-door parser's
  own refusal message (`smtlib.rs`).
- `Budget::Other(String)` — the pass-through inside
  `DeclineReason::from_unknown`: a route returned `Unknown` with a budget-style
  `UnknownKind`, and the detail is that route's own, already-typed
  `UnknownReason::detail`. `Incomplete(UnknownReason)` is explicitly excluded
  from ADR-2101's 44 for the identical reason; `Budget::Other`'s payload comes
  from the same upstream type and gets the same exemption.
- `VerifierRejected::Backend(String)` — `uf-arith-lazy-overbound-pre-lia`'s
  `SolverError::Backend(detail)` arm.

Everything else is a named, payload-free (or, for two `UnsupportedDetail`
constructions built from a `format!` already in hand, a single pre-formatted
`String` field) variant: four `Budget` producers, ten `VerifierRejected`
producers, one `UnsupportedDetail` producer (`OwnershipInconsistency`, ADR-2100's
own marker text). Full per-variant list and Display text: `route_trace.rs`.

### 2. `record_route_refusal` (ADR-2100's ownership table) is touched at the construction site only

Two `auto.rs` sites construct `UnsupportedDetail::OwnershipInconsistency` from
an already-built `format!` string inside `record_route_refusal` and its sibling
non-decision reporter — both part of the route-ownership machinery ADR-2100
landed and the concurrent QUANT-LADDER-OWNERSHIP lane is extending. Per this
lane's own brief, the diff there is the `DeclineReason::UnsupportedDetail(...)`
constructor call only: the `match (route.kind(), route.ownership_of(query))`
arms, `route.owns()`, `route.label()` and the ownership table itself are
untouched.

### 3. The rustc count: 25, not 44 — and why

Deleting the `String`-accepting constructors and retyping the three payloads,
`cargo check -p axeyum-solver --lib --features full` named **25** distinct
production construction sites (13 in `auto.rs`, 4 in `nia_linearize.rs`, 2 in
`nia_square.rs`, 1 each in `int_real_relax.rs` and `smtlib.rs`, 4 in
`span_log.rs`'s `classify()` consumer, which reads every `DeclineReason`
variant's detail to build its own span record and so breaks on the same type
change as a producer would). `cargo check --lib --tests` then named 9 more —
all test-code constructions (`route_trace.rs`'s own unit tests, one
`span_log.rs` test, one `tests/unknown_reason_coverage.rs` assertion) — and
`--all-targets` on default features named 3 more in a downstream consumer,
`axeyum-bench/examples/diagnose_evidence.rs`, whose `decline_detail` helper
borrowed a `&str` field the three variants no longer share (fixed by rendering
through `Display` into an owned `String`, matching every existing caller's
logic via one shadow-bind).

**25 production sites, not 44.** Three things explain the gap, and none of
them is a missed site:

1. **`unsupported_decline(message: &str) -> DeclineReason` is one helper with
   sixteen call sites**, not sixteen constructions. ADR-2101's own doc comment
   on it says "eleven sites in this file matched `Err(SolverError::Unsupported(_))`"
   (now sixteen, measured fresh) — every one of those calls a function whose
   *signature* (`&str` in, `DeclineReason` out) did not change, so rustc has
   nothing to flag at the call site; only the helper's one-line body needed
   retyping. This is the intended shape, not an evasion: those sixteen sites
   share one classification (a backend's own opaque message) and one place to
   get it right is better than sixteen copies that could drift.
2. **`DeclineReason::from_unknown` is the same shape for `Budget`.** It is
   called from roughly thirty sites across the ladder (quantified rungs, NIA,
   NRA, EUF, MILP, ABV) that hand it an already-built `UnknownReason`; the
   funnel's own one-line `Budget::Other(reason.detail.clone())` construction
   is what changed, not its thirty callers.
3. **ADR-2101's per-file table (`auto.rs` 11, `span_log.rs` 6, …) counted a
   different, coarser unit than "one `DeclineReason::X(String)` construction
   per line".** Textually re-deriving it: `grep -c` for the bare variant
   names (`UnsupportedDetail(`, `Budget(`, `VerifierRejected(`) across
   `crates/axeyum-solver/` gives 12 / 13 / 17 total *occurrences*, which
   includes the enum definition, the `Display` impl, the JSON-render match
   arm, `from_unknown`'s internal construction, and unit-test fixtures — not
   only production constructors. `VerifierRejected`'s 17 matches the raw
   occurrence count exactly; `UnsupportedDetail`'s 11 is that count minus the
   enum's own definition line. `Budget`'s claimed 16 does not reconcile the
   same way against a raw occurrence count of 13 in this tree, and is, as far
   as this lane could re-derive, an overcount in the original table — restated
   here rather than silently corrected, per this lane's own brief ("if they
   differ, say which sites the ADR missed or double-counted").

So: **25 is this lane's verified, compiler-checked count of distinct
production `DeclineReason::{UnsupportedDetail,Budget,VerifierRejected}`
constructor call sites** (excluding the shared `unsupported_decline`/
`from_unknown` funnels' many callers, each of which is a call to an
already-typed function rather than a new construction). It is not a
re-derivation of ADR-2101's 44 by the same method; it is what the compiler
actually names once the type exists to enumerate against.

### 4. Byte-stability

`to_json`'s `"detail"` JSON member is rendered via `detail.to_string()`
(`Display`) rather than borrowing the old `String` field directly — the only
change to `render_json`. Every `Display` impl was written by copying the exact
string literal(s) the site it replaces used, so `to_json`'s output is
byte-identical for every existing pinned string. Verified:

- `every_outcome_variant_renders_its_documented_shape`,
  `detail_strings_are_json_escaped`,
  `default_to_json_is_unchanged_by_timing_support`,
  `an_unsupported_decline_with_a_message_renders_the_message` (all
  `route_trace.rs`) — unchanged assertions, green.
- `ROUTE_TRACE_JSON_SCHEMA_VERSION` stays **2** — no field added, removed or
  renamed, only the Rust type backing one JSON string member.
- `scripts/route_trace_reader.py` and its control suite
  `scripts/tests/test-route-trace-reader.py` — 12 of 12 pass unchanged; the
  reader parses JSON and never sees a Rust type.
- The 19 `dispatch/reason:` suites `hooks/pre-push` runs (read out of the hook
  by `bench-results/real-opaque-20260914/run-dispatch-reason-suites.sh`, not
  retyped) — all green, including `unknown_reason_coverage.rs`, which
  destructures `DeclineReason::UnsupportedDetail` directly and needed one
  constructor-site fix (wrap in `UnsupportedDetail::Backend`), no assertion
  text changed.

Ad hoc test placeholder text with nothing external pinning it (`"nodes"`,
`"replay"`, `"cnf-nodes=2000000"` in `route_trace.rs`'s and `span_log.rs`'s own
unit tests) is kept **uniform**, routed through the `Other`/`Backend`
catch-all rather than retyped into a named variant that would misrepresent
what those fixtures test (JSON rendering/escaping mechanics, not a specific
producer) — said here rather than left implicit.

### 5. Driven-producer coverage: 5 of 19, 14 named undriven

`crates/axeyum-solver/tests/decline_detail_typed.rs`. Five `#[test]`s each
construct an actual query (a `QF_UFDT` datatype goal, an unparseable script, an
oversized single-variable polynomial coefficient, a nonlinear two-variable
integer goal under a 1-nanosecond timeout, a nonlinear integer goal under a
1-millisecond timeout) and assert the trail carries the *specific* variant —
not merely that some decline happened.

| driven | how |
|---|---|
| `UnsupportedDetail::Backend` | `QF_UFDT` goal a native decider refuses by name |
| `UnsupportedDetail::IngestRefusal` | `"(assert ("` — unparseable at ingest |
| `Budget::SquareCoefficientGuardExceeded` | `a·x² > 5`, `a = 2^41`, over `nia-square`'s `2^40` guard |
| `Budget::NiaRelaxationSliceExpired` | `x·y=7 ∧ x+y=8` under a 1 ns timeout |
| `Budget::Other` | the `resource_capped_lia_records_budget` fixture, re-asserted against the typed variant |

Three exhaustive accounting functions (`unsupported_detail_account`,
`budget_account`, `verifier_rejected_account`; no wildcard arm) name, for every
one of the 19 declared variants, either the driving test or the reason it is
not driven here — checked by `every_typed_detail_variant_is_accounted_for`,
which constructs one instance of each variant and asserts the classification
is non-empty. The 14 undriven, by reason:

- **Trust-anchor branches (10):** `VerifierRejected::{MbqiCandidateUnchecked,
  MbqiQuickReplayFailed, CasNormalFormDisagreement,
  CasDivisibilityCertificateFailed, CasIdealCombinationFailed,
  NiaRelaxationReplayFailed, NiaRefinementNoNewLemma,
  SquareWitnessReplayFailed, RealRelaxationSatDoesNotTransfer,
  CoercionRelaxCouplingFailed}`. Each fires when a route replay-checks a
  candidate *it itself produced* and the check fails — reaching the decline
  from a query means constructing the underlying decider bug (a CAS refuter's
  two independent derivations disagreeing, an exact discriminant/rational-root
  witness that does not satisfy its own equation), the identical shape ADR-2060
  found for `SimplexDecline::{ModelDidNotReplay,CertificateFailedSelfCheck}`
  ("Two of those 27 are worth naming on their own... those are the two trust
  anchors of this entire route").
- **Adversarial-instance questions (2):** `Budget::NiaRefinementRoundCapReached`
  (needs 64 consecutive non-converging spurious relaxation models — a
  research question, not a query this lane assembled by hand) and
  `VerifierRejected::Backend` (a specific lazy-overbound sub-route's internal
  backend error, not reproducible from the public front door without
  reproducing that backend's own failure).
- **A three-stage internal chain (1):** `Budget::IntBoxEnumerationCapExceeded`
  needs `prove_int_box` to prove a box, the exact-bounded-box blast to *also*
  decline on it, and the box's case count to exceed the enumeration cap — three
  internal decisions to reverse-engineer rather than one query shape.
- **A concurrent lane's own surface (1):** `UnsupportedDetail::OwnershipInconsistency`
  fires only when a route's declared `Ownership::Complete` (auto.rs's ownership
  table, ADR-2100) disagrees with what it actually refused — a real
  ownership/behaviour mismatch is the bug the QUANT-LADDER-OWNERSHIP lane's own
  surface would construct, not a query shape this ADR owns.

### 6. Mutation

`SUITES["typed-decline-detail"]` (`scripts/tests/mutation_controls.py`): one
mutation, `nia-square`'s coefficient-guard decline reports
`Budget::NiaRelaxationSliceExpired` instead of
`Budget::SquareCoefficientGuardExceeded`. Run:

```
typed-decline-detail: baseline green, 6 tests
  nia-square's coefficient-guard decline reports the wrong Budget variant killed 1: budget_square_coefficient_guard_exceeded_is_driven_by_an_oversized_coefficient
```

Kills exactly the one test that pins that variant; the other four driven tests
and the accounting test are untouched, because they pin different producers
(`Budget::Other`, `Budget::NiaRelaxationSliceExpired` itself from a *different*
call site, `UnsupportedDetail::{Backend,IngestRefusal}`) or construct variant
instances directly rather than calling this producer.

Fixing this lane's own construction site broke a **different, pre-existing**
mutation: `SUITES["route-ownership-marker"]`'s "the inconsistency report on an
owning decider's refusal" anchored on
`record_route_refusal`'s `Ownership::Complete` arm as a single unbroken line;
ADR-2104 wraps that arm in a block and gives its payload a typed constructor,
so the anchor's *text* moved even though the arm's *behaviour* did not. Updated
the anchor's find/replace text to match the new two-line shape; the mutation's
intent (shadow the real arm with one that calls `unsupported_decline` instead)
is unchanged, and re-run confirms it still kills exactly the one test
(`auto::tests::an_owning_deciders_refusal_is_reported_and_a_declining_routes_is_not`)
its neighbour mutation already killed before this lane touched anything.
`--check-anchors`: **stale=0** (was 1, from this same site, immediately after
this lane's first commit — caught and fixed before the lane's own exit
criteria were checked).

## Consequences

- A consumer can now distinguish, by type, *which* budget gate or *which*
  verifier-rejection fired, not only that one did — Phase 3 (the outcome
  ledger, named in ADR-2101's consequences) inherits this rather than the
  string bug.
- The 14 undriven variants are a named, reasoned backlog, not an unexamined
  gap: ten are trust-anchor branches whose driving would require inducing the
  bug they exist to catch, matching ADR-2060's own experience.
- `Budget::Other` and `VerifierRejected::Backend`/`UnsupportedDetail::{Backend,
  IngestRefusal}` remain `String`-carrying by design — the same rule that keeps
  `Incomplete`/`OutOfMemory` stringly elsewhere in this taxonomy — and are not
  a residual "44 minus 25" of unfinished typing.

## Alternatives rejected

**One `DeclineDetail` enum shared across all three `DeclineReason` variants.**
Rejected: `UnsupportedDetail`, `Budget` and `VerifierRejected` have disjoint
producer sets and disjoint vocabularies (an ownership-inconsistency marker has
no analogue in a budget cap), and a single enum would need either a
reason-crossing wildcard (defeating the exhaustiveness guarantee) or three
sub-enums nested inside one wrapper — no simpler than three top-level enums,
and it would rename every existing `DeclineReason::Budget(String)` call site's
*type path* as well as its payload, widening the diff into `auto.rs`'s
ownership machinery for no additional safety.

**Force every `unsupported_decline`/`from_unknown` caller through a distinct
compiler-named site by changing the helpers' signatures.** Considered, to make
the rustc count closer to 44. Rejected: the sixteen `unsupported_decline`
callers and ~30 `from_unknown` callers genuinely share one classification each
(an opaque backend message; an already-typed `UnknownReason` pass-through), so
forcing sixteen or thirty near-identical edits would not add a real
distinction — it would inflate the compiler count without inflating the
information the trail carries, which is precisely the "dispatch table with one
entry" anti-pattern this repository's own discipline (evidence-and-checker-
discipline.md) warns against.

**Drive all 19 variants from a query, accepting whatever effort that takes.**
Rejected for the ten trust-anchor branches specifically: driving them means
constructing the decider bug the branch exists to report, which is not a test
of the *branch* but of whether the underlying decider can be broken — a
different, and separately valuable, project (fuzzing/differential testing of
each decider), not this ADR's.
