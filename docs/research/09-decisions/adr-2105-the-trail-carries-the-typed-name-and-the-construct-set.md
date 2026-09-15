# ADR-2105: the trail carries the typed name and the construct set — two members ADR-2102 named and left undone, both closed by moving `features` off a process-global onto the trace itself

Status: accepted
Index-summary: The two gaps ADR-2102 named as "left undone" and did not fix: `route_trace.rs`'s `to_json` wrote `detail` but no `name` member, so `decline_names` was empty on all 220 of ADR-2102's own ledger rows; and `features` lived in a process-global `AtomicU32` (`route_ownership::LAST_QUERY_CONSTRUCTS`) read by a separate `; features` prose line, the exact "instrument reports through a string, consumer reads it with a grep" shape ADR-2101 closed for everything else. Both are now trace members. `RouteTrace::to_json` emits a per-attempt `"name"` beside `"detail"` for the three ADR-2104 typed-detail variants (`UnsupportedDetail`/`Budget`/`VerifierRejected`), and a top-level `"features"` member — moved onto `RouteTrace::record_features`/`RouteTrace::features`, first writer wins, with `RouteTrace::absorb` preserving the same rule across a merge. `auto.rs`'s `route_ownership` module loses `LAST_QUERY_CONSTRUCTS`, `record_query_constructs` and `reset_query_constructs`; its one call site in `check_auto_dispatch_inner` now hands the rendered construct set straight to the recorder already threaded through dispatch (`with_recorder`), which is a no-op for every NESTED sub-solve — the exact population the old global's own doc comment worried about overwriting the outermost scan. First-writer-wins is proven end to end by a quantified query (`∀x:Int. x <= x` — valid, proven by a sub-solve that scans `{Int}` but runs with no recorder at all — plus an unrelated `y:Real > 0`) whose one genuinely-outermost dispatch scans `{Real}`; the recorded `features` is `"Real"`, never `"Int"`. Schema bumped 2 → 3 (two new members, same "adding is not a rename but bump anyway" rule ADR-2101's own bump to 2 used). `scripts/route_trace_reader.py` accepts schema 1/2/3, exposes `Attempt.name` (already wired, now populated) and the new `RouteTrail.features`; `scripts/outcome_ledger.py`'s `features_from_capture` reads the JSON member from schema 3 on and falls back to the `; features` prose line otherwise, so a committed schema-1/2 sweep stays readable without a re-run. Byte-stability tests extended, not loosened: every existing pinned literal keeps its bytes, `schema_version` reads `3`, and new members appear only where a producer actually recorded one.
Index-status: accepted
Date: 2026-09-15

## Context

ADR-2102 (the outcome ledger) shipped `decline_names` as a column and named,
without fixing, exactly why it would be empty on every row it could measure:

> `decline_names` is EMPTY on all 220 rows because `route_trace.rs`'s
> `to_json` does not emit a `name` member yet — that producer change is the
> trace lane's surface and is named as remaining work, with the reader path
> driven by a fixture so the column is not unfalsifiable.

The same ADR also introduced `features`, and shipped it the way ADR-2101's
own plan describes as the shape five instruments failed in the week before
it: a process-global (`route_ownership::LAST_QUERY_CONSTRUCTS`, a
compare-exchanged `AtomicU32`) written deep inside the dispatcher, read back
by `smtcomp_cli` as a *separate* `--trace` line (`; features …`), and parsed
a second time by `scripts/outcome_ledger.py`'s `features_from_stdout`. That
is the instrument-reports-through-a-string, consumer-reads-it-with-a-grep
shape ADR-2101 closed for `partial` and the 32 route labels — `features`
just hadn't been migrated yet, because at the time `RouteTrace` had no way to
receive it: every dispatch call already threads a
[`Recorder`](../../../crates/axeyum-solver/src/route_trace.rs), but nothing
routed the construct scan through it.

This lane closes both gaps, on the trail's own wire format.

## Decision

### 1. A per-attempt `name` member, for the three ADR-2104 typed details

`RouteTrace::render_json`'s three typed-detail arms
(`DeclineReason::UnsupportedDetail`, `Budget`, `VerifierRejected`) now emit
`"name":<detail.name()>` immediately after `"reason"`, before `"detail"`:

```json
{"route":"lia-dpll","outcome":"declined","reason":"budget",
 "name":"nia-relaxation-slice-expired","detail":"…"}
```

`detail` is unchanged — this is additive, and `Unsupported`, `NotApplicable`
and `Incomplete` (whose classification already has a home: the bare reason
token, and `kind` for `Incomplete`) carry no `name` member, matching
ADR-2104's own scope. `Attempt.name` in `route_trace_reader.py` was already
wired to read this member (`obj.get("name")`) — ADR-2101 anticipated the
field and left it unpopulated on purpose, calling it out as a fixture-driven
column ahead of its producer. It is populated now.

### 2. `features` moves onto the trace

`RouteTrace` gains a `features: Option<String>` field, already rendered to
its wire form (`"Int|Real"`, or `"none"` for an empty set) rather than a raw
`ConstructSet` — `route_trace.rs` stays independent of `auto`'s construct
vocabulary, the same boundary `detail` already respects for every other
producer's message.

* `RouteTrace::record_features(rendered)` sets it **only when still `None`**
  — first writer wins, within one trace.
* `RouteTrace::features() -> Option<&str>` reads it.
* `RouteTrace::absorb` merges the same way: `self.features` stays if already
  `Some`, otherwise takes `other.features.clone()`. This is what makes the
  rule survive a merge, not only a single dispatch — a SECOND
  genuinely-outermost dispatch sharing one thread's attribution (the front
  door's post-dispatch second chances) must not silently replace the file's
  first-scanned construct set.
* `render_json` emits `"features":<rendered>` right after the `partial`
  block and before `attempts`, present exactly when `Self::features` is
  `Some` — the same "present exactly when there is something to say" rule
  `detail` already follows on an attempt. Absent (schema ≥ 3) is the CLI's
  `not-dispatched`; `Some("none")` is a real, different answer (the scan ran
  and found nothing).

`auto.rs`'s one call site (`check_auto_dispatch_inner`, right after
`let query = features.constructs();`) changes from

```rust
route_ownership::record_query_constructs(query);
```

to

```rust
with_recorder(rec, |t| {
    t.record_features(route_ownership::render_query_constructs(query));
});
```

`route_ownership` loses `LAST_QUERY_CONSTRUCTS`, `record_query_constructs`
and `reset_query_constructs` (and the now-dead `ConstructSet::bits`/
`from_bits` the static alone used); `render_query_constructs` — the pure
rendering function, already split out from the global read specifically so
it was testable without touching a process-global — is kept unchanged and is
now the ONLY thing `check_auto_dispatch_inner` calls.

### 3. Why moving the write to the recorder gives first-writer-wins almost for free

The old global's own doc comment worried about "a later sub-solve" as the
threat to first-writer-wins, and used a compare-exchange to guard against it
regardless of *who* asked to write. Tracing the call graph this lane's brief
asked for:

* A NESTED dispatch — a route's own `check_auto` call made while
  `route_trace::with_outermost_dispatch` is already `true` for an enclosing
  frame, or while `solve`'s `NestedDispatchGuard` (armed for the span of the
  quantified ladder) is up — takes `check_auto`'s "thin wrapper" path,
  `check_auto_with_recorder(…, &mut None)`. `rec` is `None`. `with_recorder`
  is then a no-op by construction: the sub-solve's `Features::scan_within`
  still runs (it always did — the dispatch ladder needs it regardless of
  telemetry), but there is no trace to hand the rendering to.
* Every recursive `check_auto_dispatch`/`check_auto_dispatch_inner` call
  that reuses the SAME `rec` (the preprocessing-reduced retry, the
  coercion-relaxed retry, the MILP-declined-then-relaxed retry — three sites
  in `auto.rs`, all inside `check_auto_inner`) is reached from exactly one
  of three mutually exclusive branches of one `match`, so at most one of
  them ever calls `check_auto_dispatch_inner` per top-level
  `check_auto_with_recorder` invocation.

So in the current call graph, a genuinely-outermost, recorder-bearing
dispatch writes `features` **at most once** per trace it owns, and every
nested sub-solve is structurally unable to write at all — first-writer-wins
is a property of the call graph, not of an atomic. `RouteTrace::absorb`'s
own first-writer-wins rule is the part of the OLD guarantee that is not
automatic this way: it is what protects a trace from a **second**
genuinely-outermost write reaching it later (a scenario the current call
graph does not exercise today, but the front door's documented "seven
post-dispatch string second chances" could), so it is implemented and
tested directly rather than left to accident.

### 4. Proof: an end-to-end quantified query, not only a unit test

`crates/axeyum-solver/tests/route_trace.rs::quantified_valid_universal_sub_solve_does_not_own_the_recorded_features`
constructs `∀x:Int. x <= x` (valid — its negation `c > c` over a fresh
constant is UNSAT by plain LIA) plus an unrelated `y:Real > 0`, with
preprocessing off (so word-level reduction cannot eliminate the `Real`
conjunct before the one recorded scan runs). `quant_valid_universal
::eliminate_valid_universals`'s validity sub-check dispatches `¬body[x:=c]`
— construct scan `{Int}` — through plain `check_auto`, nested under `solve`'s
armed `NestedDispatchGuard`: `rec` is `None`, so this scan is never even
offered a trace to write to. Once the universal is proven valid it is
rewritten to `true`; the residual `[true, y > 0]` carries no more
quantifier, so the ladder disarms and dispatches it as the one genuinely
outermost `check_auto` this whole solve ever makes — scan `{Real}`. The
test asserts the recorded `RouteTrace::features()` is `Some("Real")`: not
`"Int"`, not a merge of both, and not absent. A companion pair of pure unit
tests (`route_trace.rs`'s own `json_tests` module,
`record_features_is_first_writer_wins_within_one_trace` and
`absorb_preserves_the_first_recorded_features`) pin the mechanism directly,
independent of the dispatcher.

### 5. Schema 2 → 3

`ROUTE_TRACE_JSON_SCHEMA_VERSION` bumped to `3`. Same rule ADR-2101's own
bump to `2` used: adding a member is not a rename or removal by the
constant's own stated rule, and the bump is the whole point anyway — without
it a reader cannot tell a v2 object (no `name`/`features` member, and
therefore no way to ask) from a v3 object that states `features` absent on
purpose (`not-dispatched`, a real answer). Every byte-stability test in
`route_trace.rs` and `tests/route_trace.rs` was extended to the new schema
number and, where the fixture used a typed-detail decline, the new `name`
member — no assertion was loosened; every previously-pinned byte is still
pinned, plus what is new.

### 6. The reader, and the ledger

`scripts/route_trace_reader.py`:

* `KNOWN_SCHEMA_VERSIONS` gains `3`.
* `Attempt.name` (already declared, reading `obj.get("name")`, per ADR-2101's
  own forward-looking design) is populated by a real schema-3 capture for the
  first time.
* `RouteTrail.features: str | None` is new, read from `obj.get("features")`.
  Its own docs say plainly what its `None` does and does not mean: below
  schema 3, or with no trail at all, `None` means "cannot be asked" (the
  member does not exist); at schema 3 or above, `None` means the JSON stated
  it — the real `not-dispatched` answer. A caller has to check
  `schema_version` beside the value, the exact discipline `partial_source`
  already enforces for `partial`.
* The module docstring's "Schema versions" section, and the CLI's row output
  (`_COLUMNS`/`_row`), were extended to match.
* Its control suite (`scripts/tests/test-route-trace-reader.py`) gained three
  schema-3 fixtures (`V3_COMPLETE`, `V3_NOT_DISPATCHED`, `V3_PARTIAL`) and
  three tests; the freshness control
  (`test_the_fixtures_match_the_rust_renderer_bytes`) was repointed at the
  CURRENT (schema-3) pinned bytes in `route_trace.rs` — the schema-1/2
  fixtures stay as frozen examples of a historical wire format this reader
  still promises to read, with nothing live left in `route_trace.rs` for
  them to stay fresh against. 15 of 15 tests pass (was 12).

`scripts/outcome_ledger.py`:

* `features_from_capture(trail, text)` is the new entry point:
  `trail.features` when `trail.schema_version >=
  FIRST_SCHEMA_WITH_FEATURES_MEMBER` (`= route_trace_reader
  .FIRST_SCHEMA_WITH_NAME_AND_FEATURES`, re-stated as its own constant
  rather than imported as a bare int, so a reader-side schema bump the
  ledger's mapping did not follow is a visible constant question rather than
  a silent divergence), else `features_from_stdout(text)` — the prose
  fallback, kept verbatim and re-documented as exactly that: a fallback, not
  the primary source it used to be.
* `row_from_capture` now computes `features` AFTER the trail lookup (it used
  to run before it, when the only source was the stdout text) — which
  source answers depends on the trail's schema.
* `decline_names` needed no code change: it already read `a.name` off the
  reader's `Attempt`, driven only by a fixture until this lane (per ADR-2102
  itself). It is populated by a real capture now too.
* Its control suite (`scripts/tests/test_outcome_ledger.py`) moved its
  `_trail_line` fixture helper's default to schema 3 (`schema_version=3`,
  with an optional `features=` member) and added a `schema_version=2`
  override. **One test is deliberately kept on schema 2**
  (`CaptureToRow.test_the_four_features_answers_stay_apart`), the ONE
  retained proof that a committed schema-1/2 sweep's `features` still comes
  from the `; features` prose line. A new adversarial test,
  `test_schema_3_features_come_from_the_json_member_not_the_prose_line`,
  attaches a prose line that states the OPPOSITE of each row's JSON member
  and asserts the JSON member wins — a regression that read prose first
  would not have been caught by any pre-existing test, since none of them
  made the two disagree on purpose. 44 of 44 tests pass (was 43).

`python3 -m py_compile` is clean on all four touched Python files.

## Measurements

### Positive control: a real capture from ADR-2102's own ledger population

Two files from `bench-results/ledger/`, run through `scripts/ledger-run-one.sh`
against this lane's own release build (`cargo build --release -p axeyum-bench
--example smtcomp_cli`, commit `4856a56de`), appended to a fresh sweep and
printed with `outcome_ledger.py show`.

The first, `UFLIA/boogie/FormulaTerm_plus-noinfer_2.smt2` (from
`t1-uflia-20260915.tsv`), decides in 3 attempts with one payload-free
`not-applicable` decline — `features=not-dispatched` (the ladder's own EGRAPH
rung decided it before the quantifier-free ladder was ever reached, ADR-2100's
common case) and `decline_names` empty, because `NotApplicable` carries no
typed name by design. Not the positive control by itself, but the honest
negative half: a value can be a real, non-`ABSENT` answer (`not-dispatched`)
while still carrying no typed name, and the row shows exactly that
distinction rather than hiding it.

The second, `QF_LRA/2017-Heizmann-UltimateInvariantSynthesis
/_array1.i_3_2_2.bpl_11.smt2` (from `qflra93-20260915.tsv`, ADR-2045's
undecided-`QF_LRA` population), is the positive control: **both columns
non-empty**.

```
sweep_id: trail-wire-adr2105-evidence
arm: A
corpus_path: QF_LRA/2017-Heizmann-UltimateInvariantSynthesis/_array1.i_3_2_2.bpl_11.smt2
binary_sha: 4856a56de
features: Real
verdict: unknown
exit_status: 0
decided_by: none
bound_by: nra
attempts: 14
partial: no
decline_reasons: dl-online=not-applicable|nra-real-root=not-applicable|nra=incomplete|
  fd:string-gate=budget|fd:source-string-semantic-unsat=budget|fd:word-route=budget|
  fd:online-string=budget|fd:membership=budget|fd:lex-order=budget|fd:length-lia=budget|
  fd:source-string-sat-probe=budget|fd:bounded-completeness-unsat=budget
decline_names: (empty)|(empty)|(empty)|other|other|other|other|other|other|other|other|other
```

`features=Real` (the LRA scan, non-empty and not `not-dispatched`) and 9 of
12 `decline_names` entries are `other` — `Budget::Other`, the
`DeclineReason::from_unknown` pass-through the eight post-dispatch string
second-chance stages hit after the reduced solve's own `nra` decline. The
first three declines (`dl-online`, `nra-real-root`, `nra`) carry no name
because `not-applicable` and `incomplete` are not typed-name variants — the
same honest distinction the first row shows, now sitting beside real typed
names in one row. This is the exact shape ADR-2102 shipped empty on all 220
of its own rows.

### Byte stability

`cargo test -p axeyum-solver --lib --features full route_trace`: 25 of 25
(json_tests, partial_tests, route_enum_tests — was 21, +4 for the new
`features` tests). `cargo test -p axeyum-solver --features full --test
route_trace`: 13 of 13, including
`quantified_valid_universal_sub_solve_does_not_own_the_recorded_features`,
`verdict_invariance_over_lcg_corpus` and `trace_is_deterministic_across_runs`.
`cargo test -p axeyum-bench --example smtcomp_cli`: 21 of 21. `cargo test -p
axeyum-solver --features full --test decline_detail_typed`: 6 of 6. `cargo
test -p axeyum-solver --features full --test corpus_regression`: 2 of 2. The
19 `dispatch/reason:` suites `hooks/pre-push` runs
(`bench-results/real-opaque-20260914/run-dispatch-reason-suites.sh`): all
green. `cargo check -p axeyum-solver -p axeyum-bench --all-targets` on
DEFAULT features: clean.

### Mutation

`SUITES["trail-typed-name-and-features"]`
(`scripts/tests/mutation_controls.py`): one mutation, `to_json`'s
`UnsupportedDetail` arm emits a wrong hardcoded `name` instead of
`detail.name()`. Kills exactly
`route_trace::json_tests::an_unsupported_decline_with_a_message_renders_the_message`
and nothing else — the other pinned-literal tests (`every_outcome_variant
_renders_its_documented_shape`, `default_to_json_is_unchanged_by_timing
_support`, `detail_strings_are_json_escaped`) pin a `Budget`/`VerifierRejected`
`name`, not an `UnsupportedDetail` one, so they are untouched by this
specific arm. `--check-anchors`: stale=0.

## Consequences

* `decline_names` and `features` are populated columns on every new ledger
  row, not fixture-driven placeholders — ADR-2102's own committed 220 rows
  stay schema-1/2 (unaffected; still readable) and every sweep from here
  on gets both for free.
* The process-global `route_ownership::LAST_QUERY_CONSTRUCTS` is gone; a
  process that dispatches many queries (a test binary, a library embedding)
  no longer has ANY cross-query leakage risk on this axis, because the value
  now lives on the `RouteTrace` object each call actually owns.
* A future producer of a second genuinely-outermost dispatch within one
  attribution stream (the front door's documented "seven post-dispatch
  string second chances") inherits a tested first-writer-wins guarantee on
  `features` rather than having to re-derive one.

## Alternatives rejected

**Keep `features` as a process-global and only add the `name` member.**
Rejected: the brief and ADR-2102's own consequences section name `features`
as unfinished work in the identical shape ADR-2101 closed for everything
else — fixing `name` alone would leave the plan's stated rule ("the trace is
the API; the prose is a rendering") half-applied to the one field still
failing it.

**Force every nested sub-solve through a real (non-`None`) recorder so
first-writer-wins is enforced by a compare-exchange on the trace, matching
the old global's mechanism exactly.** Rejected: it would mean threading a
trace into `check_auto`'s "thin wrapper" path and every recursive
`check_auto_dispatch` retry, widening this lane's diff into machinery
`route_ownership`/`NestedDispatchGuard`'s own design (ADR-2100/ADR-1906)
already argues should stay internal detail of the route that recurses — and
buys nothing beyond what `with_recorder`'s existing `None`-is-a-no-op
contract already gives for free.

**Re-derive `features` from the `.smt2` text in the ledger reader instead of
crossing the JSON boundary.** Rejected for the reason ADR-2102 itself gives:
a second authority that drifts from the one the dispatcher already computed
is the exact shape every one of the five instruments the dispatch-and-
instrumentation plan's §0 catalogues failed in.
