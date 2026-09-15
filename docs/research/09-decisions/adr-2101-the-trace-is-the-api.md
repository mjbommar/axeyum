# ADR-2101: the trace is the API and the prose is a rendering — completeness became a field, the 32 route labels became a type, and seven consumers stopped grepping

Status: accepted
Index-summary: Phase 2 of `docs/plan/dispatch-and-instrumentation-2026-09-15.md`. Five instruments lied in one week with **one shape**: each reports through a STRING, each consumer reads it with a GREP, nothing typechecks the contract. Three changes close that shape for route telemetry. **(1) Completeness is a FIELD.** `RouteTrace` carries `partial: Option<PartialReading>` and the JSON carries `"partial"` plus, on a partial reading, `in_flight_after` and `open_segment_ns`; the `; partial ` prose prefix is unchanged in bytes and is now READ OFF the field by `route_attribution_report_lines` instead of applied from outside by the one function that knew the convention existed. Schema bumped **1 → 2** deliberately — adding a member is not a rename, but without the bump a reader cannot tell a v1 object (completeness ABSENT, unknown) from a v2 one that says `false`, and treating the first as the second is exactly how ADR-2075's watchdog files were swept into an aggregate that thought it had totals. **(2) The 32 route labels became `Route`**, declared through one macro that emits the enum, the exhaustive `as_str`, the authority list `ALL` and the inverse `from_wire` from a single list; the 32 `pub const` are now DEFINED as `Route::X.as_str()`, so there is one source of the bytes rather than two that agree today. `Route` is deliberately **not** total over the trail — a dispatch rung label is an `auto.rs` string literal with no declaration to derive from, `from_wire` answers `None` for one, and a test pins that as a POSITIVE control on the negative answer. **(3) One reader**, `scripts/route_trace_reader.py`, with 12 control tests whose exit status is the finding. Consumers under `scripts/` that parse route prose: **before 7, after 0**. The migration found three LIVE defects, not hypothetical ones: two scripts anchored on `^; route-trail `, which the watchdog path never prints, so every file killed mid-search read as "no route cost anything"; and `euf-online-atoms-sweep.sh` searched the TRAIL line for `bound_by=`, a field that only ever appears on the PROSE line, so `bound_by` has been empty on every row that sweep has ever written. Positive control on the migration: across **251** committed `--trace` logs carrying BOTH channels, the reader's `decided_by`/`bound_by`/`attempts` agree with the CLI's own prose on **251 of 251** — the numbers do not move, the channel does. Exit criterion B re-derives **21 of 21** corrected figures across ADR-2075 / ADR-2020 / ADR-2060, printed beside the old wrong ones. Two of those three are honest limits rather than results and say so: ADR-2020's census has **0** route-trail columns (verified, not asserted) and ADR-2060's 28 counts PROGRAM POINTS on the pre-fix tree, where the committed enumerator now correctly reports **0** — the current typed vocabulary is **23** variants across five enums.
Index-status: accepted
Date: 2026-09-15

## Context

`docs/plan/dispatch-and-instrumentation-2026-09-15.md` opens with a measured
claim: eleven lanes on the quantified divisions measured budget policy at zero
from every angle and found, instead, one dispatch bug five times and **five
instruments that reported the wrong thing**. The five share a shape, not a
subject:

| ADR | how it lied |
|---|---|
| 2075 | a census grepped `^; route `; the watchdog path prints `; partial route ` — a DELIBERATE prefix whose consumer half was never written |
| 2060 | one give-up string for **28 program points and 15 causes**; an `i128` overflow reported as a timeout |
| 2020 | a census split records on `;` when the `why=` field contains `;`, truncating its own largest bucket |
| 2085 | `git log -G<symbol>` matches patch TEXT; a function body does not repeat its own name |
| 2065 | an enumerator cut each file at the first `#[cfg(test)]`, which is mid-file |

Every one: the instrument reports through a **string**, the consumer reads it
with a **grep**, and nothing typechecks the contract between them.

What already existed and was under-used: `route_trace.rs` records every attempt
as a struct with a byte-stable `to_json()`, and `smtcomp_cli` has printed
`; route-trail {to_json_with_timing()}` on every traced file since ADR-1906. The
JSON was already in every output file. **The gap was entirely on the consumer
side, plus the `partial` prefix.**

## Decision

Three changes, in the direction **JSON → prose, never prose → parse**. The
human-readable lines stay, for `git grep` and for eyes.

### 1. Completeness is a field, not a prefix

`RouteTrace` gains `partial: Option<PartialReading>`, where

```rust
pub struct PartialReading {
    pub in_flight_after: Option<&'static str>,
    pub open_segment: Duration,
}
```

`RouteTrace::marked_partial()` captures both **now**, so the completeness
travels with the trace through a clone, a mirror and a serialisation instead of
living only in the format string of one printer. The watchdog path in
`smtcomp_cli` marks FIRST and renders second; `route_attribution_report_lines`
derives the `; partial ` marker from `trace.is_partial()`.

The prose is byte-identical to what it printed before. What changed is which of
the two channels is the source of truth.

`PartialReading` names the **boundary**, not the route in flight, and the type's
own name says so. An attempt is recorded when it FINISHES, so on a killed run
the route actually consuming the budget has contributed nothing to `bound_by` —
which is why `open_segment` has to travel beside it. `RouteTrail
.bound_by_is_the_answer` on the reader side is the executable form of that
caveat.

**Completeness is part of `PartialEq`.** A partial reading and a completed run
that recorded the same attempts are not the same observation, and an equality
that says they are is the prose prefix's collapse with a `==` in front of it.
Only the presence of the reading and its `in_flight_after` participate —
`open_segment` is a wall clock and would break the determinism contract.

### 2. Schema 1 → 2, deliberately

`ROUTE_TRACE_JSON_SCHEMA_VERSION`'s own rule is "bump on any field
rename/removal". Adding `partial` is neither, so by that rule this did not have
to bump.

It bumped anyway, and that is the load-bearing decision. Without it a reader
cannot distinguish:

* a **v1** object, where completeness is ABSENT and therefore unknown, from
* a **v2** object that states `"partial":false`.

Treating the first as the second is precisely how ADR-2075's watchdog files were
swept into an aggregate that thought it had totals. The version is what lets the
shared reader say *"this artifact predates the field"* instead of guessing.

Every artifact committed before this ADR is schema 1, so the reader needs a
compatibility path or it can re-derive nothing. For schema 1 **and only schema
1** it falls back to the `; partial ` line prefix — legitimate exactly there,
because that is the shim and there is one of it — and reports
`partial_source == "prefix"` so a caller that must not infer can check.

### 3. The 32 route labels are a type

`Route` is declared through one macro that emits the enum, `as_str`, `ALL` and
`from_wire` from a single list. A second, hand-maintained `name()` table is the
exact shape ADR-2060 found lying; here a variant without a wire string does not
compile, and one with a wire string is in `ALL` and in `from_wire` by
construction.

`as_str` is a `const fn`, so the 32 constants in `front_door_stage` and
`quant_rung` are **defined** as `Route::X.as_str()`. One source of the bytes.
`auto.rs` is untouched and every existing consumer keeps the constant it already
used, which is what keeps this merge compatible with a concurrent lane editing
`auto.rs` heavily.

**What `Route` is not total over, and why that is the honest answer.** The
dispatch ladder's own rung labels (`"qf-bv"`, `"lia-dpll"`, …) are string
literals at their call sites inside `auto.rs`, not declared constants, so there
is no authority to derive an enum from. Typing them is the ownership work
(Phase 1), not this. `from_wire` returns `None` for a dispatch rung, and
`a_dispatch_rung_label_is_deliberately_not_a_route` pins that as a **positive
control on the negative answer** — without it, a `from_wire` that answered
`None` for everything would pass the round-trip test by accident.

Count: 32 declared constants (14 front-door + 18 quantified) plus the `"probe"`
label `record_probe` hardcodes = **33 variants**. The brief said 32; the
thirty-third is a real label that appears in the trail and had no declaration at
all, which is itself the finding.

### 4. One reader

`scripts/route_trace_reader.py` parses the `route-trail` JSON and exposes
`decided_by`, `verdict`, `bound_by`, `last`, `attempts`, `total_elapsed_ms`,
`partial`, `partial_source`, `in_flight_after`, `open_segment_ns`,
`bound_by_is_the_answer` and `decline_reasons()`.

It **refuses**, by name and with a non-zero command exit status, on:

* a file with no trail line (`NoTrailLine`, carrying the path);
* a file whose instrument ran and recorded nothing (`; route unavailable:`) —
  kept DISTINCT from the above, because "never traced" and "traced and empty"
  are different findings and collapsing them is how an absence becomes a zero;
* a schema it does not know (`UnknownSchema`), rather than reading it
  optimistically.

`decided_by_counts` refuses a population containing partial readings unless
told `include_partial=True`. A partial trail's `decided_by` is a statement about
the moment the reading was taken, not the run's answer; summing those into a
decision rate is ADR-2075's error with a dictionary in front of it.
`bound_by_counts` refuses by default too but documents that including partials
is reasonable there — an undecided file is exactly where the question matters —
provided `bound_by_is_the_answer` is read beside it.

## Measurements

### Consumers that parse route prose, under `scripts/`

**Before 7, after 0.**

| consumer | what it did | what the migration found |
|---|---|---|
| `lia-counter-report.py` | `startswith("; route ")` | its `bound_by on undecided files` histogram silently dropped exactly the undecided files it exists to describe |
| `nra-loss-classify.py` | both prefixes, by hand | knew the convention; now nothing does |
| `trace-sweep-report.py` | both prefixes + `; partial route-open` | the open segment is now a JSON member written from the same captured reading the prose renders, so the two cannot drift |
| `qf-nia-dispatch-census.py` | `^; route decided_by=…` regex | a watchdog-killed file fell into the `else` and was censused `bound_by=none bound_ms=-1` |
| `qf-nia-sat-inslice-budget.py` | `^; route-trail ` regex | **LIVE DEFECT** — the watchdog path prints `; partial route-trail `, so a killed file returned an EMPTY per-route budget and read as "no route cost anything" |
| `portfolio-oracle.py` | `startswith("; route-trail ")` | **LIVE DEFECT** — same anchor, and the population a portfolio oracle most needs is exactly the killed one |
| `euf-online-atoms-sweep.sh` | hand-rolled JSON regex | **LIVE DEFECT** — searched the TRAIL line for `bound_by=`, a field that only appears on the PROSE line. `bound_by` has been empty on every row this sweep has ever written |

One correction to the brief's list: it named
`bench-results/silent-hang-20260915/split.py` as a prose consumer. It is not —
it reads a TSV **column** produced by `phase-census.sh` and never opens a log.
The seventh real consumer is `euf-online-atoms-sweep.sh`.

Consumers under `bench-results/` are not migrated. They are dated receipts of
completed lanes; rewriting them would edit published evidence rather than fix a
tool. The count there is **17 files / 29 sites**, listed by
`grep -rnE '(startswith|grep|re\.(compile|search|match)).*; (partial )?route'`.

### The migration does not move any number

**251 of 251.** Across every committed `--trace` log that carries BOTH the prose
`; route …` line and the trail JSON, the reader's `decided_by`, `bound_by` and
`attempts` equal the CLI's own prose. The channel changed; the numbers did not.

### Re-derivations (exit criterion B): 21 of 21

`bench-results/trace-api-20260915/rederive.py`, exit status is the finding.

**ADR-2075 — through the reader**, on the six committed `prof/*/stdout.txt`
receipts:

| receipt | old `^; route ` grep | reader `bound_by` | partial | `; partial ` lines |
|---|---|---|---|---:|
| fp-dafny | **NO** | `q:bool-skeleton` | yes | 15 |
| fp-havoc-sum | **NO** | `q:bool-skeleton` | yes | 11 |
| fp-hoare | yes | `q:egraph` | no | 0 |
| fp-mqueue | **NO** | `q:ground-subset` | yes | 14 |
| fp-zohar | yes | `q:egraph` | no | 0 |
| havoc-sum | **NO** | `q:bool-skeleton` | yes | 10 |

The old consumer can attribute **2** of 6; the reader attributes **6** of 6, and
each names a real `bound_by`. That is ADR-2075's headline — *"There was never an
absence"* — re-derived from the bytes rather than quoted.

Population figures, by the ADR's own filter over
`skeleton-reach-20260914/ref/fd-census-208.tsv`: inherited **13** (with the
awk's own positive control printing **142**, so the 13 is a filter result and
not an empty scan); re-derived OUT **4** where P5 predicted at most 2; corrected
bucket **9** against the **12** inherited from ADR-2040 §8. The nine split by
innermost running phase: `none` 3, `euf:fc-pair-scan` 2, `euf:offline` 2,
`euf:round-incremental-arith` 2.

One correction to ADR-2075's own cross-reference: its *"Fourteen lines."* (line
51) is attributed to `UFNIA/sledgehammer/Hoare/z3.850818.smt2`, but the
committed receipt for that file took a different give-up path
(`ResourceLimit`, not `Watchdog`) and prints **0** `; partial ` lines. The
receipt on disk that prints exactly **14** is `prof/fp-mqueue`. The number is
right; the file it points at is not.

**ADR-2020 — not the reader's artifact, and that is checked rather than
asserted.** `round-head-20260914/census/FAMILY.shard0*.tsv` has 26 columns and
**0** occurrences of `route-trail`. The corrected figures are re-derived with
the committed `census-binding-cause.py`:

| | outer string (OLD) | binding cause (CORRECTED) |
|---|---:|---:|
| distinct buckets | **5** | **10** |
| largest bucket | **25** | **22** |
| leader | `Timeout｜preprocessed dispatch timeout after reduced solve` | `lazy linear arithmetic pre-SAT skeleton exceeds the joint resource boundary` |

The reader's contribution here is **structural**, not numeric: the `;`-in-a-field
defect is unreachable through it, driven by
`test_a_detail_containing_the_old_separators_survives_whole`, whose fixture
carries `;`, the `;QPROBE ` separator invented to work around it, an `=`, a
quote and a newline, and must come back byte-identical. The fixture also asserts
that it actually contains those characters — a hostile fixture that is not
hostile is a vacuous control.

**ADR-2060 — likewise not a trail read.** Its 28 counts program points in
`lra.rs` on the PRE-FIX tree. Re-running the committed
`enumerate-producers.py` on today's tree reports **0** `Decision::TimedOut`
constructions, which is the expected post-fix answer and is itself the check
(the enumerator prints `NOT FOUND` when it never reaches its subject, and it did
not). The typed vocabulary that replaced the one sentence, counted from the
enums:

| enum | variants |
|---|---:|
| `GaveUp` | 5 |
| `FmDecline` | 5 |
| `SimplexDecline` | 7 |
| `ElimBail` | 4 |
| `CollectDecline` | 2 |
| **total** | **23** |

ADR-2060 landed 22; `SimplexDecline` has since grown to 7. Old: **1** reason a
consumer could tell apart, behind **28** program points and **15** causes.

### Typed reasons: what this ADR did and did not do

The brief asked for the ADR-2060 treatment on *every remaining terminal reason*.
Counted, on the route-trace `DeclineReason` specifically (excluding the
similarly named enums in `axeyum-cas` and `axeyum-lean-import`, which a
word-unbounded grep conflates with it):

| variant | free string? | src sites |
|---|---|---:|
| `Unsupported` | no | 14 |
| `NotApplicable` | no | 30 |
| `UnsupportedDetail(String)` | **yes** | 11 |
| `Budget(String)` | **yes** | 16 |
| `VerifierRejected(String)` | **yes** | 17 |
| `Incomplete(UnknownReason)` | kind typed, detail free | 15 |

**44 producer sites still emit a free-string detail**, across `auto.rs` (11),
`span_log.rs` (6), `nia_linearize.rs` (4), `nia_square.rs` (2),
`int_real_relax.rs` (1), `smtlib.rs` (1) and the rest. **This ADR did not typify
them**, and says so rather than implying it did: the classification axis
(`reason` + `kind`) is already typed and already survives to the reader, and
typifying the *detail* is a compiler-enumerated refactor across the solver of
the same size as ADR-2060's own, which is a lane rather than a slice of one.
What this ADR does guarantee is that the distinctions the producer DOES make
survive to every consumer — driven by
`test_two_declines_sharing_a_reason_token_stay_distinguishable`, where two
declines sharing a route and a detail and differing only in `reason`/`kind` must
stay countable apart.

### Mutation

`SUITES["route-trace-completeness"]` in `scripts/tests/mutation_controls.py`,
three mutations, each making one producer emit the wrong variant. They are
deliberately **self-consistent** — the wire string moves at its single
definition, so `as_str`/`from_wire`/`ALL` still agree with each other — because
the whole point is that a test deriving its population from the authority cannot
notice, and only a test pinning the EXTERNAL contract can.

## Consequences

* Phase 3 (the outcome ledger) can store typed reasons and a `partial` column
  without inheriting the string bug. That was its stated dependency.
* A census that names a front-door stage or a quantified rung that does not
  exist now fails to compile. One that names a dispatch rung still does not —
  that is Phase 1's surface.
* Committed schema-1 artifacts stay readable, with `partial_source == "prefix"`
  marking every inference.
* The 44 free-string decline details are a named, counted backlog rather than an
  unexamined one.

## Alternatives rejected

**Leave `to_json()` byte-identical and put `partial` only in the timed
rendering.** Rejected: the two renderings would then disagree about what a trace
IS, and a consumer reading the wrong one would silently lose the field — a
second thing that drifts, which is the risk §7 of the plan names.

**Do not bump the schema.** Rejected for the reason §2 gives: without the bump a
v1 artifact and a v2 `"partial":false` are indistinguishable, and the whole
point of the field is to make that distinction unmissable.

**Type the dispatch rung labels too.** Rejected as out of scope and as a merge
hazard: `auto.rs` is being edited heavily by the ownership lane, and the labels
have no declaration to derive an enum from, so typing them means choosing the
vocabulary — which is a decision, not a refactor.

**Migrate the `bench-results/` consumers.** Rejected: they are dated receipts of
completed measurements. Editing them changes published evidence.
