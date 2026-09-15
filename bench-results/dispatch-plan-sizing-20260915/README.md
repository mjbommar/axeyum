# Dispatch plan sizing — 2026-09-15

Two measured inventories for `docs/plan/dispatch-and-instrumentation-2026-09-15.md`
(Phase 1 and Phase 2), produced by lane PLAN-SIZING on `bb58b0bc2`. Feeds
ROUTE-OWNERSHIP (Phase 1, `phase1-ceiling.tsv`) and TRACE-API (Phase 2,
`consumers.tsv`). No Rust written, no ADR filed, no cargo run by this lane.

Status: both deliverables are DONE. `consumers.tsv` is 254/254 classified.
`phase1-ceiling.tsv` covers all 645 undecided Tier 1 rows (644 captured, 1
genuine process death with zero output) via a documented re-capture — see
below for why the re-capture was necessary and what it did and did not
establish.

**Note on how this was produced.** Two of the five parallel fork subagents
dispatched to classify `consumers.tsv` chunks continued working past their
assigned scope after finishing their chunk — inheriting this session's full
context, they picked up the rest of the brief and independently rebuilt
both deliverables in parallel with the coordinating session, including two
extra commits. That was caught, the extra agents were stopped, and their
work was folded in where it was correct (it independently converged on the
same harness identification and two real corrections to `consumers.tsv`
that are credited in that section). The numbers and text below are the
coordinating session's reconciled final pass.

## Deliverable 1 — `consumers.tsv`

Every Python/shell file under `bench-results/` and `scripts/` matching
`grep -rlE 'route[= ]|decided_by|bound_by|route-trail' --include='*.py'
--include='*.sh' bench-results scripts`, classified BY READING each file
(not by a second grep), against the rubric in the lane brief: `reads`
(prose-route / route-trail / both / other), `handles_partial` (yes/no/n.a.),
`splits_on_semicolon` (yes/no, the ADR-2020 bug), `last_commit`, `note`.

Candidate count from the seed grep: **254** files (the brief's own estimate
was "~175"; the wider `--include` glob against the current tree finds more).
**All 254 read and classified — this is not a sample.**

### The seed grep has a big false-positive class: "route" is two unrelated words

This codebase uses "route" for two completely different things: (1) the
solver's runtime dispatch route — the `; route decided_by=... bound_by=...`
prose line and the `; route-trail {...}` JSON that
`crates/axeyum-bench/examples/smtcomp_cli.rs` prints under `--trace`, which
is what this deliverable is about — and (2) the fact ledger's `proof_route`
field (`artifacts/ontology/fact.schema.json`: `kernel-lean` /
`cas-certificate` / autogenesis / import, i.e. HOW a theorem was proved,
completely unrelated to solver dispatch). Most of `scripts/`'s fact-ledger
tooling (`check-*.py`, `gen-*.py`, `validate-*.py`, `create-autogenesis-*.py`
and their `scripts/tests/` unit tests) matched the seed grep on this second
sense only. Every one of those is still a row below — `reads=other`,
`handles_partial=n.a.`, with a note naming the actual (non-routing) field —
rather than silently dropped, so the denominator stays honest.

### Counts

Two independent full passes were made over the same 254 files (see "How this
was produced" below); the numbers here are from the read-every-file merged
pass in the committed `consumers.tsv`.

| `reads` | count |
|---|---:|
| `other` | 207 |
| `prose-route` | 27 |
| `route-trail` | 15 |
| `both` | 5 |
| **direct readers of solver stdout (`prose-route`+`route-trail`+`both`)** | **47** |

The 207 `other` rows split into two populations, named in each row's `note`:
a **false-positive majority** — "route" is also the fact ledger's
`proof_route` field (`artifacts/ontology/fact.schema.json`: `kernel-lean` /
`cas-certificate` / autogenesis / import — HOW a theorem was proved, unrelated
to solver dispatch), autogenesis `route_hypotheses`, a `--route` CLI flag, or
plain English; these never touch `smtcomp_cli` stdout — and a smaller set of
**indirect consumers**, which read a `decided_by`/`bound_by`/`total_ms`
column out of a derived census TSV that some OTHER script already extracted
from the raw line. Both kinds are kept as rows (not dropped) so the
denominator stays honest; **47** is the count of call sites Phase 2's "one
shared reader" directly replaces — the indirect consumers follow for free
once their upstream census switches to the JSON.

`splits_on_semicolon`: **2 of 254**, one root cause —
`scripts/qf-nia-dispatch-classify.py:34`,
`detail.split(";")[0]` on a give-up `detail` field whose own value can
contain a literal `; the reduced solve's own reason was …` (the file's own
docstring shows the carrier string); `qf-nia-dispatch-crosstab.py` inherits
the bug by importing that file's `decompose()`. Every other file: `no`.

`handles_partial`, restricted to the 47 direct readers: **19 yes, 28 no**.
More than half the files that read solver routing output do not account for
the `; partial ` prefix — this is ADR-2075's finding reproduced at
population scale. The `no` rows split into two shapes, both named in their
notes: an anchor with no `(partial )?` alternation at all (fields come out
empty/`None` on a partial run), and an optional `(partial )?` group that
MATCHES the partial line but never records that it did (partial and
complete readings get silently merged) — scored `no` either way, since
matching without distinguishing is not "accounting for" it.

### Positive controls

- **`prose-route`**: `bench-results/lemma-input-20260915/route-line-census.sh`,
  line 24: `if grep -q '^; route ' "$f"; then` … line 26:
  `elif grep -q '^; partial route ' "$f"; then` — greps the prose line, both
  prefixes, buckets each row COMPLETE/PARTIAL/ABSENT, parses no JSON.
  (`handles_partial=yes`.)
- **`route-trail`**: `bench-results/route-attribution-2026-09-07/scripts/aggregate.py`,
  line 68: `TRAIL_RE = re.compile(r"^; route-trail (\{.*\})\s*$", re.MULTILINE)`
  then `json.loads(m.group(1))` — parses the JSON, never the prose line. The
  anchor does not match `; partial route-trail`, so a partial trail returns
  `None`, indistinguishable from "no trail printed". (`handles_partial=no`.)
- The cleanest counter-example to both bugs at once is
  `scripts/trace-sweep-report.py` (`reads=both`, `handles_partial=yes`):
  `elif line.startswith("; route ") or line.startswith("; partial route "):`
  immediately followed by `elif "route-trail " in line: blob =
  json.loads(...)` — a substring match that catches the JSON whether or not
  it carries the `partial` prefix.

### How this was produced, and a concordance check

Five classification passes (one per ~50-file chunk), each opening every
file, merged by path against the seed list: 254 expected, 254 classified, 0
missing, 0 extra. A second, fully independent pass over the same 254 files
(an earlier commit on this branch, `58ec16053`) agreed on `reads` for **251
of 254**. The three disagreements were rows that pass's own notes say it did
NOT open ("no narrow-marker match … not independently re-verified beyond the
grep sweep"): `scripts/qf_nia_a3_census.py` does `json.loads` and checks
`schema_version == 1` on the trace at lines 155/174 — `route-trail`, not
`other` — and its two test files build route-trail-schema fixtures to
exercise it. That pass also reported `splits_on_semicolon` as 0 of 254; the
`detail.split(";")[0]` above is at the line quoted, confirmed in source. The
committed `consumers.tsv` is the read-every-file pass with these three
corrections folded in.

## Deliverable 2 — `phase1-ceiling.tsv`

Tier 1 divisions (AUFLIRA, UFNIA, UFLIA, AUFDTLIRA, QF_NIA, UF, UFDTLIRA),
undecided rows from `bench-results/tier1-current-20260914/` (the README
there names the current file per division; AUFLIRA's is
`AUFLIRA-postmerge-787bbefee.tsv`, the other six are the base `78ca906c2`
sweep). Undecided = `verdict` not in `{sat, unsat}` (645 rows total,
confirmed against the tier1-current README's own decided counts).

**Per-file route-trail outputs do not exist for this sweep as run — confirmed,
not just absent from a search.** Two independent things are both true:

### Where the per-file outputs live, and why they had to be re-captured

The `bench-results/tier1-current-20260914/` README does not name a per-file
output location. The harness that actually produced those seven TSVs was
identified by exact match on row counts and paths:
`/nas3/data/axeyum/harness/postmerge-board-dt/` —
`scripts/t1-driver.sh` runs `scripts/board-run.sh` over
`lists/T1_<DIVISION>.NN.txt` shards, writing `out/T1_<DIVISION>.shardNN.tsv`.
Confirmed: all seven divisions' row counts (200 each) and the first AUFLIRA
row's path/verdict line up between `bench-results/tier1-current-20260914/*.tsv`
and `out/T1_*.shard*.tsv`. Six divisions ran on binary `78ca906c2`
(`bin/smtcomp_cli-78ca906c2`); AUFLIRA's current file is the later re-run on
`787bbefee` (`bin/smtcomp_cli-787bbefee`), matching the tier1-current README.

1. **`board-run.sh` never persists a per-file raw output.** It captures
   stdout into a shell variable, greps ONE token (the verdict) out of it, and
   discards the rest:

       raw=$(env -u AXEYUM_DATATYPE_NATIVE_REFUSAL timeout ... "$AX" "$f" 2>/dev/null)
       v=$(printf '%s\n' "$raw" | grep -m1 -oE '^(sat|unsat|unknown)$')
       printf '%s\t%s\t%s\t%s\t%s\n' "$f" "${v:-none}" ... >> "$OUT"

   This is not a one-off: the same discard-after-grep pattern is in three
   other independent harness scripts checked for comparison
   (`quant-rounds/route-hit.sh`, `tier1-divisions/shard-run.sh`,
   `nested-array-ir/shard-run.sh`) — it is the harness convention, not a bug
   in this one script.
2. **Even if `raw` had been kept, it would have carried no routing lines at
   all.** `; route`, `; partial route` and `; route-trail` only print under
   `--trace` (`crates/axeyum-bench/examples/smtcomp_cli.rs`, "off by
   default" — a competition run's stdout must stay byte-identical without
   it), and `board-run.sh` does not pass `--trace`. Confirmed directly: the
   pinned `78ca906c2` binary run on an undecided AUFDTLIRA row without
   `--trace` prints only the bare verdict token.

**Both are genuine absences, not a search failure.**

### The re-capture

Rather than report `NOT AVAILABLE` for all 645 undecided rows across all
seven divisions and hand ROUTE-OWNERSHIP nothing to size against, this lane
re-ran EXACTLY the undecided rows — same `binary_sha` per division
(`787bbefee` for AUFLIRA, `78ca906c2` for the other six, both still present
at `/nas3/data/axeyum/harness/postmerge-board-dt/bin/`), same corpus file
(`/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/`),
same `24000` ms budget, same `8 GiB` `ulimit -v` — with `--trace` added.
`--trace` is documented as arming instrumentation only (the module doc:
"the human `;` lines stay suppressed" without it, present with it, and
nothing else about dispatch changes); it is not expected to move a verdict.
This is a supplementary re-capture of the SAME binary on the SAME files, not
a different run substituted for the original — the original sweep's `verdict`
column is carried alongside the recapture's own for exactly this check.

Raw captures (645 files, one per undecided row, `--trace` stdout) are **not
committed** — they are large, mechanically regenerable from `phase1-ceiling.tsv`'s
own `division`+`path` columns plus the `binary_sha` rule above (`787bbefee`
for AUFLIRA, `78ca906c2` for the rest), and are not themselves the spec'd
deliverable. They were produced in
`/tmp/claude-1000/.../scratchpad/plan-sizing/raw/<DIVISION>/<idx>.out` for
this session and are not expected to survive it; re-running is cheap (the
binaries and corpus are the permanent artifacts, at the `/nas3` paths above).

`phase1-ceiling.tsv` columns: `division`, `path` (relative to the corpus
root), `partial` (yes/no — a watchdog-timeout trail is still a trail),
`attempts` (count, including the `fd:parse` probe), `last_route`,
`decided_by`, `decline_reasons` (the ordered set of distinct `reason` values
across the trail, `|`-joined, never `;`-joined), `stopped_by_unknown`,
`bound_by` and `ceiling_hit` (both extra, beyond the brief's required set,
kept for auditability — see below), and `capture_status` (`ok` or
`no-output-captured` for the one genuine failure).

### `decided_by` / `bound_by`, and the two metrics

`decided_by` and `bound_by` are not stored fields in the JSON — they are
*computed* from the `attempts` array, replicating `route_trace.rs` exactly:
`decided_by` is the LAST attempt (scanning in reverse) whose `outcome` is
`"decided"` (`None` → `none`, true for every row here since these are all
undecided by construction); `bound_by` is the attempt with the max
`elapsed_ns`, ties broken by the LAST such attempt (`max_by_key` semantics).

- **`stopped_by_unknown`** is well-defined from the trail alone: the LAST
  recorded attempt's `reason` is `budget` / `incomplete` / `verifier-rejected`
  (an actual `Ok(Unknown)` — the route engaged, tried, and gave up; these are
  `DeclineReason::Budget`, `::Incomplete`, and `::VerifierRejected` in
  `route_trace.rs`) rather than `unsupported` / `not-applicable`
  (`DeclineReason::{Unsupported,UnsupportedDetail,NotApplicable}` — an
  `Err(Unsupported)`-style "not mine, keep going" that structurally cannot
  be why the ladder stopped). This maps 1:1 onto the plan doc's own two-way
  split of how a rung can not-decide.
- **The Phase 1 ceiling as the plan defines it** — "`attempts` is less than
  the ladder's length for that shape, i.e. a route below was never tried" —
  needs the ladder's fixed ORDER and each route's Features-ownership
  predicate, to check "a route below the last-attempted one specifically
  owns this file's features." **That predicate does not exist yet —
  building it is Phase 1's own deliverable**, so it cannot be used to size
  Phase 1 before Phase 1 exists. This lane instead reports a documented,
  narrower PROXY: group all 645 rows by their trail's TERMINAL route (the
  `last_route` that produced the final decline), and take the max `attempts`
  observed within that group as a stand-in "how far a trail with this same
  ending has gotten elsewhere." `ceiling_hit=yes` iff `stopped_by_unknown=yes`
  AND this row's own `attempts` is strictly below that group's max — i.e.
  some other file that also ended at the identical route got further before
  ending there, so a route below plausibly exists and this file's ladder
  stopped short of it. This conditions on the SAME failure mode (same
  terminal route) rather than the plan-doc alternative of "any route ever
  seen anywhere in the division," which is looser.

**The proxy is nearly saturated and therefore not very discriminating: 598
of 604 stopped_by_unknown rows (99.0%) hit it.** That is itself the honest
finding, not a bug in the proxy — natural variance in *how many declines
happen before* the terminal route (load, scheduling, which cheap probes ran
first) means almost every group of 2+ rows has SOME member that went one
attempt further, so "some other file with the same ending did marginally
more" is true almost everywhere and cannot narrow the field. **Read
`stopped_by_unknown` (604/645, 93.6%) as the solid, well-defined number.**
The 598 `ceiling_hit` count is reported because the brief asks for it, but
it should not be read as "598 files are fixable by Phase 1" — it is closer
to an upper bound on `stopped_by_unknown` itself than a real, tighter
estimate. **Sizing the real ceiling needs the ownership predicate — that is
what makes it ROUTE-OWNERSHIP's Phase 1 deliverable and not something a
proxy can shortcut.**

### The numbers

24 s wall / 8 GiB `ulimit -v` per file, same as the original board-run.sh
envelope, `--trace` added. `division` boundary is the same 7-division Tier 1
set the brief specifies — **this is NOT the 16-division / 3,200-file public
board** (`docs/plan/GAP-LOG-2026-09-12.md`,
`bench-results/board-ab-20260914/`), which is a different, QF_*-heavy
division set (16 divisions × 200 files) run on a different harness
(`board-ab-driver.sh`). Two of these seven divisions — `UF` and `QF_NIA` —
also appear on that 16-division board, but as separate sample runs; the
other five (`AUFLIRA`, `UFNIA`, `UFLIA`, `AUFDTLIRA`, `UFDTLIRA`) do not
appear on it at all. Do not add these counts to that board's totals.

| division | undecided | captured | stopped_by_unknown | ceiling_hit (proxy) | attempts==1 |
|---|---:|---:|---:|---:|---:|
| AUFLIRA | 22 | 22 | 20 | 18 | 0 |
| UFNIA | 147 | 147 | 136 | 135 | 5 |
| UFLIA | 115 | 115 | 107 | 106 | 0 |
| AUFDTLIRA | 79 | 79 | 68 | 67 | 0 |
| QF_NIA | 116 | 116 | 114 | 113 | 1 |
| UF | 110 | 109 | 108 | 108 | 0 |
| UFDTLIRA | 56 | 56 | 51 | 51 | 0 |
| **total** | **645** | **644** | **604** | **598** | **6** |

(`UF` denominator is 110 undecided but only 109 captured — one file,
`UF/sledgehammer/Arrow_Order/smtlib.663965.smt2`, produced a genuinely empty
0-byte capture under the 40 s outer `timeout`; not re-attempted, reported
as `capture_status=no-output-captured` rather than silently dropped.)

**Verdict-invariance check**: for every one of the 644 captured rows, the
re-capture's own bare verdict (last line of stdout) matches `unknown` — the
same classification the original (no-`--trace`) sweep recorded. `--trace`
did not move a single verdict on this population, consistent with the
module doc's claim that it arms instrumentation only.

**`attempts == 1` — the ladder never got past the first rung: 6 of 644
(0.9%)**, all in QF_NIA (1) and UFNIA (5). **This does NOT agree with
ADR-2045's 74 of 93 (79.6%)**, and the two numbers are not measuring
comparable populations: ADR-2045's bucket is QF_LRA (not a Tier 1 division
in this brief) and its 74/93 figure is "one ROUTE (the offline dense-matrix
LRA engine) accounts for the outcome" — a `bound_by`-concentration measure —
not a literal `attempts == 1` count. Read literally, `attempts == 1` would
mean the trace has exactly one entry total (including the `fd:parse` probe
that is attempt #1 on every trace here), which is structurally rare for any
query complex enough to reach a quantified/datatype Tier 1 division: there
is almost always a probe plus several cheap `not-applicable` declines before
whatever consumes the clock. QF_LRA's ladder is short enough that "one
route decided the outcome" and "the ladder never got past the first rung"
are close to the same statement; on these seven divisions they are not.
The closer analogue to ADR-2045's actual metric — "how much of `stopped_by_
unknown` is one `bound_by` route" — is a real question this data can answer
but was out of this lane's scope; `phase1-ceiling.tsv`'s `bound_by` column
is there for whoever picks it up.
