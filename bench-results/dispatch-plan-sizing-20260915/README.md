# Dispatch plan sizing — 2026-09-15

Two measured inventories for `docs/plan/dispatch-and-instrumentation-2026-09-15.md`
(Phase 1 and Phase 2), produced by lane PLAN-SIZING on `bb58b0bc2`. Feeds
ROUTE-OWNERSHIP (Phase 1, `phase1-ceiling.tsv`) and TRACE-API (Phase 2,
`consumers.tsv`). No Rust written, no ADR filed, no cargo run by this lane.

Status: `consumers.tsv` is DONE (254/254 classified). `phase1-ceiling.tsv`
is in progress — the route-trail re-capture this deliverable required is
still running; see that section for what is measured vs. still pending.

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

| `reads` | count |
|---|---:|
| `other` | 210 (of which **160 are the `proof_route` false positive** above or plain-English "route"/"a way to do X"; the remaining **50** genuinely touch solver-routing data, but indirectly — an unanchored `decided_by=`/`bound_by=` regex, or a column already extracted into a derived census TSV by another script in the same family) |
| `prose-route` | 27 |
| `route-trail` | 12 |
| `both` | 5 |
| **genuine solver-routing consumers (`prose-route`+`route-trail`+`both`+the 50 genuine `other`)** | **94** |

`splits_on_semicolon`: **0 of 254** — the ADR-2020 `;`-split bug was not
found in any file in this population (either already fixed everywhere, or it
never occurred here; either way, worth stating plainly rather than leaving
the column silently all-`no` with no comment).

`handles_partial`, restricted to the 94 genuine consumers: **19 yes, 75 no**
(the other 160 rows are `n.a.` — true false positives). **80% of the files
that read solver routing output do not account for the `; partial ` prefix
at all** — this is ADR-2075's finding (one instrument's "second-largest
unexplained bucket") reproduced at the scale of the whole candidate
population, not just the one census it was originally found in.

### Positive controls

- **`prose-route`**: `scripts/lia-counter-report.py`, `parse_route_line()`:
  `if not line.startswith("; route "):` — matches the literal prose line,
  parses no JSON. (It also does NOT match `"; partial route "`, which is
  exactly the ADR-2075 bug — noted in its own row.)
- **`route-trail`**: `scripts/portfolio-oracle.py`, `parse_trace()`:
  `if line.startswith("; route-trail "):` — matches only the JSON line, no
  prose fallback. (Same partial-prefix bug: does not match
  `"; partial route-trail "`.)
- The cleanest counter-example to both bugs at once is
  `scripts/nra-loss-classify.py` (`reads=both`, `handles_partial=yes`):
  `elif line.startswith("; route ") or line.startswith("; partial route "):`
  immediately followed by a separate `"route-trail " in line` branch that
  `json.loads()`s the trail regardless of the partial prefix — its own
  comment documents a PRIOR version of the script that missed partial and
  silently misclassified every timeout as "no route ran".

## Deliverable 2 — `phase1-ceiling.tsv`

Tier 1 divisions (AUFLIRA, UFNIA, UFLIA, AUFDTLIRA, QF_NIA, UF, UFDTLIRA),
undecided rows from `bench-results/tier1-current-20260914/` (the README
there names the current file per division; AUFLIRA's is
`AUFLIRA-postmerge-787bbefee.tsv`, the other six are the base `78ca906c2`
sweep). Undecided = `verdict` not in `{sat, unsat}` (645 rows total,
confirmed against the tier1-current README's own decided counts).

**Per-file route-trail outputs do not exist for this sweep as run.** Full
account below (this is itself a finding, not a search failure — see
"Where the per-file outputs live" below).

TBD: ceiling counts per division, `attempts == 1` counts, ADR-2045
cross-check.
