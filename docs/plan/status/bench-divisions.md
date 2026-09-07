# Lane: bench-divisions — per-division timing profile: where the 24s budget actually goes

<!-- plan-section: lane-status -->

**Landed (`WIP`, bench-divisions, 2026-09-07).** Reproducible per-division
timing sample and stage breakdown for all 12 parity-board divisions
(`bench-results/bench-divisions-2026-09-07/`), full writeup at
[`docs/research/12-performance/bench-divisions-2026-09-07.md`](../../research/12-performance/bench-divisions-2026-09-07.md).

**Headline: only 15.6% of sampled wall clock (222.3 s of 1422.8 s, 93 files
across 12 divisions) is accounted for by `smtcomp_cli --trace`, the only
front-door stage instrument in this tree.** Five divisions (QF_ABV, QF_BV,
QF_IDL, QF_RDL, QF_UFLIA) are **zero-coverage** — every sampled loss routes
through an engine (`dl-online` difference logic, `sat-bv` bit-blast, or an
early dispatch decline) that never touches the generic CDCL(T) driver
`--trace` instruments, each independently consistent with that division's
own already-documented cause. QF_LRA (71.3%) and QF_UF (69.2%) are the only
divisions with majority coverage; both corroborate (different population,
same direction) their existing cause docs.

**Methodology correction found mid-sweep**: naively summing all seven
`; theory-layer` duration fields gave QF_UF 130.7% traced — impossible.
Traced to source: `theory_assert_ms` is nested inside `boolean_propagate_ms`
(`crates/axeyum-solver/src/cdclt.rs`, `assign()` called from
`unit_propagate()`, itself wrapped whole by the boolean-propagate timer).
Fixed by excluding `theory_assert_ms` from the additive total (reported
separately) and keeping the known-wrong naive sum in `aggregate.json` under
an explicit `_DO_NOT_TRUST` key rather than deleting the evidence.

**Not done**: no dispatch-level (`explain_corpus --json --timed-trace`,
diagnostic-only) breakdown for the 5 zero-coverage divisions — that is the
concrete next step for them, since `--trace` structurally cannot see their
dominant routes. `BvLayerStats` (bit-blast/CNF-encode/solve/model-lift,
already measured internally for QF_BV/QF_ABV) is not wired to any CLI flag;
a `--bv-stats` flag on `smtcomp_cli` is the natural follow-on. Parse time,
rewrite time, and model-replay time are untraced everywhere — no instrument
in this tree isolates them.

Build: `d51d4ef04878b40f5d00a1a6b4aed405b35cae4e`, s7, release,
`cargo build --release -p axeyum-bench --example smtcomp_cli` (no
`--features full` — invalid on `axeyum-bench`). Sweep ran idle
(`/proc/loadavg` ~1.0 throughout, 16-core s7), ~24 minutes wall for all 12
divisions.

<!-- plan-section: landed-changes -->

| 2026-09-07 | bench-divisions | Diary + status file opened, QF_IDL zero-coverage finding (`7b66ad607`) |
| 2026-09-07 | bench-divisions | Full 12-division timing sweep, methodology correction, results committed |
