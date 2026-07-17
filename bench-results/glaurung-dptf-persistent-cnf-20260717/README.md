# Dptf ordered persistent-CNF control

- Date: 2026-07-17
- Glaurung capture implementation: `4fce79f` on the isolated
  `axeyum-retained-cnf-snapshot` branch, based on `403a5c5`
- Axeyum snapshot API base: `46f8f707`
- Driver SHA-256:
  `074be1b90deb21897538a6b093af9826e62610ffd878c92289af31c5ca3f724b`
- Host: 12th Gen Intel Core i9-12900K, 24 logical CPUs, x86_64,
  Linux 7.0.0-27-generic
- Rust: `rustc 1.97.0-nightly (f53b654a8 2026-04-30)`
- Cargo.lock SHA-256:
  `24d903a6c2a8d2a039705f58ecba800efaea563af8634119c0f7c27755ae9ea7`
- Repetitions: 5 complete ordered replays per core
- Per-check timeout: 250 ms
- Report SHA-256:
  `68c49ae673538ad67da675c3735b69d6e56fed4ef1978dc634483f4027ffa0c9`

The Glaurung run made 561 decisions: 317 SAT and 244 UNSAT. Its replay-checked
SAT cache answered 130 SAT queries without entering the retained SAT core. The
capture therefore emits 431 solver-call snapshots: 187 SAT and 244 UNSAT,
across seven path-owned sessions. Persistent clause additions made before a
cache hit are present in the next solver-call snapshot, so no SAT-core state
transition is omitted.

Each snapshot contains the complete monotone Axeyum input-clause prefix and the
exact active frame/one-shot selectors. The runner verifies metadata, DIMACS
hashes, profile identity, positive-unit assumptions, and append-only prefixes
before timing. It then replays the complete ordered stream through one retained
BatSat instance and one retained Z3 Boolean instance per path. Each core keeps
its own learned state. Learned clauses are intentionally not copied between
cores because BatSat exposes no stable portable learned-clause format.

All 2,155 measured rows per core return the expected verdict; there are no
unknowns, errors, or prefix/identity failures. Snapshot sizes range from 0 to
39,567 variables and 0 to 70,666 clauses. Empty SAT snapshots are legitimate
zero-constraint calls.

## Timing interpretation

The table uses one median per solver call across the five complete replays,
then sums those 431 medians. Clause addition and solving are separate measured
boundaries.

| Core | Clause-add median sum | Solve median sum | Median solve | Solve p95 |
|---|---:|---:|---:|---:|
| Retained BatSat | 8.031 ms | 128.141 ms | 0.109 ms | 1.405 ms |
| Retained Z3 Boolean | 91.801 ms | 429.009 ms | 0.441 ms | 4.121 ms |

The per-call geometric mean of Z3/BatSat solve medians is **3.5527x**, favoring
BatSat. Split by verdict it remains BatSat-favored: 3.0401x on 244 UNSAT calls
and 4.3537x on 187 SAT calls. Z3 also spends more time ingesting the same
ordered clause additions.

This closes the learned-state/topology hypothesis narrowly: persistent Z3 does
not beat persistent BatSat when both consume Axeyum's Boolean encoding and the
same solver-call sequence. Consequently, warm native Z3's end-to-end Dptf win
cannot be attributed to a generally faster Z3 Boolean core on Axeyum CNF. The
remaining causal boundary is representation and integration: native Z3 retains
word-level SMT structure, whereas this control deliberately gives it Axeyum's
already-bit-blasted CNF.

This is not an end-to-end speed baseline. It omits Glaurung translation,
bit-blasting, model lifting, replay-cache service, and consumer work; the
diagnostic capture also perturbs outer timing. Absolute values must not be
substituted for the fair four-cell results. The next publication control is a
neutral end-to-end SMT solver, followed by the timeout-sensitive and
authoritative-finding gates.

[`report.json`](report.json) contains all 2,155 rows, exact identities, shapes,
outcomes, and raw nanosecond durations. The hash-bound 169 MiB snapshot/profile
pack remains outside git at the paths recorded in that report; its profile
SHA-256 is
`bcfe1e0dd1219134c75155a29decac16df3945fd4f1be21af807c221cf4cd608`.
