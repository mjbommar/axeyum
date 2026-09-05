# SAT-core priority gate (b), measured 2026-09-05

Lane `perf-gate-b-sat-core`. This directory answers one question left open by
[the 2026-09-05 SAT/SMT performance and architecture
review](../../docs/research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md)
(§2.2 item 4) and by the [benchmarking and performance
methodology](../../docs/research/08-planning/benchmarking-and-performance-methodology.md)'s
Decision Gates section:

> Custom CDCL core: building it is settled identity, not contingent
> (ADR-0002); this gate decides *priority*. It jumps the queue ahead of
> encoding work when, on the public + client tiers, (a) SAT time dominates
> end-to-end time, and (b) the best Rust adapter shows a consistent material
> gap to CaDiCaL/Kissat on Axeyum-generated CNF specifically.

Gate (a) was already measured true on the p4dfa and Noetzli families (SAT
share 0.974 and ~0.95). Gate (b) had never been measured — no artifact under
`bench-results/` contained a CaDiCaL or Kissat run before this one. This
directory is that measurement.

## Method

1. **Reference solvers**, cloned via `scripts/fetch-references.sh`'s URL list
   and built locally with their own `./configure && make`:
   - CaDiCaL 3.0.1, commit `c60730422e758ef1cebe7aeddf2dda31c996bf04`
     (2026-07-19), `g++ -O3 -DNDEBUG`.
   - Kissat 4.0.4, commit `8af8e56f174b778aef3aa45af9f739b2a5f492c2`
     (2025-10-16), `gcc -O3 -DNDEBUG`.
   Both built cleanly on the first attempt; no fallback was needed.

2. **CNF dump.** `crates/axeyum-bench/examples/dump_dimacs.rs` (unmodified,
   pre-existing) bit-blasts a QF_BV `.smt2` file to DIMACS after the same
   word-level preprocessing (`canonicalize_terms` → `propagate_values` →
   `solve_eqs_bounded` → `elim_unconstrained` → re-canonicalize) the fair
   corpus runs use, then Tseitin-encodes. Two corpora:
   - **p4dfa** (`.../QF_BV/20221214-p4dfa-XiaoqiChen/`), the family the
     review's gate (a) measurement used (SAT share 0.974): **all 113 files
     dumped, 0 failures.** Sizes range from a few thousand to ~2M CNF
     variables (`string4x16.*` files are the largest).
   - **Noetzli** (`20190311-bv-term-small-rw-Noetzli`, found under
     `/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/QF_BV/`
     — NOT under `/nas3/data/axeyum/corpus/public/`, contrary to the brief's
     assumed path; located with `find`). The full family is **1575 files**,
     each tiny (median CNF 17.7 KB, max 566 KB, 79.6 MB total) — running four
     engines × 1575 files at a 20 s budget was not tractable inside this
     lane's session. **All 1575 dumped, 0 failures**, but only a **seeded,
     deterministic 100-file sample** (Python `random.Random(20260905)`,
     `random.sample` over the sorted file list, seed and exact file list
     recorded in [`noetzli-sample-seed20260905.txt`](noetzli-sample-seed20260905.txt))
     was carried through the engine sweeps. **p4dfa is exhaustive; Noetzli is
     a 100/1575 sample.** Treat the Noetzli numbers as indicative, not a full
     head-to-head.

3. **Four engines, identical DIMACS, same 20 s per-instance budget, `taskset
   -c 0-7`** (this host, `s4`, is a 12th-gen Intel i5-12600K — a hybrid P/E
   core part; pinning to the first 8 (P-)cores follows the same convention
   the frontier-ratchet reference-frame note uses), one engine at a time:
   - **BatSat** via `axeyum_cnf::solve_with_rustsat_batsat_timeout` (the
     default pure-Rust adapter).
   - **native** — the proof-producing CDCL core,
     `axeyum_cnf::solve_with_drat_proof_within`
     (`crates/axeyum-cnf/src/proof_sat.rs`).
   - **CaDiCaL** and **Kissat**, invoked as external processes (`-q`, DIMACS
     exit-code convention: 10 = SAT, 20 = UNSAT).
   A new example, `crates/axeyum-bench/examples/gate_b_sweep.rs` (committed),
   drives BatSat + native together and does the model checking for all four
   engines; a Python driver (kept in the session scratchpad, not committed —
   it only shells out to already-built solver binaries and does no
   SMT/SAT work of its own) drives the two external engines with the same
   `taskset`/timeout/verify plumbing. Every `sat` verdict, internal or
   external, is checked by evaluating the returned model against the DIMACS
   CNF with `axeyum_cnf::CnfFormula::evaluate` (`gate_b_sweep verify` for the
   externally-captured models) — the same trusted code path in every case.

4. **Resumable batches, not one long run.** A single sweep over all 113
   p4dfa files at a 20 s-per-engine budget needs on the order of an hour of
   wall time (most p4dfa instances exhaust the budget on every engine tried),
   which is longer than any single foreground tool call this lane could make
   without violating the "no background waiting" operating rule. `gate_b_sweep
   sweep` (and the external Python driver) append one TSV row per file and
   skip any file whose name is already a row, so the same command run
   repeatedly with a `max_files` cap turns one long sweep into a sequence of
   short, resumable, single-tool-call batches. Load average was recorded
   before and after each engine's *first and last* batch on a family (see
   `load-<engine>-<family>.log` in this directory) — this ambient load was
   never controlled by this lane (see Caveats).

## Results

### p4dfa — 113/113 files, 20 s budget, exhaustive

| Engine | Decided (sat+unsat) / 113 | PAR-2 mean (s) |
|---|---:|---:|
| BatSat | 4 | 38.729 |
| native (proof core) | 6 | 38.107 |
| CaDiCaL 3.0.1 | 10 | 37.203 |
| Kissat 4.0.4 | 11 | 36.941 |

**Zero cross-engine disagreements, zero invalid SAT models**, across all 113
files × 4 engines (452 (engine, file) results checked; a `sat` model is
checked by `CnfFormula::evaluate`, a disagreement is any pair of engines that
both decided the same file but to different sat/unsat verdicts).

### Noetzli — 100/1575 files (seeded sample), 20 s budget

| Engine | Decided (sat+unsat) / 100 | PAR-2 mean (s) |
|---|---:|---:|
| BatSat | 86 | 5.604 |
| native (proof core) | 86 | 5.605 |
| CaDiCaL 3.0.1 | 88 | 5.247 |
| Kissat 4.0.4 | 89 | 4.613 |

Zero cross-engine disagreements, zero invalid SAT models on the sample.

Full per-instance data: [`results.json`](results.json) (both families;
per-family versions are [`results-p4dfa.json`](results-p4dfa.json) and
[`results-noetzli-sample.json`](results-noetzli-sample.json)),
[`per-file.tsv`](per-file.tsv) (flat table, both families;
per-family: [`per-file-p4dfa.tsv`](per-file-p4dfa.tsv),
[`per-file-noetzli-sample.tsv`](per-file-noetzli-sample.tsv)). Raw per-engine
sweep TSVs (`internal-*.tsv`, `cadical-*.tsv`, `kissat-*.tsv`) are the
ground truth the aggregated files were built from.

## The gate (b) verdict

**Gate (b) — "does the best Rust adapter show a consistent material gap to
CaDiCaL/Kissat" — reads mixed, not a clean yes.**

- On **p4dfa**, the family gate (a) was measured against, Kissat (11/113)
  and CaDiCaL (10/113) each decide 4–7 more files than BatSat (4/113) and the
  native core (6/113) at the same 20 s budget. That is a real gap and it runs
  in the expected direction (mature C solvers ahead of the two Rust engines),
  but the *absolute* numbers are tiny on every engine — this family is hard
  for all four solvers at 20 s, and "10 vs 4" is a difference of six files
  out of 113, not a wholesale unlock. PAR-2 tracks the same story: all four
  engines cluster in a narrow 36.9–38.7 s band (out of a 40 s two-timeout
  ceiling), because most of the corpus times out for everyone.
- On the **Noetzli sample**, the gap nearly vanishes: 86–89 out of 100 decide
  for every engine, and PAR-2 spans 4.6–5.6 s. Kissat is fastest, BatSat and
  the native core are statistically indistinguishable from each other, and
  CaDiCaL sits in between. This is the easier family (SAT share ~0.95 in the
  methodology note came from an even larger decided population there) and it
  does not show a material gap at all.
- **The native proof-producing core is at least as good as BatSat
  everywhere measured** — 6 vs 4 decided on p4dfa, tied at 86 on the Noetzli
  sample, and never slower in PAR-2 mean. Nothing here supports treating
  BatSat as the stronger of the two in-tree engines; if anything the native
  core (already used for LRAT certification, ADR-0613) is the better default
  candidate of the two Rust options.
- **Net:** a gap to CaDiCaL/Kissat exists and is measured, but it is neither
  large nor uniform across families — it is visible on the hard family and
  nearly absent on the easy one. That is weaker evidence for jumping the
  native-core-as-default queue than "consistent material gap" would suggest;
  it is stronger evidence that **encoding/preprocessing, not raw CDCL
  strength, is still where axeyum's QF_BV time actually goes on families like
  Noetzli** (consistent with the review's D1/D2 architecture findings — the
  CDCL(T) driver used by every non-QF_BV division has no clause arena, no
  blocking literals, and cannot be measured by this experiment at all, since
  this whole sweep is pure Boolean CNF with no theory layer).

## What this does not establish

- **Noetzli is a 100-file sample, not the full 1575-file family.** The
  sample is seeded and its exact file list is recorded
  (`noetzli-sample-seed20260905.txt`), so it is reproducible, but a different
  sample could show a different PAR-2 spread. Nothing here should be read as
  "Noetzli decided/PAR-2 at scale" — only p4dfa is exhaustive.
- **This measures raw CDCL strength on flat CNF, nothing about CDCL(T).**
  Every division below 70% decide-rate in the parity ledger (QF_LIA, QF_RDL,
  QF_LRA, QF_UFLIA, QF_IDL, QF_NIA) runs on the third Boolean engine named in
  the review's D1 finding (`CdclT` in `cdclt.rs`), which has its own
  `Vec<Vec<Lit>>` clause storage and was not exercised here at all — this
  experiment is QF_BV pure-SAT only.
- **The host was heavily loaded by unrelated lanes throughout** (`load
  average` in the `load-*.log` files here ranges 12–33 typical, one spike to
  111 during the Kissat/Noetzli batch) despite `taskset -c 0-7` pinning —
  other lanes' processes were not necessarily excluded from cores 0–7.
  Absolute wall-clock numbers (and therefore PAR-2) carry that noise; the
  *ordering* between engines on the same instance, run back-to-back under the
  same ambient conditions, is the more reliable signal than the absolute
  seconds.
- **No profiling was done.** This says how many instances each engine
  decides and how long it took, not *why* — no flamegraph or per-phase
  breakdown of where CaDiCaL/Kissat spend their extra decided instances that
  BatSat/native do not reach.
- **`dump_dimacs.rs` has no size guard.** Every file dumped in this run
  happened to complete within the 60 s dump timeout used to drive it; a
  larger public family could time out at the dump stage before ever reaching
  a solver, and that failure mode was not exercised here (0 dump failures
  observed, not 0 dump failures ruled out in general).

## Files in this directory

- `README.md` — this file.
- `results.json`, `results-p4dfa.json`, `results-noetzli-sample.json` —
  per-instance records for all four engines.
- `per-file.tsv`, `per-file-p4dfa.tsv`, `per-file-noetzli-sample.tsv` — flat
  tables of the same data.
- `internal-p4dfa.tsv`, `internal-noetzli-sample.tsv` — raw BatSat + native
  sweep output (`gate_b_sweep sweep`).
- `cadical-p4dfa.tsv`, `cadical-noetzli-sample.tsv`, `kissat-p4dfa.tsv`,
  `kissat-noetzli-sample.tsv` — raw external-engine sweep output.
- `load-<engine>-<family>.log` — `uptime` before/after each engine's sweep
  on each family.
- `noetzli-sample-seed20260905.txt` — the 100 sampled Noetzli CNF file names
  (seed 20260905), so the sample is reproducible.
