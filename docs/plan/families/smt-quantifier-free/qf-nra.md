# QF_NRA — nonlinear real arithmetic

<!-- Family: [SMT, quantifier-free](README.md) · Plan: [PLAN.md](../../../../PLAN.md) -->

**State:** on the board. Entered 2026-09-06/07, solver commit `00373a7d42`.

## Ledger row

From `bench-results/PARITY.md` (`## QF_NRA — 2026-09-07T01:33:46Z`):

| field | value |
|---|---|
| axeyum solved | 110/200 |
| reference solved | 186/200 |
| **ratio (axeyum / reference)** | **59.1%** |
| **disagreements** | **0** |
| soundness | SOUND |
| both / axeyum-only / reference-only | 109 / 1 / 77 |
| reference | `cvc5 1.3.4 [git f3b21c4 on branch HEAD]`, plain invocation (no portfolio) |
| protocol | 24s wall, 8GiB, per-file, `taskset -c 0-7` on s5 (idle host) |
| benchmark list | `bench-results/parity-lists/QF_NRA.txt` (sha256 `d645dd907edd`, 200 files, stride sample of the 12,154-file corpus, stride 60) |

Zero disagreements: axeyum never returned a `sat`/`unsat` that conflicted with
either a declared `:status` or with cvc5. This is a genuine measurement, not
an aspiration — see the corpus size / frontier context below, which predates
the run.

| | |
|---|---|
| Corpus size (SMT-LIB 2024 non-incremental) | 12,154 files |
| 2026 frontier | Z3-GEX, then Z3-alpha2; SMT-RAT leads the quantified NRA |
| Harness changes needed | **None.** Same input format, same 24 s / 8 GiB protocol, same runner — confirmed by the run itself. |

## Why this one

It is a division of SMT-COMP itself and the cheapest possible addition to the board: the runner needs nothing new. We ship nonlinear real routes and CAS-backed certificates and had never scored either against a reference before this slice.

## Cause (census of the 77 reference-only losses)

Full method and per-file data: `bench-results/parity-losses-20260906/README.md`
and `QF_NRA.census.tsv`. Summary: population is **front-door**
(`smtcomp_cli`/`solve_smtlib` via the scored sweep's sidecar); each file's
cause class is the route with the largest `elapsed_ns` in
`explain_corpus --json --timed-trace`'s attempt list (excluding the `probe`
fragment-detection step) — the route that actually spent the budget, not
whichever route ran or printed last. This is stated explicitly because the
2026-09-05 S3 loss census used the last-route's-message method and was
refuted on 67/70 files across two other divisions (`b57800c06`/`f3ce8ef58`);
this census does not share that defect.

| `cause_class` | files | share |
|---|---:|---:|
| `nra-cross-product-admission-bound` | 62 | 80.5% |
| `nra-refinement-incomplete` | 7 | 9.1% |
| `diagnostic-instrument-inconclusive` | 5 | 6.5% |
| `cas-ideal-refuter-incomplete` | 1 | 1.3% |
| `nra-real-root-not-applicable` | 1 | 1.3% |
| `wide-int-admission-incomplete` | 1 | 1.3% |

**89.6% of the losses (69/77) are one cause**: the generic multi-variable
nonlinear-abstraction route (`nra`) either declines outright because its
deterministic cross-product admission bound (2) is exceeded — every one of
the 62 files here blew past it, up to 7,874 cross-products in one case — or
runs its refinement loop to a fixpoint without deciding. This is exactly the
documented boundary in `crates/axeyum-solver/src/capabilities.rs`'s QF_NRA
entry ("sound-incomplete only on the hard coupled/high-degree tail"),
confirmed by measurement. By source family, the loss is concentrated in
`meti-tarski` (50/116 files in the sample, mostly `sqrt`/transcendental
approximation encodings) and `LassoRanker` (14/14 — every sampled file from
this family is unsolved); `hycomp` is nearly fully covered (43/46). The
remaining three losses are singletons: a Geogebra geometry file where the CAS
ideal-refuter found no combining sign, a `kissing`-packing file outside the
single-variable real-root route's domain, and one file with an integer
literal outside the i128 range (`wide-int-admission`, ADR-1702 slice 2 — an
already-tracked, separate gap). 5 of 77 losses (6.5%) could not be
causally classified: `explain_corpus`, the diagnostic instrument used for
route-timing attribution, itself errored or exceeded its external 45s bound
on those five before producing a trace; their front-door loss is still solid,
only the *cause* is unattributed by this instrument.

**No capability slice is authorised by this document alone** — this is the
entry measurement only, per the exit criterion below. A capability slice
targeting `nra-cross-product-admission-bound` (an nlsat/CAD engine for the
coupled multi-variable case) would be the highest-leverage next step by
volume, but that is a separate decision.

## Exit criterion for the entry slice — MET

A committed benchmark list, a reference build pinned by version, one ledger
entry with zero disagreements, and a census of the losses **before** any
capability slice is authorised. Entering is a measurement task; it is finished
when the row exists, not when the ratio is good. All four are done as of this
slice; the ratio (59.1%) is reported as-is.

## Owning documents

- [The survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md), section 2
- Measurement protocol: `scripts/parity-run.sh`
- Loss census: `bench-results/parity-losses-20260906/README.md`,
  `bench-results/parity-losses-20260906/QF_NRA.census.tsv`
- Lane status: `docs/plan/status/qf-nra-entry.md`
