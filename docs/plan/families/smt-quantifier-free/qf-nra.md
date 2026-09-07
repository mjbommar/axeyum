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

**Second, checked, defect**: `explain_corpus` runs the flat assertion view
(`check_auto_explained`), not `solve_smtlib` — the population above is
front-door, but the *cause class* still comes from `explain_corpus`'s own
execution, which could in principle diverge from the front door's route.
This is verified, not assumed: `QF_NRA.census.tsv` carries
`explain_corpus_flat_verdict` and `class_vs_front_door` per file. **0 of the
72 classified rows show the flat view deciding a `sat`/`unsat` the front
door did not** (`UNCONFIRMED-divergent` count = 0) — every classified row's
flat verdict is `flat-unknown`, consistent with the front door's `unsolved`.
That rules out the concrete failure mode (a class attributed from an
execution that actually decided differently) for all 72; it does not prove
route identity on files where both sides simply say `unknown`. The 89.6%
figure below carries that qualifier.

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

## Follow-up: the dominant cause was acted on (lane `nra-admission-bound`, 2026-09-07)

The `nra-cross-product-admission-bound` class above (62 files, 80.5%) was the
brief for a capability slice. Its outcome corrects part of this document.

**What the bound protected, measured.** It was introduced (`9a8b09220`) as an
OOM guard. Re-run on the 62 files with the bound lifted, same 24 s / 8 GiB
protocol: **zero memory aborts in 124 runs**, peak RSS 3,315 MiB vs 3,316 MiB
against an 8 GiB cap. It protected **wall time**, not memory — and on **25 of
the 62 it protected nothing**, those files being refused one layer down by
`lra_theory::MAX_ONLINE_LRA_ATOMS` in the same time and the same memory. The
census read the declining route's message, which named the first gate in a chain
rather than the one that refused; correction block in
`bench-results/parity-losses-20260906/README.md`.

**The slice.** [ADR-1751](../../../research/09-decisions/adr-1751-nra-admission-is-the-consumers-capacity.md):
admission is now the consuming engine's distinct-LRA-atom capacity rather than a
cross-product count of 2, with the pre-ADR behaviour preserved byte-identically
at or below the old line and a bounded deadline share above it.

**Measured effect on this list** (`QF_NRA.txt`, 200 files, sha256
`d645dd907edd`, one binary `c2d7635815d5`, arms interleaved, s6):

| | legacy | shipped default |
|---|---:|---:|
| decided | 110/200 | **112/200** |
| verdict regressions | — | 0 |
| disagreements | — | 0 |
| memory aborts in 400 runs | 0 | 0 |

The legacy arm reproduces this document's ledger row exactly (110/200), which is
what makes 112 comparable. Both new results are `sat`, both agree with cvc5 run
directly, and both carry `evidence kind=sat-model certified=1`.

**What remains.** 60 of the 62 are still lost, and they are now a **capability**
gap rather than an admission-policy one: 35 are admitted and the
linear-abstraction relaxation does not close them, 25 are refused by the atom
capacity. The decline text's own answer — "this needs a nlsat/CAD engine" — is
still the right one for them, and `MAX_ONLINE_LRA_ATOMS` is the next bound on
this route (its own doc records that lifting it needs the atom-normalization
memory addressed first). Full record:
[`docs/research/12-performance/nra-admission-bound-2026-09-07.md`](../../../research/12-performance/nra-admission-bound-2026-09-07.md).
