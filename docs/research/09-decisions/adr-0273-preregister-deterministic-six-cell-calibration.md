# ADR-0273: Preregister deterministic six-cell work-bound calibration

Status: accepted
Date: 2026-07-19

Result state: preregistered; zero real-driver v4 rows

## Context

ADR-0272 closes the topology-equivalent neutral baseline and rejects an Axeyum
performance-lead headline. PLAN item 3 is now the active publication experiment:
run the same `{Z3, Axeyum, Bitwuzla} x {cold, warm}` topology on a harder driver
under deterministic per-check work bounds and retain the authoritative findings
at census scale.

The bound cannot be one shared number. Z3 exposes `rlimit`, Axeyum's BatSat path
exposes deterministic progress-check polls, and Bitwuzla exposes cooperative
termination-callback polls. Equal numbers in those interfaces are not equal
work. Choosing three limits after observing the full census would also make the
result adaptive. This ADR therefore freezes a calibration stage before any v4
real-driver execution. A later ADR must freeze the selected triplet before the
338-function confirmation may run.

The mechanism is complete before this registration:

- Axeyum `72375263` makes the retained SAT path honor
  `SolverConfig::resource_limit`, resets it per solve, and distinguishes
  deterministic resource exhaustion from wall timeout.
- Isolated Glaurung `dc06a3740d989f5a71f3a1cef4ba5111c5188f36`
  (mechanism commits `15162427a828c400ac9635c6a4d43c7b3753f56d` and
  `dc06a3740d989f5a71f3a1cef4ba5111c5188f36`) wires
  `GLAURUNG_Z3_RLIMIT`, `GLAURUNG_AXEYUM_PROGRESS_CHECK_LIMIT`, and
  `GLAURUNG_BITWUZLA_TERMINATION_POLL_LIMIT` through all six cells. It keeps a
  separately typed wall safety cap, prevents resource exhaustion from entering
  Axeyum's timeout continuation/cold-retry routes, and emits the fail-closed v4
  trace contract.
- Axeyum `241dab31` adds the v4 consumer. It validates distinct units and limits,
  requires typed stop reasons, rejects outcome/stop drift across repetitions,
  and reports resource-limit, wall-timeout, and other nondecisions separately.

No real-driver v4 row was executed while defining this protocol.

Before executable registration, while the real-driver v4 row count remained
zero, the protocol was made executable by
`scripts/run-glaurung-six-cell-calibration.py` and
`scripts/analyze-glaurung-six-cell-calibration.py`. This exposed one omitted
environment spelling in the prose: `IOCTLANCE_ALL=1` is required to retain the
complete raw/high-confidence/diagnostic finding partition already named by the
acceptance gates below. This zero-row correction freezes that switch explicitly;
it does not change the population, ladder, selection rule, or interpretation.
The tooling also fails closed on the measured Axeyum tree identities, executable
and resolved-library hashes, driver bytes, fixed environment, run order, retained
log hashes, producer validation, and trace confinement.

## Decision

### Frozen source and input

- Glaurung source: clean isolated commit
  `dc06a3740d989f5a71f3a1cef4ba5111c5188f36` on
  `axeyum-bitwuzla-warm-baseline`.
- Axeyum source: `241dab31c4496b16ade889cd8aa30b6185b44823`.
  The measured `axeyum-solver`, `axeyum-cnf`, and `axeyum-ir` trees are
  `19774056908200a85aa986e3b7da5ceeb386c56a`,
  `8a87bca7490eaf666fbe4fcf9c054101796f5c3c`, and
  `ed3649e3a52fbd602327ea523db49bac3a883b6a`; workspace manifest and lockfile
  blobs are `e1351bec59d6601b6a60c774f1d00a01be1dc3e4` and
  `2738bf0d289afea537f444fe0152b040f68278fa`.
- Driver: `/nas4/data/workspace-infosec/glaurung/tests/fixtures/msvc-pdb/tcpip.sys`,
  SHA-256
  `ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea`.
- Calibration population: exactly the first 20 of the 338 reachable functions,
  the same bounded prefix used by ADR-0262. Historical wall-timeout results may
  motivate this population but are not v4 calibration rows.
- Solver/runtime identities remain ADR-0272's registered Z3 4.13.3 and official
  Bitwuzla 0.9.1 build. The registered release executable is
  `/home/mjbommar/.cache/codex/glaurung-six-cell-target/release/examples/ioctlance`,
  SHA-256
  `d96520a04d5dd4825957dc3e07e1fd11a24bad220c55baae539ec9f8a10db5f7`.
  Before the first calibration process, `ldd` resolved the following complete
  file-backed set (the synthetic `linux-vdso.so.1` mapping has no file to hash):

  | resolved library | SHA-256 |
  |---|---|
  | `/home/mjbommar/.cache/codex/bitwuzla-0.9.1/lib/x86_64-linux-gnu/libbitwuzla.so.0` | `4e994b7a527e207dfdde3dcc289133f72e423e54e4ce67ba8ff2211c1b48bb1c` |
  | `/home/mjbommar/.cache/codex/bitwuzla-0.9.1/lib/x86_64-linux-gnu/libbitwuzlabb.so` | `3bc0a9fb5f1d4f5799ba2c71aec40b3616ad04a03942e5d23f639bb96b64a75b` |
  | `/home/mjbommar/.cache/codex/bitwuzla-0.9.1/lib/x86_64-linux-gnu/libbitwuzlabv.so` | `df3ffc2e41e92ff04c017b77b0e5b14b391ae687482542d47162b90aae0bfab3` |
  | `/home/mjbommar/.cache/codex/bitwuzla-0.9.1/lib/x86_64-linux-gnu/libbitwuzlals.so` | `83e70c846dcf33d0c8a3ecdf88e74b9fc7ce48de3aa1fc034c130190ab1365da` |
  | `/lib64/ld-linux-x86-64.so.2` | `223b94a42758f2434da331cc0aa62db1af5b456481762c5caceefa1a2d1eb8fb` |
  | `/usr/lib/x86_64-linux-gnu/libc.so.6` | `d763925433ff9b757390549e1b20c085f5e6de27ae700fe89194178d96a8a2b0` |
  | `/usr/lib/x86_64-linux-gnu/libgcc_s.so.1` | `9d339ecb409578d6a5d587e6c537a8f9589b8a13fefba30d167433a4b5758bee` |
  | `/usr/lib/x86_64-linux-gnu/libgmp.so.10` | `fda9699eef15deda5f1c626e9140377a7f5d88c41516a54278ac02429cb20fa5` |
  | `/usr/lib/x86_64-linux-gnu/libm.so.6` | `670fb59bd462ee2f833e2ed7c0a1814e0dcdbec0b8bfa048bec46e2e6fd66334` |
  | `/usr/lib/x86_64-linux-gnu/libmpfr.so.6` | `1aed080b3143049fbe016cd82cdc5fb47db386386556cc1bb37cfccc133c0fae` |
  | `/usr/lib/x86_64-linux-gnu/libstdc++.so.6` | `5bb0d21308f123b6ad46c6f35b42cedfcb8d6d439a53aa3dae04d880aaffdde3` |
  | `/usr/lib/x86_64-linux-gnu/libz3.so.4` | `eff8f0f91482d0809aae7aa0ed54cb52ff5ee9b5fe1ed1d2bfa9153c4a2fcfaf` |

Cold Z3 remains the sole exploration/model authority. Use A0's `AnyModel`
default and do not enable minimum, maximum, site-hash, set-valued policies, or
symbolic memory. Calibration is about A1 work configuration, not another
concretization sweep.

### Frozen backend-specific ladders

Run every row of this 14-tier table; do not stop early when one backend reaches
the target:

| tier | Z3 `rlimit` | Axeyum progress checks | Bitwuzla termination polls |
|---:|---:|---:|---:|
| 0 | 3 | 1 | 1 |
| 1 | 10 | 2 | 2 |
| 2 | 30 | 4 | 4 |
| 3 | 100 | 8 | 8 |
| 4 | 300 | 16 | 16 |
| 5 | 1,000 | 32 | 32 |
| 6 | 3,000 | 64 | 64 |
| 7 | 10,000 | 128 | 128 |
| 8 | 30,000 | 256 | 256 |
| 9 | 100,000 | 512 | 512 |
| 10 | 300,000 | 1,024 | 1,024 |
| 11 | 1,000,000 | 2,048 | 2,048 |
| 12 | 3,000,000 | 4,096 | 4,096 |
| 13 | 10,000,000 | 8,192 | 8,192 |

The aligned tier numbers are execution ordering only. The manifest and report
must state `cross_backend_unit_equivalence: false`; no ratio or fairness claim
may compare the numeric limits.

### Frozen execution protocol

Build one release `ioctlance` executable with
`solver-z3,solver-axeyum,solver-bitwuzla`. Run three fresh sequential processes
per tier, 42 processes total, tier-major and repetition-minor, pinned to logical
CPU 2. Each process uses a unique ordered-trace directory and exactly:

```text
GLAURUNG_FAIR_SHADOW=1
GLAURUNG_CHECK_TIMEOUT_MS=60000
GLAURUNG_Z3_RLIMIT=<tier value>
GLAURUNG_AXEYUM_PROGRESS_CHECK_LIMIT=<tier value>
GLAURUNG_BITWUZLA_TERMINATION_POLL_LIMIT=<tier value>
GLAURUNG_AXEYUM_REPLAY_SAT_CACHE=1
GLAURUNG_AXEYUM_WARM_MAX_LIVE_PATHS=9
GLAURUNG_AXEYUM_WARM_MAX_ASSERTIONS_PER_PATH=512
IOCTLANCE_ALL=1
IOCTLANCE_MAX_ANALYZED_FUNCTIONS=20
IOCTLANCE_SOLVE_BUDGET=400000
IOCTLANCE_SOLVE_SECS=900
IOCTLANCE_DEADLINE_SECS=2400
IOCTLANCE_ANNOTATE_CONFIDENCE=1
```

Do not enable synchronous Axeyum profiling, query dumping, CNF snapshots,
shadow-split output, warm timeout continuation/cold retry overrides, or an
authority-policy selector. Wrap each process with the repository memory guard,
`taskset -c 2`, and an outer 2,700-second process cap. Retain stdout, stderr,
exit status, raw trace, producer-validator result, executable hash, and dynamic
link report for every process. A failure is retained and is not silently rerun.

### Selection rule fixed before calibration

For each backend independently, select the smallest tier value for which both
its cold and warm cells satisfy all of the following on all three repetitions:

1. at least 95% of ordered occurrences decide;
2. the complete per-occurrence outcome vector is byte-identical across the
   three repetitions;
3. every decided verdict agrees with cold Z3 whenever both decide;
4. every nondecision is typed `resource-limit`; and
5. there are zero `wall-timeout`, `other`, operational error, no-solver,
   fallback, or invalid-delta rows.

The three selected limits may come from different tier indices. If any backend
has no qualifying value, calibration is rejected and no census confirmation is
authorized. Do not relax 95%, extend a ladder, drop cold or warm, or select a
larger value for prettier full-census results without a new ADR.

The calibration report must retain every tier and separately list, per backend
and topology, decided/resource-limit/wall/other counts, SAT/UNSAT/unknown
partitions, warm created/retained counts, exact ordered outcome hashes, timings,
and the mechanically selected value. Timing is descriptive only: calibration
does not rank solvers and does not enter the publication performance scalar.

### Confirmation boundary

Successful calibration does not itself authorize the census run. A subsequent
ADR must commit the exact selected triplet, frozen executable identity, full
338-function resource/deadline/solve boundaries, repetition count, finding and
fixed-work gates, and the analysis treatment of the 20-function calibration
prefix before any full-census v4 row is observed.

The intended confirmation remains PLAN item 3: the same six-cell topology under
the frozen limits, cold-Z3-authoritative raw/high-confidence findings, and a
complete 338-function census. Those findings are a deterministic bounded census
under one authority, not labeled recall and not cross-backend finding parity.
ADR-0262's first-20 canonical authority result remains the existing bounded
cross-authority control.

## Validity and interpretation

This calibration is accepted only if all 42 processes have exact source/input/
binary/configuration identity, publish validator-clean v4 traces, analyze the
same 20/338 function prefix, and reproduce each tier's full ordered outcome and
stop-reason vectors. Any wall safety hit, hidden outer deadline/timeout stop,
operational error, fallback, decided disagreement, source drift, or unstable
finding/work partition rejects calibration.

Raw and high-confidence findings are retained to verify fixed exploration but
are not a selection input. The tcpip population is unlabeled and currently
zero-high-confidence on the earlier prefix; cardinality cannot establish recall
or precision. No calibration timing or limit number supports a cross-solver
speed or equal-work claim.

## Alternatives

- Use one equal numeric limit for all solvers: rejected because the units are
  backend-specific and incomparable.
- Pick generous limits without calibration: rejected because that may reproduce
  the all-decided easy regime rather than characterize the harder frontier.
- Tune on the full 338-function census: rejected because it would adapt the
  confirmation boundary to its own results.
- Reuse the 250 ms wall: rejected because wall time is machine-load-sensitive
  and ADR-0262 already shows that 100--1000 ms is a no-op on this prefix.
- Make LeastUnsigned part of the matrix: rejected because its 25x solve-count
  cost and finding-set change would confound the work-bound experiment; A0 is
  already implemented and measured.
- Call the eventual cold-Z3-authoritative findings backend parity: rejected
  because shadow verdict agreement does not make the neutral cells exploration
  authorities.

## Consequences

A1 is now implementation-complete and moves from “wire resource limits” to
“register the exact release/linkage, then execute the preregistered calibration.”
It remains configuration and measurement, not a solver research project. A0
remains completed reproducibility infrastructure, A2 symbolic memory remains
closed, and the paper trajectory continues to be correctness + deployability +
rigorously bounded performance.
