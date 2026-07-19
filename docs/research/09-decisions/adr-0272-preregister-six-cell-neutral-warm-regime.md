# ADR-0272: Preregister the six-cell neutral warm regime map

Status: proposed
Date: 2026-07-19

## Context

ADR-0215/0217 replaced the invalid fresh-Z3/retained-Axeyum headline with a
topology-equivalent `{Z3, Axeyum} x {cold, warm}` map. That map is genuinely
workload-dependent: warm Axeyum wins on IntcSST and SurfacePen, is at parity on
vwififlt, and loses on DptfDevGen. ADR-0222/0223 add cvc5 as a neutral verdict
oracle and cold/reset external-SMT point, but neither an external reset protocol
nor an external retained text protocol is an in-process topology peer.

The reviewer checklist therefore still has one performance confound: the two
in-process implementations in the fair map are both project participants. A
neutral in-process solver must receive the same cold and retained source-owner
topologies before the regime map can be framed as more than a two-implementation
comparison.

Glaurung ADR-031 implements the missing mechanism on isolated commit
`2961d7c1bca03f14b77b12fb852d193413207982`. It adds a benchmark-only direct
binding to the official Bitwuzla 0.9.1 C API, extends the ordered measurement
contract to v3, and keeps cold Z3 authoritative. This ADR freezes the experiment
before implementing the Axeyum-side v3 analyzer and before observing any
real-driver timing row.

## Decision

Run one self-contained six-cell experiment over the four previously accepted
drivers. Every authoritative ordered check must independently time, in a
cyclically rotated order:

1. cold Z3: shared thread-local context, fresh solver;
2. warm Z3: retained solver for the exact source owner;
3. cold Axeyum: fresh solver;
4. warm Axeyum: retained direct-lineage solver for the same source owner;
5. cold Bitwuzla: shared thread-local term manager, fresh solver; and
6. warm Bitwuzla: retained solver for the same source owner.

All warm cells consume the same immutable source-prefix ancestry, serial owner
lease, one-scope-per-persistent-assertion transition, and temporary-assumption
partition. Cold Z3 remains the only exploration and model-choice authority.
Bitwuzla is a benchmark-only neutral cell and must never enter production solver
selection.

### Frozen source and runtime identities

- Glaurung: clean isolated commit
  `2961d7c1bca03f14b77b12fb852d193413207982`.
- Axeyum implementation baseline:
  `a9abc6cdcdda0451e6a9b6aca5f8ff924e49e513`; the measured path is unchanged
  from that revision. Its `axeyum-solver` tree is
  `ec3a38f3244d1d2e9d3b57f66f6079fca19ceba6`, `axeyum-ir` tree is
  `ed3649e3a52fbd602327ea523db49bac3a883b6a`, workspace manifest blob is
  `e1351bec59d6601b6a60c774f1d00a01be1dc3e4`, and lockfile blob is
  `2738bf0d289afea537f444fe0152b040f68278fa`.
- Bitwuzla: official tag `0.9.1`, source commit
  `8d1eb01093ae54d9b4586456b69c3bf31000a4c2`; linked
  `libbitwuzla.so.0` SHA-256
  `4e994b7a527e207dfdde3dcc289133f72e423e54e4ce67ba8ff2211c1b48bb1c`.
  The three installed internal libraries have SHA-256 values
  `3bc0a9fb5f1d4f5799ba2c71aec40b3616ad04a03942e5d23f639bb96b64a75b`
  (`libbitwuzlabb.so`),
  `df3ffc2e41e92ff04c017b77b0e5b14b391ae687482542d47162b90aae0bfab3`
  (`libbitwuzlabv.so`), and
  `83e70c846dcf33d0c8a3ecdf88e74b9fc7ce48de3aa1fc034c130190ab1365da`
  (`libbitwuzlals.so`).
- The current resolved arithmetic dependencies are Ubuntu `libgmp10`
  `2:6.3.0+dfsg-5ubuntu2`, SHA-256
  `fda9699eef15deda5f1c626e9140377a7f5d88c41516a54278ac02429cb20fa5`,
  and `libmpfr6` `4.2.2-3`, SHA-256
  `1aed080b3143049fbe016cd82cdc5fb47db386386556cc1bb37cfccc133c0fae`.
  Z3 is Ubuntu `libz3-4` `4.13.3-1build1`, SHA-256
  `eff8f0f91482d0809aae7aa0ed54cb52ff5ee9b5fe1ed1d2bfa9153c4a2fcfaf`.
  The final executable's complete `ldd` resolution and hashes must be retained
  before capture; a build RUNPATH is not accepted as proof of a transitive
  dependency's identity.
- Toolchain and host registration: `rustc 1.97.0-nightly
  (f53b654a8 2026-04-30)`, Linux `7.0.0-27-generic`, x86_64, host `server0`.

The Glaurung feature must fail closed when `BITWUZLA_LIB_DIR` is absent and must
reject a runtime API version other than exactly `0.9.1`. The default Glaurung
build must remain valid without any Bitwuzla environment configuration.

### Frozen driver population

Use these exact files from the frozen Glaurung tree, in this driver order:

| driver | SHA-256 |
|---|---|
| `samples/binaries/platforms/windows/vendor/realworld/sqfs-intel-DptfDevGen.sys` | `074be1b90deb21897538a6b093af9826e62610ffd878c92289af31c5ca3f724b` |
| `samples/binaries/platforms/windows/vendor/realworld/win10-vwififlt.sys` | `13c3b69a5d0179ed3cc2c999ff97edbaedd63da55ddb74427251c360706a3820` |
| `samples/binaries/platforms/windows/vendor/realworld/windows-update-intel-audio-IntcSST.sys` | `f7c8e4f106baa5b2a1a18e60731ad42a6f734aee1d049576eaf6d123d5629750` |
| `samples/binaries/platforms/windows/vendor/realworld/windows-update-SurfacePenBleLcAddrAdaptationDriver.sys` | `3c062dc57832caab776bec99656798474af7ffb59ef751c9a004a95c0ae74405` |

These are the same four named regimes used by ADR-0215/0217. Do not add or
remove a driver after observing results. The new six-cell captures are
self-contained; historical v2 timings may be shown for context but may not be
pooled with the new revision.

### Frozen execution protocol

Build once under the repository's 64 GiB guard with two Cargo jobs:

```sh
BITWUZLA_LIB_DIR=/home/mjbommar/.cache/codex/bitwuzla-0.9.1/lib/x86_64-linux-gnu \
BITWUZLA_RUNTIME_LIB_DIRS=/home/mjbommar/.cache/codex/bitwuzla-0.9.1/lib/x86_64-linux-gnu \
CARGO_TARGET_DIR=/home/mjbommar/.cache/codex/glaurung-six-cell-target \
CARGO_BUILD_JOBS=2 \
/home/mjbommar/projects/personal/axeyum/scripts/mem-run.sh \
  cargo build --release --example ioctlance \
  --features solver-z3,solver-axeyum,solver-bitwuzla -j2
```

Run five sequential fresh processes per driver, driver-major, pinned to logical
CPU 2. Each process uses a unique `GLAURUNG_ORDERED_TRACE_DIR` and exactly:

```text
GLAURUNG_FAIR_SHADOW=1
GLAURUNG_CHECK_TIMEOUT_MS=250
GLAURUNG_AXEYUM_REPLAY_SAT_CACHE=1
GLAURUNG_AXEYUM_WARM_MAX_LIVE_PATHS=9
GLAURUNG_AXEYUM_WARM_MAX_ASSERTIONS_PER_PATH=512
IOCTLANCE_DEADLINE_SECS=600
IOCTLANCE_MAX_ANALYZED_FUNCTIONS=100000
IOCTLANCE_SOLVE_BUDGET=20000
IOCTLANCE_SOLVE_SECS=60
```

Do not enable query dumping, Axeyum synchronous profiling, CNF snapshots,
shadow-split output, authority-policy changes, or any adaptive warm policy.
Wrap each process in `scripts/mem-run.sh taskset -c 2`. Preserve every raw trace,
stdout/stderr log, exit status, manifest, producer-validator result, executable
hash, and dynamic-link report. A failed or noisy run is retained; it is not
silently replaced. Any retry requires a new preregistration unless failure is a
pure runner/schema defect that occurs before a timing row is observed.

### Analyzer contract fixed before capture

Extend `scripts/analyze-glaurung-paired-traces.py` additively for
`glaurung-ordered-check-measurement-v3`, preserving v1/v2 behavior. The v3
consumer must:

- bind `neutral_measurement_backend` to non-authoritative Bitwuzla 0.9.1;
- require all six positive timings and valid outcomes on every check;
- reject any operational result or decided disagreement in any cell;
- require exact ordered check identities, configuration, source, driver,
  purpose, scope digest, warm execution class, and check count across the five
  repetitions;
- require all three warm execution classes to be only `warm-created` or
  `warm-retained` for an accepted performance row; fallback or invalid-delta
  classes reject that driver's performance result;
- report all-cell decision populations and created/retained counts rather than
  hiding `unknown`; and
- retain the legacy cold-Z3/warm-Axeyum aliases only as compatibility fields,
  never as the neutral headline.

For each driver, report these nine preregistered paired contrasts separately:

```text
cold: Z3/Axeyum, Z3/Bitwuzla, Axeyum/Bitwuzla
warm: Z3/Axeyum, Z3/Bitwuzla, Axeyum/Bitwuzla
reuse: Z3 cold/warm, Axeyum cold/warm, Bitwuzla cold/warm
```

For every contrast, the population contains only occurrences decided by both
named cells in every repetition. Collapse each occurrence across repetitions by
the geometric mean of its paired ratios, then report the geometric mean across
occurrences, a deterministic 10,000-sample bootstrap 95% interval with seed 0
(using distinct fixed offsets per contrast), nearest-rank p50/p90/p95/p99
latencies, and per-process geomean coefficient of variation. Ratios are always
named numerator/denominator; values greater than one favor the denominator.
Never report a ratio of sums.

Also report one stricter all-six population. A driver supports the neutral
regime claim only if every occurrence is decided with one identical verdict in
all six cells and all five repetitions, all warm checks are created/retained,
and each primary warm pair's process-geomean CV is at most 3%. A gate failure is
a result: retain and classify the driver as inconclusive under this protocol.
Do not pool drivers into one headline scalar, rank solvers by majority vote, or
infer a causal explanation merely from their ordering.

### Zero-row boundary

At this registration there are no real-driver v3 timing rows and no v3 analyzer
implementation. The only observations are mechanism tests: the linked version,
full-width model lifting, full Glaurung QF_BV translation, incremental scope and
assumption restoration, source-ancestry sibling rewind, six-cell SAT execution,
and v2/v3 structural fixtures. The all-three-backend library suite passes
1,030/1,032 tests; the two residual WinAPI signature-render failures reproduce
on the untouched baseline and are documented by Glaurung ADR-030.

## Evidence

The design directly closes reviewer-checklist item 1's neutral warm-baseline
part without changing solver authority. It also preserves the checklist's
strict-correctness lesson: malformed Bitwuzla model text becomes an explicit
error, all cells expose `unknown` and operational failures, and the independent
producer validator rejects partial or mixed v2/v3 records.

The experiment is intentionally not the timeout-sensitive/harder-driver tier.
That remains PLAN item 3 and will use a deterministic resource bound after this
neutral map is accepted or retained as inconclusive.

## Alternatives

- Treat cvc5 reset/retained text protocols as the missing in-process cell:
  rejected because process, parsing, and serialization topology differ.
- Use Bitwuzla only as a correctness oracle: rejected because it does not test
  the warm performance mechanism.
- Make Bitwuzla authoritative: rejected because it would change exploration and
  confound the measurement.
- Share one Bitwuzla solver while calling the cell cold: rejected because it
  would retain solver state unavailable to the other cold cells.
- Compare only the three warm cells: rejected because the within-solver
  cold/warm effects are necessary to interpret topology.
- Add a harder driver now: rejected because that is a separately bounded and
  separately preregistered experiment.

## Consequences

The immediate trajectory is now precise: implement and test the registered v3
consumer, build the frozen executable, verify its dynamic linkage, run exactly
the four-driver N=5 campaign, and accept or retain the result without tuning.
Only then does the integration lane move to PLAN item 3's deterministic harder
tier. A0 remains completed reproducibility infrastructure; this ADR does not
reopen concretization coverage or symbolic memory.
