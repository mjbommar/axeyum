# QF linear A5 pre-SAT boundary monotonicity v1 result — 2026-08-10

## Outcome

The [preregistered](qf-linear-a5-pre-sat-boundary-monotonicity-v1-preregistration-2026-08-10.md)
moderate-envelope candidate passes its target and safety-control gates. The
candidate retains the joint 1,024-atom/4,096-CNF-variable trigger, but admits a
query inside the conjunctive rectangle of at most 1,280 atoms and at most 8,192
variables. No timeout, memory ceiling, normalization budget, route order, or
proof policy changes.

This repairs one deterministic historical-decision loss. It is not an A5 score
gain and does not credit the failed V2 census. The complete three-division
sequence must restart from QF_LRA row 1 after exact commit, push, and the full
repository gate.

## Failed census boundary

Exact pushed repair `5a53012e13757e4f992e6197d83b9f12a6268471`
passed the complete `just check` gate, then produced structurally valid atomic
QF_LRA, QF_IDL, and QF_RDL captures with 200 rows and zero stderr each. The
strict derivation stopped before producing outputs because
`QF_LRA/sal/windowreal/windowreal-no_t_deadlock-17.smt2` changed from historical
UNSAT to typed resource `unknown`.

The non-credited
[`V2-census-attempt-001.failure.json`](evidence/qf-linear-a5/failures/V2-census-attempt-001.failure.json)
binds the exact 11,859,024-byte binary, all three raw-capture and metadata
digests, the 600 emitted records, and the first derivation error. Aggregate
decision counts were insufficient: QF_LRA still rose from 86 to 89 total
decisions because gains hid the one loss.

## Candidate discriminator

The preliminary release candidate was built from base `5a53012e1` with source
diff SHA-256
`eda066b52f534ccc1b742fca3511d316ec6eef5c4e9c32b14ca52b458e529a83`.
Its 11,859,360-byte binary has SHA-256
`48f21d7d3cc14846ff423bcd33c7425a5b5bade1f444861a213ef9337af17e3c`.
All observations started at one-minute load 10.97 or 11.46 on the required
24-core host, used a fresh process with inherited 8 GiB `RLIMIT_AS`, retained
the 24,000 ms query timeout, exited 0, and emitted zero stderr.

| Role | Verdict | Observations | Wall time | Peak RSS | JSONL SHA-256 |
|---|---|---:|---:|---:|---|
| lost `windowreal` control | UNSAT | 3/3 | 0.10--0.20 s | 16,920--17,468 KiB | `842ec285aba3d7997ce452a2bebcf7dd179f78e18fa5634306134781889c8b54` |
| `pursuit-safety-16` abort control | typed pre-SAT unknown | 1/1 | 0.10 s | 15,356 KiB | `4e8ce39ccaf529b4234026ff6542484845b5f7c7b7159c565940180fa2925a94` |
| `tgc_io-safe-20` abort control | typed pre-SAT unknown | 1/1 | 0.10 s | 17,276 KiB | `9a60c6076f2c5e5bb94ff8d5641879d6da14ae31a6a5215c80c8737d00828368` |
| 31,944-variable IDL control | typed pre-SAT unknown | 1/1 | 18.32 s | 50,192 KiB | `8dfd9a3a5db73b1f4d5e3acd656700ca7b482fc413a5f3b36ad0830a870f93b1` |

The target's three route traces are byte-identical and terminate with
`lira-dpll` UNSAT. Every safety control terminates with the joint-boundary
resource decline before the first SAT round. The candidate therefore changes
only the one measured pre-SAT decline among all 600 non-credited V2 rows.

## Exact pushed-commit replay

Repair commit `8a6de50ac96c2a8e0056c405f446417563d83a89` is exact across
local `HEAD`, its upstream-tracking ref, and the remote topic ref. Its normal
pre-push gate passed compile, format, non-vacuous corpus, workspace/default and
full-feature solver unit, capability-frontier, always-on integration, and
evidence suites. The hook's first attempt could not materialize its detached
checkout on the `/tmp` tmpfs; the identical exact-SHA checkout and unchanged
gate passed with `TMPDIR` on disk-backed storage. No verification step was
bypassed.

The release executable rebuilt from the clean exact pushed commit is
11,859,344 bytes with SHA-256
`eec4813b557165ec95afc43912ad9fc2b5400ec94db5b7134ecacd50b100867d`.
Every credited replay observation started at one-minute load 11.83, used one
fresh process with the inherited 8 GiB address-space limit and 24,000 ms query
timeout, exited 0, and emitted zero stderr. An earlier same-binary observation
set started above the registered load boundary and is diagnostic-only.

| Role | Verdict | Observations | Wall time | Peak RSS | JSONL SHA-256 |
|---|---|---:|---:|---:|---|
| lost `windowreal` control | UNSAT | 3/3 | 0.10 s | 16,296--16,856 KiB | `842ec285aba3d7997ce452a2bebcf7dd179f78e18fa5634306134781889c8b54` |
| `pursuit-safety-16` abort control | typed pre-SAT unknown | 1/1 | 0.10 s | 14,864 KiB | `4e8ce39ccaf529b4234026ff6542484845b5f7c7b7159c565940180fa2925a94` |
| `tgc_io-safe-20` abort control | typed pre-SAT unknown | 1/1 | 0.10 s | 16,448 KiB | `9a60c6076f2c5e5bb94ff8d5641879d6da14ae31a6a5215c80c8737d00828368` |
| 31,944-variable IDL control | typed pre-SAT unknown | 1/1 | 18.12 s | 49,868 KiB | `8dfd9a3a5db73b1f4d5e3acd656700ca7b482fc413a5f3b36ad0830a870f93b1` |

The exact target output is byte-identical to the preliminary target output,
and every exact control digest is likewise unchanged. The pushed repair
therefore passes the preregistered discriminator; this still does not credit
the invalidated V2 census.

## Focused gates

- formatting and strict all-target/all-feature solver Clippy pass;
- both exact helper-boundary unit tests pass;
- all 1,091 all-feature solver-library tests pass;
- deep-input no-abort passes 16/16;
- online LIA/LRA and generic CDCL(T) integrations pass 41/41, including
  nonzero deterministic differential coverage;
- QF_LRA/Z3 differential fuzz passes 5/5 over 1,500 generated cases with 1,499
  agreements, one typed Axeyum unknown, and zero disagreements; and
- simplex/Z3 fallback differential passes 1/1 over 1,200 jointly decided cases
  with zero unknowns, timeouts, or disagreements in 118.53 seconds.

## Complete repository gate

Exact pushed documentation checkpoint
`3267432a71818fb0671df8f2324f15e213debc08`, whose code includes repair
`8a6de50ac96c2a8e0056c405f446417563d83a89`, passed one uninterrupted
external-frontier `just check`. It ran from `2026-08-10T09:01:57Z` through
`2026-08-10T10:48:47Z` (6,410 seconds) and exited 0. Local `HEAD`, upstream,
and the remote topic ref were exact at the gated checkpoint before and after
the run. The 585,679-byte log has SHA-256
`dc8e3b37f9d253b9122a1ebf483d8fd4f445fc17a282b4f356b8e94bef9062b1`.

The gate includes strict formatting and linting, all-feature workspace tests
and doctests, the 9/9 external progress frontier with five retained artifacts,
both ignored CAS moment-family proofs, warning-denied rustdoc, QF_BV and
reflection gates, the 162-file Glaurung corpus in raw and canonical modes,
foundational resources, rules-as-code, SMT-COMP resume/scoring contracts, Lean
contracts, parity documentation, plan authority, and link validation. The V2
census is therefore authorized to restart at QF_LRA row 1. The existing three
captures remain permanently non-credited regardless of this repair's success.
