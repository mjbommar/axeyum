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

## Remaining release gate

Amend ADR-0377 and the earlier A5 repair record, validate documentation and
plan authority, commit and push the bounded repair, then rebuild and repeat the
target/control discriminator at the exact pushed commit. One uninterrupted
external-frontier `just check` must exit 0 before the V2 census restarts. The
existing three captures remain permanently non-credited regardless of this
candidate's success.
