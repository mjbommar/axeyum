# Arithmetic A1 retained-result closure — 2026-08-06

## Verdict

Arithmetic deadline and resource enforcement is complete for the bounded A1
contract. The implementation is integrated on `main`; all six preregistered
200-file arithmetic divisions were rerun from row 1 with the shipped default
configuration, 24-second wall budget, 8 GiB per-file cap, and cvc5 1.3.4 as the
installed reference. Axeyum produced zero disagreements.

The retained measurements are:

| Division | Axeyum | Reference | Ratio | Disagreements | Solver commit | Current sidecar SHA-256 |
|---|---:|---:|---:|---:|---|---|
| QF_NIA | 34/200 | 89/200 | 38.2% | 0 | `a505e67e7` | `392e6cc33423518a44015a98cb1c7fdf867ea1c33ffd1cb77f761316acb5d524` |
| QF_LIA | 117/200 | 140/200 | 83.6% | 0 | `a505e67e7` | `9cb1801270054d570948d24c4384aadbd5220769eaf477cdccffecbe51f2f72d` |
| QF_LRA | 86/200 | 146/200 | 58.9% | 0 | `8ea6a7cad` | `106913be84886cdb2e83894cdde8d327ea7c3cad75504e397d8a6876a88e9add` |
| QF_RDL | 105/200 | 155/200 | 67.7% | 0 | `b353419e7` | `be59cfacc18eab60225d5f0990e6614d1b55299a60f809c77992ca56d034aab1` |
| QF_IDL | 68/200 | 124/200 | 54.8% | 0 | `198f2dc1b` | `2debb3525937eefd6a1b0a62c4aedb406766f80f0a558393ade9df7594a0d862` |
| QF_UFLIA | 94/200 | 180/200 | 52.2% | 0 | `71ca85d9f` | `921299a93e2895d59741115036150156e7a294d8182f5e2e46086b9330c00b78` |

The differing solver stamps are intentional. Each ledger entry records the
clean commit from which its release executable was reproducible; intervening
commits after `a505e67e7` either hardened measurement identity, integrated the
IDL repair, or retained already-completed results.

## A1 implementation and gates

Commit `96ff85930` (merge `14f80a2bf`) established one query-global arithmetic
deadline across sequential routes, inserted cancellation checks inside CAD
work, and imposed deterministic online-LRA normalization ceilings. The focused
deadline, LRA, and CAD tests passed, followed by the all-feature solver gate:
1,073 library tests plus all integration and doctest binaries. The repaired
250 ms public QF_NIA case returns bounded `Unknown(Timeout)`, and the historical
8 GiB QF_LRA normalization abort now declines around 13 MiB.

The clean topic branch for the later IDL repair, commit `4477f2bb9`, completed
terminal `CARGO_BUILD_JOBS=2 just check`, including format, all-feature Clippy,
workspace tests and doctests, the 9/9 progress frontier, both retained order-255
CAS proofs, rustdoc, QF_BV profiles, reflection, Glaurung, foundational
resources, rules-as-code, SMT-COMP resume checks, parity docs, Lean checks,
plan authority, and links. Its exact-SHA pre-push gate was green. Merge
`198f2dc1b` also passed the immutable-SHA pre-push workspace-library,
progress-frontier, and evidence gates. On integrated main, the focused DL suite
passed 46/46 and the auto-dispatch fallback regression passed 1/1.

A first broad post-merge attempt failed while linking because the filesystem
had only 585 MiB free; this was an environmental `No space left on device`
failure, not a test verdict. The completed topic `just check`, exact merge-SHA
pre-push gate, and post-merge focused tests are separate evidence states; no
terminal full `just check` on the merge commit is claimed.

## QF_IDL root cause and repair

The first current-main QF_IDL sweep found a real retained-decision regression:
the checked difference-logic probe consumed the whole request budget before the
ordinary arithmetic fallback could run. Bypassing the probe restored
`sal/lpsat/lpsat-goal-18.smt2` as UNSAT in about 7.4 seconds. The old credited
solver, the pre-repair parent, and the initial current build all returned
unknown when the probe was allowed to exhaust its share.

The repair starts the probe deadline at entry and polls it during mode and DAG
scanning, linearization, equality expansion, encoding, clause materialization,
and solving. The default 24-second allocation remains 18 seconds for the probe
and 6 seconds for fallback. Numeric equality gates with at least 128 and at
most 1,024 atoms use a measured 12/12 split. A global 12/12 policy was rejected
because it lost five retained controls. The adaptive policy preserved all 171
QF_IDL/QF_RDL controls in a full A/B check.

The final clean QF_IDL sweep produced 68/200 rather than the pre-fix 66/200.
Against the credited baseline it gained
`BubbleSort_safe_blmc016.smt2` (UNSAT) and
`rand_15_75_1235849326_0_k=3_v=7_e=30_sat.gph.smt2` (SAT), with no losses.
Against the immediate pre-fix sweep it gained the same graph SAT case and
recovered `lpsat-goal-18.smt2` (UNSAT), with no losses. All 200 normalized
basenames were unique in both comparisons. Reference-only count movement is
wall-time noise and does not affect Axeyum credit.

## Retention qualification

QF_NIA, QF_LRA, QF_RDL, QF_IDL, and QF_UFLIA were monotone against their
accepted retained controls. QF_UFLIA's complete 200-row status matrix was
identical after normalizing the legacy basename-only sidecar to exact paths.

The QF_LIA whole sweep recorded 117 rather than the older 118. The sole missing
row, an `ex3000...` benchmark, was rerun independently three times and returned
UNSAT each time in about 8.1 seconds, well inside the 24-second protocol. It is
therefore classified as shared-host sweep timing noise, not a semantic or
resource-regression loss. The ledger deliberately retains the lower 117 result.

## Measurement identity repair

During the six-run sequence, the legacy resume mechanism was found to key rows
only by basename. Commit `5ce07c55e` (merge `8ea6a7cad`) replaced it with a
fail-closed exact-path normalizer. Exact committed-list paths are the canonical
keys; legacy basename-only sidecars are accepted only when the mapping is
unique. Duplicate rows, ambiguous basenames, and population drift fail closed.
The retained arithmetic runs in this note were fresh, non-resumed sweeps.

## Storage recovery

The post-merge linker failure exposed accumulated build artifacts rather than a
source defect. Bounded cleanup reclaimed old Cargo targets from merged clean
worktrees and `~/.cache/axeyum-agent-targets`, then removed only clean merged
worktree checkouts plus one redundant detached `/tmp` checkout. Dirty and
unmerged worktrees and all branches were preserved. The result was 885 GiB free
at cleanup completion (882 GiB after the retained runs), cache size 81 MiB, and
44 registered worktrees, down from 62.

This incident motivates A11 in the canonical plan: inventory and retire
disposable worktrees and targets before free space becomes a correctness or CI
problem, without deleting live or unmerged work.

## Git and remote evidence

- arithmetic resource implementation: `96ff85930`, merge `14f80a2bf`;
- resume identity repair: `5ce07c55e`, merge `8ea6a7cad`;
- IDL repair: `4477f2bb9`, merge `198f2dc1b`;
- retained ledgers: `c5d617c10`, `b353419e7`, `54b366517`, `71ca85d9f`, and
  `ebbabb34c`;
- current audited `main`: `ebbabb34c9e2aa213a5e7aa7f1634acc68b2e374`, equal
  to `origin/main` when this result was written.

The last observed terminal full remote CI remains run `31076938255` at
`94082977d`; the latest observed docs run is `31108211479` at `54b366517`, both
green. No GitHub workflow run was visible yet for `198f2dc1b`, `71ca85d9f`, or
`ebbabb34c`. Those remote gates are therefore unobserved/pending, not green.
