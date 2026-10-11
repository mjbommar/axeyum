# OMT correctness validation — 2026-10-10

CON-5 is active in branch `fix/omt-correctness-20261010`, worktree
`/home/mjbommar/projects/personal/axeyum-omt-correctness`. Implementation commits: `3c7a4db1a` and `4555a025d`. Main remains at the
planning commit until the implementation gates finish. The entire user-feedback
goal remains open; this is one implementation increment.

## Verified evidence

- Commit `3c7a4db1a`: fresh `optimize` 25/25, `optimize_robustness` 14/14,
  `smtlib` 102/102. Generic OMT rejection, ray-based unboundedness, numeric
  ceilings, shared text deadlines and lexicographic priority controls passed.
- Same compiled integration binary, filter `ray_`: 4/4 baseline. Snapshot
  `/data0/axeyum/scratch/snap-omt-correctness-3c7a4db1a` deleted only the
  equality-preserving slope constraint (`Op::Eq => continue`). Mutant built
  and ran the same 4 tests: 3 passed, exactly 1 failed, exit 101.
  `ray_cannot_ignore_a_coupled_upper_bound` incorrectly returned Unbounded
  instead of Optimal(10). This is a measured kill, not a build failure.
- Follow-up closed-affine coefficient guard: `--lib --features full
  ray_constant_controls` ran 2/2 tests. Both valid ground arithmetic and
  underspecified div/mod-by-zero coefficient classes were exercised.
- `cargo fmt --all --check`, generated plan/ADR checks and whitespace passed
  before the coefficient follow-up; rerun formatting/checks after final edits.
- Module-graph ratchet was compared to the parent/main sources: both report
  the same cycle-member failures, largest cycle 139,932 lines, and evidence
  fan-out failures. No new cycle members or fan-out destinations were introduced.
  The parent exits 1: this is a pre-existing red gate, not a pass.

## Additional verified controls

- Coefficient snapshot `4555a025d`: replacing only `affine_constant`'s syntactic
  decline with empty-assignment evaluation built and ran both baseline controls.
  The exact arithmetic control passed; the div/mod-by-zero control failed.
  Baseline 2 pass; mutant 1 pass/1 fail, exit 101. Exactly one guard control died.
- Independent finite population: 128 seeded two-variable affine maximization
  problems on [-4,4]^2, compared to exhaustive mathematical enumeration.
  `affine_optimization_matches_an_independent_finite_population`: 1 test passed,
  all 128 cases agreed, 0.23 s.
- Workspace library run stopped in axeyum-cas: 2,139 passed, 1 failed, 11 ignored.
  The untouched `matgroup::tests::psl2_f7_isomorphic_to_gl3_f2` timing guard
  measured 13.476 s against its 5 s budget. Its isolated compiled-binary rerun
  passed 1/1 in 1.82 s. This is not a passing workspace gate.
- Initial front-door group stopped in `qf_slia_fixed_splice`: corpus 2/2,
  online_string_front_door 48/48, fixed-splice 81 pass/1 fail. The failed
  `large_split_replace_pipeline_retains_the_fast_source_fallback` fixture uses
  a 5 s budget. Its isolated rerun passed 1/1 in 4.54 s. The two later test
  targets were not executed by that stopped cargo invocation. A serial
  five-target rerun is now required and running.

## Running validation — no completion credit yet

Live tool handles at this record: solver full library suite `53469`,
integration/fuzz/frontier runner `67664`. Workspace handle `5907` is terminal
(failed as above); coefficient mutation `24255` is terminal with the expected
one-test kill. Serial front-door rerun handle is recorded in the active turn;
its log path starts `/var/tmp/axeyum-omt-front-recheck-`.
The independent finite-population run `97892` is terminal (passed).
The solver full suite began with 2,007 tests before the 2 added coefficient
controls; the follow-up control run has 2,009 total collected and ran 2.
Integration/fuzz/frontier logs are under
`/var/tmp/axeyum-omt-gates-7pwuny00`. Re-poll the live handles; do not restart
merely because a poll has no new output. Validate process state if a handle is
missing, and record final exit/counts before assigning credit.

Both required checker mutations are complete; never reapply them to the active
worktree. Broad gates still need terminal results and a clean workspace rerun
before integration. The full solver run began before the two added coefficient
controls; rerun the final 2,009-test suite if its final result warrants doing so.

## Still required for CON-5

Preemptible optimization ingest; Python optimizer result/model API; source-bound feasible
models and no-better-solution certificates; independent optimization differential
fixtures and explicit box/lex semantics. Resource exhaustion is Unknown, and
an arbitrary SAT result remains ineligible for optimization gold answers.

Other feedback tracks (CAS traces/exact syntax, SAT route exports/Alethe gaps,
signed literals, Date/rule API and sourced statute pack) remain queued in PLAN.

## Remaining-budget follow-up — 2026-10-10

All LIA/BV lexicographic, box and Pareto child calls now receive the remaining
absolute budget; all four single BV optimizers check expiry before the first
probe and pass the remaining timeout to each probe. Fresh integration runs:
optimize 25/25; optimize_robustness 16/16, including zero-budget coverage of
unsigned/signed minimize/maximize.

The five linear differential suites are terminal: 4 + 5 + 8 + 2 + 1 = 20
passing tests (see linear_differentials.log). The frontier runner remains live.
Full-library handle 53469 is now missing and its process is absent; terminal
output was not retained, so no full-library completion credit is assigned.
Serial front-door handle 25752 remains live. Frontier output modifies
bench-results/frontier/bv_reduction.json; that generated measurement is excluded
from this code commit until the full measurement concludes.

## Frontier terminal result

Runner 67664 exited 1: its original front-door group failed as recorded above;
linear differentials all passed; progress_frontier had 11 pass/1 fail in 443.77 s.
`frontier_nra_degree` retained N=40 but calibrated pinned timing 39.4 ms exceeded
the committed 23.0 ms ceiling (load 23.25, calibration scale 1.96x). No timing
threshold or baseline is changed. A quiet isolated rerun is needed; calibration
already compensates for machine speed, so load alone does not prove innocence.
Generated frontier JSON files are uncommitted measurements, not implementation
changes. Serial front-door runner 25752 remains live.

## Serial front-door completion and fresh broad gates

Handle 25752 completed exit 0: corpus 2, online_string_front_door 48,
qf_slia_fixed_splice 82, stoi_len_abstraction 13, word_first_fallback 13;
158 passed total. The previously timed-out fixture passed unchanged.
Fresh logged full-library and workspace reruns now run sequentially via handle
56794, logs `/var/tmp/axeyum-omt-final-gates-1ouedtr1/`; use one test thread.
The full solver suite includes the 2 coefficient controls (2,009 collected
expected). No result is credited yet. These runs use source `9e572a32a`;
subsequent changes in this commit are documentation only.

## Fresh full-feature gate terminal finding

Logged solver_full gate completed: 2008 passed, 1 failed, 0 ignored in
1576.44 seconds. The failing test is
`euf_egraph::tests::check_qf_uf_with_config_is_bounded_by_timeout`: the generous
budget pigeonhole control returned Unknown (`boolean skeleton undecided`)
instead of Unsat. No timeout threshold or untouched EUF source was changed.
This is a red gate requiring quiet/parent investigation, not a pass attributed
to load. Workspace gate remains live: authoritative cargo process 2304299 was
observed with `--workspace --lib -- --test-threads=1`; its log is
`/var/tmp/axeyum-omt-final-gates-1ouedtr1/workspace.log`.
