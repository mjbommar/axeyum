# Python OMT validation record

## 2026-10-11 — source 933fbbe02

Native build runner 56910 completed successfully, log
`/var/tmp/axeyum-python-omt-933fbbe-native.log`. Sealed package:
`/var/tmp/axeyum-omt-933fbbe-python-w3t35nug/package`; imported path checked.
SHA-256 `89d3ef632addb05f453fa4ee2814b51ed34f8bab81cfcc1547a9fd108cae8e85`.
Python runner 75545 terminal zero: 127 collected, 93 passed, 34 skipped, 3.60s.
Suites: test_smt_optimization, test_smt, test_smt_proof_regressions,
test_rules_dates, test_rules_packs, test_rules_statute_deadline. Skipped CLI
comparisons do not count as passing. All six OMT tests executed and passed.

Full solver then workspace runner 55477: logs
`/var/tmp/axeyum-omt-933fbbe-required-ocedt22l/`; per-job exit files authoritative.
Still running, no full-gate credit. Stub generator runner 53264: log
`/var/tmp/axeyum-omt-933fbbe-stub.log`, no result credited.
Private snapshot `/data0/axeyum/scratch/snap-python-omt-results-933fbbe02`;
mutation baseline runner 75540, log
`/var/tmp/axeyum-omt-933fbbe-mutation-baseline.log`, compiling. No guard mutation
has been performed yet. Required follow-up: both replay-guard mutations,
string-lifting discriminating control, CLI nonzero controls, generated stub gates,
front-door suites, arithmetic differential fuzzes, and broader validation.

Follow-up: baseline 75540 terminal zero, 7 passed / 0 failed / 0 ignored.
Mutation runner 45506 now checks both guards sequentially; completion uncredited
until its asserted terminal result. New Python test
`test_declared_string_model_is_lifted_without_decoding_real_bitvectors` passes
against the sealed revision binary; OMT suite now 7 collected / 7 passed, 0.15s.
Separate probes also replayed Int and BV optima with String model `AB`.

Added `python/examples/smt_optimization.py` and user-guide API documentation.
The sealed extension executes all four lex/box model replays with expected
values and explicit false gold eligibility; example terminal exit zero.

Independent finite-domain optimum controls: new Python test enumerates original
integer tuples for 24 cases (two x bounds, two y bounds, three coupled sum
bounds, minimize/maximize first objective). It derives the lexicographic
optimum without calling the solver, checks both exact reported values, replays
every retained model, and checks each witness belongs to the enumerated feasible
population. Fresh sealed-binary OMT suite: 8 collected, 8 passed, 0.13s. This
finite regression oracle does not grant general optimality-certificate credit.

Current full-solver log now explicitly reports
`euf_egraph::tests::check_qf_uf_with_config_is_bounded_by_timeout ... ok`
at line 557. Earlier integration failure is not reproduced on this source run;
full suite remains live and this single test is not a full-gate pass.
Optimality route inspection: `alethe_lra.rs::prove_lra_unsat_alethe` converts
assertions into assumptions and emits `la_generic`; `check_alethe_lra` validates
the proof's content rather than receiving the original query. OMT acceptance
therefore requires an independent assertion-to-assumption binding check as well
as the proof checker; never use self-contained proof validity as source binding.
