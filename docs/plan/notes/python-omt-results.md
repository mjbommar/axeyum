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
