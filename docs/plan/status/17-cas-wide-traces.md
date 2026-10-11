# Lane: cas-wide-traces — promoted coefficients and closed rational steps

<!-- plan-section: lane-status -->

**LIB-5/LIB-6 wide trace evidence (`WIP`, cas-wide-traces, 2026-10-11).** Child
of435de8c46. ADR-6500 specifies v2 arithmetic/codec while retaining v1 width and
domain limits. Promoted normalization bounds intermediate coefficients at16384
bits, width-weighted work, shape/expansion/degree, and constant powers at512.
Three arithmetic tests passed. V2 traces retain source/endpoints, local witnesses,
continuity/premises/context and per-step certificates; v1 remains narrow.

Added v2 constant-divisor wire/head and explicit nonzero side-condition binding.
Original-input domain validation also rejects an empty trace for division by0.
Symbolic divisors require the separate external-context guarded API. Current
Rust suites: 8 v1 + 7 v2 passed, 0 failed/ignored, v2 1.49s;
`/var/tmp/axeyum-cas-wide-division-tests.log`. V2 includes full exact 360-period
amortization with two checked division steps, missing conditions and empty
undefined-quotient controls. An earlier zero-test lib filter was uncredited;
all v1 credit comes from the integration suite.

Python `normalize_trace(..., wide=True)` opts in; default remains v1. Getters
and source-bound replay transport wide values without narrowing. Fresh native
68539 passed; sealed package
`/data0/axeyum/artifacts/python/cas-wide-trace-zyb2jcxy/package`, SHA256
`8d15fa2aa3664369c9031fbe191aeeb46032fe11720ea15072d74e45dde83f55`;
imported native path verified. 34 Python trace tests passed, 0 skipped, 9.07s,
`/var/tmp/axeyum-cas-wide-python-tests.log`. Independent Fraction comparisons
cover positive/negative/zero rates and zero principal; separate-process payment
replay does not call the producer. Updated amortization example verifies bytes.
Amortization example completed with exact 2859/2849-bit numerator/denominator
and zero-rate2500/3. Stub generation completed:27 modules/658 items. Runtime stub check passed:
1867 symbols; type check1817 parameters/1732 typed,131 Any all allowlisted.
Private controls completed:baseline7 passed; condition/domain/bit guards each
removed cause6 passes+1 intended failure, exit101; snapshot restored bytewise.
Own lint failed convert length115/100; extracted division validation helper.
Post-refactor suites passed8 v1+7 v2,0 failed/ignored;
`/var/tmp/axeyum-cas-wide-postlint-tests.log`. Source commitc6b0a5db1.
Full lint58742 live: `/var/tmp/axeyum-cas-wide-clippy-v2.log`.
Serial full CAS29000 live: `/var/tmp/axeyum-cas-wide-full-cas.log`.
Neither aggregate is credited. Parent solver2028 passed; workspace pending.

Cost example `python/examples/cas_trace_cost.py` launched37796; output
`/var/tmp/axeyum-cas-wide-trace-cost.json`, not yet credited.

Next: finish broad gates, wide guarded quotients, cost measurements, kernel
reconstruction and branch integration. Entire feedback goal remains active.
