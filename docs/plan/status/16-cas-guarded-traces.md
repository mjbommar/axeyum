# Lane: cas-guarded-traces — conditional quotient certificates

<!-- plan-section: lane-status -->

**LIB-5 guarded traces (`WIP`, cas-guarded-traces, 2026-10-11).** Child of
71d640d68. ADR-6400 specifies caller-bound nonzero context and polynomial
witnesses; original version-1 traces remain unconditional. Implemented original
quotient/result/context transport, exact denominator premise, checked
cross-multiplication, syntactic cancellation producer and bounded byte replay.
Kernel admission is separate. Initial Rust and signature-rerun suites each
passed 3 tests, 0 failed/ignored. New context-extension control added; focused
job24408 running, `/var/tmp/axeyum-cas-guarded-tests-v3.log`.

Python exposes `cancel_trace`, `replay_guarded_trace`, guarded trace/result
classes and explicit production/checking/refusal outcomes. JSON replay returns
the checked object after one parse. Fresh native77101 passed; sealed package
`/var/tmp/axeyum-cas-guarded-python-04jfnbsk/package`, SHA256
`4e100b9c0f070c4af1e0983f3ca063c5604b763977625dc6c7c7055ded153708`.
Twenty-one guarded/unconditional Python tests passed, 0 skips, 0.47s, including
separate-process and assumption/subject/result/premise/witness/envelope controls.
Updated example checks x*x/x = x under x != 0, rejects a missing context.
`/var/tmp/axeyum-cas-guarded-python-tests.log`.

Stub generation24855 passed: 27 modules/658 items. Runtime signature gate:
1867 symbols/5 aliases/319 synthesized dunders. Type gate: 1816 parameters,
1731 typed, 131 allowlisted Any, 46 Any returns, 95.3%. Generated CAS/SMT stubs
included. Imported parent source repairs from 61d220a4d/5dfed320c: fallible
midpoint conversion, priority syntax, documented checker-length allowance and
linted docs/test names. Parent full lint: 925 targets/27 crates/0 diagnostics;
this is parent evidence, not this child's broad-gate credit.

Next: private context/identity/zero guard mutations, own full CAS/workspace/lint
gates, fresh integrated native replay. Nested cancellation, wide trace
coefficients, runtime/size measurements and kernel admission remain required.
Full feedback goal is active; no integrated-main or broad completion claim.
