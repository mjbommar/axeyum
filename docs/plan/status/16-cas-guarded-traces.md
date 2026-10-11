# Lane: cas-guarded-traces — conditional quotient certificates

<!-- plan-section: lane-status -->

**LIB-5 guarded traces (`WIP`, cas-guarded-traces, 2026-10-11).** Child of
71d640d68. ADR-6400 specifies caller-bound nonzero context and polynomial
witnesses; original version-1 traces remain unconditional. Implemented original
quotient/result/context transport, exact denominator premise, checked
cross-multiplication, syntactic cancellation producer and bounded byte replay.
Kernel admission is separate. Initial Rust and signature-rerun suites each
passed 3 tests, 0 failed/ignored. Context-extension control added; focused
job24408 passed 4 tests, 0 failed/ignored, `/var/tmp/axeyum-cas-guarded-tests-v3.log`.

Python exposes `cancel_trace`, `replay_guarded_trace`, guarded trace/result
classes and explicit production/checking/refusal outcomes. JSON replay returns
the checked object after one parse. Fresh integrated native9129 passed; sealed package
`/var/tmp/axeyum-cas-guarded-integrated-python-ubkp2p19/package`, SHA256
`22d70d4986bbf002270e88f708bf04ac1a216bdd5b9a385ad7451b636993988c`.
235 CAS/trace/OMT Python tests passed, 0 skips, 1.03s; initial 21 trace tests also
passed with separate-process and assumption/subject/result/witness controls.
Updated example checks x*x/x = x under x != 0, rejects a missing context.
`/var/tmp/axeyum-cas-guarded-integrated-tests.log`.

Stub generation24855 passed: 27 modules/658 items. Runtime signature gate:
1867 symbols/5 aliases/319 synthesized dunders. Type gate: 1816 parameters,
1731 typed, 131 allowlisted Any, 46 Any returns, 95.3%. Generated CAS/SMT stubs
included. Imported parent source repairs from 61d220a4d/5dfed320c: fallible
midpoint conversion, priority syntax, documented checker-length allowance and
linted docs/test names. Parent full lint: 925 targets/27 crates/0 diagnostics;
this is parent evidence, not this child's broad-gate credit.

Private controls72512 completed in snapshot `snap-cas-guarded-traces-controls-322a4cced`:
baseline 4 passed; each context/identity/zero guard removal produced 3 passed,
exactly 1 intended failure, exit101. Source restored byte-identical. Log
`/var/tmp/axeyum-cas-guarded-controls.log`. Trust registry passed: 1291 public
functions, 151 certified (floor held), 114 checker, 1026 uncertified.
Own lint96940 and broad runner42378 running. Logs:
`/var/tmp/axeyum-cas-guarded-clippy.log`,
`/var/tmp/axeyum-cas-guarded-required-322a4cced/`; no broad pass credited.

Next: complete own CAS/solver/workspace/lint gates and integration. Nested
cancellation, wide trace coefficients, cost measurements and kernel admission
remain required; the full feedback goal is active.
