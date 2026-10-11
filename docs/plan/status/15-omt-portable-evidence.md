# Lane: omt-portable-evidence — byte replay without optimization search

<!-- plan-section: lane-status -->

**Portable OMT evidence (`WIP`, omt-portable-evidence, 2026-10-11).** Isolated
child of 0a0a3b144. ADR-6302 specifies original-source, selected-objective and
lex-prefix certificates with named models/columns and source-bound Farkas replay.
Strict transport and counted byte checker rebuild subject/objectives, models,
lex prefixes and strict-better source bindings without optimization search.

Fixed internal relaxation-column lookup: certificates carry explicit namespace
tags; no user/helper lookup fallback. Enabled the bounded set-option whitelist
and added priority retargeting and namespace corruption controls. Seven focused
Rust tests passed, 0 failed/ignored, 0.03s in
`/var/tmp/axeyum-omt-portable-tests-v3.log`; compilation and the earlier five-test
run also passed. Fixed two CAS test format-string Clippy errors observed on the
parent; full lint rerun remains required.

Parent source-bound branch front-door gates completed: 2/48/13/82/13 tests,
158 total, all 0 failures/ignored, in
`/var/tmp/axeyum-omt-gold-required-_volk68z/`. Those are parent evidence, not
portable-child broad-gate credit. Parent full solver passed 2021 tests, 0
failed/ignored, 865.62s (`solver-full.log`); workspace remains uncredited.

Python now exports objective certificate JSON and provides counted replay against
caller-supplied source via `check_optimization_certificate`. Fresh native build
75801 passed; sealed package
`/var/tmp/axeyum-omt-portable-python-hy6yxe7f/package`, SHA256
`79eaea84038abb9cbfc2cc71f42c556f46e8d23be3fa295eca82fb07aa2ddc1e`.
Fifteen Python tests passed, 0 skipped, including separate-process replay without
optimization and invalid subject/value/prefix/envelope controls. Updated example
ran four model replays plus counted certificate checks. Logs:
`/var/tmp/axeyum-omt-portable-python-tests.log`. Stub generation56496 running.

Additional fresh-extension proof/Date/pack/statute suites passed 43 tests, 0
skipped, 4.26s (`/var/tmp/axeyum-omt-portable-consumer-tests.log`): 58 Python
tests total across both runs. Read-only formatting and generated-plan gates pass.
Private snapshot `snap-omt-portable-evidence-mutation-0b44e2703` baseline:
7 passed; removing source guard: exactly 1 intended failure, 6 passed, exit101.
Priority mutation1108 running; log `/var/tmp/axeyum-omt-portable-mutations.log`.
Full lint45243 pending/running, `/var/tmp/axeyum-omt-portable-clippy.log`.

Next: finish generated stub validation, priority mutation and broader gates.
Integer-only/BV/Boolean optimality producers, preemptible replay and kernel
reconstruction remain open; full feedback goal remains active.
