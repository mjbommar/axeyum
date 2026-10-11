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
portable-child broad-gate credit. Parent full solver/workspace not yet credited.

Next: Python certificate export and counted JSON replay, fresh extension and
separate-process controls, snapshot guard mutations, then broader gates.
Integer-only/BV/Boolean optimality producers, preemptible replay and kernel
reconstruction remain open; full feedback goal remains active.
