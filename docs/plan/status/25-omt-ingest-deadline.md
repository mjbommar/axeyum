# Lane: omt-ingest-deadline — preemptible OMT intake

<!-- plan-section: lane-status -->

**CON-5 O1 (`WIP`, omt-ingest-deadline, 2026-10-11).** Child f038d6147.
ADR7000 specifies shared ingest/search/check deadline and explicit intake unknown
without fabricated objectives. Reader deadline polling implemented for main loop,
comments, strings, quoted symbols and atoms; typed parser now uses it. Parser library passed96/0 failed/ignored,3.04s; new lexical budget controls
passed4/0 failed/ignored. Typed optimizer now uses budgeted parse and represents
intake exhaustion with explicit reason/no fabricated rows. Solver check45956
passed42.47s (full-feature compile). Legacy box/lex parse now uses shared
budget; Python exposes intake_unknown reason. Added3 solver integration controls
(zero-budget typed/legacy and finite optimum/model/gold positive);48715
passed3/0 failed/ignored, /var/tmp/axeyum-omt-ingest-optimization-tests.log.
Python tests now require zero-budget intake reason/no fabricated rows, including
long comment inputs in both modes. Fresh Python run pending. Next: command
reread now uses shared deadline; typed priority reuses same command list.
Command rerun86284 passed3/0 failed/ignored; Python check16361 passed30.02s; getter compiles.
Fresh native build launched, source frozen; no Python pass credited yet. Next: direct command-budget
controls, fresh Python,
full solver/workspace/front-door gates and controls. Full goal remains incomplete.

User guide now documents shared intake timeout and checking intake_unknown before
indexing. Native build57554 remains live; no fresh Python result credited.

Native build57554 passed56.73s; sealed omt-ingest-deadline-_59vtrwq/package,
SHA256aad1b5679a57484c64dfcef63849113bf16e2604ebe18cbff32b14a2b25f0702.
Initial pytest command referenced nonexistent portable file:0 tests credited.
Corrected actual two suites passed17/0 skipped,0.25s;
/var/tmp/axeyum-omt-ingest-python-tests-v2.log. Added3 direct command controls
(original start, no-deadline tokens/priority, resource mapping);58300 passed3/0
failed/ignored. Private initial lexical poll removal34997 live; no control pass
credited yet. Stub generation33160 live. Portable checker parsing/Farkas replay
still runs without a deadline, so checking-budget requirement remains open.
