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
(zero-budget typed/legacy and finite optimum/model/gold positive);48715 running,
passed3/0 failed/ignored, /var/tmp/axeyum-omt-ingest-optimization-tests.log.
Python tests now require zero-budget intake reason/no fabricated rows, including
long comment inputs in both modes. Fresh Python run pending. Next: command
reread wiring, fresh Python,
full solver/workspace/front-door gates and controls. Full goal remains incomplete.
