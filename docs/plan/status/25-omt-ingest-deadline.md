# Lane: omt-ingest-deadline — shared intake and evidence budgets

<!-- plan-section: lane-status -->

**CON-5 O1 (`WIP`, omt-ingest-deadline, 2026-10-11).** Child f038d6147.
ADR7000: lexical/typed parsing and OMT objective/priority reads share original
start/deadline. Typed intake unknown has reason/no fabricated rows; Python getter
and guide updated. Parser96 tests passed; lexical4 passed; OMT integration3 then
4 with portable budget controls passed. Direct command controls3 passed.
Private lexical initial-poll removal: baseline4 ->3 passed/1 intended failure;
restored bytewise, /var/tmp/axeyum-omt-lexical-*.log.

Native build57554 passed56.73s. Sealed omt-ingest-deadline-_59vtrwq/package,
SHA256aad1b5679a57484c64dfcef63849113bf16e2604ebe18cbff32b14a2b25f0702.
Corrected actual two Python suites passed17/0 skipped,0.25s; initial command
referenced nonexistent test file and ran0. Stub33160 passed27 modules/661 items;
drift/type gates passed. These precede the latest checker API/evaluator changes.

Portable check_within shares parsing/command/Farkas deadline and reports explicit
resource_limited. Python checker has timeout_ms default2000. Compile44161 passed
11.25s with2 unused wrappers; removed wrappers. Budget integration64565 passed4.
Latest checker needs fresh native build/stubs/private controls and broad gates.

ADR7100 adds eval_within: None is resource exhaustion, Some is actual Value.
Same deadline propagates through iterative terms and finite quantified bindings;
existing eval/memo signatures unchanged. Primitive operators remain atomic.
IR library92005 passed104/0 failed. Evaluator integration passed3/0 failed;
portable model replay now uses eval_within for original assertions/objective;
OMT integration passed4/0 failed. Controls prove expired intake vs false and
preserve nested finite quantifier semantics, not mid-enumeration interruption.
Next: producer replay budgets, fresh Python, private controls, broad gates, integration.
Logs /var/tmp/axeyum-omt-{ingest-*,checker-budget-tests,deadline-ir-tests}.log.
Entire feedback objective remains incomplete.
