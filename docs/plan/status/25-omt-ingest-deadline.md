# Lane: omt-ingest-deadline — shared intake and evidence budgets

<!-- plan-section: lane-status -->

**CON-5 O1 (`WIP`, omt-ingest-deadline, 2026-10-11).** Child f038d6147.
ADR7000: lexical/typed parsing and OMT objective/priority reads share original
start/deadline. Typed intake unknown has reason/no fabricated rows; Python getter
and guide updated. Parser96 tests passed; lexical4 passed; OMT integration3 then
4 with portable budget controls passed. Direct command controls3 passed.
Private lexical initial-poll removal: baseline4 ->3 passed/1 intended failure;
restored bytewise, /var/tmp/axeyum-omt-lexical-*.log.

Fresh native build2415 passed46.62s at ca62f7bf2. Sealed package
/data0/axeyum/artifacts/python/omt-ingest-deadline-1r9m56mg/package;
SHA25691e40f6df3ba95ae20f808c83939cfa0dec45412c82df7de0ebbdabc426bc2ae.
OMT Python18 passed/0 skipped,0.30s. Stub72102 passed27 modules/661 items;
drift27 modules/1874 symbols and type1824 params/1739 typed/131 allowed Any
passed against this binary. Broad CAS/OMT/Rules Python18641 passed1123/0
skipped,67.49s. Private mutation4465: baseline12 ->11 pass/1 intended
original_constraint_model_tampering failure after removing false-assertion guard;
restored bytewise in snapshot ca62f7bf2. Full solver59611 running, not credited.

Portable check_within shares parsing/command/model/Farkas deadline and reports
resource_limited. Python checker timeout_ms defaults2000. Front-door14307 passed:
corpus2, online48, word-first13, fixed-splice82, stoi13; all0 failed/ignored.

ADR7100 adds eval_within: None is resource exhaustion, Some is actual Value.
Same deadline propagates through iterative terms and finite quantified bindings;
existing eval/memo signatures unchanged. Primitive operators remain atomic.
IR library92005 passed104/0 failed. Evaluator integration passed3/0 failed;
portable model replay now uses eval_within for original assertions/objective;
OMT integration passed4/0 failed. Controls prove expired intake vs false and
preserve nested finite quantifier semantics, not mid-enumeration interruption.
Targeted Clippy75893 passed42.60s with warnings denied. Producer final replay
now shares its deadline; exhaustion clears model/value/no-better evidence and
returns ResourceLimit unknown. Generic checker preserves quantified certificates
(atomic checks between polls); ordinary assertions use eval_within. OMT controls
passed4. Private optimization group initially11 pass/1 stale zero-intake row
expectation failed; corrected to empty rows plus reason/no gold. Rerun89587
passed12/0 failed (2021 filtered). Clippy60534 passed23.39s with warnings denied;
initial run caught public expect/panic docs, replaced with fail-closed fallback.
Next: remaining broad gates, mid-quantifier budget controls, integration.
Logs /var/tmp/axeyum-omt-{ingest-*,checker-budget-tests,deadline-ir-tests}.log.
Entire feedback objective remains incomplete.
