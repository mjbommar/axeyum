# Lane: cas-traces — LIB-5 certified rewrite logs

<!-- plan-section: lane-status -->

**CAS step traces (`WIP`, cas-traces, 2026-10-10).** First opt-in polynomial
producer/checker carries full input/result and before/after trees, ordered IDs,
locations, stable rules/arguments, premises/context/side conditions and local
normal-form witnesses. Eight fresh integration tests passed; examples compiled
but their zero-test harnesses are only build evidence. Separate-process replay
accepted 1 genuine claim and rejected all 5 corruptions; focused clippy passed.
Context-guard mutation: baseline 5 pass; mutant 4 pass/1 fail. Fresh Python bindings passed 6 tests and the rational four-step export demo.
Final-source rebuild passed: six Python tests, byte-identical Rust/Python
exports and two standalone replays. Generated stubs contain 649 items.
Malformed local witnesses now report their failing step; focused clippy passes.
Latest rebuilt extension passes seven Python tests including that diagnostic. ADR-2500 is proposed pending validation.
Next: complete gates and guarded division,
then kernel reconstruction. Wide trace coefficients also remain pending. No
kernel admission or LIB-5 completion is claimed. Evidence:
[trace lane](../notes/cas-traces.md).
