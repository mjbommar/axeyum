# Lane: boolean-alethe — EVD-6 source-bound propositional proofs

<!-- plan-section: lane-status -->

**Boolean Alethe (`WIP`, boolean-alethe, 2026-10-10).** Text proof API now
emits source-bound Boolean refutations for not/and/or/equality/xor/constants plus implication/Boolean ite,
reusing the existing proof tail. Literal source syntax survives IR folding;
quoted atoms serialize/reparse. Fresh checks: six solver proof tests, four CNF
controls, 645 CNF library tests and focused clippy pass. Pinned Carcara accepts
seven exports without holes and rejects two source/premise corruptions.
False-pin mutation: baseline 3 pass; mutant 2 pass/1 fail. ADR-2600 proposed.
Conditional rows: two checker tests pass; 13 exports pass pinned Carcara.
Nine SAT controls replay; conditional mutation kills exactly one test.
Negative-real multiplication now checks, including a nested-negation bridge;
five arithmetic exports are accepted by Carcara, but a changed-coefficient
source also passes: the unpatched checker fails source binding. An isolated pinned guard-patched
checker now passes all 18 exports and rejects that changed source. Both new
arithmetic mutations kill exactly one test. Fresh public Python: five tests pass;
five full,z3 arithmetic differential suites: 20 tests pass. Updated CNF library: 645 pass. Full solver: 2007 pass; five front-door suites: 158 pass. Workspace remains live.
Next: scoped/macro source reconstruction, elaboration/checking
budget propagation, broader Python coverage, kernel reconstruction and full
workspace gates. Boolean+LIA composition is in progress (ADR-2800): five new tests pass, source quoting and serialized replay repaired;
portable integer elaboration remains. All 16 targeted Rust proof tests, focused clippy and seven fresh Python tests pass.
Gates pin 446aae38b (logs in notes); workspace PID 3297276 remains live.
The negative-real repair still needs remaining source/coercion controls. No full EVD-6 completion or integration claimed.
Details: [notes](../notes/boolean-alethe.md).
