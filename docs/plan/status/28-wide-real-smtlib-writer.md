# Lane: wide-real-smtlib-writer — exact intake and source export

<!-- plan-section: lane-status -->

**LIB-6 X0 / EVD-5 / P0 (`WIP`, wide-real-smtlib-writer, 2026-10-11).**
Isolated childb8b237c65; details in
[notes](../notes/28-wide-real-smtlib-writer.md). Promoted Real writer/intake
repair, exact4096-digit decimals, safe FP decline and wide NRA sign comparisons
are committed. Private decimal/FP/NRA guard removals each kill exactly one
intended test; sources restored bytewise.
Datatype source export now includes recursive field dependency declarations,
real sort/operator names and bare nullary constructors. Six new controls pass;
post-refactor SMT396 tests pass0 failures/ignores; Clippy-D passes2.00s.
Fresh native SHA c7f03e70144ae150b9859a9a73c644e996a27ca0038dbc82d21c602edddf7145:
SAT/proof/OMT28 passes and combined consumer1133 passes0 skips86.90s. All six
exporter sources reparse; Z3 reports UNSAT; guarded external LRAT checks and
SAT model controls pass. Original LRAT checker fails the tampered-CNF control;
no unmodified-upstream credit. Source-to-CNF translation evidence remains absent.
CAS ratchet records two genuine Pi evidence functions, not trace logging;
153 floor holds. Wasm default build passes32.66s with37 warnings.
Original writer snapshot: six regressions fail0 passes/6 failures/0 ignores,
exit101. Final parser frontdoors158 passes0 failures/ignores. MSRV1.88 workspace
check passes1m41s; fact validation exits0. Full solver74254 on wide-decimal/NRA source passed2033 tests0 failures/ignores
909.38s; it predates later datatype/Python code. Workspace87947 still running. Tracked-note CATALOG regenerated and plan/link gates pass. Earlier workspace jobs81069/58007 terminal143/-15; no pass credited.
Source-bound Python replay childfe3094477: expose existing Rust checker and
restored text constructor; ADR8000 distinguishes trusted encoding from an
independent translation proof. Fresh native SHA10021c3dfa772267b520db5c9744fd96c602717043a5e4da3edd97eaf57b84cc:
SAT/proof/OMT37 tests pass0 skips0.68s, including nine new controls and two
producer-disabled child replays. Py Clippy-D passes2m13s. Guard deletion: baseline9 passes ->8 passes/1 intended failure; source restored
bytewise. Stub generation qualifies5 integer annotations shadowed by Expr.int;
proof/stub35 tests pass0 skips2.17s, including mypy runtime comparison. Drift
27 modules/1876 symbols and type ratchet95.4% pass. Generator Clippy-D passes.
Current export/census exits0; two source-bound routes, six Z3 UNSAT sources.
Reference-miter replay childef595e7de: ADR8300 factors deterministic miter
construction out of search and binds both saved CNFs to the same original
assertions. Seven correspondence controls plus existing producer fixtures
running8798; no pass credited. Next: collect controls, private guard mutations,
Python end-to-end export/replay, broad gates and integration. No broad completion claim;
overall goal stays active.
