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
check passes1m41s; fact validation exits0. Full solver74254(parent) and
workspace87947 still running, no passes credited. Tracked-note CATALOG regenerated and plan/link gates pass. Earlier workspace jobs81069/58007 terminal143/-15; no pass credited.
Source-bound Python replay childfe3094477: expose existing Rust checker and
restored text constructor; ADR8000 distinguishes trusted encoding from an
independent translation proof. Nine controls written, no pass credited.
Next: fresh native tests, private source-binding guard control, collect broad
gate outputs, integrate, and finish remaining proof/conditional trace gaps. No broad completion claim;
overall goal stays active.
