# Lane: wide-real-smtlib-writer — exact intake and source evidence

<!-- plan-section: lane-status -->

**LIB-6 X0 / EVD-5 / P0 (`WIP`, wide-real-smtlib-writer, 2026-10-11).**
Isolated child9fd9721d0. Details and prior receipts in
[notes](../notes/28-wide-real-smtlib-writer.md).
Promoted Real writer/intake fixes, exact4096-digit decimals, safe FP decline,
wide NRA signs and datatype declaration/operator export are committed.
Private decimal/FP/NRA guards each kill one test; datatype original6 fail vs
fixed6 pass. SMT396 passes0 failures/ignores; parser frontdoors158 pass;
MSRV1.88 workspace check and default Wasm build pass; facts2971 check0 errors.
Pi evidence ratchet153 holds. Earlier fresh consumer1133 tests pass0 skips.

Python saved clausal text/source replay committed (ADR8000): native
10021c3dfa772267b520db5c9744fd96c602717043a5e4da3edd97eaf57b84cc.
SAT/proof/OMT37 and proof/stub35 pass0 skips; source guard deletion9->8/1;
source restored. CAS shadowed integer annotations fixed in structured generator;
27 modules/1876 symbols drift and95.4% type ratchet pass. Export/census exits0,
two source-bound routes and six Z3 UNSAT sources. No unmodified LRAT checker
credit (guarded checker is pinned); no general theory map/kernel claim.

Reference-miter replay9fd9721d0 (ADR8300) reconstructs both source correspondences
without SAT search. Seven new controls and nine existing producer fixtures pass
0 failures/ignores; solver Clippy-D passes37.72s. First private final-checker
replacement also removed type validation:4 pass/3 fail, not an exact-one guard
result. Sources restored; next mutation isolates nested final DIMACS guard.
Python composite API committed7437a1356; fresh native build passes4m16s.
Sealed native dab497034b3f4b733d3fc70c49d89ba702f14946e9b6882deeb76b6595451356;
focused end-to-end/source/SAT/proof/OMT49 pass0 skips7.03s. Stub refresh live.

Full solver74254 passed2033 tests0 failures/ignores909.38s on wide-decimal/NRA
source; predates newer code. Current full solver77505 passes2033 tests0 failures/ignores826.10s.
Census/end-to-end15 pass0 skips; CLI six clausal/two reference fixtures exits0.
Older datatype workspace87947 still running, no pass credited. Earlier workspace81069/58007
terminal143/-15, not passes. Next: exact guard controls, fresh Python checks,
current workspace18900 live; integration and conditional trace evidence remain.
Overall goal remains active.

Nested conditional child04f5337fd started in isolated worktree; ADR8400
binds congruence, definedness, caller context and aggregate replay limits.
Implementation/controls pending; no new trace completion claim.
