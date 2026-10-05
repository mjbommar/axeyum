## Workstream state

All tracks are `PAUSED` since `a38d5f5da` (2026-09-17) with nothing in flight;
the state column is what a resuming lane inherits.

| Track | State | Boundary |
|---|---|---|
| SOL — solver parity | `PAUSED`; A13 queue closed 2026-09-17 (ADR-2147 and ADR-2148 shipped, ADR-2134 and ADR-2149 OFF) | Every measured number is on an old frame; SOL-1 re-measure gates any new scoring. |
| LIB — library / flywheel | `PAUSED`; L0–L4 phases done through S6, C3, G5, D5 (2026-08-30/31) | The loop has closed by hand, never automatically (LIB-1); statement families not started (LIB-2). |
| EVD — evidence and Lean | `PAUSED`; Lean chair's Next Ten all ticked; BatSat removed (ADR-1910) | QF_BV evidence last measured 2026-08-17; SOS fallback still present. |
| CON — consumers | `PAUSED`; the 2026-09-16 improvement lists closed for Axeyum (16/16) | Glaurung's default-backend decision is open (CON-1); cindergraph and Glaurung are pushed by the user only. |
| ENG — hygiene | `WIP` — this consolidation | Two gates red on `a38d5f5da` (ENG-1); 198 agent worktrees and 14 unmerged branches (ENG-2). |
