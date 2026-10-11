# Feedback branch integration — 2026-10-11

Base: da0e38a0a, retaining its wide transport, signed powers, bounded Python
parser and promoted evalf repair. Rules branch import: c3c747eb9. Native source
is unchanged by the rules import; Python source merges cleanly. Historical audit
conflicts retain a7df59e83's main planning correction; generated PLAN and ADR
index are rebuilt from combined sources. Integration uses linear imports via
lane-commit because the helper refuses MERGE_HEAD; original branch objects and
history are retained. Main checkout is unchanged. No combined gate pass yet.

Signed-literal import from 343a289c8 merges without source conflicts. Generated
PLAN/CATALOG/ADR views are rebuilt. Rules import landed in 38d55bb78 (26 files).
Post-merge hygiene passed with shape-duplicate and kernel-projection checks
explicitly unavailable; that is not full-gate evidence. Pinned recount initially
received no paths and exited usage-error; no pass is inferred from that command.
The merge touches no kernel pin inventory; affected parser files are checked
separately. Combined native/runtime gates await the remaining imports.

Signed-literal integration landed as 6c0aeda87 (14 files). Post-merge hygiene
passed with its existing explicitly skipped scopes; parser rounding-mode array
recount found five declared/five actual entries. No pin found in sexpr.rs.
OMT import from a536b76d0 merges cleanly in solver source; only generated views
conflict and are rebuilt. Its source-lane full solver failure and live workspace
are retained as evidence, not transformed into a combined green gate.
