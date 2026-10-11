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

OMT import landed in 4564410fe (12 files); post-merge hygiene passed with its
existing skipped scopes. Boolean/LIA/negative-real proof import from de0b570f3
merges cleanly in source, including smtlib.rs alongside OMT changes. Generated
views are rebuilt. Original evidence boundaries remain: portable Boolean/real
checks used a source-binding guard-patched Carcara; lia_generic composition is
internal-only; source lane full solver passes 2007 but its workspace remains
live. No original pass is credited as a combined integration gate.

Proof integration landed as 4dc2dfd87 (31 files); combined cargo fmt read-only
check and generated-document checks pass. Trace import cd5287f84 merges cleanly
in native/Python source. Conflicting CAS status/history retain the newer
CAS-parent c0a083978 documents, including its 2139-pass/one timing-failure CAS
suite result, instead of the trace child's older Rust-only account. Trace wire
still explicitly declines wide coefficients and conditional division; importing
it does not satisfy those remaining requirements. Next: fresh combined build
and regression gates, then remaining implementation work.
