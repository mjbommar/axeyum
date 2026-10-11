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

Trace integration landed as 2a111e062 (20 files). Fresh combined gate runner
63353 is live against source 2a111e062bd6242c13e96dac8b098ba68d7a188a.
Logs: /var/tmp/axeyum-feedback-combined-gates-invfxf_7. Dedicated Cargo target:
/home/mjbommar/projects/personal/axeyum/target/feedback-integration.
Sequence: native extension build, immediate sealed package/hash, combined Python
CAS/trace/rules/SMT suites, Rust CAS integration regressions, parser library and
signed-literal controls, then full-feature solver proof/OMT/front-door regressions.
All commands retain counts/exit status. Handle polling confirms it is live and
its build log advances through CAS/solver compilation. No terminal result or
combined pass is credited. Full required gates and remaining features still apply.

Combined native build completed successfully. Sealed package:
/var/tmp/axeyum-feedback-combined-gates-invfxf_7/package; native SHA-256
831f35b5f744de86057caa8cdbeb3a23abe0b805f64227ad0641597a4b14238c.
Python: 350 pass, 34 skipped, 384 collected (3.54 seconds). Skipped tests in
SMT suites are same-Rust-engine CLI route comparisons and fresh CLI cases; no pass is
credited to them. Rust CAS integrations: four nonzero suites, 8/4/2/4 pass
(18 total). Parser: 96 library plus five signed-literal tests pass (101 total),
not the older source-lane aggregate count. All these scopes have zero failures.
Full-feature solver regression phase remains live in 63353, advancing through
SMT-LIB cases. Its final counts and broad required gates remain uncredited.

Focused runner 63353 is terminal successful. Solver regression suites have
6/5/5/25/16/1/102 passes (160 total), all nonzero, zero failures/ignored;
SMT-LIB suite completed in 33.31 seconds. Combined scoped Rust total is 279
(18 CAS + 101 parser + 160 solver), with 350 Python passes and 34 explicit skips.
These results cover the combined source 2a111e062, not every required broad gate.

Required-gate runner 88821 is now live at ce8e28222b0132398ad734c1a9e52051b051f407
(document-only successor of the same implementation). Logs:
/var/tmp/axeyum-feedback-required-gates-bewczwlv. Sequence: five mandatory string
front-door suites, full-feature solver library, workspace library, with every
terminal row required nonzero. The initial corpus phase is active; no broad
pass is claimed. At that point CLI skips, independent oracle tests, lint, remaining
features and eventual main landing still require work.

CLI follow-up: prior build handle 50330 is missing, and no matching build process
is live. Its executable exists and was exercised successfully; no recovered
terminal build status is inferred. CLI SHA-256:
dfbaddbe8f47070eba7f3da9c49c032ea8656d80f29064e5609502fce5b8ffd2.
Using the existing AXEYUM_SMTCOMP_CLI override and the sealed native package,
the same eleven Python suites pass all 384 collected tests, zero skips, in
7.89 seconds (runner 60730, terminal exit 0). This closes 28 CLI route comparisons
and six signed CLI cases; both routes use the same Rust solver, so these are
not independent Z3 checks. Fixed the stale build hint: smtcomp_cli belongs to
axeyum-bench, not axeyum-solver.

Runner 88821 remains live, independently confirmed by PID 3700375 and active
cargo child 3707885. Five required front-door suites completed with
2/48/13/82/13 passes (158 total), each exit 0/nonzero. Full solver is active;
workspace has not yet started. Broad completion remains unproven.
