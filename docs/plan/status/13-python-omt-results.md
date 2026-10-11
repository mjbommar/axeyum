# Lane: python-omt-results — CON-5 typed models and explicit objective modes

<!-- plan-section: lane-status -->

**Python OMT reports (`WIP`, python-omt-results, 2026-10-11).** Isolated from
integration9221ebb67. ADR-6300 adds typed Rust/Python optimization reports with
exact Int/unsigned-BV values, direction/sort, explicit lex/box semantics, shared
budgets and original model/value replay. Separate models retained for boxed
objectives; lexicographic witnesses include earlier optimum pins. Scoped/popped,
reset and post-query objectives now select the same query snapshot as assertions;
legacy text optimizers share this correction. Compile check and initial native build pass. Seven focused Rust tests pass
again after retaining the full Script and declared-string lift metadata
(`/var/tmp/axeyum-python-omt-retained-script.log`: 7 passed, 0 failed/ignored).
Six Python controls await fresh rebuild on this revision.
Gold eligibility stays false until source-bound no-better evidence is checked;
generic self-contained evidence checks cannot provide that binding by themselves.
Next: nonzero focused tests, fresh native/stubs, replay guard mutations, required
full gates, then source-bound optimality certificates and preemptible ingest.
Existing integration EUF full-gate failure remains unresolved. No goal completion.
