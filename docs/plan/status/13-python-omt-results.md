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
Fresh extension at 933fbbe02: six selected Python suites report 93 passed,
34 skipped (CLI-dependent controls); all six OMT controls pass. Binary SHA-256
89d3ef632addb05f453fa4ee2814b51ed34f8bab81cfcc1547a9fd108cae8e85.
Full solver/workspace runner 55477 and stub runner 53264 are live, not passes;
private mutation baseline 75540 passed all seven Rust tests; two guard
mutations run under 45506 in the private snapshot. Added fresh Python lifting
control: declared String decodes, actual BV stays BV. Added independent
24-case finite-domain optimum oracle; OMT suite now 8 passed.
Gold eligibility stays false until source-bound no-better evidence is checked;
generic self-contained evidence checks cannot provide that binding by themselves.
Next: nonzero focused tests, fresh native/stubs, replay guard mutations, required
full gates, then source-bound optimality certificates and preemptible ingest.
Prior EUF failure does not reproduce in this run: its heavy timeout test
passes; full solver/workspace still live. No goal completion.
