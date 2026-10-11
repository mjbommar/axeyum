# ADR-7000: OMT intake shares the search and checking deadline

Status: accepted; audited OMT contract adopted, final integration gates remain open
Date: 2026-10-11

OMT parsing and command rereads currently run without preemption. Reuse the
caller start/deadline across lexical intake, typed parsing, active objective/
priority reads, optimization, witness recovery and evidence validation. Reader
polls include comments, quoted strings/symbols and long atoms; no deadline means
no clock reads. Resource exhaustion is unknown, never unbounded or a parse error.

If intake expires before objective identities are known, typed reports carry an
explicit intake-unknown reason with no fabricated objective rows, complete false
and no gold eligibility. Legacy outcome-only APIs return an explicit unknown
outcome. Invalid syntax observed before exhaustion remains a parse error. Keep
source-bound checking and independent validation exact. Test zero/expired budgets,
valid finite optima and degenerate large lexical populations; use positive controls
and guard mutations. No wall-clock threshold is a correctness assertion.

## Adoption and later composition

The implemented bounded contract is adopted. Later ADR-6301/6302 bind finite
integer optimality evidence to the original query; ADR-7000/7100 carry shared
cooperative deadlines through intake and model replay. Earlier follow-up lists
above record the original increment and are superseded where these later
contracts supply the implementation. See the
[current validation receipts](../../plan/notes/28-wide-real-smtlib-writer.md)
and [completion audit](../../plan/user-feedback-completion-audit-2026-10-11.md).
Current fresh-native OMT suites and full-feature solver regressions cover
feasible/optimal/unknown/unsupported outcomes and changed evidence. A checked
affine recession witness, not search exhaustion, justifies unboundedness.
Gold remains false when strict-better evidence is absent; integer-cut, BV and
other unsupported certificate producers retain explicit declines. Shared
linearization/checking is not advertised as independent implementation or
kernel admission. Final workspace/all-target verification and main integration
remain open.
