# ADR-7000: OMT intake shares the search and checking deadline

Status: proposed
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
