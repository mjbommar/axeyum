# L0/S4 — independent proof replay

<!-- plan-section: lane-status -->

Lane: `l0-s4-independent-replay`. Phase S4 of the trusted-library safety
roadmap (ADR-0717). Status: **in progress** — this is an early commit made
before the work is complete, per lane discipline.

## What S4 is for

S0's matrix (`artifacts/safety-matrix/safety-matrix.tsv`) reports
`independent_replay` at **8 / 2117** proved facts, the thinnest of its nine
protections. That number is what facts *claim*: `gen-safety-matrix.py`
matches `checker_command` text against a regex and never executes anything.

S4's job is the census that actually executes, plus the grading discipline
that keeps Axeyum acceptance and Lean acceptance separate.

## Progress

- [x] read the roadmap S4 exit, ADR-0717 threat model, S0 handoff
- [ ] representable / non-representable census with typed reasons
- [ ] `missing=0` enforcement, zero-executed-cases is failure
- [ ] inheritance guard (no grade by family sampling)
- [ ] wrong-goal / wrong-proof mutations rejected
- [ ] monotone floor registered in both aggregate gates
