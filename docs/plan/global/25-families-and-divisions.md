## Families and divisions

Every SAT/SMT family we measure, could measure, or have decided not to yet.
One file per family and per division under
[`docs/plan/families/`](docs/plan/families/README.md); that tree is the source
of truth for a division's **state, cause, lever and exit criterion**. The
[ledger](bench-results/PARITY.md) owns the measurements and the
[parity plan](docs/plan/smt-parity-plan-2026-09-05.md) owns the S1–S12 slice
history. Nothing is restated in two places.

| Family | On the board | Next action | State |
|---|---|---|---|
| [SMT, quantifier-free](docs/plan/families/smt-quantifier-free/README.md) | 10 divisions | S7, then the S2 follow-up | measured; arithmetic-first by weight |
| [SMT, quantified](docs/plan/families/smt-quantified/README.md) | UF | **front-door census** | no established cause; no lever authorised |
| [The certificate chain](docs/plan/families/evidence/README.md) | none, by construction | cite prior art in ADR-1704; emit the artifact in S7 | one open hole (preprocessing), one contract with no producer |
| [Propositional SAT](docs/plan/families/sat/README.md) | not entered | three slices: a CNF entry point, binary DRAT, RAT in the elaborator | closer than assumed; the only arena that *mandates* certificates |
| [SMT-COMP's other tracks](docs/plan/families/smt-comp-tracks/README.md) | not entered | model validation | proof exhibition **does not exist** any more |
| [Hardware model checking](docs/plan/families/model-checking/README.md) | not entered | scope a model-checking front end | best architectural fit; AIGER in, AIG certificate out |
| [Boolean optimization and counting](docs/plan/families/boolean-optimization/README.md) | not entered | none yet | no input formats implemented; standing opportunity |

### Three things this table exists to keep visible

1. **Three divisions have no established cause** — QF_UF's remaining four,
   UF's thirty-two, and QF_RDL's fourteen since the last re-census — and two of
   those previously had a cause that was **refuted** by re-measurement. A
   division without a cause gets a census, not a slice.
2. **Our reference is not the frontier in six divisions.** OpenSMT, Yices2 and
   SMTInterpol lead the quantifier-free arithmetic and equality logics we score
   against cvc5. Every ledger row names its reference, so no number is wrong —
   but "parity" there means parity with cvc5, not dominance. See
   [the survey](docs/research/02-ecosystems/competition-landscape-2026-09/README.md).
3. **The certificate chain has no board row at all.** A division can reach
   parity with empty certificates and nothing on the board would show it. That
   is why the evidence family is listed beside the divisions rather than under
   them.
