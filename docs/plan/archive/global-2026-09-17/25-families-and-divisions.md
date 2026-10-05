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
| [SMT, quantifier-free](docs/plan/families/smt-quantifier-free/README.md) | **11 divisions** (QF_NRA entered 2026-09-07) | S7b; then QF_RDL's 14 and QF_UF's 4, neither with a front-door cause | measured; QF_NRA's 62-file admission bound is now the largest named cause on the board |
| [SMT, quantified](docs/plan/families/smt-quantified/README.md) | UF | the flooded cap-hit refutation check, scored on 7 files | **cause established 2026-09-07**: the population is 100% refutation and half its budget goes to a model finder that cannot decide it |
| [The certificate chain](docs/plan/families/evidence/README.md) | none, by construction | S7b emits the artifact from a real route; port the witness to `eliminate_functions` | prior art cited; the array-elim recheck now interprets rather than re-derives (ADR-1721); trust holes 6 -> 7, which is the metric getting honest |
| [Propositional SAT](docs/plan/families/sat/README.md) | not entered | RAT in the BACKWARD elaborator, the one piece left | **entry surface landed 2026-09-07** (ADR-1722): CNF entry point, binary DRAT, RAT in the forward elaborator |
| [SMT-COMP's other tracks](docs/plan/families/smt-comp-tracks/README.md) | not entered | model validation | proof exhibition **does not exist** any more |
| [Hardware model checking](docs/plan/families/model-checking/README.md) | not entered | scope a model-checking front end | best architectural fit; AIGER in, AIG certificate out |
| [Boolean optimization and counting](docs/plan/families/boolean-optimization/README.md) | not entered | none yet | no input formats implemented; standing opportunity |

### Three things this table exists to keep visible

1. **Two divisions have no established cause** — QF_UF's remaining four and
   QF_RDL's fourteen since the last re-census. UF's thirty-two were the third
   and now have one (2026-09-07), arrived at only after **two** earlier causes
   were refuted by re-measurement. A division without a cause gets a census,
   not a slice; and a lever that the cause points at still gets built and
   measured before it is believed — UF's obvious one gained 0 of 32 and cost 1
   of 24.
2. **Our reference is not the frontier in six divisions.** OpenSMT, Yices2 and
   SMTInterpol lead the quantifier-free arithmetic and equality logics we score
   against cvc5. Every ledger row names its reference, so no number is wrong —
   but "parity" there means parity with cvc5, not dominance. See
   [the survey](docs/research/02-ecosystems/competition-landscape-2026-09/README.md).
3. **The certificate chain has no board row at all.** A division can reach
   parity with empty certificates and nothing on the board would show it. That
   is why the evidence family is listed beside the divisions rather than under
   them.
