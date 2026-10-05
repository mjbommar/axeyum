## Families and divisions

The per-division source of truth for **state, cause, lever and exit criterion**
is [`docs/plan/families/`](docs/plan/families/README.md); measurements live in
the [ledger](bench-results/PARITY.md). This table is the index.

| Family | On the board | State, 2026-10-05 |
|---|---|---|
| [SMT, quantifier-free](docs/plan/families/smt-quantifier-free/README.md) | 15 divisions | QF_UF closed at 200/200; every other gap has a named cause except QF_RDL's last 2 (not re-censused since S1). The family tree has no files yet for QF_DT, QF_S and QF_UFLRA, and still lists QF_FP and QF_UFLRA as "not entered" although both have ledger rows (SOL-5). |
| [SMT, quantified](docs/plan/families/smt-quantified/README.md) | UF (90/93) | cause measured ([uf.md](docs/plan/families/smt-quantified/uf.md)); nested-binder activation measured and OFF (ADR-2149, proposed). UFNIA, UFLIA, AUFDTLIRA are scored on A13 lists, not the board. |
| [Certificate chain](docs/plan/families/evidence/README.md) | none, by construction | a division can reach parity with empty certificates and no board row shows it — hence EVD. |
| [Propositional SAT](docs/plan/families/sat/README.md) | not entered | CNF entry point and binary DRAT landed (ADR-1722); RAT in the backward elaborator is the piece left. |
| [SMT-COMP other tracks](docs/plan/families/smt-comp-tracks/README.md) | not entered | model validation is the cheap entry. |
| [Hardware model checking](docs/plan/families/model-checking/README.md) | not entered | best architectural fit (AIGER in, AIG certificate out); unscoped. |
| [Boolean optimization / counting](docs/plan/families/boolean-optimization/README.md) | not entered | no input formats. |

Two standing cautions. **Our reference is not the frontier** in several
divisions — OpenSMT, Yices2 and SMTInterpol lead some logics we score against
cvc5, so "parity" means parity with the named reference
([survey](docs/research/02-ecosystems/competition-landscape-2026-09/README.md)).
And **a division without an established cause gets a census, not a slice.**
