# axeyum-cnf

CNF construction and propositional reasoning for Axeyum: Tseitin encoding with
AIG/CNF bindings, DIMACS I/O, pure-Rust SAT adapters, incremental solving,
bounded inprocessing, XOR reasoning, DRAT, a RUP-only positive-hint LRAT slice,
and a selected Alethe core. DRAT additions that require RAT reasoning are
rejected by the current LRAT elaborator.

The [crate documentation](src/lib.rs) contains a compile-tested checked-UNSAT
example. Read [CNF, SAT, and propositional
evidence](../../docs/internals/cnf-and-sat.md) before interpreting assurance:
an UNSAT without a proof is lower assurance, while a checked DRAT or LRAT
artifact establishes UNSAT for the encoded CNF. The in-tree CDCL core is the
only SAT engine; the BatSat adapter was removed (ADR-1910).

```sh
cargo test -p axeyum-cnf
```
