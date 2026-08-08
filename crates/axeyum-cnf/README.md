# axeyum-cnf

CNF construction and propositional reasoning for Axeyum: Tseitin encoding with
AIG/CNF bindings, DIMACS I/O, pure-Rust SAT adapters, incremental solving,
bounded inprocessing, XOR reasoning, DRAT, a RUP-only positive-hint LRAT slice,
and a selected Alethe core. DRAT additions that require RAT reasoning are
rejected by the current LRAT elaborator.

The [crate documentation](src/lib.rs) contains a compile-tested checked-UNSAT
example. Read [CNF, SAT, and propositional
evidence](../../docs/internals/cnf-and-sat.md) before interpreting assurance:
the BatSat adapter's proofless UNSAT is lower assurance, while a checked DRAT or
LRAT artifact establishes UNSAT for the encoded CNF.

```sh
cargo test -p axeyum-cnf
```
