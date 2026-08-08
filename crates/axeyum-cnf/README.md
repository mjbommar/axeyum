# axeyum-cnf

CNF construction and propositional reasoning for Axeyum: Tseitin encoding with
AIG/CNF bindings, DIMACS I/O, pure-Rust SAT adapters, incremental solving,
bounded inprocessing, XOR reasoning, DRAT/LRAT, and a selected Alethe core.

The [crate documentation](src/lib.rs) contains a compile-tested checked-UNSAT
example. Read [CNF, SAT, and propositional
evidence](../../docs/internals/cnf-and-sat.md) before interpreting assurance:
the BatSat adapter's proofless UNSAT is lower assurance, while a checked DRAT or
LRAT artifact establishes UNSAT for the encoded CNF.

```sh
cargo test -p axeyum-cnf
```
