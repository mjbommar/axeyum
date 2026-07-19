# Accepted v2: satisfiable-CNF checker control

ADR-0255's post-v1 correction passes without changing the real source, CNF,
proof, exporter, or checker:

- the unchanged real DIMACS/DRAT pair again makes pinned `drat-trim` exit 0 and
  print `s VERIFIED`;
- the exact 10-byte satisfiable control `p cnf 1 0\n` has its preregistered
  SHA-256;
- the exact same two-byte real proof checked against that control makes
  `drat-trim` exit 1, report `no conflict`, and print `s NOT VERIFIED`.

This accepts one real standard-format interoperability result plus a separate
checker sanity/binding control. It does not erase ADR-0254's rejected final-line
mutation, estimate coverage, certify the source-to-CNF reduction, or provide
solver-performance evidence.

The real proof is deliberately described precisely: it is only the empty-clause
line because the 2,166-clause input CNF is already UNSAT by unit propagation.
This is valid DRAT interoperability, but not evidence that `drat-trim` consumes
a long learned-clause trace. A nontrivial external-proof cell would require a
separately preregistered selection protocol with every attempted row retained.
