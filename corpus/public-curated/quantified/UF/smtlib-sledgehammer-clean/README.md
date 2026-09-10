# SMT-LIB sledgehammer UF slice (committed)

Vendored from the SMT-LIB 2024 non-incremental release, division `UF`, family
`sledgehammer/`. Names flatten the original path (`/` -> `__`) in the same style
as the sibling `cvc5-regress-clean/` directory.

Provenance, from the files' own `:source`: *"Benchmarks from the paper:
'Extending Sledgehammer with SMT Solvers' by Jasmin Blanchette, Sascha Bohme,
and Lawrence C. Paulson, CADE 2011. Translated to SMT2 by Andrew Reynolds and
Morgan Deters."* Every file here carries a `(set-info :status ...)` line.

## Why these are committed rather than read from the NAS corpus

Each file pins a **capability** that a `corpus/regression/` entry cannot pin.
That gate is a soundness gate by construction: it skips `unknown`, so a file
that regresses from `unsat` to `unknown` is silently counted as a coverage gap
and the suite stays green. A capability needs a test that asserts the verdict.
See `crates/axeyum-solver/tests/quant_skolem_egraph_routing.rs`.

## Contents

| file | logic | status | what it pins |
|---|---|---|---|
| `smtlib__UF__sledgehammer__Hoare__smtlib.1116374.smt2` | UF | `unsat` | the Skolemized assertion set reaches the e-graph instantiation loop even when trigger instantiation left no residual quantifier (`auto.rs`, `skolemized_egraph_retry`) |
