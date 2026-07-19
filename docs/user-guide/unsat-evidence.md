# UNSAT Evidence

Axeyum can export a scalar `QF_BV` refutation as two standard text files:

- `problem.cnf` — the bit-blasted query in DIMACS CNF;
- `proof.drat` — a DRAT refutation of that CNF.

When the current DRAT proof contains only steps the elaborator supports, the
bundle also includes `proof.lrat`, whose explicit hints permit linear-time
checking. `manifest.json` binds the input and every output by SHA-256 and records
that Axeyum independently rechecked the exported text before writing the
bundle.

## Export one SMT-LIB query

The command accepts one flat `QF_BV` script with exactly one `check-sat`:

```sh
cargo run --release -p axeyum-bench --bin qfbv-proof-export -- \
  query.smt2 proof-bundle
```

The output directory must not already exist. The exporter rejects
`push`/`pop`, `reset-assertions`, `check-sat-assuming`, multiple checks, and
non-`QF_BV` logic rather than silently proving a different flat query. A
satisfiable or inconclusive query exits nonzero and creates no output bundle.

On success:

```text
proof-bundle/
├── manifest.json
├── problem.cnf
├── proof.drat
└── proof.lrat       # present when DRAT-to-LRAT elaboration succeeds
```

`manifest.json` is the completion marker. It records the source byte hash,
assertion/check counts, output byte counts and hashes, and `self_rechecked:
true`.

## Check without the producing solver

Axeyum's Rust API rechecks from text alone:

```rust
let ok = proof.recheck()?;
assert!(ok);
```

The exported pair is also consumable by standard external tools such as
`drat-trim`:

```sh
drat-trim proof-bundle/problem.cnf proof-bundle/proof.drat
```

An external checker is deliberately not a runtime dependency. The default
Axeyum build stays pure Rust; consumers choose and pin any additional checker
used by their artifact or CI policy.

## What the proof establishes

DIMACS+DRAT proves that the exported CNF is unsatisfiable. This is a strong,
portable clausal certificate, but by itself it does not prove that the
SMT-LIB-to-CNF reduction is correct. Keep these assurance statements distinct:

| Evidence | Machine-checked claim | Remaining boundary |
|---|---|---|
| SAT model replay | The model satisfies the original parsed assertions | Parser/IR semantics |
| DIMACS + DRAT | The exported CNF is UNSAT | Term lowering and CNF correspondence |
| End-to-end QF_BV certificate | Independent reference lowering agrees and the final CNF is DRAT-refuted | Bounded reference/checker TCB |

Use `certify_qf_bv_unsat_end_to_end` when the source-to-CNF boundary, rather
than only the clausal result, must be checked. Its miter proof and final DRAT
proof are independently rechecked. A resource-bounded `NotCertified` is a
coverage result, never permission to relabel the query `sat` or `unsat`.

## Rust API

For a typed query, call `export_qf_bv_unsat_proof`:

```rust
use axeyum_solver::{UnsatProofOutcome, export_qf_bv_unsat_proof};

match export_qf_bv_unsat_proof(&arena, &assertions)? {
    UnsatProofOutcome::Proved(proof) => {
        assert!(proof.recheck()?);
        std::fs::write("problem.cnf", &proof.dimacs)?;
        std::fs::write("proof.drat", &proof.drat)?;
    }
    UnsatProofOutcome::Satisfiable => { /* no UNSAT proof exists */ }
    UnsatProofOutcome::Inconclusive => { /* preserve as inconclusive */ }
}
```

Array, UF, and combined elimination routes have companion exporters, but their
DRAT proves the reduced clausal query modulo the named trusted eliminations.
Read the [capability matrix](../research/08-planning/capability-matrix.md) and
[trust ledger](../research/08-planning/trust-ledger.md) before describing those
as source-level proofs.
