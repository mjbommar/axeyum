# UNSAT Evidence

Axeyum can export a scalar `QF_BV` refutation as two standard text files:

- `problem.cnf` — the bit-blasted query in DIMACS CNF;
- `proof.drat` — a DRAT refutation of that CNF.

When the current DRAT proof contains only steps the elaborator supports, the
bundle also includes `proof.lrat`, whose explicit hints permit linear-time
checking. `manifest.json` binds the input and every output by SHA-256 and records
that Axeyum independently rechecked the exported text before writing the
bundle.

This export API is distinct from
`SolverConfig::with_prove_unsat(true)`. That verdict-only mode requires a
checked DRAT proof before returning `Unsat`, and fails closed to `Unknown` when
the proof core exhausts its budget, but it does not return or write the proof
artifact. Use the exporter below when the certificate itself is required.

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

## Python replay of saved certificates

Restore the exported text and check it against the caller's original typed
assertions. Constructing an `UnsatProof` stores data; it does not accept its claim.
For example, after exporting the Boolean query `p` and `not p`:

```python
from pathlib import Path
from axeyum import ir
from axeyum.solver import proofs

arena = ir.Arena()
p = arena.bool_var("p")
assertions = [p, arena.not_(p)]

bundle = Path("boolean")
lrat_path = bundle / "proof.lrat"
proof = proofs.UnsatProof(
    (bundle / "formula.cnf").read_text(),
    (bundle / "proof.drat").read_text(),
    lrat_path.read_text() if lrat_path.exists() else None,
)
assert proof.recheck_for_bool_terms(arena, assertions) is True
assert proof.recheck_for_bool_terms(arena, [p]) is False
```

This method also accepts supported BV expressions under Boolean assertion roots.
It reconstructs the deterministic bit-blast/Tseitin CNF, requires exact DIMACS
agreement, then checks the refutation. It reuses the trusted reduction and does
not prove that reduction independently. It accepts `ir.Arena` terms;
`smt.parse` owns a distinct Script arena. Array, UF, datatype and finite-width
LIA elimination certificates need their own source correspondence checks.

`False` means a source/CNF mismatch or rejected proof. Unsupported terms and
malformed proof text raise `AxeyumError`; mixed arena handles raise `EpochError`.
Saved text is limited to 8 MiB per component and 16 MiB total; exceeding a cap
raises a resource-limit `ValueError`. Replay uses the existing unlimited Rust
checker contract. An absent LRAT remains `None` and permits DRAT checking;
a present invalid LRAT cannot silently fall back to a successful DRAT check.

## Python reference-miter certificates

For supported Boolean and BV terms, request a certificate containing both the
reference-lowering miter refutation and the final query refutation:

```python
outcome = proofs.certify_qf_bv_unsat_end_to_end(
    arena, assertions, timeout_ms=20_000,
)
assert outcome.status == "certified"
certificate = outcome.proof
assert certificate is not None

# These strings can be saved and restored in a separate process.
restored = proofs.EndToEndUnsatProof(
    certificate.faithfulness.dimacs,
    certificate.faithfulness.drat,
    proofs.UnsatProof(
        certificate.unsat.dimacs,
        certificate.unsat.drat,
        certificate.unsat.lrat,
    ),
)
assert restored.recheck_for_bool_terms(arena, assertions) is True
```

Source replay reconstructs the expected final CNF and reference miter from the
supplied original terms, requires exact correspondence for both, and checks
both refutations without SAT search. `recheck_refutations()` checks only the
two clausal proofs; use `recheck_for_bool_terms()` to establish correspondence
to the supplied query. Independent reference lowering, miter construction and
Tseitin encoding remain trusted; this API does not admit a kernel theorem.

The other statuses are `satisfiable` and `not-certified`, each with no proof.
An unsupported input or exhausted certification search can yield `not-certified`;
that status carries no SAT/UNSAT verdict. The timeout limits the two SAT searches
under one deadline; construction and checking use the unlimited Rust contract.
Restored text is capped at 8 MiB per component and 16 MiB per clausal proof,
with at most 32 MiB across the composite. Missing final LRAT remains `None`;
the reference miter currently supplies DRAT without LRAT.
