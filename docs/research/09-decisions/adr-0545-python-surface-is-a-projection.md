# ADR-0545: The Python Surface Is a Projection — Submodule Is Trust Tier, No Admission Authority

Status: accepted
Date: 2026-08-24
Index-summary: `axeyum._native` (PyO3, abi3) exposes the Rust engines and knowledge artifacts to Python as a projection; submodule names the trust tier; nothing callable from Python admits a fact, writes a ledger, relaxes a checker, or changes a footprint.
Index-status: accepted

## Context

The Python layer (strand `docs/python-2026-08/`) binds the SMT front door,
the IR and solver, the CAS and its certificate routes, the Lean-style kernel,
the two untrusted producers, and read-only accessors over every knowledge
artifact, and an agent loop drives them. The hard rules say semantics,
model/proof lifting, and checker routes must be explicit before a surface goes
public, and the flywheel's identity is *untrusted fast search, trusted small
checking*. A scripting layer is exactly where that boundary gets blurred by
convenience: a `bool` that means two things, a helper that writes "just this
once", a default that hides a budget.

Measured while building it (2026-08-24): PyO3 0.29.2 compiles under the
workspace `unsafe_code = "deny"` with clippy pedantic `-D warnings` on both
stable and nightly; the built `.so` links no `libpython`, so the default build
stays free of C/C++ (ADR-0002); `scripts/` has zero third-party imports and
every gate there runs on a fresh host. Two contract violations were caught by
review before landing: a replay that returned `False` both for "replayed and
wrong" and for "nothing to replay", and a replay state built through a
different route than the verdict it claimed to check.

## Decision

1. **Projection.** No function exists in Python that does not exist in Rust.
   The binding may wrap, name, and convert; it may not decide.
2. **Submodule is trust tier.** `R` (read/pure): `ir`, `knowledge`, the
   inventory half of `kernel`, the pure half of `cas`. `P` (propose —
   untrusted search): `smt`/`solver` verdict producers, `producers`, the
   `produce()` half of `cas.certify`. `C` (check/replay): `Outcome.replay`,
   `check_model`, `Evidence.check_outcome`, `UnsatProof.recheck`, every
   `Certificate.check`, `Kernel.add_declaration`. A `C` result is falsifiable:
   it exposes report counts or a three-valued outcome, never a bare `bool`
   that can also mean "did nothing".
3. **No admission authority.** Nothing callable from Python writes
   `artifacts/facts/`, the operation registry, the nursery, the overlay, or a
   prelude. The agent's tier-C tools are deferred (`requires_approval`) and a
   model-free supervisor decides; the only ledger-adjacent call is the
   read-only transaction *proposal* script. `scripts/` stays standard-library
   only, so the trusted gates never import the binding.
4. **Values, not exceptions, for the three honest non-answers.** `unknown`,
   `declined`, and `None` (outside the fragment / overflow) are values.
   Exceptions are for malformed input, budget misuse, kernel rejection, and
   `ReplayUnavailable` — which exists so that `replay() == False` has exactly
   one meaning: replayed, and the model does not satisfy the assertions.
5. **Replay checks the producer's own result.** The replay state is the front
   door's model lifted onto the parsed script's arena, never a re-solve
   through another route; a value the arena cannot represent (a lifted string
   against a packed encoding) is re-packed through a self-checking encoder or
   refused, never guessed; a quantified assertion is declared unreplayable up
   front.
6. **Handles are epoch-checked.** Kernel and arena ids are only meaningful
   relative to the object that interned them; every handle carries that
   object's epoch and a mismatch raises `EpochError` rather than reaching a
   Rust panic or a silently different term.
7. **Every Python gate prints a nonzero count** (`PYTEST|collected=N`,
   `STUBS|compared=M`, `EPISODES|checked=N`), and `scripts/check.sh` reports
   the gate as SKIPPED — never passed — on a host without `uv`.

## Consequences

- Widening any tier-C surface, giving an overlay or catalog edge admission
  weight, or letting an agent write the ledger requires a new ADR.
- The abi3 wheel forfeits free-threaded builds (3.14t needs a separate
  non-abi3 wheel later); `#[pymodule(gil_used = true)]` until the `Sync`
  audit of the mutable classes is done.
- The binding costs a second front-door call on `sat` to obtain a replayable
  model; removing it needs a Rust entry point returning verdict, arena,
  assertions and model together.

## Evidence

- `crates/axeyum-py/`, `python/axeyum/`, `python/tests/` (1,026 tests at
  `27c601025`); `docs/python-2026-08/01-pyo3-maturin.md` through `07-*.md`;
  `docs/python-2026-08/studies/pyo3-maturin-feasibility.md` (the measured
  probe); review fixes in `27c601025`.
