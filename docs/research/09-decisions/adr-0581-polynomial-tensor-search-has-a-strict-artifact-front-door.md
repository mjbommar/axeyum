# ADR-0581: Polynomial-tensor search has a strict artifact front door

Status: accepted
Date: 2026-08-26
Index-summary: Full-polynomial GF(2) rank search exports DIMACS and admits SAT or UNSAT artifacts only through replay

## Context

ADR-0564 made bounded rank complete for an arbitrary in-memory `GF(2)` tensor, but the only
end-to-end synthesis example constructs matrix-multiplication tensors. The programme's named
target is full polynomial multiplication `P_6`; reaching it required either ad hoc code or
mislabeling it as a generic/matrix experiment. External proof-producing solvers also needed a
strict model-import path parallel to the Rado route.

## Decision

Add a family-native `synthesize_gf2_polynomial_tensor` driver. It constructs the target with
`Gf2Tensor::full_polynomial_multiplication`, selects the complete baseline or complete
summand-order encoding, and supports four explicit routes: deterministic DIMACS export,
pinned-witness calibration, strict SAT Competition model import plus portable JSON output, and
file-backed textual DRAT checking.

A SAT artifact receives credit only after the imported assignment satisfies the exact CNF,
lifts through the encoding layout, and passes the independent CAS coefficient replay. An UNSAT
artifact receives credit only after the file-backed backward checker accepts it against the
regenerated formula. Internal bounded search keeps the same replay/check contract. Terminal file
modes are mutually exclusive, and model import requires a paired output path.

## Evidence

- The published rank-17 `P_6` decomposition pins into the ordered formula and the resulting SAT
  model lifts and replays all 396 coefficients.
- A small `P_2` control exports deterministically, accepts a complete external SAT model, writes
  a portable decomposition, and rejects malformed or incomplete model payloads through the
  shared strict parser.
- Focused controls, all-target/all-feature Clippy, and warning-denied Rustdoc cover the new
  consumer without changing the generic encoding or any retained formula hash.

## Consequences

The actual polynomial family can now use Axeyum's search, external solver, model, proof, CAS,
and artifact boundaries end to end. This adds no new tensor-rank theorem and no new symmetry
claim. A timeout or proof prefix remains `UNKNOWN`; the rank-16 `P_6` question changes only when
a replayed model or checked complete refutation exists.
