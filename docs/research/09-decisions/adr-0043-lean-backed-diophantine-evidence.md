# ADR-0043: Lean-backed Diophantine evidence (integer-infeasibility unsat carries a self-check + kernel-checked Lean module)

Status: accepted
Date: 2026-06-21
Relates to: ADR-0042 (the integer prelude + `int_reconstruct`), P2.4 (the
`DiophantineCertificate`), ADR-0041 (the same pattern for SOS), ADR-0031 (the
trust ledger), and the evidence pipeline (`crates/axeyum-solver/src/evidence.rs`,
`trust.rs`).

## Context

Integer-systems infeasibility (`x+y=0 ∧ x−y=1 ⇒ 2x=1`, or cancelling systems
`x=1 ∧ x=2 ⇒ 0=1`) is decided by the `DiophantineCertificate` (P2.4) — an integer
Farkas combination with an independent re-checker `check_diophantine_certificate`
— and, as of ADR-0042, reconstructs to a **kernel-checked (and real-`lean`-checked)
Lean `False`**. But there is no `Evidence` variant for it: the standard evidence
path routes integer unsats through the Alethe `lia_generic` cert, which — STATUS
P3.3 notes — **Carcara cannot check** for integer systems (it is a Carcara hole).
So the one integer-infeasibility route that *is* independently checkable (the
Diophantine self-check) and *is* Lean-backed is not surfaced as first-class
evidence.

## Decision

Add a first-class self-checking, Lean-backed `Evidence` variant for the Diophantine
route, mirroring `Evidence::UnsatSos` (ADR-0041):

- `Evidence::UnsatDiophantine { equalities: Vec<Equality>, certificate:
  DiophantineCertificate, lean_module: Option<String> }`.
- `produce_diophantine_evidence(arena, assertions) -> Result<Option<EvidenceReport>,
  SolverError>`: when `prove_lia_unsat_by_diophantine_certified` accepts the system,
  emit the variant; populate `lean_module` best-effort from
  `reconstruct_diophantine_to_lean_module` (None when reconstruction declines a
  shape — the certificate self-check still backs the unsat).
- `Evidence::check`: re-validate `check_diophantine_certificate(&equalities,
  &certificate)` AND, when a module is carried, **re-run**
  `reconstruct_diophantine_to_lean_module` (the kernel re-checks the freshly-built
  proof; the stored string is never trusted alone).
- `TrustId::Diophantine`: `certified` (it has an independent per-result checker AND
  a kernel-checked reconstruction), pedantic level `10` (an exact self-checked
  certificate, like `Farkas`/`Sos`), reference ADR-0042. Regenerate the
  golden trust-ledger doc.

## Consequences

- Integer-systems infeasibility becomes a first-class certified + Lean-backed
  evidence route — re-checkable two independent ways (the integer-Farkas self-check
  and the kernel-checked Lean reconstruction), and unlike the `lia_generic` Alethe
  route it is *actually* independently checkable in-tree and externally in Lean.
- The variant shape touches every `Evidence` match arm (mechanical); no other route
  changes. The re-check cost is one Diophantine elimination + one bounded
  reconstruction per `check`.
- Scope: the Diophantine (integer-equality-systems) fragment. Integer-inequality
  cuts (Gomory) remain future work; this surfaces the equality-systems route that
  is already decided and reconstructed.
