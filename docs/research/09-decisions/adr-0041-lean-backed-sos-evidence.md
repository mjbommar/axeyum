# ADR-0041: Lean-backed SOS evidence (the SOS unsat carries its kernel-checked Lean module)

Status: accepted
Date: 2026-06-21
Relates to: [ADR-0039](adr-0039-degree-2-sos-psd-certificate.md) (the SOS
decision), [ADR-0040](adr-0040-sos-lean-reconstruction.md) (SOS→Lean
reconstruction), [ADR-0036](adr-0036-lean-kernel-crate.md) (the in-tree Lean
kernel), and the evidence/trust pipeline (`crates/axeyum-solver/src/evidence.rs`,
`trust.rs`).

## Context

The degree-2 SOS unsat route now reconstructs to a kernel-checked Lean `False`
across both strict directions (ADR-0040). But that proof lives behind the separate
`prove_unsat_to_lean_module` entry; the route's **evidence** (`Evidence::UnsatSos`)
carries only the self-checking `SosCertificate` (re-validated by
`SosCertificate::verify`). So a normal solve of an SOS-decided unsat yields evidence
*without* the Lean proof — short of the destination-3 promise that **every unsat
carries a machine-checkable certificate accepted by a Lean-grade kernel**.

The mechanical blocker assumed earlier (the producer holds `&TermArena` but
reconstruction needs `&mut`) does **not** exist for SOS: `reconstruct_sos_proof`
takes `&TermArena` (it reads the query and builds *kernel* terms in a separate
`Kernel`; it never mutates the IR arena). So both `produce_nra_sos_evidence` (which
has `&TermArena`) and `Evidence::check(arena, assertions)` can run the SOS
reconstruction directly.

## Decision

Make `Evidence::UnsatSos` **carry its rendered Lean module** when reconstruction
succeeds, and re-derive-and-check it on `Evidence::check`.

- Add `pub fn reconstruct_sos_to_lean_module(arena: &TermArena, assertions:
  &[TermId]) -> Result<String, ReconstructError>` (reconstruct.rs): the immutable
  SOS-only entry — confirm the fragment is `Sos`, run `reconstruct_sos_proof`, gate
  (`infer` + `def_eq False`), and render the Lean module. Errors (declines) when the
  query is not an SOS-reconstructable unsat.
- Change `Evidence::UnsatSos(SosCertificate)` →
  `Evidence::UnsatSos { certificate: SosCertificate, lean_module: Option<String> }`.
  `produce_nra_sos_evidence` populates `lean_module` from
  `reconstruct_sos_to_lean_module` (best-effort: `None` when the shape is decided by
  the certificate but outside the current reconstruction slice — the certificate
  self-check still backs the unsat).
- `Evidence::check` for `UnsatSos`: re-validate `certificate.verify()` AND, when a
  `lean_module` is present, **re-run** `reconstruct_sos_to_lean_module(arena,
  assertions)` and require it succeeds. The re-derivation re-checks the proof
  through the trusted kernel (the kernel is the verifier — a stored string is not
  trusted; it is re-built and re-`infer`-checked), mirroring how the Alethe evidence
  variants re-run their checker rather than trust the carried proof.

The stored module is for *output* (`get-proof`-style inspection); the *check* is the
re-derivation, so a tampered/garbage `lean_module` cannot make `check` pass without
the kernel independently accepting a freshly-reconstructed proof.

## Consequences

- An SOS-decided unsat's evidence now carries a kernel-checked Lean proof — the
  first non-bitblast/non-LRA theory route to do so through the standard evidence
  path, a concrete step on destination-3 (Lean parity) for the NRA/SOS fragment.
- `TrustId::Sos` stays `certified`; the new fact is that the route's evidence is
  *Lean-backed*, re-checkable two independent ways (the rational `LDLᵀ`
  self-check **and** the kernel-checked reconstruction).
- The variant shape change touches every `Evidence::UnsatSos` match arm (mechanical);
  no other evidence route changes. The re-check cost is one reconstruction per
  `check` call (bounded: SOS reconstruction is degree-2, no search).
- Scope: only the SOS fragment. A general "Lean-backed evidence" trait across all
  fragments (so every reconstructable unsat carries its module uniformly) is a
  larger follow-up once more fragments are routed through `Evidence`.
