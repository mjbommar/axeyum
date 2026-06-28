# QF_BV Bit-Blast Evidence

## Problem Shape

Tiny unsat shape:

```text
(x & 1) = 1
(x & 1) = 0
```

Fragment: `QF_BV`.

Expected result: `unsat`.

The regression uses a 24-bit `x` so the query bypasses tiny term-level
enumeration and exercises the clausal bit-blast route.

## Solver Route

Axeyum lowers the original Bool/BV terms to AIG, then CNF, then SAT. The search
engine is not trusted: an `unsat` answer is accepted only with an independently
checked proof artifact, and a `sat` answer is accepted only after replaying the
lifted model against the original terms.

## Evidence Artifact

Current checked artifact: a DRAT-style SAT certificate for the generated CNF.

Important boundary: the plain DRAT route certifies the SAT refutation of the CNF
but does not by itself prove every bit-blast lowering step in the Lean kernel.
The cookbook keeps that distinction explicit.

## Checker

The focused evidence test is
`unsat_evidence_carries_a_recheckable_drat_certificate` in
[crates/axeyum-solver/tests/evidence.rs](../../../crates/axeyum-solver/tests/evidence.rs).

It checks:

- the produced evidence is an unsat certificate;
- the backend provenance is recorded;
- `Evidence::check` re-runs the stored proof checker against the original query.

Related test:
`qf_bv_drat_unsat_reports_bitblast_tseitin_sat_steps` records the trust-step
ledger for the DRAT path.

## Lean Reconstruction

Status: partial.

Some QF_BV sub-fragments reconstruct to Lean, including comparison and selected
bit-vector reductions. The broad DRAT fallback is not the same as a
Lean-kernel-checked proof of the original formula.

## Trust Boundary

Trusted or not yet kernel-certified:

- general bit-blast faithfulness on the plain DRAT fallback;
- any solver search used to discover the contradiction.

Checked:

- the DRAT certificate for the generated CNF;
- replay of SAT models on the original terms for satisfiable cases.

Downgrade behavior:

- if evidence cannot be produced or checked, the route must not report a proved
  result.

## Commands

Focused:

```sh
cargo test -p axeyum-solver --test evidence unsat_evidence_carries_a_recheckable_drat_certificate
cargo test -p axeyum-solver --test evidence qf_bv_drat_unsat_reports_bitblast_tseitin_sat_steps
```

Broader:

```sh
cargo test -p axeyum-solver --test evidence
```

## Links

- [SMT Fragment Atlas](../../atlas/README.md)
- [atlas JSON](../../../artifacts/ontology/smt-fragments.json)
- [support matrix](../../research/08-planning/support-matrix.md)
- [trust ledger](../../research/08-planning/trust-ledger.md)
- [QF_BV parity path](../../PARITY-STATUS-AND-PATH.md)
