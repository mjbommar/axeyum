# Trust Ledger

The authoritative table is the
[generated trust ledger](../research/08-planning/trust-ledger.md). It records
the trusted and independently checked steps that can occur in each result path.

The ledger is rendered from code and protected by a golden test:

```sh
cargo test -p axeyum-solver --test trust_ledger --features full
```

## Reading assurance correctly

- **Checked** means an independent checker validates the named certificate or
  replay obligation.
- **Validated** means testing/differential evidence supports the route, but no
  complete per-query certificate closes every layer.
- **Trusted** identifies code or a transformation meta-argument still inside
  the trusted computing base.
- **Absent/partial** means no stronger claim should be inferred from a solver
  verdict or downstream proof.

Assurance is per route and per layer, not per logic label. A checked DRAT proof
of a CNF refutation does not automatically check the source-to-CNF transform.
A replayed SAT model does not imply an independently checked UNSAT route for the
same fragment.

See [Proof and evidence obligations](../contributor-guide/proof-and-evidence-obligations.md)
for the change checklist and the [Proof Certificate Cookbook](../proof-cookbook/README.md)
for concrete routes.

