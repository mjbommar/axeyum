# axeyum-cas

Proof-carrying computer algebra for Axeyum. Symbolic transforms produce
certificates that are checked or lowered to decidable IR obligations; the crate
does not treat a successful algebraic search as proof by itself.

The extensive API examples live in the [crate documentation](src/lib.rs). Two
larger tours are executable:

```sh
cargo run -p axeyum-cas --example cas_tour
cargo run -p axeyum-cas --example certified_calculus
```

Current proof-route assurance belongs in the generated
[trust ledger](../../docs/reference/trust-ledger.md).
