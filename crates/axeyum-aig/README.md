# axeyum-aig

Deterministic and-inverter graphs (AIGs) for Axeyum. The crate owns primary
inputs, complemented literals, structurally hashed AND nodes, derived Boolean
gates, evaluation, construction statistics, and ASCII AIGER debug export. It
has no dependency on another Axeyum workspace crate.

The compile-tested example is in the [crate documentation](src/lib.rs). The
place of AIGs in the solve pipeline is explained in
[Bit-blasting](../../docs/internals/bit-blasting.md).

```sh
cargo test -p axeyum-aig
```
