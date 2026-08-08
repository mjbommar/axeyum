# axeyum-rewrite

Rewrite contracts, deterministic denotation-preserving canonicalization, and
explicit model reconstruction for broader equisatisfiable transformations.
Every registered rule declares a stable ID, precondition, preservation class,
projection obligation, and validation route.

The default canonicalizer contains only denotation-preserving rules. Array,
function, bounded-integer, quantifier, equation-solving, value-propagation, and
unconstrained-elimination passes are separate APIs with their own admission and
reconstruction contracts.

Use the compile-tested example in the [crate documentation](src/lib.rs), then
read [Rewriting and reconstruction](../../docs/internals/rewriting.md) or the
[contributor checklist](../../docs/contributor-guide/adding-a-rewrite.md).

```sh
cargo test -p axeyum-rewrite
```
