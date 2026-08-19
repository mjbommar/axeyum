# Equality-elimination composition control

Date: 2026-08-19

## Result

The failure beneath the first `Nat.fib_add_two` attempt is repaired and pinned
without a second target execution.

The imported recursor has this universe shape:

```text
Eq.rec.{motive, carrier}
```

For a proposition-valued motive over `Nat`, the correct instance is therefore
`Eq.rec.{0,1}`. The failed producer used `{0,0}`; the first diagnostic candidate
`{1,0}` was also correctly rejected because it still placed `Nat` in the
`Prop` carrier slot.

With `{0,1}`, the independent kernel accepts fresh generic transitivity and
`Nat.succ` congruence declarations. Both have empty axiom footprints and no
theorem dependencies. Their declaration identities are respectively
`cc4b8c535ad43a4ff88462ce4a4800ae9b3e7bb29a08b2b894206798d0eae49e`
and
`fff923e8148cfd27c1bfb62f03c334e6d62998e613c2b4735494a84998df0b01`.

## Controls

Two synthetic tests build only the in-tree logic prelude. One requires
`Eq.rec.{0,1}` to accept a `Type` carrier and its reversed universe order to
fail. The other independently infers the complete local transitivity theorem.

A separate exact-source control imports the pinned Lean 4.30 r080 stream and
repeats transitivity plus congruence against its real `Eq.rec`. It does not
resolve the target definition and reports zero target submissions and zero
target outcomes.

## Sequencing

Bottom-up, the equality-composition constructor is now ready. Top-down,
`Nat.fib_add_two` remains the correct foothold for the Fibonacci/GCD chain.
The exhausted v1 policy cannot be reused: the next increment must freeze a new
v2 policy against tooling commit `b69a7534a`, keep the same two-template/two-
submission/one-invocation/zero-retry ceiling, and explicitly bind these control
hashes before any second target run.

## Reproduction

```sh
cargo test -p axeyum-lean-import --example nat_fib_iterate_recurrence
cargo run -p axeyum-lean-import --example nat_fib_iterate_recurrence -- \
  --composition-control --stream /path/to/r080.ndjson
```

