# Notes: 193-nat-numeral-accel

Detail moved out of [`../status/193-nat-numeral-accel.md`](../status/193-nat-numeral-accel.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The cost is a ledger-wide RENDERING change, and this is the decision to
make.** `lean_pp` prints `Lit::Nat(n)` as `n` where it printed `AxNat.zero` /
`AxNat.succ AxNat.zero`. `AxNat.succ x0` is unchanged — a successor of a
*variable* is built by `succ`, not `num` — which is what confirms only numerals
moved. Measured:

| surface | count |
| --- | ---: |
| `cargo test -p axeyum-lean-kernel --lib` | **913 passed, 12 failed** — every failure a pinned rendered statement |
| pinned statements | 6 `rat_prelude_tests.rs`, 3 `int_prelude_tests.rs`, 1 `nat_prelude_tests.rs`, 2 `creal_tests.rs` |
| autogenesis scripts matching the old rendering | 3 (two are gates) |
| fact `evidence` / `checker_command` | **5** |
| fact `formal.statement` | **388** — documentation, so these drift *silently* rather than going red |

**The 12 pins were deliberately NOT repinned.** A drift pin rewritten
mechanically is how a real drift gets masked, and `AxNat.zero` also renders from
a direct `zero()` call `num` never touched, so a textual rewrite is unsound —
each needs the string the kernel actually renders. And the 388 silently-drifting
statements are a ledger question with `artifacts/` outside this lane's scope.

**Recommended alternative, unmeasured, zero rendering blast radius:** make
`Nat.zero` reduce to `Lit::Nat(0)` so unary towers collapse bottom-up in `whnf`
and `reduce_nat_binop` fires, leaving every stored and rendered term as it is.
Two caveats the ADR states and this lane did not test: the `div 13125 25` stack
overflow probably **survives** (the tower is still walked at depth 13,125), and
a new eager probe on `whnf`'s hot path is not free — ADR-0536 records the binary
acceleration alone taking a build 8.7 s → 33.0 s.

**One consequence to know before narrowing anything in `tc.rs`.**
`Kernel::nat_offset`'s `Lit::Nat` arm is now load-bearing for
`build_nat_prelude` itself: deleting it makes the nat prelude fail to admit
(`TypeMismatch`), where before it was invisible to the prelude. That is the one
prediction this lane got wrong — it was expected to kill one test and killed all
five.

**Not run:** `cargo test --workspace --lib` (did not run — the kernel sweep is
667 s and consumed the budget). `cargo doc`, `clippy` did not run.
