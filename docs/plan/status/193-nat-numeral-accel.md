# Lane: nat-numeral-accel — prelude `Nat` numerals and the kernel's binary literal fast path

<!-- plan-section: lane-status -->

**Your lane's block (`needs-decision`, nat-numeral-accel, 2026-08-28).** The
diagnosis held and is now measured rather than read; the fix works and is sound;
**and the benefit is not where it was expected, while the cost is somewhere
nobody looked.** All three parts matter and only the set of them is honest.

**The mechanism (confirmed, mine).** `NatOps::num` built `succ^n Nat.zero`.
`Kernel::reduce_nat_binop` fires only when both arguments whnf to `Lit::Nat`,
and `Nat.zero` is a constructor with no definition, so a unary tower never does
— ~2,280 numeral call sites across `nat`/`int`/`rat`/`creal`/`complex` were all
on the slow side of a fast path built, tested by four suites, and trusted since
the Lean import work. `examples/nat_numeral_whnf_probe` prices it: `Nat.mul 125
105` 52,399 µs → 10 µs; `Nat.gcd 512 1875` **25.6 s → 16 µs** (1.6 million×);
`Nat.div 13125 25` **stack-overflows** unary, at exactly the magnitude
`Rat.normalize` forms.

**The fix (landed on this branch, ADR-0613).** `num` emits `Lit::Nat(n)`;
`num_unary` keeps the constructor spine. All seven preludes still build, so
every proof term written against the unary form re-passes
`Kernel::add_declaration` — **no proof edited, blast radius zero on proofs**.
Guard: `tests/nat_prelude_numerals_are_literals.rs`, five assertions, each
mutation-verified. Reverting `num` to unary kills exactly the two shape tests
and leaves both defeq tests green, which is the point.

**The benefit is ~zero on today's tree.** Interleaved A/B, same binary from the
two `num` bodies, `AXEYUM_PRELUDE_CACHE=0`: `creal` **14.91 s → 14.23 s**
(4.6%, and a second round under load 6.2 put the *unary* side at 23.4 s — noise
larger than the effect); `nat` 193.5 → 191.2 ms; `rat` 762.6 → 784.4 ms.
**Treat `creal_prelude_builds` as unchanged.** The committed preludes do not
spend meaningful time reducing closed `Nat` at large magnitudes; the 587 s →
113.5 s incident was one declaration forming a 13,125-magnitude `Nat`. What the
change buys is that the shape stops being a landmine, not that today is faster.

Do not quote the brief's 94.85 s `creal_prelude_builds` figure. Measured here on
`main` at `f3ecf4004`, release, cache off: **15.54 s / 15.35 s** via
`prelude_build_timing` — a different harness from the test, but nothing near 94 s
either way.

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

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-numeral-accel | `NatOps::num` → `Lit::Nat`: `reduce_nat_binop` now reachable (1.6M× on `gcd 512 1875`), no proof edited, prelude-build win measured at ~zero, and 12 pins + 3 scripts + 5 fact checkers + 388 fact statements move on rendering (ADR-0613, proposed) |
