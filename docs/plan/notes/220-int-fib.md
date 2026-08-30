# Notes: 220-int-fib

Detail moved out of [`../status/220-int-fib.md`](../status/220-int-fib.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**`Int.fib` is independently checked by evaluation, not only by this
theorem's type-check** — `fib_computes_the_sign_extended_sequence`
(`int_prelude_tests.rs`) reduces `fib` at six concrete indices (both signs:
`fib(3)=2, fib(2)=1, fib(-1)=1, fib(-2)=-1, fib(-3)=2, fib(-4)=-3`) against
the hand-computed sequence, with a negative control at `fib(-2)` (`fib(-2)`
must NOT compute to `1`) guarding against a definition that silently dropped
the sign.

Measured `axiom_footprint`: **empty** for both `Int.fib` and
`Int.fib_two_mul_add_one_pos` (`theorem_axiom_footprint`, `integer` row: `610
theorems, 610 axiom-free`, environment carries 0 trusted declarations in the
`integer` prelude). `int_prelude::` full sweep: **37 -> 38 tests, all green**
(added `fib_computes_the_sign_extended_sequence`); no test removed, no
regression. `cargo fmt --check` and `cargo clippy --all-targets -D warnings`
both clean on the touched files.

**No target carried a HELD-OUT or MUTATION marker.** Checked
`scripts/fact-frontier.py` directly: the sixth "open `integer-fibonacci`"
fact, `F:ml430-mutation-aabb80b1f89f0c5847364692`, carries
`⛔ MUTATION (boundary-widening-biconditional)` — skipped, not attempted, as
instructed.

**Kernel rejected nothing on the landed declarations** — both `declare_fib`
and `declare_fib_two_mul_add_one_pos` kernel-checked on the first attempt
after compiling. (Two ordinary `cargo check` compile-error rounds first, both
missing imports — `BinderInfo`/`Declaration`/`ReducibilityHint`/`Shape`/
`case_split` — fixed before any kernel run.)

**Not attempted** (left for the next lane): the other three open
`integer-fibonacci` facts —
`F:ml430-int-fib-add-181b6a2c` (`Int.fib_add`, the general addition formula
`fib(m+n) = fib(m-1)fib(n) + fib(m)fib(n+1)` for arbitrary `m, n : ℤ` — needs
genuine two-sided induction over `ℤ`, substantially larger than this lane's
scope), `F:ml430-int-fib-of-odd-66560495` (needs an `Int.Odd`/`Int.Even`
predicate pair, which does not exist in this kernel at all — only `Nat.Odd`/
`Nat.Even` are declared), and `F:ml430-int-fib-two-mul-0e70f3dd` plus
`F:ml430-int-fib-two-mul-add-two-0ba4a948` (both `needs first:
F:ml430-int-fib-add-181b6a2c`, blocked on the addition formula above).
