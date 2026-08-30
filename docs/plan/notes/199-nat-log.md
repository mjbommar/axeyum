# Notes: 199-nat-log

Detail moved out of [`../status/199-nat-log.md`](../status/199-nat-log.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**What the kernel rejected: nothing.** All six declarations were accepted on the
first attempt, and `every_nat_declaration_is_checked_and_axiom_free` (which
reads `kernel.environment()`, not a list) is green over all of them.

**`Nat.clog` is reachable and is NOT a separate problem.** It is the same fuel
recursion with the step `clog b n = clog b ((n + b - 1) / b) + 1` under the same
`2 ≤ b ∧ 2 ≤ n` guard, so `Nat.ble_eq_false_of_lt` and the whole boundary-case
technique transfer verbatim. Its four boundary facts (`clog_zero_left`,
`clog_one_left`, `clog_zero_right`, `clog_one_right`) should be `refl` case
analyses exactly as here. The genuinely harder tier is the same for both:
`log_le_self`, `log_lt_self`, `log_mono_right`, `clog_pos`, `log_le_clog` need
`logAux b f n ≤ f` proved with the argument GENERALIZED in the motive
(`∀ n, logAux b f n ≤ f`), which is a real induction rather than a case split.

**Not attempted, deliberately:** the twelve `F:ml430-nat-log-*` mirror facts stay
`open`. Our `Nat.log` is a *different definition* from Mathlib's, so claiming
their statements is a reconciliation question (`artifacts/autogenesis/`
proposition-reconciliation pipeline), not a hand-written status flip. Flipping
them by hand would be the checker-that-cannot-fail defect.

**Pre-existing red, NOT mine:** `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` fails on
`examples/nat_numeral_whnf_probe.rs:105` (`many_single_char_names`), from
commit `ceff1cdfe`. `--lib --tests` is clean.
