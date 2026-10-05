# Lane: nat-helper-dedup — promote nat_prelude private helpers duplicated 2-3 ways

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-helper-dedup, 2026-08-28).** Promoted the
three genuine duplicate groups the brief named, all confirmed byte-for-byte
identical before consolidation:

- `two_divisor_dichotomy` (`d ∣ 2 → d = 1 ∨ d = 2`) — three copies:
  `irrational.rs`'s `two_divisor_dichotomy`, `perfect.rs`'s `divisors_of_two`,
  and a third inlined directly inside `primes.rs`'s `Nat.prime_two`
  construction (not its own `fn`, but the identical term-building sequence).
  Promoted to `nat_prelude/ops.rs` as `pub(super) fn two_divisor_dichotomy`,
  self-contained (uses an inline `or_rec` application rather than depending
  on `or_elim`/`or_cases`, since those remain private per-file combinators
  used extensively elsewhere in `irrational.rs` and `primes.rs`). 4 call
  sites re-pointed (1 in `irrational.rs`, 2 in `perfect.rs`, 1 inlined
  construction in `primes.rs`'s `prime_two` replaced with a direct call).
- `two_mul_eq_add_self` (`Eq (mul two k) (add k k)`) — two copies:
  `powsq.rs`'s `two_mul_eq_add_self` and `primes.rs`'s
  `two_mul_eq_add_local`. Promoted to `ops.rs` under the more descriptive
  original name. 4 call sites re-pointed (2 in `powsq.rs`, 2 in `primes.rs`).
- `bool_true_or_false` (`Or (beq b true) (beq b false)`, `Bool.rec`) — the
  brief named two copies (`totient.rs`, `primes.rs`); a third turned up while
  re-pointing call sites: `perfect.rs` had its own copy too, used at **5**
  internal call sites, byte-identical and even self-documented as "local
  copy of `totient.rs`'s `bool_true_or_false`" — so the duplication was
  already known and recorded, just never acted on. All three promoted to
  `ops.rs`. 7 call sites re-pointed total (1 `totient.rs`, 1 `primes.rs`, 5
  `perfect.rs`).

Placed in `nat_prelude/ops.rs` rather than `helpers.rs`: the brief named
`ops.rs` as the shared-machinery location, `ops.rs` is in this lane's scope
and `helpers.rs` is not, and every one of the five touched files already
`use super::ops::{NatDev, NatOps}`, so promoting into that same module means
callers just widen an existing import rather than adding a new one.

**A fourth latent duplicate was found and deliberately left alone**:
`irrational.rs`'s `or_elim` and `primes.rs`'s `or_cases` are an identical
generic `Or`-elimination combinator (build a motive, apply `Or.rec`), and the
same shape recurs dozens more times inline across `order.rs`, `division.rs`,
`bezout.rs`, `crt.rs`, `parity.rs`, `perfect.rs` and others — none of which
are in this lane's scope. Consolidating `or_elim`/`or_cases` themselves would
touch files this lane does not own and is a separable, much larger task (the
`or_rec` idiom appears at ~60+ call sites project-wide). Left as-is; noted
here rather than silently expanded.

Verified: `cargo check -p axeyum-lean-kernel` clean; `clippy --all-targets
--all-features -D warnings` clean (also fixed one pre-existing
`uninlined_format_args` clippy violation in `nat_prelude_tests.rs` at
`coprime_two_left`'s axiom-footprint assertion, unrelated to this lane's
diff but blocking the gate); `RUSTDOCFLAGS="-D warnings" cargo doc -p
axeyum-lean-kernel --no-deps` clean; `cargo test -p axeyum-lean-kernel --lib
nat_prelude::` — **98 passed, 0 failed** before and after (identical count:
promoting a private `fn` to a shared `pub(super) fn` does not change the
kernel environment, since none of these helpers were ever
`declare_*`d/registered as kernel declarations — they are Rust-level
proof-term builders consumed by declarations, not declarations themselves).
`the_build_is_deterministic`'s pinned `67 + 347` and
`every_nat_declaration_is_checked_and_axiom_free`'s environment-derived
coverage assertion both pass unchanged.

`scripts/check-shape-duplicates.py`: **10 groups before, 10 groups after
(re-measured with a fresh `--release` `shape_search` build after landing the
`perfect.rs` fix too), both all-allowlisted.** Unchanged, as predicted —
that script's `--duplicates` census walks `kernel.environment()` for
declarations that share an admitted *type shape*, and none of the
consolidated helpers were ever kernel declarations (no
`.theorem(...)`/`.definition(...)` call names them), so the tool cannot see
them and never could. This is exactly the retrieval blind spot the task
named: a private Rust `fn` is invisible to any index over the kernel
environment, which is why it gets rebuilt (or, as with `bool_true_or_false`,
rebuilt with a comment admitting it) instead of found and reused.

Nothing the kernel rejected — every consolidation was a pure refactor
(move + rename + re-point call sites), the proof-term construction for each
promoted function is byte-identical to (one of) its former copies, and the
theorem statements it discharges are unchanged.

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-helper-dedup | promoted `two_divisor_dichotomy` (3→1), `two_mul_eq_add_self` (2→1), `bool_true_or_false` (3→1, found a 3rd copy in `perfect.rs` beyond the brief's two) to `nat_prelude/ops.rs`; re-pointed 15 call sites across `irrational.rs`/`perfect.rs`/`primes.rs`/`powsq.rs`/`totient.rs`; census unchanged at 10/10 (tool is blind to private-fn duplication by construction) |
