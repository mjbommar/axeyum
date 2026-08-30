# Notes: 197-nat-helper-dedup

Detail moved out of [`../status/197-nat-helper-dedup.md`](../status/197-nat-helper-dedup.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
