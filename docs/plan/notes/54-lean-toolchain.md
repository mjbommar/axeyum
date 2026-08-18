# Notes: 54-lean-toolchain

Detail moved out of [`../status/54-lean-toolchain.md`](../status/54-lean-toolchain.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The guard is exercised, not asserted.** `scripts/tests/test-lean-toolchain-policy.sh`
(now in `just check` and `check.sh`, ahead of the gate) points both entry points
at the non-pinned 4.34.0-rc1 and requires the refusal by name, checks that the
shell gate and the Rust probe resolve the *same* binary, and — control 5c —
requires the same suite to **pass** once the deviation is stated, so 5b's failure
cannot be dismissed as "4.34 is broken here". Three separate one-guard deletions
each killed **exactly one** control. It also fails rather than passing when no
second toolchain is installed to exercise the wrong-toolchain case.

**4.34 breakage fixed, not merely diagnosed.** `Environment.addDeclCore` gained a
`maxRecDepth : USize` parameter in 4.34, so the replay script died before reading
a byte of the stream; the call is now resolved at elaboration time and
`real_lean_kernel_replay` passes under **both** toolchains (positive replay and
tampered negative control alike).

**Next:** `real_lean_wire_differential`'s own `pinned_lean()` is now a redundant
assertion of the same policy rather than a competing one — collapse it onto
`lean_probe::lean_bin()` when that file is next touched. Unrelated finding for
whoever owns it: `cargo clippy -p axeyum-lean-import --tests -- -D warnings`
fails on `real_lean_wire_differential.rs:458` (`too_many_lines`, 121/100) on
unmodified `HEAD` content.
