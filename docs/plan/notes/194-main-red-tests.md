# Notes: 194-main-red-tests

Detail moved out of [`../status/194-main-red-tests.md`](../status/194-main-red-tests.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Still owed, and outside this lane's scope (`artifacts/` was not mine to
touch):** raise `artifacts/kernel-stack-envelope.tsv`'s two `creal` rows to
`debug 16777216` / `release 8388608`. Until that lands the envelope gate stays
red — correctly.

## 2. `qfbv_proof_export` — the exporter could not succeed on any input

`crates/axeyum-bench/src/bin/qfbv-proof-export.rs` refused every script
containing a `ScriptCommand` other than `Assert` or `CheckSat`. Commit
`81361cdd1` (2026-08-21, "a command is answered or says `unsupported` — never
dropped") made `set-logic` and `set-option` **positional** `ScriptCommand`s; the
exporter landed 2026-07-19 (`ba9ff7c6c`), before that. From `81361cdd1` onward
the binary *required* `(set-logic QF_BV)` ten lines above and then refused the
script for containing a `set-logic` command — no input could pass.

Replaced the two-variant allowlist with an **exhaustive match carrying no
wildcard arm**, so the next `ScriptCommand` variant is a compile error here
rather than a silent refusal, and the refusal now names the offending command
instead of listing four it might have been.

Also fixed the three pre-existing `clippy -D warnings` errors in
`reconstruct/arithmetic/axreal_call_site_guard.rs` (two `usize as i64` casts, one
missing backtick) — same scope, and they blocked the gate.
