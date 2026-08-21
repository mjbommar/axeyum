# Lane `agent-prepush-scope` — the kernel step of `hooks/pre-push`

Detail behind [`../status/100-prepush-scope.md`](../status/100-prepush-scope.md).

## The step, and what was wrong with it

`hooks/pre-push` ran the kernel package wholesale:

```sh
gated_test "kernel suites (unit + integration)" \
  cargo test -p axeyum-lean-kernel --quiet
```

It is there for a real reason and it is not being deleted: `cargo test
--workspace --lib` runs unit tests only and skips every `tests/*.rs`, which is
how `axeyum-lean-kernel --test axiom_footprint` sat RED on `main` for a day. That
crate is where the trusted surface is asserted, so a stale assertion there is a
stale claim about axiom-freedom.

What was wrong is duplication. Fifteen of the crate's 46 integration suites hand
generated modules to a real `lean` binary, and `scripts/check-lean-gate.sh`
already owns those — with a toolchain pin, a counted floor, a no-skip rule and a
cross-check that every suite named the same binary. This step had none of that
accounting and ran them a second time on every push, under a comment that said
"~1.4s warm".

## Measured

Warm, on s4, in a `scripts/lane-snapshot.sh` tree at `91b40c6ab` with its own
persistent `CARGO_TARGET_DIR` (build `--no-run` first: 12 s, so no step below
pays a compile).

| | seconds |
|---|---|
| BEFORE — `cargo test -p axeyum-lean-kernel` (the removed step) | **2,296** |
| AFTER — `scripts/check-kernel-suites.sh --no-lib` (the new step) | **80** |
| the same 31 suites plus the crate's `--lib` unit tests (default, no flag) | not finished before hand-off |

The 2,216 s difference is the fifteen real-Lean suites plus the crate's unit
tests, both of which another step already covers. A dedicated `--lib`-only run
to split those two apart was still going when this lane was asked to wrap up, so
that row is honestly blank rather than estimated.

The unit half matters more than expected: the crate has 375 lib tests and a
dozen of them (`complex::`, `creal::`, `creal_model::`, `prelude_cache::`) each
run past 60 s. `hooks/pre-push` runs `cargo test --workspace --lib` two steps
earlier and the kernel has no cargo features, so that step already selects
exactly these tests — the wholesale step was paying for them twice as well.
Hence `--no-lib`.

## The split is discovered, not listed

A hand-written list of 31 suite names is a list someone forgets to extend, and
the failure is silent: a new non-Lean suite simply never runs at push time.
`scripts/check-lean-golden-pins.sh` solved the same shape by discovering
membership from the act itself (`assert_golden_module`), and this follows it: a
suite is real-Lean exactly when it carries `#[path = "support/lean_probe.rs"]` —
the shared resolver that finds the pinned toolchain, prints the
`AXEYUM-LEAN-TOOLCHAIN` banner the real-Lean gate cross-checks, and turns a
missing binary into a failure under `AXEYUM_REQUIRE_LEAN=1`.

The deliverable is the assertion that the partition is TOTAL:

> every `crates/axeyum-lean-kernel/tests/*.rs` is in exactly one of
> { runs at push time } or { owned by `scripts/check-lean-gate.sh` }

Both directions are checked, because the failure modes differ: a real-Lean suite
missing from that gate's table (it would run nowhere), a table entry whose file
is gone, and a table entry that needs no Lean (it would run in both halves).

## What it found on its first run

`real_lean_string_monoid_crosscheck`, landed 2026-08-17, invokes a real `lean`
and was in **no** gate's table. Only the wholesale `cargo test` ever ran it — the
one runner that counts nothing, enforces no pin, and cannot tell a skip from a
pass. Removing the duplication without this gate would have turned it into a
suite nothing runs at all.

It had a second defect the first one hid. It printed

```
AXEYUM-LEAN-CHECKED|string-monoid|1|lean accepted, …
```

by hand, and `scripts/check-lean-gate.sh` parses exactly `AXEYUM-LEAN-CHECKED
<tag> checked=<n>`. Listing it without noticing would have failed that gate with
`0-lean-checks` — or worse, if the parse had been laxer, added a suite whose
Lean invocation never reached the floor. It now calls
`lean_probe::report_checked`, which emits the parsed shape and refuses a zero
count, and a tenth guard refuses any future hand-written marker line. Verified
against the pinned toolchain: 2 tests, `checked=1`, banner
`matches_pin=true`. `CHECK_FLOOR` 218 → 219.

## Diff-scoping, derived rather than judged

The step is now scoped to `crates/axeyum-lean-kernel/**` plus the two gate
scripts and the root manifests. Unlike the frontier ratchet's filter — a
judgement call about which crates can move a decision — this one is derived:
`crates/axeyum-lean-kernel/Cargo.toml` declares exactly one dependency,
`num-bigint`, and nothing from this workspace. No change under another crate can
move these suites.

The partition assertion (`--list`, no cargo) runs on **either** branch. That is
what makes the skip safe: it is the thing that would notice a real-Lean suite
dropping out of `check-lean-gate.sh`'s table on a push that did not touch the
kernel.

## Controls

`scripts/tests/test_check_kernel_suites.py`: 15 tests, each driving the shipped
script against a synthetic tree via `AXEYUM_KERNEL_SUITES_ROOT` and a stub
`AXEYUM_CARGO`. Registered with the mutation harness as
`kernel-suite-partition`; all **10 guards deleted, 10 killed exactly one control
each** (`python3 scripts/tests/mutation_controls.py kernel-suite-partition`).

Registering it needed one harness fix. `Unittest.build` ran `py_compile` over
every mutated subject, so a **shell** subject reported `SyntaxError` and all ten
mutations scored `DID NOT BUILD` — a whole suite unmeasurable for a reason that
has nothing to do with the mutation, in the harness whose entire point is
telling those apart. Shell subjects now parse with `bash -n`.
