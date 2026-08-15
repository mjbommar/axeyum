# Lane diary: `lean-gate-honesty`

**2026-08-14.** Seven suites hand generated modules to an external `lean` binary.
All seven printed `ok` on a machine where Lean 4.30.0 was installed. Nothing
outside this repository had ever read our exported bytes; when one finally did,
it rejected them (`a5975725f`). The rejection has been fixed. This lane fixes the
reason it was invisible for as long as it was.

## The measurement that starts it

```
$ ls ~/.elan/toolchains/
leanprover--lean4---v4.30.0
$ which lean
$ echo $?
1
```

`elan` installs toolchains under `~/.elan/toolchains/<name>/bin/lean` and puts
nothing on `PATH` unless its shim directory is sourced. Every suite's private
`lean_bin()` looked at `AXEYUM_LEAN_BIN` and `PATH` and stopped. Two of them also
tried `~/.elan/bin/lean` — elan's *shim* directory, which does not exist on this
box at all. So `which lean` printed nothing, a lane read that as "Lean is
absent", and ten test binaries skipped and passed.

This is the zero-coverage trap already recorded in CLAUDE.md's Gotchas, in its
sharpest form: the tool ran, exited 0, and answered a question nobody had asked.

## Baseline, recorded before touching anything

```
AXEYUM_LEAN_BIN=~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean \
AXEYUM_REQUIRE_LEAN=1 cargo test -q -p axeyum-solver --features full \
  --test int_inequality_lean_reconstruct
  -> 14 passed   (11 passed / 3 FAILED before a5975725f)
```

All seven suites green with the binary supplied by hand. The defect was never
that the checks fail; it was that nothing ran them.

## What changed

**One discovery implementation, not eight.**
`crates/axeyum-lean-kernel/tests/support/lean_probe.rs`, shared by `#[path]` into
both crates' test trees (both are `publish = false`). Order:
`AXEYUM_LEAN_BIN` → `PATH` → `$ELAN_HOME`/`~/.elan/toolchains/*/bin/lean`
(directory names sorted, newest first) → elan's shim.

One rule in there is load-bearing and easy to get backwards: **an explicit
`AXEYUM_LEAN_BIN` is authoritative in both directions.** If it is set and does
not resolve, discovery returns `None` rather than searching on. Without that,
`AXEYUM_LEAN_BIN=/nonexistent` — the negative control for this entire gate —
would quietly find the elan toolchain and the control would prove nothing. The
pre-existing copies fell through to `PATH`, which was harmless only because
`PATH` had no `lean`; adding elan discovery would have silently broken the
control.

**A skip stops reading as a pass.** `lean_bin_or_skip(tag, not_checked)` panics
under `AXEYUM_REQUIRE_LEAN=1` and otherwise prints

```
AXEYUM-LEAN-SKIPPED nat-literal not_checked=3 -- SKIPPED, this is NOT a pass. …
  Discovery: AXEYUM_LEAN_BIN=/nonexistent (NOT a file -- an explicit override is
  never overridden by search)
```

and every suite that *did* run prints `AXEYUM-LEAN-CHECKED <tag> checked=<n>`.
A skip now carries a magnitude and an explanation of where discovery looked. An
unattributable zero is the thing this file exists to prevent.

**The count is the gate's output.** `scripts/check-lean-gate.sh` discovers the
toolchain, sets `AXEYUM_REQUIRE_LEAN=1`, runs ten suites with `--nocapture`, and
sums the markers. It fails on: a suite failure, a suite that compiled to zero
tests, any `AXEYUM-LEAN-SKIPPED` line, a suite that ran tests but reported zero
Lean checks, and a total below a floor of 35 (measured 40). Absent toolchain is a
FAILURE by default; `AXEYUM_ALLOW_NO_LEAN=1` accepts it with a banner that says
in words that zero Lean checks ran.

Added to `scripts/check.sh` and the `justfile` `check` recipe at the same
position, immediately after `gate-liveness` — the two gates one level apart:
`gate-liveness` counts tests, this counts external kernel invocations.

## Controls

| control | result |
| --- | --- |
| toolchain present, **no env vars at all** | `10 suites, 33 tests, 40 real-Lean checks`, exit 0 |
| `AXEYUM_LEAN_BIN=/nonexistent` | gate exits 1, names the three places it searched; no bare `ok` |
| …plus `AXEYUM_ALLOW_NO_LEAN=1` | exit 0 with `SKIPPED -- 0 real-Lean checks ran. This is NOT a pass` |
| suite run directly, no toolchain, no require | prints `AXEYUM-LEAN-SKIPPED … not_checked=3` |
| `a5975725f`'s hunk reverted in `lean_pp.rs` | `11 passed / 3 FAILED`, gate exits 1 |

The last one is the one that matters: with the export fix reverted the gate
reproduces the pre-fix signature exactly, **with no environment variables set**.
The revert was applied in place, measured, and restored byte-identically
(md5 `7f78ceec…` before and after) — a full scratch copy of a 1.4 GB tree with a
cold `target/` was not affordable on a box `systemd-oomd` had already killed once
today.

Note the second line of that failing run:

```
check-lean-gate: int_inequality_lean_reconstruct  14 test(s),  0 real-Lean check(s)
```

The suite-failure check and the zero-checks check fire independently. Either
alone would have caught it; the point of having both is that the second one also
catches a suite that stops *invoking* Lean while still passing.

## What running these for the first time found

`lean_crosscheck` (70 proof families, one representative module each) is **not**
in the gate, and the reason is a real defect rather than cost. Its first run
against a real Lean rejects one of the 70:

```
lean REJECTED the quant_bv_source_instance_set module
  error: Application type mismatch: The argument axeyum_proof_share_33
  has type Prop of sort `Type` but is expected to have type
  ∀ (x2 : axeyum_proof_share_69), ?m.5 ⋯ of sort `Prop`
  error(lean.unknownIdentifier): Unknown identifier `axeyum_proof_share_160`
```

69 of 70 pass. The writer's proof-sharing pass is emitting shares that Lean reads
as `Prop`-valued *statements* where proof *terms* are required, and is naming
shares it never declares. That is an open writer defect in the
`quant_bv_source_instance_set` family, not a gate defect, and my diff does not
touch generation — the suite was skipping before, so this was latent, not caused.
It is named in `scripts/check-lean-gate.sh` as an explicit exclusion with the
command to reproduce it, so the omission is written down rather than silent. It
should be added to the gate as soon as the family is fixed; ~60 s is affordable.

## What is still open

- The `quant_bv_source_instance_set` rejection above.
- A skipped suite still prints cargo's own `test result: ok` line. Short of
  `#[ignore]`, which would hide the check from `--list`-based liveness ratchets
  too, that line is not ours to change; the marker line next to it, and the gate
  that greps for it, are the answer.
- Ten suites is what exists today. Any new suite that shells out to `lean` must
  be added to the manifest in `scripts/check-lean-gate.sh`; nothing enforces
  that yet, which is the same class of hole one level up.
