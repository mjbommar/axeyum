# ADR-0514: The pinned Lean toolchain is the one that runs, and every run names it

Status: accepted
Index-summary: One resolution policy for the external `lean` binary, shared by `scripts/check-lean-gate.sh` and `lean_probe.rs`: `lean-toolchain`'s pin is what runs, a non-pinned toolchain is a named refusal rather than a silent substitution, and every suite prints the binary and version that produced its verdicts
Index-status: accepted

Date: 2026-08-17

Related: [ADR-0458](adr-0458-lean-modules-declare-whether-they-contain-reasoning.md),
[ADR-0465](adr-0465-the-axiom-ledger-is-derived-not-transcribed.md).

## Context

Real-Lean cross-checks are the only evidence in this repository that something
outside it has read our exported bytes. Which `lean` produced that evidence was,
until today, an unstated fact about the machine.

Two implementations of toolchain discovery existed and disagreed:

- `scripts/check-lean-gate.sh` tried `command -v lean` first, so on a host with
  elan's shim directory on `PATH` it found elan's **default** toolchain;
- `crates/axeyum-lean-kernel/tests/support/lean_probe.rs` skipped `PATH` when
  nothing was there and took elan's toolchain directories **sorted
  newest-name-first**.

Measured on the development host on 2026-08-17 with `v4.30.0` (the pin) and
`v4.34.0-rc1` both installed, those two rules select **different binaries**, and
the difference is not cosmetic:

- under 4.34, 21 of 77 `lean_crosscheck` families were rejected while all 77
  passed under 4.30 (module headers; fixed in `b760fd6ae`);
- `scripts/lean/replay-lean4export.lean` did not even elaborate under 4.34, so
  `real_lean_kernel_replay` failed on committed content for a reason unrelated
  to what it tests;
- nothing in either tool's output named the Lean that produced its verdict.

A gate whose answer depends on an unstated environment fact is this
repository's signature defect, and the two-implementation split is the
mechanism that let it exist unnoticed.

## Decision

**The pin runs, one policy implements it, and every run states which binary and
version produced its verdicts.**

The pin is the `lean-toolchain` file at the repository root — the same file
`elan` and `lake` read, so there is no second place to keep in sync. Resolution,
implemented once in `lean_probe.rs` and mirrored step for step in
`check-lean-gate.sh`:

1. `AXEYUM_LEAN_BIN`, authoritative in **both** directions — set and
   unresolvable means resolution stops, never falls through to a search.
2. The pinned toolchain's own elan directory
   (`$ELAN_HOME/toolchains/leanprover--lean4---v4.30.0/bin/lean`).
3. `PATH`'s `lean`, **only if `--version` matches the pin**.
4. Any other installed elan toolchain, sorted, **only if `--version` matches**.
5. elan's shim, **only if `--version` matches**.

There is no "newest wins" step and no unversioned fallback. A host with only a
non-pinned Lean resolves nothing and says so. Under `AXEYUM_REQUIRE_LEAN=1`, a
resolved toolchain that is not the pin is a hard failure naming both versions,
unless `AXEYUM_LEAN_ALLOW_UNPINNED=1` states the deviation — which is then
printed on every banner as `matches_pin=false`.

Stating it is half the decision. Every suite prints
`AXEYUM-LEAN-TOOLCHAIN <tag> bin=… version=… source=… pinned=… matches_pin=…`,
and `check-lean-gate.sh` **fails** if any suite reports a binary other than the
one the gate resolved, or reports none at all. A result that does not name its
checker is not evidence.

## Evidence

`scripts/tests/test-lean-toolchain-policy.sh`, exercised on this host against
Lean **4.30.0** (`d024af099ca4bf2c86f649261ebf59565dc8c622`) and **4.34.0-rc1**
(`3447a668783dbce1a8fdb97101dd067687b2b418`), both installed:

| control | claim |
|---|---|
| 1 | the shell gate resolves the pinned 4.30.0 |
| 2 | the Rust probe resolves the **same binary** — the control that would have caught the original defect |
| 3 | an unresolvable `AXEYUM_LEAN_BIN` fails by name and does not search on |
| 4 | no toolchain + `AXEYUM_ALLOW_NO_LEAN=1` is a loud skip naming the zero |
| 5a | the shell gate refuses a non-pinned toolchain, naming both versions |
| 5b | the Rust probe refuses it too, so a suite run without the gate cannot silently check a different claim |
| 5c | with the deviation stated the same suite **passes**, so 5b's failure is the guard firing and not "4.34 is broken here" |

The controls are not decorative. Three separate one-guard deletions each killed
**exactly one** of them and left the rest green:

| guard deleted | control that died |
|---|---|
| the version filter in `lean_probe`'s candidate loop (restoring "newest wins") | 2 |
| `lean_bin_or_skip`'s `matches_pin` assertion | 5b |
| `check-lean-gate.sh`'s mismatch `exit 1` | 5a |

The per-suite cross-check was exercised the same way: spoofing the gate's
resolved path made it name the disagreeing suite, and suppressing the banner
made it fail with `unnamed-toolchain`.

Control 5 refuses to pass vacuously — with no second toolchain installed it
reports that it could not ask the question and **fails**, rather than reporting
green over an unexercised guard.

Full gate after the change: 17 suites, 57 tests, **223 real-Lean checks** (floor
208), 37 theory families (floor 37), every suite confirming the same binary.

## Alternatives

**"Always newest."** Rejected, and it would break suites by design.
`real_lean_strict_positivity_crosscheck` asserts the exact commit
`d024af099ca4bf2c86f649261ebf59565dc8c622` for frozen-source reproduction, and
`real_lean_wire_differential` is a differential against the reference
implementation — which means nothing when run against "whatever was installed".
Newest-wins also makes the checked claim change when someone installs a release
candidate for an unrelated reason, which is precisely the failure being closed.

**Leave the two implementations and document the order.** Rejected: the two
already carried comments claiming they mirrored each other, and both comments
were true when written and false today. The cross-check replaces the comment
with a measurement.

**Keep `PATH` first.** Rejected: `PATH` is host state. It is retained only as a
version-checked candidate, so a non-elan install of the pinned version still
works.

## Consequences

- Moving to a newer Lean is one explicit act: edit `lean-toolchain`, and both
  entry points follow in the same commit. Any suite asserting a frozen commit
  must be updated in that commit, which is now a visible cost rather than a
  silent regression.
- A host with only a non-pinned toolchain fails loudly instead of quietly
  checking something else. `scripts/provision-fleet-host.sh` already installs
  the pin.
- `scripts/lean/replay-lean4export.lean` now elaborates under both 4.30 and
  4.34: `Environment.addDeclCore` gained a `maxRecDepth : USize` parameter in
  4.34, and the call is resolved at elaboration time by
  `first | exact … | exact …`, which fails loudly if neither arity type-checks.
  That shim is deliberately the only version-conditional construct in the file,
  so any other future incompatibility breaks visibly rather than being absorbed.
- `real_lean_wire_differential`'s own `pinned_lean()` is now a redundant
  assertion of this policy rather than a competing one. It can be collapsed onto
  `lean_probe::lean_bin()` whenever that file is next touched; it is left in
  place because a second, independent check of the pin costs nothing.
