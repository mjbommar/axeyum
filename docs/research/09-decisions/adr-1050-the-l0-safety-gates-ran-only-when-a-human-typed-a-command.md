# ADR-1050: the seven L0 safety gates ran only when a human typed a command; wire them by measured cost, not by kind

Status: accepted
Date: 2026-08-31
Index-summary: All seven L0 trusted-library safety gates were referenced ZERO
times in `.github/workflows/ci.yml`, `hooks/pre-push` **and**
`scripts/local-ci.sh` — the file `ci.yml` itself calls "the authoritative gate
for main" — so seven phases of safety work ran only when a human typed
`just check`. This ADR wires all seven, splitting them by MEASURED seconds
rather than by whether they shell out to cargo (two "pure Python" gates cost
58s and 55–72s, which refutes the obvious split), keeps the ~545s push
battery from growing by more than ~1.2s, places the pre-push block ABOVE the
Rust-only early exit because every L0 gate guards non-Rust content, and adds
`scripts/check-l0-gate-enforcement.py` so the wiring cannot silently regress.

## Context

The L0 programme is seven independent gates over the trusted library: trust
closure, settled-fact statement identity, semantic control fixtures, the
kernel differential against pinned Lean, the credit transaction ledger,
proposition duplication, and held-out closed evaluation. Each is careful work
— several are mutation-verified, and `check-kernel-differential.py`
deliberately re-derives its verdict from the test's output text rather than
trusting the harness exit status.

None of them ran automatically.

Measured 2026-08-31 in this worktree, with positive controls in the same run
so a zero could not be a broken query:

| file | L0 gates named | control (`scripts/` refs) |
| --- | --- | --- |
| `.github/workflows/ci.yml` | **0** | 44 |
| `hooks/pre-push` | **0** | 28 |
| `scripts/local-ci.sh` | **0** | 10 |

The third row is the one that was not in the brief and matters most.
`ci.yml`'s own comment says the heavy gate "lives in `scripts/local-ci.sh`,
run on local hardware" and calls it "the authoritative gate for main". It does
not run these either. There were three automated contexts, not two, and the
gates ran in none of them.

This is the checker-that-cannot-fail defect moved one level up. The checkers
are excellent; nothing invoked them.

## Measurement

Every gate timed in the foreground, this host, uncontended. Warm figures are a
second run against a warm `target/`:

| gate | first run | warm | what it needs |
| --- | --- | --- | --- |
| `check-holdout-closed-evaluation` | 0.06s | — | pure Python |
| `check-settled-fact-statements` | 0.09s | — | pure Python |
| `check-semantic-control-fixtures` | 1.09s | — | pure Python |
| `check-credit-transaction-ledger` | 10.6s | — | pure Python |
| `check-kernel-differential` | 27s | 7s | `cargo test` **+ pinned Lean** |
| `check-proposition-duplication` | 54.7s | 72s | pure Python (load-sensitive) |
| `check-trust-closure` | 103s | 58s | `cargo run --release` |

**The obvious split does not survive contact with the numbers.** "Pure Python
is cheap, cargo is expensive" is wrong in both directions here:
`proposition-duplication` is pure Python and costs more than
`kernel-differential`, which builds and runs real Lean. The split has to be
made on measured seconds.

## Decision

### 1. `hooks/pre-push` runs only the three sub-two-second gates

`settled-fact-statements` (0.09s), `holdout-closed-evaluation` (0.06s),
`semantic-control-fixtures` (1.09s) — about **1.2s** added, against a battery
this repository documents at **~545s uncontended, with single steps reaching
2,699s under lane contention**.

The other four stay out. Together they are ~2.5 minutes, and a gate people
escape with `--no-verify` is worse than no gate.

### 2. That block runs ABOVE the Rust/TOML early exit

This is the substantive placement decision, not a tidiness one. The hook exits
at

```
exit 0 # docs/bench-results/scripts-only push — no cargo gate needed
```

when no `*.rs`, `*.toml` or `Cargo.lock` changed. Every L0 gate guards JSON and
documentation content: `artifacts/facts/`, the proposition corpus, the credit
ledger, the nursery partition. **A push touching only the content these gates
exist to protect takes that exit.** Below it, the wiring would be decorative on
exactly the changes that matter. The block therefore sits above it and runs
unconditionally, and `check-l0-gate-enforcement.py`'s G5 guard pins that.

### 3. CI placement follows the measurement, reusing existing jobs

- **`docs-links`** (existing, no cargo, already runs ~40 `python3 scripts/…`
  checks): the five pure-Python gates, ordered cheapest-first so a fast
  violation is reported without paying for the slow ones. ~85s, no build.
- **`lean-inductive-crosscheck`** (existing): `check-kernel-differential` and
  its mutants companion. It belongs here and nowhere else — the script sets
  `AXEYUM_REQUIRE_LEAN=1`, under which a missing toolchain is a hard failure
  rather than a skip, and this job already installs the pinned Lean 4.30.0
  through `scripts/install-pinned-lean.sh` and exports that same variable. In
  any job without Lean it would go red for the wrong reason.
- **`l0-trust-closure`** (NEW job): `check-trust-closure` alone, because it
  shells out to `cargo run --release -p axeyum-lean-kernel --example
  kernel_declaration_projection` and **no existing CI job does a release build
  at all** (measured: zero `--release` occurrences in `ci.yml` before this).
  `--release` is mandatory for that example — in debug it SIGABRTs on stack
  depth, which reads as a broken tool rather than a resource limit. A separate
  job runs in parallel, so it extends the critical path only if it becomes the
  slowest job.

The `kernel_differential` test target ran in no automated context before this:
0 references in all three files, against controls of 9, 14 and 3 `cargo test`
invocations in those same files.

### 4. No wired gate may have its failure swallowed

`ci.yml` legitimately carries `continue-on-error: true` on two lean-parity
steps, for a documented reason. So the property enforced is **per-step, not
per-file**: no L0 step carries it, and no L0 command is spelled `|| true`.

## Proof that each wired gate can fail

Wiring a gate whose failure is swallowed is worse than not wiring it. Each was
broken and restored in an isolated `/data0` snapshot — never in `artifacts/` of
the checkout:

| gate | mutation | clean | broken | restored |
| --- | --- | --- | --- | --- |
| settled-fact-statements | corrupt a settled fact's pinned statement | 0 | **1** | 0 |
| semantic-control-fixtures | pinned `counterexamples` 26 → 27 | 0 | **1** | 0 |
| holdout-closed-evaluation | plant `Nat.add 2 2 = 4` in a held-out row | 0 | **1** | 0 |
| trust-closure | truncate the projection (1,941 failures) | 0 | **1** | 0 |
| proposition-duplication | clone a settled fact → `SHARED-DECLARATION-PAIR` | 0 | **1** | 0 |
| credit-transaction-ledger | `--empty-fixtures` / `--empty-boundaries` | 0 | **1**/**1** | 0 |
| kernel-differential | `--self-test`: G1–G6 each fire on their own case | 0 | — | 0 |

**One honest negative.** Deleting `_verify_staged_integrity` from
`credit-transaction-ledger.py`'s `apply()` does **not** fail its gate: the
content-rejection property reaches `commit`, not `apply`. That is a surviving
mutant in a gate this lane was scoped not to modify, and it is recorded here
rather than fixed.

Two earlier mutation attempts on the same gate matched nothing and reported
`NO MUTATION APPLIED` — a reminder that a mutation which does not apply looks
exactly like a guard that is covered.

## The enforcement gate

`scripts/check-l0-gate-enforcement.py`, ~0.1s, six guards: G1 every gate in a
CI run-step; G2 no L0 step with `continue-on-error: true`; G3 no command
spelled `|| true`; G4 the three cheap gates in `hooks/pre-push`; G5 that block
above the early exit; G6 it has a failure branch. Plus a vacuity guard —
parsing zero CI steps is itself a failure, since G1–G3 would otherwise pass on
an empty file.

Registered in `scripts/tests/mutation_controls.py` as `l0-gate-enforcement`,
11 controls, each guard killed by the test that names it.

**Its own self-test found two defects in it before it was committed**, both of
the kind it exists to prevent:

- G4 matched gate names appearing in **comments**, so a gate deleted from the
  loop while still named in the block comment above read as wired. Comments are
  stripped now.
- G5 used first-occurrence, so a second invocation added *below* the early exit
  left the guard silent. Last-occurrence is the property actually wanted.

And registering it reproduced the same failure a third time: appended at EOF,
the `SUITES` entry landed **below** `if __name__ == "__main__":`, so it never
executed before `main()` read the registry. The file parsed, the tests passed,
and the suite was absent — visible only because `--help` listed 49 suites and
not mine. Beside the table is not in the table.

## Consequences

- A push costs **~1.2s** more; a docs-only push, which previously cost ~0,
  now costs ~1.2s and is gated for the first time.
- CI gains one job and ~85s of pure-Python steps inside an existing job. The
  new `l0-trust-closure` job pays a cached release build of one crate.
- `scripts/local-ci.sh` is deliberately NOT changed by this lane; it is out of
  the briefed scope, and it remains a gap — see below.

## What is still not wired

`scripts/local-ci.sh` runs none of the seven and this ADR does not change that.
CI and the pre-push hook now cover them, so the gap is no longer total, but the
file `ci.yml` calls authoritative for `main` still does not check L0 safety.

The gate most worth wiring that could not be wired here is
`check-kernel-differential` in **`hooks/pre-push`**. It is the only L0 gate
that compares this kernel against real Lean — the strongest soundness signal in
the set — and at 7s warm it is affordable. It cannot go there because
`AXEYUM_REQUIRE_LEAN=1` makes a missing toolchain a hard failure, and Lean is
present on one fleet host of five. Every lane on the other four would be unable
to push. It runs in CI instead, where the toolchain is installed and pinned.
