# Lane notes: expect-axioms — the ledger must see a trusted number move both ways

Detail for [`../status/101-expect-axioms.md`](../status/101-expect-axioms.md).

## What was already true (and what the brief got wrong)

The brief reported "58 facts use `--require-axiom-free` and NONE uses
`--expect-axioms`". Measured 2026-08-18 from the JSON, not from grep:

| quantity | brief | measured |
|---|---|---|
| fact files running `nat_axiom_inventory` in a `checker_command` | 58 | **28** |
| `--require-axiom-free` occurrences in those commands | 58 | **31** |
| `--expect-axioms` in those commands | 0 | **0** (correct) |

`grep -rl nat_axiom_inventory artifacts/facts/` returns 59 — 31 of those mention
it only in `notes` prose. One fact (`F-schedule-critical-chain-infeasible`) does
use `--expect-axioms 26`, but on `infeasibility_farkas_lean`, a different
example. The example's own module doc also said 58; corrected.

More importantly the *premise* was largely already satisfied.
`docs/plan/lean-axiom-ledger-v1.json` has pinned every default prelude's trusted
surface **by value** since ADR-0465, `--check` re-derives it, and a fall fails
that comparison exactly as a rise does. `string` 1 -> 0 and `integer` 1 -> 0 were
already absorbed there; only the example's doc comment was stale.

And converting the 28 facts would have changed no bit: `--require-axiom-free L`
literally pushes `(L, 0)` into the same expectation list `--expect-axioms L=0`
does. The only preludes any fact names are `nat` (23), `integer` (6), `logic`
(2) — all measuring 0, the floor. Nothing can fall below zero.

## The gap that was real

`creal` (ADR-0483) and `complex` (ADR-0479) were in **no** measurement the
ledger consumed: they need `--include-constructed`, added the same day, and the
ledger's coverage command did not pass it. Their counts could move either way
unobserved. `rat` was measured but absent from `EXPECTED_PRELUDES`, so the
explicit coverage guard did not cover it.

## Profile, because it decided the design

Measured on s4, `nat_axiom_inventory --include-constructed`: **2 m 03 s debug,
10.3 s release** (12x); without the flag 2.3 s / 0.23 s. Marginal rebuild after
touching `lib.rs`: 8.9 s release against 6.4 s debug. So the coverage command
moved to `--release`. Keeping the row source (`prelude_axiom_inventory`) on
debug makes the existing cross-check a cross-*profile* check as a side effect.

Two minutes was the reason not to put this in 28 `checker_command`s. Ten
seconds once, in a generator that already runs, is affordable.

## Guard mutation control

`python3 scripts/tests/mutation_controls.py lean-axiom-ledger` — 81 s, baseline
green, 11 mutations, **no survivors**. Ten killed exactly one test. Two
exceptions, both recorded rather than smoothed over:

- `fall reported as IMPROVEMENT` kills **2**: the nonzero fall (`real` 32 -> 30)
  and the fall to zero (`creal` 1 -> 0). One guard, two scenarios — the second
  pins the zero boundary that motivated the work. This is not the failure
  CLAUDE.md warns about (N guards all rejecting through one shared check); every
  guard here is individually load-bearing.
- `--include-constructed on the coverage command` kills `setUpClass`, i.e. all
  39 tests: it is upstream of the measurement, so it cannot be isolated. The
  guards that make dropping it *fail* rather than pass quietly are the three
  `EXPECTED_PRELUDES` entries, and those isolate cleanly.

## Near-miss caught while working

Mid-session the shared worktree measured `creal: axiom=30` and
`complex: axiom=30` — all 30 rows the `Real.*` axiomatized package, i.e. the
constructed carriers appearing to rest on the very axioms they exist to replace.
Clean `HEAD` (`659948a3e`, measured in a `lane-snapshot.sh` tree) gives 0/0, and
three runs an hour later gave 0/0 again with the same files still dirty. It was
transient WIP in another lane's uncommitted `PreludeKey::CReal` template cache
(`prelude_cache.rs`, ADR-0464) — a template restore wired to the wrong slot
would produce exactly that. Not mine to fix; the pin is taken from `HEAD`, and
the gate would have reported it as
`REGRESSION: creal trusted surface ROSE 0 -> 30`.
