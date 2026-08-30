# Notes: s6-wire-real-ledger

Detail moved out of [`../status/s6-wire-real-ledger.md`](../status/s6-wire-real-ledger.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Crash sweep**: one full transaction over the real write set performs **23**
low-level write ops (fixture was 26 -- no separate `graph.json` write here,
since "graph" is a read-only fingerprint of the settled-id-set + pins bytes,
not a write target). Re-running with a fault injected at each of the 23 and
calling `recover()` converges to byte-identical OLD or NEW state at every
single one.

**Four staleness dimensions, mapped honestly onto the real ledger** (there is
no single `graph.json` or receipt schema for the real ledger, so these are
new choices, not a literal port): receipt = a pointer file in a new
`artifacts/.credit-txn/` namespace; source = the fact's own JSON bytes; graph
= hash of (sorted settled fact-id set + current pins.json bytes); checker =
hash of the actual bytes of the four source files this wrapper depends on
(no hand-maintained version string to forget to bump). All four reject with
their own exception class; a fresh-pass control commits without rejecting.

**Idempotent replay, and a corrected assumption caught by the gate's own
first run**: `run_ledger_transaction` short-circuits a replayed
`(fact_id, receipt)` before recomputing the cascade, confirmed. But unlike the
fixture's append-only `dashboards/settled.md`, both real rebuilt targets
(pins.json, safety-matrix) are FULL REBUILDS KEYED BY fact_id, so calling
`propose/commit/apply` directly twice WITHOUT the guard does NOT corrupt
content -- measured, not assumed (an earlier draft of this test asserted the
opposite and was wrong; see ADR-0810). The guard's real, measured value here
is skipping a whole wasted transaction on replay, not preventing corruption.

**Mutation table**: 9 guards this wrapper owns (four staleness checks against
the real dimensions, two transaction-state preconditions, corrupt-staging
call site, content-rejection via `validate_one`, idempotent-replay
short-circuit), each deleted in a scratch copy
(`scripts/tests/test-credit-transaction-ledger-mutations.sh`, never the
shared checkout), each killing EXACTLY its own canary. All 9 pass. Two
further defensive checks (the pins `rewrite()` refusal, the safety-matrix
`run_controls()` failure) are named as intentionally excluded from this
table -- they guard third-party logic this wrapper reuses rather than
reimplements.

22 tests in `scripts/tests/test-credit-transaction-ledger.py`, all green.
Registered in both `justfile` and `scripts/check.sh` as
`credit-transaction-ledger`, `credit-transaction-ledger-tests`,
`credit-transaction-ledger-mutations`.

**Confirmed unaffected, before vs. after (byte-identical output)**:
- `scripts/validate-facts.py`: 2273 facts checked, 0 errors, identical.
- `scripts/check-settled-fact-statements.py`: 2123 settled, 2123 pinned, 0
  drifted, identical.
- `scripts/check-autogenesis-holdout-isolation.py`: 116 held-out, 0
  references, identical -- no held-out row was ever touched.
- `scripts/gen-adr-index.py --check`: passes after regenerating for
  ADR-0810 (duplicate_numbers unchanged at the grandfathered 0166,0167).

No real fact's status was flipped as a side effect of any test; every test
runs against a `shutil.copytree` scratch copy the gate builds itself, using
`F:ml430-mutation-c86940b52af8159ca9b381d6` (an outcome-blind mutation fact
with no expected truth value) as the fixture target.

**One honest sentence on what a real flip still does non-atomically**: a
fact flip through this transaction leaves `artifacts/ledger-coverage.json`
and the product-health snapshot exactly as stale as they already were --
"the ledger" as a whole is not one atomic unit, only the three targets this
transaction covers are.
