# Lane: s6-wire-real-ledger — wire `credit-transaction.py` into the real fact flip

<!-- plan-section: lane-status -->

**Done, s6-wire-real-ledger, 2026-08-30.** [ADR-0810](../../research/09-decisions/adr-0810-wire-the-credit-transaction-into-the-real-fact-ledger.md)
records the full measurement. Follow-on to
[ADR-0785](../../research/09-decisions/adr-0785-credit-transactions-two-phase-commit-with-a-crash-sweep-that-actually-crashes.md)
(`l0-s6-credit-transaction`), which built and verified the two-phase-commit
engine over a self-contained fixture ledger but deliberately did not wire it
into `artifacts/facts/`. Summary:

**The measured real write set differs from what ADR-0785's follow-on note
assumed.** That note named three targets ("the fact JSON, the settled pins
file, and the generated dashboards"). Instrumenting an actual flip found "the
generated dashboards" is not one thing: `gen-safety-matrix.py` and
`gen-product-health.py` are pure-Python/fast, but `gen-ledger-coverage.py`
invokes `cargo run --release -p axeyum-lean-kernel` (a multi-minute kernel
build/run, not a per-fact write), and `gen-product-health.py` -- despite being
fast -- reads unrelated global state (latest CI runtime receipt, autogenesis
operation/outcome artifacts, `justfile`/`check.sh` content) that has nothing
to do with any one fact. So the transaction covers three targets, all full
rebuilds:

1. `artifacts/facts/<id>.json`
2. `artifacts/ontology/settled-fact-statement-pins.json` (via
   `check-settled-fact-statements.py`'s own `rewrite()`, reused unmodified)
3. `artifacts/safety-matrix/safety-matrix.tsv` +
   `artifacts/safety-matrix/safety-matrix-summary.md` (via
   `gen-safety-matrix.py`'s own `classify`/`render_tsv`/`render_summary`/
   `run_controls`, reused unmodified)

`artifacts/ledger-coverage.json` and `artifacts/product-health-v1.json` /
`docs/plan/generated/product-health.md` are NOT covered, named explicitly.

**`scripts/validate-facts.py` has a ZERO-line diff from this lane.** The
wiring reuses its `validate_one(path, fact, known_ids)` directly via
`importlib`, gating every proposed fact before a transaction is proposed, and
never needed to touch the file the task said I "may edit."

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

<!-- plan-section: landed-changes -->

| 2026-08-30 | s6-wire-real-ledger | `scripts/credit-transaction-ledger.py` wires ADR-0785's engine into the real write set (fact JSON, pins manifest, safety-matrix) by reusing `validate-facts.py`/`check-settled-fact-statements.py`/`gen-safety-matrix.py` unmodified; gate + 22-test suite + 9-guard mutation table; registered in justfile and check.sh; ADR-0810. |
