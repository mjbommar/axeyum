# Lane: s6-wire-real-ledger — wire `credit-transaction.py` into the real fact flip

<!-- plan-section: lane-status -->

**In progress, s6-wire-real-ledger, 2026-08-30.** Follow-on to
[ADR-0785](../../research/09-decisions/adr-0785-credit-transactions-two-phase-commit-with-a-crash-sweep-that-actually-crashes.md)
(`l0-s6-credit-transaction`), which built and verified the two-phase-commit
engine over a self-contained fixture ledger but deliberately did not wire it
into `artifacts/facts/`. This lane's job is that wiring.

Initial commit landed with the baseline measurements captured below and the
scratch-copy measurement harness in place; the transaction wrapper and crash
sweep against the REAL write set are being built next. This file will be
updated with the final measured write set, boundary count, and guard table
before the lane is done — see ADR-0810 for the full record once it lands.

**Baselines recorded before any change (this worktree, 2026-08-30):**

- `python3 scripts/validate-facts.py` — exit 0. `2273 facts checked, 0 errors
  (computed=2 conjectured=3 open=143 proved=2121 refuted=4)`.
- `python3 scripts/check-settled-fact-statements.py` — exit 0.
  `SETTLED_FACT_STATEMENTS|settled=2123|pinned=2123|unpinned=0|...|PASS`.
- `python3 scripts/check-autogenesis-holdout-isolation.py` — exit 0.
  `AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1110|settled=0|references=0|verdict=PASS`.

**Measured, not assumed, so far:** the real dashboard-generation scripts
split into two classes. `scripts/gen-safety-matrix.py` and
`scripts/gen-product-health.py` are pure-Python/fast (facts + a few
autogenesis artifacts + a `git merge-base` call), so they are safe to
regenerate synchronously inside a transaction. `scripts/gen-ledger-coverage.py`
invokes `cargo run --release -p axeyum-lean-kernel` — a multi-minute kernel
build/run — and CANNOT reasonably be part of a per-fact atomic file
transaction. This is being treated as a boundary the transaction does not
cover, named explicitly rather than silently excluded (see the final report
in ADR-0810 for the resolution).

<!-- plan-section: landed-changes -->

| 2026-08-30 | s6-wire-real-ledger | Started: baselines captured, scratch-copy measurement harness for the real write set. |
