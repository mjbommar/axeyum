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

Detail moved to [`../notes/s6-wire-real-ledger.md`](../notes/s6-wire-real-ledger.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | s6-wire-real-ledger | `scripts/credit-transaction-ledger.py` wires ADR-0785's engine into the real write set (fact JSON, pins manifest, safety-matrix) by reusing `validate-facts.py`/`check-settled-fact-statements.py`/`gen-safety-matrix.py` unmodified; gate + 22-test suite + 9-guard mutation table; registered in justfile and check.sh; ADR-0810. |
