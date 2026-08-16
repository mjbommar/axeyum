# Lane: ledger-integrity — a checker that cannot fail is not a checker

<!-- plan-section: lane-status -->

**Claim-dashboard gate, finding-8 re-measurement, and PLAN.md returned under its
ceiling** (`WIP`, ledger-integrity, 2026-08-16). Three defects behind a dashboard
reporting 38 claims against an actual 104; finding 8 re-measured as remediated
(177/177 checker runs can fail) after a regex audit of my own produced 19 false
positives; and `plan-authority` taken from 233,888 bytes to 46,820 by archiving
finished lanes to [`docs/plan/archive/`](../archive/README.md). Full record:
[`diary-ledger-integrity.md`](../../refactor-2026-08/diary-ledger-integrity.md).

**Next.** Discharge `Int.euclidean_decomposition`, the last `int_prelude` axiom.
Measured: the ofNat transfer lemmas are definitional, so only the `negSucc`
branch and Int-typed `Exists` helpers remain. Then bind its checker to the
theorem rather than to a gate-wide run.

<!-- plan-section: landed-changes -->

| 2026-08-16 | `pending` | Claim dashboard regenerated and gated: `gen-claims-dashboard.py --check` added and wired into `generated-trackers` (justfile) and `check.sh`; `validate-claims.py` now type-checks `frontier.known` / `would_settle` / `attack_notes` against `claim.schema.json`; the one schema-violating claim normalised. DASHBOARD.md goes from a stale 38 claims / 1 family / 81 rows to the actual 104 / 3 / 266. Both negative controls exercised. |
