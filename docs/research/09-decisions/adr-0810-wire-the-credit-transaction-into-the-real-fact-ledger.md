# ADR-0810: wire the credit-transaction engine into the real fact ledger

Status: accepted
Date: 2026-08-30
Index-summary: L0 S6 follow-on. `scripts/credit-transaction-ledger.py` wires
ADR-0785's two-phase-commit engine into the REAL write set, measured by
instrumenting an actual flip rather than assumed: `artifacts/facts/<id>.json`,
the settled-fact-statement pins manifest, and the safety-matrix TSV/MD, all
full rebuilds reusing `validate-facts.py`'s `validate_one`,
`check-settled-fact-statements.py`'s `rewrite()`, and `gen-safety-matrix.py`'s
`classify`/`render`/`run_controls` UNMODIFIED. Crash sweep over the real 23
write ops (all resolve to OLD or NEW), four staleness dimensions against real
paths, idempotent replay, content rejection. `scripts/validate-facts.py` has a
ZERO-line diff -- the wiring never needed to touch it.
Lane: `s6-wire-real-ledger`

Implements: [ADR-0717](adr-0717-library-construction-is-graph-directed-through-an-artifact-compatible-trust-anchor.md)
phase S6, follow-on to [ADR-0785](adr-0785-credit-transactions-two-phase-commit-with-a-crash-sweep-that-actually-crashes.md).

## Context

ADR-0785 built and mutation-verified a two-phase-commit engine
(`scripts/credit-transaction.py`) over a SELF-CONTAINED FIXTURE ledger
(`facts/`, `receipts/`, `pins/`, `graph/`, `dashboards/`), deliberately not
wired into `artifacts/facts/` because that touches `scripts/validate-facts.py`
and the real pins file, owned by other lanes at the time. Its own status file
named the gap explicitly: "wire this engine into the real fact-flip path...
that requires touching `scripts/validate-facts.py` and files this lane's
scope excluded."

This ADR is that wiring.

## What was measured, not assumed

**The real write set is not what the ADR-0785 follow-on note assumed.** That
note named three targets: "the fact JSON, the settled pins file, and the
generated dashboards." Instrumenting an actual flip end to end found:

1. `artifacts/facts/<id>.json` -- as assumed.
2. `artifacts/ontology/settled-fact-statement-pins.json` -- as assumed, and
   it is a FULL REBUILD keyed by fact_id (`check-settled-fact-statements.py`'s
   `rewrite()` reconstructs the whole `pins` array from current ledger state
   every time), not an incremental append. This matters for idempotence (see
   below).
3. "The generated dashboards" is not one thing. Reading the three scripts
   that regenerate ledger-derived documents found they split into two
   structurally different classes:
   - `scripts/gen-safety-matrix.py` and `scripts/gen-product-health.py` are
     pure-Python (no `cargo`), reading only facts + a handful of JSON
     artifacts, fast enough to run inside a transaction.
   - `scripts/gen-ledger-coverage.py` invokes `cargo run --release
     -p axeyum-lean-kernel` -- a multi-minute kernel build/run. This is a
     MEASUREMENT, not a write derivable from the fact content alone, and
     folding a cargo invocation into a per-fact file transaction would make
     every single fact flip pay a kernel rebuild.
   - `gen-product-health.py`, despite being fast, reads unrelated GLOBAL
     state that has nothing to do with any one fact: the latest CI runtime
     receipt, autogenesis operation/outcome artifacts, and the literal
     content of `justfile`/`scripts/check.sh`. Wiring it in would make a fact
     flip transaction fail for reasons that have nothing to do with the fact
     being flipped.

   So this transaction covers `gen-safety-matrix.py`'s two outputs
   (`artifacts/safety-matrix/safety-matrix.tsv`,
   `artifacts/safety-matrix/safety-matrix-summary.md`) and explicitly does
   NOT cover `gen-ledger-coverage.py`'s or `gen-product-health.py`'s outputs.
   Named here rather than silently excluded, per CLAUDE.md: "a boundary you
   skipped and did not name is the defect this whole phase exists to
   prevent."

**The idempotence guard's actual value differs from the fixture's.** The
fixture's `dashboards/settled.md` is append-only text
(`dash + f"- {fact_id}\n"`), so replaying without the higher-level guard
produces a REAL duplicate line -- that is what ADR-0785 demonstrated. The
real wiring's two rebuilt targets (pins.json, the safety-matrix files) are
both FULL REBUILDS KEYED BY fact_id, so calling `propose()`/`commit()`/
`apply()` directly twice, bypassing the guard entirely, does NOT corrupt
content -- confirmed by measurement
(`scripts/check-credit-transaction-ledger.py::run_guard_skips_recomputation_on_replay`):
the pin row count for the fact stays at 1 either way. The guard's measured,
honest value here is skipping a whole wasted transaction (cascade
recomputation, `validate_one`, `rewrite()`, `run_controls`, staging, commit,
apply) on replay, not preventing corruption. It stays in
`run_ledger_transaction` regardless, because a future append-style dashboard
(the real `gen-product-health.md`, if it is ever wired in, or any future
target) would not have this property.

## Decision

`scripts/credit-transaction-ledger.py` reuses `scripts/credit-transaction.py`
UNMODIFIED for everything generic -- the fault-injectable IO primitives
(`io_write_new_file`, `io_replace`), the `Journal`/`WriteOp`/`Inputs`
dataclasses, the applied-transaction registry, `_verify_staged_integrity`, and
the four staleness exception classes -- and reimplements only the
FIXTURE-SPECIFIC orchestration (`propose`/`commit`/`apply`/`recover`, which
hardcode fixture paths) against the real paths.

`scripts/validate-facts.py`, `scripts/check-settled-fact-statements.py`, and
`scripts/gen-safety-matrix.py` are loaded via `importlib` and their EXISTING
pure functions called directly:

- `validate_one(path, fact, known_ids)` gates the proposed fact content
  before a transaction is ever proposed.
- `check-settled-fact-statements.py`'s `read_pins()`/`rewrite()` compute the
  new pins bytes. `rewrite()` does its own I/O (reads and writes its module's
  `PINS` global directly), so it is called with `PINS` monkey-patched to a
  scratch file for the duration of the call -- the REAL function runs
  unmodified, nothing durable is touched, and the result bytes are harvested
  from the scratch file afterward. `rewrite()`'s own anti-laundering refusal
  (ADR-0763, unamended statement drift) is inherited for free: a nonzero
  return aborts the transaction proposal.
- `gen-safety-matrix.py`'s `build_fanout`/`classify`/`render_tsv`/
  `render_summary`/`run_controls` compute the new matrix bytes, including its
  own control suite (duplicate-id check, pin-set provenance controls,
  positive controls) -- inherited for free the same way.

None of these three files were edited. `scripts/validate-facts.py` has a
ZERO-line diff from this lane.

**Four staleness dimensions, mapped onto the real ledger** (no single
`graph.json` or receipt schema exists yet for the real ledger, so these are
new, honest choices rather than a literal port):

- **receipt**: `artifacts/.credit-txn/receipts/latest/<id>.sha256`, a pointer
  file in this wrapper's own new namespace (`artifacts/.credit-txn/`, chosen
  so it collides with nothing the rest of the repo reads), mirroring the
  fixture's receipt-pointer model exactly.
- **source**: the target fact's own on-disk JSON bytes, as in the fixture.
- **graph**: since the real ledger has no single dependency graph file, this
  hashes the combination of (a) the sorted set of currently-settled fact ids
  and (b) the current pins manifest bytes -- the two things that actually
  feed the cascade this transaction rebuilds. A concurrent lane settling
  ANOTHER fact, or a concurrent pins rewrite, invalidates an in-flight
  transaction exactly as a graph change would in the fixture.
- **checker**: rather than a hand-maintained version string someone has to
  remember to bump (the fixture's `CURRENT_CHECKER_VERSION` constant), this
  hashes the actual bytes of the four source files this wrapper depends on
  (`validate-facts.py`, `check-settled-fact-statements.py`,
  `gen-safety-matrix.py`, and the wrapper itself). A source edit to any of
  them between propose and commit is what "stale checker" means here, and it
  cannot silently drift out of sync with a version bump someone forgot.

**The "receipt" is the proposed fact's own canonical JSON bytes.** ADR-0717's
`theorem-credit` receipt schema (S0-S5) has not landed. Rather than invent a
placeholder schema, this wrapper treats the caller's decided fact content as
the receipt; when a real schema lands, only `receipt_bytes`'s definition
needs to change.

## What was measured, not asserted (the crash sweep)

One full `run_ledger_transaction()` call over the real write set performs
**23** low-level write ops (fewer than the fixture's 26, because there is no
separate `graph.json` write here -- the "graph" dimension is read-only
fingerprinting, not a write target). The sweep re-runs the transaction once
per op index with a fault injected at that exact op, confirms `SimulatedCrash`
fires, calls `recover()`, and diffs the resulting `artifacts/facts` +
`artifacts/ontology` + `artifacts/safety-matrix` subtree against BOTH the
pre-transaction and post-transaction snapshots. All 23 op indices resolve to
byte-identical OLD or NEW state; none resolve to neither.

**Nine guards, mutation-verified in a scratch copy** (never the shared
checkout): four staleness checks against the real dimensions, the two
transaction-state preconditions, the corrupt-staging call site, the
content-rejection guard around `validate_one`, and the idempotent-replay
short-circuit. Each deleted guard kills EXACTLY its own designated canary
from `scripts/tests/test-credit-transaction-ledger.py`. All nine pass
(`scripts/tests/test-credit-transaction-ledger-mutations.sh`).

Two further defensive checks exist (the pins `rewrite()` refusal path, the
safety-matrix `run_controls()` failure path) but are NOT in the mutation
table: they guard THIRD-PARTY logic this wrapper reuses rather than
reimplements, and constructing a fixture that trips those specific paths
(rather than `validate_one`, which a dangling `depends_on` triggers directly)
was judged out of scope for this lane. Named here rather than silently
omitted.

**The gate never touches the live ledger.** Every check in
`scripts/check-credit-transaction-ledger.py` builds its own scratch copy
(`shutil.copytree` of `scripts/`, `artifacts/facts/`, `artifacts/ontology/`,
`artifacts/safety-matrix/` into a `tempfile.mkdtemp()` directory) and runs the
transaction, sweep, or fixture against that copy only.

**Confirmed unaffected**: `scripts/validate-facts.py` and
`scripts/check-settled-fact-statements.py` produce byte-identical output on
the real ledger before and after this lane's changes (2273 facts, 0 errors;
2123 settled, 2123 pinned, 0 drifted). `scripts/check-autogenesis-holdout-isolation.py`
is unchanged (116 held-out, 0 references). No held-out row, and no real
fact's status, was touched by any test in this lane -- every test operates on
a scratch copy or the specific fixture `F:ml430-mutation-c86940b52af8159ca9b381d6`
(an outcome-blind mutation fact with no expected truth value, chosen for its
minimal size and because flipping it in a scratch copy carries no
mathematical claim).

## What this transaction still does NOT make atomic

Stated plainly, per the task's own standard: `artifacts/ledger-coverage.json`
(the `cargo`-derived kernel measurement) and `artifacts/product-health-v1.json`
/ `docs/plan/generated/product-health.md` (the whole-repo health snapshot,
dependent on CI/autogenesis state unrelated to any one fact) are regenerated
by their own scripts on their own cadence, outside this transaction. A fact
flip through `run_ledger_transaction` leaves those two artifacts exactly as
stale as they already were before this lane -- this is not a regression, but
it means "the ledger" as a whole is not one atomic unit; the three targets
this transaction DOES cover are.

## Alternatives

**Extend `scripts/credit-transaction.py`'s `propose_transaction`/`run_transaction`
to take real paths as parameters.** Rejected: those functions hardcode the
fixture's `targets` dict and `_fact_path`, and the task's instructions were
explicit that the fixture engine's tested behavior must not be disturbed.
Reimplementing the thin orchestration layer against real paths, while reusing
every generic primitive, is a smaller and safer diff than parameterizing the
existing tested functions.

**Reimplement pins/safety-matrix computation logic in the wrapper instead of
reusing `check-settled-fact-statements.py`/`gen-safety-matrix.py`.** Rejected:
duplicated logic drifts from the real gates it is supposed to match. The
monkey-patched-global technique (point the shared module's `PINS` constant at
a scratch file, call its real `rewrite()`, harvest the result) reuses the
exact production code path with no drift risk, at the cost of a small,
documented amount of indirection.

**Wire in `gen-product-health.py` and `gen-ledger-coverage.py` too, on the
theory that "the generated dashboards" means all of them.** Rejected after
measuring their actual inputs: one is a multi-minute cargo invocation, the
other depends on state that has nothing to do with the fact being flipped.
Both would make routine fact flips slow or spuriously fail. Named as
uncovered boundaries instead of forced in.

## Consequences

Flipping a real fact to `proved` (or `computed`) can now go through
`python3 scripts/credit-transaction-ledger.py run <fact_id> <new_fact.json>`,
committing the fact JSON, the pins manifest, and the safety-matrix files
atomically, with fresh-read staleness checking against a concurrent lane. The
mechanism, its crash sweep, staleness fixtures, and mutation table live under
this lane's paths (`scripts/credit-transaction-ledger.py`,
`scripts/check-credit-transaction-ledger.py`,
`scripts/tests/test-credit-transaction-ledger*`) and are registered in both
`justfile` and `scripts/check.sh`, alongside and independent of the
ADR-0785 fixture gate.

Wiring `gen-product-health.py` and `gen-ledger-coverage.py` into a broader
atomic unit, if ever wanted, is separate follow-on work against those
scripts' own maintainers, not implied by this ADR.
