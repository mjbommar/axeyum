# Notes: 138-flywheel-2-batch-dispatch

Detail moved out of [`../status/138-flywheel-2-batch-dispatch.md`](../status/138-flywheel-2-batch-dispatch.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Result: 26 declines, 0 proofs — a full-population result, not a partial
one.** All 11 int-modeq facts imported clean (0 axioms each) and the
producer (`propose_modeq_family`) declined every one with
`DeclineReason::TerminalNotClosed`, exactly turn one's mechanism
(unconditional identity, or a hypothesis whose sides don't syntactically
match the goal's after `whnf` — this schema has no congruence step). All 15
nat-coprime facts failed one stage EARLIER, at import, with
`StatementImportError::TrustedDeclaration` (`Nat.mod_lt` or `eq_self`,
Theorem-kind; `Quot`, Quotient-kind, for `coprime_of_lt_minFac`) — the
statement itself, before any proof is attempted, transitively reaches a
proof-bearing or foundational-primitive declaration the v1 statement-adapter
import policy refuses by design. This was NOT predicted in advance (this
task's own pre-run predictions, built from reading only the producer's
search algorithm, expected `TerminalNotClosed` for all 15) — the mismatch
between prediction and actual is this batch's main finding, and it locates a
real gap in `nat-coprime-family-v1`'s shape predicate one layer earlier than
the producer's own decline space. Full per-fact prediction/outcome table,
falsifiability check on `TrustedDeclaration` against the importer's own
source, and the six-item manual-judgment accounting (updated against turn
one's):
[`../../autogenesis/292-flywheel-2-batch-contract-dispatch.md`](../../autogenesis/292-flywheel-2-batch-contract-dispatch.md).

**After state:** `admissible_count: 0`, `declined_count: 27` (12
`producer-contract-int-modeq-family-v1`, 15
`producer-contract-nat-coprime-family-v1`), `selected_fact_id: null`,
`outcome: refused-no-admissible-candidate`. Every fact that matched either
seed contract now carries a live decline against that exact contract
version; nothing is currently dispatchable via either contract.

**Verified:** `python3 scripts/validate-facts.py` (776 facts, 0 errors,
unchanged distribution), `python3 scripts/validate-autogenesis-operations.py`
(27 operations, unchanged), `python3
scripts/validate-producer-contract-declines.py` (27 declines: turn one's
seed + this batch's 26), `python3
scripts/check-autogenesis-holdout-isolation.py` (`held_out=37|settled=0|
verdict=PASS`, unchanged) — all green, confirming no fabricated admission and
no held-out fact touched.

**Did not touch:** `scripts/fact-frontier.py`, `scripts/validate-producer-
contracts.py`, either producer contract instance, `artifacts/facts/` (0
facts proved this batch, so no evidence/status changed and no fact `notes`
edited), `artifacts/import-backlog.json`, `artifacts/autogenesis/
operations.json`, anything under `crates/axeyum-lean-kernel/src/` or
`crates/axeyum-cas/`, or `python/axeyum/agent/` — all out of scope per the
brief. Did not weaken `TrustedDeclaration`'s import guard or extend
`propose_modeq_family`'s search.
