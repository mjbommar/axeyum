# ADR-0554: A multi-target Autogenesis operation's authoritative receipt binds exactly one target, and it is verifiable

Status: accepted
Date: 2026-08-25
Index-summary: `execute-autogenesis-operation.py` gains a driver case for `axeyum-lean-import/modeq-family-multi-target-v1`. The receipt is per-fact, not per-operation: it resolves the ONE `targets[]` row naming the frontier-selected fact, binds `target_definition` plus that target's adapter/candidate manifest hashes into `identity`, and reuses the operation's own reviewed checker module (`check_target`) as the sole fresh re-derivation. Cross-target replay is refused because `identity.fact_id` is content-addressed together with everything else, and `prepare-autogenesis-fact-transaction.py` already refuses a receipt whose `identity.fact_id` disagrees with the fact being admitted. Implemented; `--verify` demonstrated failing on three distinct corrupted-receipt shapes.
Index-status: accepted

## Context

ADR-0470 fixed the boundary between machine selection and typed transaction
preparation: every authoritative operation carries a validated executor
contract, and execution emits a content-addressed receipt binding the clean
Git commit, exact frontier, registry, fact, operation, input bytes, fixed
budget, and normalized independently-checked result. Its Alternatives section
explicitly scoped this to one input artifact binding to exactly one fact, and
named the condition under which that could be lifted: *"Parameterized
multi-fact operations can be introduced only with a typed statement-to-input
derivation."*

That condition has since been met, without a follow-up ADR. Two operations
now name more than one fact in `applicability.fact_ids`:
`authoritative-mathlib-bounded-induction-factorial-family-v1` and
`authoritative-mathlib-modeq-family-v1` (originally two operations —
`authoritative-mathlib-modeq-family-v1` for four `Int.ModEq` facts and
`authoritative-mathlib-nat-modeq-family-v1` for three `Nat.ModEq` facts —
merged 2026-08-25 so `check-development-partition.py` sees a `train` fact
alongside the `development` facts it generalizes from). `fact-frontier.py`
already resolves a frontier with several simultaneously-admissible siblings to
exactly one `selected_fact_id` (`selected_inputs()` in
`execute-autogenesis-operation.py` was relaxed the same day to require
`selected in admissible`, not `len(admissible) == 1` — see the comment at
`selected_inputs`). `resolve_multi_target()` and `dry_run_multi_target()`
already exist and can independently re-derive the ONE target a selected fact
names, reusing each operation's own reviewed checker module
(`check-autogenesis-modeq-family.py` / `check-autogenesis-nat-modeq-family.py`)
rather than re-implementing the replay. What was missing, by the dry-run
docstring's own admission, is the piece that turns that into an authoritative,
content-addressed, `--verify`-able receipt: `run_registered()` and
`build_receipt()` had no case for driver
`axeyum-lean-import/modeq-family-multi-target-v1`.

Verified today before writing anything:

```
python3 scripts/fact-frontier.py --json          # selected_fact_id =
                                                  #   F:ml430-nat-modeq-symm-0a3d4d18
python3 scripts/execute-autogenesis-operation.py --frontier <that> \
    --dry-run-multi-target
AUTOGENESIS_OPERATION_EXECUTION_DRY_RUN|would_admit=F:ml430-nat-modeq-symm-0a3d4d18
  |operation=authoritative-mathlib-modeq-family-v1|target=...natModEqSymm
  |goal_sha256=...|proof_sha256=...|other_target_fact_ids=<six more>
```

## Decision

**A multi-target operation's authoritative receipt still binds to exactly one
fact — the "multi-target" property is a dispatch-time fact of the OPERATION
(it may be selected against any of several facts), never an execution-time
fact of a RECEIPT (one execution always resolves, re-derives, and binds
exactly one target).** `run_registered()` gains a driver case that:

1. Resolves the target via the existing `resolve_multi_target(operation,
   fact["id"])`, which already raises unless exactly one row in
   `executor["targets"]` names the selected fact.
2. Performs the ONE fresh, independent re-derivation by calling the
   operation's own reviewed checker module's `check_target(target,
   max_binders)` — reused via the existing `MODEQ_FAMILY_CHECKERS` lookup,
   never re-implemented. This is the only place a subprocess runs; it
   replays the target through the real kernel checker binary
   (`modeq_family_operation`) against the target's hash- and
   permission-pinned external Mathlib export and raises
   `family_module.FamilyError` on any disagreement with the committed
   candidate manifest.
3. Returns an observation built from the committed candidate manifest
   (`expected_modeq_family_target_observation`), the same pattern
   `statement-reflexivity-v1` already uses: the subprocess-driven check and
   the receipt's recorded observation are two independent constructions of
   the same content-addressed values, so an implementation bug that skipped
   the subprocess would still have to fabricate a value matching the
   committed manifest to pass `build_receipt`'s own independent
   recomputation.

`build_receipt()` gains a matching case. Its `input_identity` records:

- `formal_statement_sha256` — the fact's own statement text, as every driver
  already does;
- `target_definition` — the fully-qualified Lean declaration this specific
  execution proves;
- `statement_adapter_manifest_sha256` and `modeq_manifest_sha256` — digests of
  the two manifests that chain the fact to its adapter to its candidate;
- `external_artifact_sha256` — the hash-pinned Mathlib export the adapter
  binds to.

`request_input` additionally carries `target_fact_id` (equal to
`identity.fact_id`) purely for human legibility: `request.input_fact_id` is
inherited, unmodified, from the generic receipt shape and names the
operation's registered anchor fact (`F:ml430-int-modeq-refl-…` for this
operation), not necessarily the fact this receipt is for. A reviewer scanning
`request` without reading `identity` first should not be misled into thinking
`input_fact_id` says what was proved; `target_fact_id` says so explicitly.
This is redundant with `identity.fact_id` by design — no soundness property
rests on it, only clarity.

`derive()` now threads the frontier-selected fact through to the runner
(`runner(operation, fact=fact)`), because — unlike every existing
single-target driver — a multi-target driver's function cannot re-derive
`fact` from `executor["input_fact_id"]` alone (that field is the operation's
one registered anchor, and the operation now applies to seven). Existing
drivers accept and ignore the new keyword; none of them changes behavior.

### How does a receipt bind to one fact when the operation names seven?

By `resolve_multi_target`'s uniqueness requirement plus `identity.fact_id`.
`resolve_multi_target(operation, fact_id)` raises unless exactly one entry in
`executor["targets"]` names `fact_id`; `selected_inputs()` guarantees exactly
one fact was selected off the live frontier before that call ever happens.
The binding is *recorded*, not merely re-derivable: `identity.fact_id` and
`identity.target_definition` are both present in the receipt so a reader (or
`prepare-autogenesis-fact-transaction.py`, ADR-0468's territory) does not have
to re-run `resolve_multi_target` against the live registry just to know what a
receipt claims — though `--verify` does exactly that re-derivation anyway,
which is what makes the claim checkable rather than merely stated.

### What stops a receipt for one target being replayed as evidence for another?

Two independent things, one already existing and one this ADR adds:

1. **Existing, unmodified**: `prepare-autogenesis-fact-transaction.py` already
   refuses to build a ledger transaction when
   `execution["identity"]["fact_id"] != before_fact["id"]` (checked twice —
   once against the evidence identity, once against the transaction's own
   identity; see `build_transaction`). A receipt naming fact A cannot be
   admitted as evidence for fact B: the admission-writer checks the fact id
   before it will touch fact B's ledger entry at all, regardless of what a
   multi-target operation's receipt shape looks like.
2. **This ADR's contribution**: `receipt["execution_sha256"]` is a SHA-256
   digest over the entire receipt, `identity.fact_id` included. Changing
   `fact_id` — or `target_definition`, `goal_sha256`, `proof_sha256`, or any
   other field — without recomputing the digest is caught by
   `verify_receipt`'s own self-consistency check
   (`digest(unsigned) != claimed`). Recomputing the digest after such a
   change produces a *self-consistent but wrong* receipt; that is caught
   instead by `derive()`'s independent re-derivation of the SAME target from
   source (`actual != expected` in `verify_receipt`), because `--verify`
   never trusts the receipt under test for anything except its own digest —
   every value it compares against is re-read from the committed manifests
   and the live frontier/registry.

So the per-target `goal_sha256`/`proof_sha256`/`target_content_sha256` triple
is not what PREVENTS cross-target replay by itself (a forged, self-consistent
receipt for fact B built entirely from fact B's own real manifests would be a
VALID receipt for fact B, not a replay) — it is what makes replaying fact A's
receipt AS fact B's evidence a `fact_id` mismatch the admission-writer already
refuses, and content-addressing is what stops that receipt from being quietly
relabeled to claim fact_id B without invalidating its own digest. Verified
below by relabeling a valid receipt's `identity.fact_id` and re-signing it: it
is rejected as content-inconsistent with a fresh re-derivation, not accepted.

### Does ADR-0470's "typed statement-to-input derivation" condition hold now?

**Yes, and it was already built and reviewed before this ADR — this ADR
consumes it, it does not construct it.** Every row in
`executor["targets"]` is:

```json
{
  "fact_id": "F:ml430-nat-modeq-symm-0a3d4d18",
  "statement_adapter_manifest": "artifacts/autogenesis/mathlib-nat-modeq-family-symm-statement-adapter-v1.json",
  "modeq_manifest": "artifacts/autogenesis/mathlib-nat-modeq-family-symm-v1.json",
  "target_definition": "Axeyum.Autogenesis.Statement.NatModEqFamily.natModEqSymm"
}
```

and the chain from fact to input is typed and content-addressed at every
link: the adapter manifest's `source_fact_id` and `source_statement_sha256`
bind it to exactly one fact's exact `formal.statement` text; the candidate
manifest's `source_fact_id` and `statement_adapter` bind it to exactly one
adapter; `target_definition` is the one Lean declaration name that specific
adapter chain produces. `scripts/validate-autogenesis-operations.py`'s
`modeq-family-multi-target-v1` branch (added with the operation, not by this
ADR) already enforces every one of these bindings for EVERY target row on
every registry load — including `selected_inputs()`'s own load, so this
receipt shape never executes against a registry where that typed derivation
does not hold. This ADR's job was narrower and specific: turn "the typed
derivation exists and is validated" into "one execution of it produces a
checkable receipt," which is exactly the gap ADR-0470's Alternatives section
identified.

### What happens on partial success — six targets check, one does not?

**This question does not arise at the receipt granularity, by construction.**
Each authoritative execution binds to exactly one target (see above); there
is no notion of "partially admitting" several facts in one receipt, because
there is no receipt that ever claims more than one fact. It arises at two
OTHER granularities, both pre-existing and unmodified by this ADR:

- **Registry-load time** (`validate-autogenesis-operations.py`, part of
  `just check` / CI, runs on every commit): every target row's
  adapter/candidate manifest contract is validated against the live fact
  ledger, unconditionally, for the WHOLE `targets` list — not just the one a
  frontier happens to select. If one target's manifests stop agreeing with
  its fact (a ledger edit, a stale hash), the registry fails to load and
  `selected_inputs()` refuses for every fact under every operation, not just
  the affected one. This is fail-closed and already gates the family as a
  whole before any single member is ever dispatched.
- **Review-time re-derivation** (`check-autogenesis-modeq-family.py` /
  `check-autogenesis-nat-modeq-family.py`, named in
  `reviewed_gate_mentions`): each script re-runs the real kernel checker
  against ALL targets in its own reviewed subset (four Int facts, three Nat
  facts) and raises on the first disagreement, naming the specific failing
  `fact_id`. A regression in one target's checker replay fails the WHOLE
  script for that subset and blocks the operation from being trusted for any
  NEW dispatch in that subset — but it does not retroactively un-admit a
  fact that was already promoted on an earlier, passing run: that fact's
  ledger `evidence` row is pinned to the `goal_sha256`/`proof_sha256` values
  recorded at admission time, independent of what a sibling does later.

So: partial success across a family is a **registry/review-time** signal
(the checker gate goes red, naming which target broke, and blocks further
dispatch of that family until fixed), never a **per-receipt** state. No
receipt is ever built for six-of-seven; a receipt is built for one, or not at
all.

## Evidence

Implemented in `scripts/execute-autogenesis-operation.py`
(`modeq_family_checker_module`, `modeq_family_target_contract`,
`expected_modeq_family_target_observation`,
`run_modeq_family_multi_target_registered`, plus the new `build_receipt` and
`run_registered` branches and `derive()`'s `fact=fact` threading).

Against the live ledger and its current selection
(`F:ml430-nat-modeq-symm-0a3d4d18`):

```
$ python3 scripts/execute-autogenesis-operation.py --frontier <frontier.json> --output receipt.json
AUTOGENESIS_OPERATION_EXECUTION|a11ff214966a906eb0bb922d5309ebe4fcd19e3cf03fbe48c33c79f80b0a5257|fact=F:ml430-nat-modeq-symm-0a3d4d18|operation=authoritative-mathlib-modeq-family-v1|receipt.json

$ python3 scripts/execute-autogenesis-operation.py --frontier <frontier.json> --verify receipt.json
AUTOGENESIS_OPERATION_EXECUTION_OK|a11ff214966a906eb0bb922d5309ebe4fcd19e3cf03fbe48c33c79f80b0a5257
```

`--verify` demonstrated failing on three distinct corrupted-receipt shapes:

1. **Mutated field, stale digest** (edit `observation.proof_sha256`, leave
   `execution_sha256` unchanged):
   `AUTOGENESIS_OPERATION_EXECUTION_ERROR|execution receipt digest is missing or invalid`
2. **Forged but self-consistent** (edit `observation.proof_sha256`, then
   recompute `execution_sha256` over the mutated receipt — the same
   adversarial shape `check-autogenesis-nat-modeq-family.py` uses):
   `AUTOGENESIS_OPERATION_EXECUTION_ERROR|execution receipt is stale or mutated`
3. **Cross-target replay attempt** (relabel a valid `natModEqSymm` receipt's
   `identity.fact_id` to a sibling, `F:ml430-nat-modeq-trans-ef9d1c46`,
   recomputing both `identity.execution_id` and `execution_sha256` so the
   receipt is internally self-consistent):
   `AUTOGENESIS_OPERATION_EXECUTION_ERROR|execution receipt is stale or mutated`

Case 2 and 3 are the load-bearing ones: a self-consistent, correctly-signed
receipt is still rejected because `--verify` never trusts the receipt under
test for anything except its own digest — every compared value is
independently re-derived from the live frontier, registry, and committed
manifests.

Existing regression suite (`scripts/tests/test_execute_autogenesis_operation.py`,
13 tests): run both before and after this change (against `HEAD~1` and `HEAD`
of this same file, via a temporary swap in this worktree). Both runs produce
the identical result — 1 failure, 4 errors — confirming those are pre-existing
ledger/operation drift (a stale hardcoded operation id from before the
2026-08-25 modeq-operation merge, and admissibility drift from unrelated
facts elsewhere on the live ledger) unrelated to and unchanged by this ADR's
implementation. No test that passed before this change fails after it.

Required gates, run against this worktree's `HEAD`, shown verbatim in the
final report.

## Alternatives

### Give a multi-target receipt a list of observations, one per covered fact

Rejected. It would let one execution claim several facts at once, which is
exactly the "let the orchestrator construct a shell command" failure mode
ADR-0470 already rejected, moved into a list: nothing then forces the SAME
fresh, independent re-derivation for every list entry, and a single execution
touching several facts multiplies the blast radius of any one driver bug. One
receipt, one fact, keeps the ADR-0470 invariant that a receipt cannot itself
decide how many facts it proves.

### Add a `targets_sha256` (digest of the whole `executor["targets"]` list) to `identity`

Considered, not added. `identity.operation_registry_sha256` is already
`digest(registry)` — the ENTIRE `operations.json` content, which strictly
contains `executor["targets"]`. Any edit to any target row (including ones
unrelated to the one this receipt names) already changes
`operation_registry_sha256` and invalidates every receipt across every
operation, by design (ADR-0470). A separate `targets_sha256` would be
redundant with a field every driver already carries; it was left out to keep
the receipt to load-bearing fields only, per ADR-0470's own rejection of
storing non-load-bearing content.

### Extend `prepare-autogenesis-fact-transaction.py` in this same change

Rejected for this slice. That script's per-driver dispatch
(`build_transaction`) is where a receipt's observation becomes a ledger
evidence row, and it is ADR-0468's territory, not ADR-0470's. Adding a driver
case there is real, separate work (translating
`goal_sha256`/`proof_sha256`/`target_content_sha256`/`binders_used`/
`admitted_declarations`/`target_definition` into the evidence-row shape
`check-autogenesis-modeq-family.py`'s `check_registration_grants_dispatch_not_proof`
already expects) and this task's hard constraints forbid promoting any fact.
Flagged as the explicit next required piece in Consequences.

## Consequences

- `execute-autogenesis-operation.py --output`/`--verify` now works for
  `authoritative-mathlib-modeq-family-v1` against whichever of its seven
  facts the frontier currently selects; today that is
  `F:ml430-nat-modeq-symm-0a3d4d18`.
- The next required piece is a `axeyum-lean-import/modeq-family-multi-target-v1`
  case in `prepare-autogenesis-fact-transaction.py`'s `build_transaction` —
  without it, this receipt is real and independently checkable but cannot yet
  be turned into a ledger-write transaction. That is deliberately out of
  scope here (ADR-0468's territory; also forbidden by this task's hard
  constraints against promoting a fact).
- Future multi-target drivers (e.g. a bounded-induction family) get a
  concrete precedent to follow: resolve one target, reuse the family's own
  reviewed checker as the sole fresh re-derivation, bind
  `target_definition` plus its manifest hashes into `identity`, and add
  `target_fact_id` to `request_input` for legibility. They are not required
  to share `MODEQ_FAMILY_CHECKERS`'s exact shape, only the pattern.
- `MODEQ_FAMILY_CHECKERS` still keys on operation id, and the stale
  `authoritative-mathlib-nat-modeq-family-v1` entry (pre-dating the
  2026-08-25 merge) is unused now that both families are registered under
  `authoritative-mathlib-modeq-family-v1`. Left as-is: harmless, out of this
  ADR's scope, and removing it is a one-line follow-up for whoever next
  touches that dict.
