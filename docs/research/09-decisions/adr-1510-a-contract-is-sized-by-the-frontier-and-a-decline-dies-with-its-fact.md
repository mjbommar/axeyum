# ADR-1510: a producer contract is sized by the frontier, and a decline dies with its fact

Date: 2026-09-01
Status: Accepted
Lane: `contract-declines`

Index-summary: The 27 producer-contract dispatches of 2026-08-27 all
declined, and the autogenesis loop has produced nothing since. The
investigation
([2026-09-01-why-every-contract-dispatch-declined.md](../11-design-review/2026-09-01-why-every-contract-dispatch-declined.md))
found neither a wrong shape nor one missing capability, but two independent
defects in how a contract and a decline relate to the fact ledger.
First: **26 of the 27 declined facts are now `proved`**, closed within days
by hand-authored kernel declarations
(`crates/axeyum-lean-kernel/src/int_prelude/modeq_family.rs`,
`nat_prelude/primes.rs`) that never invoked a producer, a contract, or the
import pipeline; both contracts' shapes now have **zero** remaining real
targets, and the whole contract layer matches **2 of 217** dependency-ready
open facts (`shape_matched_count`, `python3 scripts/fact-frontier.py --json`).
A contract was therefore written against a family that another route was
about to finish, and nothing measured that at the time it was written.
Second: `scripts/validate-producer-contract-declines.py` requires a decline's
`fact_id` to resolve to a real fact but not to an *open* one, so 26 of the 27
live `(fact, contract)` suppressions name settled facts and are
indistinguishable — to every checker and to the selector — from suppressions
of live work. That is exactly the "a decline becomes a cheap way to make the
selector shut up about a fact forever" failure mode the validator's own
docstring names, materialised in its benign direction and therefore
invisible. This ADR decides both: a contract must record the open population
its shape matched at authoring time and is retired when that population
empties, and a decline is a lifecycle object that must be resolved when its
fact settles. Follows ADR-0618's precedent (a census dies when its subject
closes) and ADR-0611's (an absence claim must expire).
Index-status: Accepted

## Context

ADR-0602 introduced the producer contract as the prospective half of the
autogenesis loop: the operation registry is a retrospective receipt system
that cannot express "we could attempt this open fact", so a contract carries
a capability claim — *facts matching this shape are dischargeable via route R
with recipe X* — and deliberately has no `proved` field anywhere in its
schema. Two seed contracts were written on 2026-08-27
(`nat-coprime-family-v1`, `int-modeq-family-v1`), 27 facts were dispatched
through them, and all 27 declined honestly with typed reasons. Doc 291 made a
decline into selector input: `scripts/fact-frontier.py` reads decline
artifacts and stops presenting a declined `(fact, contract)` pair as
admissible, scoped to the contract's exact `contract_sha256` so that changing
a contract re-opens every fact it previously declined.

That machinery all works. The measurement that prompted this ADR is what
happened *around* it.

1. Both contracts' families were finished by hand, fast. All 12
   `Int.ModEq` facts and 14 of 15 `Nat.Coprime` facts are now
   `epistemic_status: proved`, closed by kernel declarations written directly
   against `Kernel::add_declaration`. Doc 296 had already identified this as
   the dominant route in the project ("125 of 132 dependency-ready facts are
   exactly this `proof-route-only` shape") and extended the receipt system to
   describe it. Nothing extended the *contract* system to notice it.

2. The contract layer's reach is now 2 of 217 ready open facts, and the only
   three facts in the 209-fact `proof-route-only` pool that either contract's
   `statement_contains` clause matches are outcome-blind mutation negative
   controls, correctly excluded by `title_prefix`. Both contracts describe
   exhausted families.

3. `declined_by_contract` sums to 27 live suppressions while `declined_count`
   — declines suppressing a fact that is still ready and open — is 1. The
   ledger of declines is 96% stale, and no gate says so.

A contract that describes an exhausted family is not wrong, and a decline
against a since-proved fact is not a lie. They are both *expired*, and this
repository already has the pattern for that: ADR-0611 (an absence claim in
prose must expire), ADR-0612 (control registration is derived, not
remembered), ADR-0618 (graduation is lifecycle — a census dies when its
subject closes). The contract and decline artifacts were built without it.

## Decision

**1. A producer contract records the open population it was sized against,
and is retired when that population empties.**

A contract gains a required `sizing` block recording, at authoring time: the
number of dependency-ready open facts its shape matched, the ledger digest
that count was taken over, and the date. `scripts/validate-producer-contracts.py`
re-executes the shape predicate against the current ledger — it already does
this for non-examples and for the vacuous-matcher guard — and fails when a
contract's shape matches **zero** open facts, directing the author to retire
it (move to a `retired/` subdirectory, or supersede it with a `-v2` whose
shape covers live work).

The point is not bookkeeping. A capability claim over an empty population
cannot be falsified by any dispatch, which makes it the same class of object
as an operation registry entry with no proof behind it — the thing ADR-0602
exists to prevent one arrow upstream. A contract must be aimed at facts that
are still open at the moment it is written, and must stop asserting anything
once they are not.

**2. A decline is a lifecycle object: it must be resolved when its fact
settles.**

`scripts/validate-producer-contract-declines.py` gains a guard: if a
decline's `fact_id` names a fact whose `epistemic_status` is not in
`{open, conjectured, empirical}`, the decline must carry a `resolution`
block naming how the fact was actually closed — the route, the artifact, and
whether the decline's own diagnosis stayed accurate. Five of the 27 already
carry exactly this shape as an `amendment` block, written voluntarily by the
`int-modeq-kernel` lane; this promotes that convention to a requirement and
gives it a checker.

The guard fails, and is mutation-testable: delete the `resolution` from one
artifact and exactly one validation must die. Landing it requires adding a
`resolution` block to the 21 artifacts that lack one, which is mechanical —
the closing commits are known.

**3. Neither rule weakens any accept path.** Both are strictly additional
guards on artifacts, not on the kernel, not on `Kernel::add_declaration`, and
not on any import or producer policy. Nothing in `trusted_substitution`,
`nat_order_substitution`, or `import_statement_ndjson`'s `TrustedDeclaration`
refusal changes. In particular this ADR does **not** decide to admit
`propext`, to exempt a Quotient primitive, or to extend any substitution
allowlist — doc 295 measured those and this lane reconfirmed the measurement
stands.

## Consequences

- Writing a contract now requires running the frontier first. That is the
  intended cost: the two seed contracts were written from what a producer
  already did, and both families were finished by another route within days,
  which is the strongest available evidence that sizing from the producer
  rather than from the frontier picks the wrong target.
- The decline ledger stops accumulating unfalsifiable suppressions. A stale
  decline currently looks, to `fact-frontier.py`, exactly like a live one; a
  `resolution` block makes the difference readable and the count checkable.
- 21 decline artifacts need a one-time `resolution` backfill. Until that
  lands, the new guard cannot be enabled without turning the gate red, so the
  backfill and the guard must land in one change.
- The immediate operational consequence is unchanged by either rule and
  should not wait for them: the selector currently reports
  `outcome: selected` with
  `F:ml430-nat-coprime-factorizationlcmleft-factorizationlcmright-e7db70ce`
  admissible and undispatched. The loop has a candidate. Dispatch it.
- **What this ADR does not decide.** It does not decide whether to build a
  third producer, nor which shape it should target. The 209-fact
  `proof-route-only` pool is dominated by `Iff`-headed (40), existential
  (14), `Decidable`-instance (10) and higher-order induction-principle (10)
  statements that no producer in the current vocabulary addresses; sizing a
  producer against that pool is a separate piece of work, and doing it
  *before* writing its contract is exactly what rule 1 requires.

## Alternatives considered

- **Delete the two contracts.** Rejected: the contracts and their decline
  artifacts are the honest record of a real experiment, and doc 291's
  re-dispatch rule already handles content change correctly. Retirement
  preserves the record; deletion destroys it.
- **Make a stale decline a warning rather than a failure.** Rejected under
  CLAUDE.md's standing rule — a checker whose exit status does not depend on
  the finding is worse than no checker, because it manufactures the
  appearance of a gate at full speed.
- **Have `fact-frontier.py` silently ignore declines against settled
  facts.** Rejected: it would make the numbers look right while leaving the
  artifacts unmaintained, and the artifacts are what a referee reads. The
  divergence between `declined_count: 1` and `declined_by_contract: 27` is
  currently the only visible symptom; hiding it removes the symptom, not the
  defect.
- **Weaken `TrustedDeclaration` to unblock the nat-coprime family.**
  Rejected, again, and for the reason doc 294/295 already recorded: the
  guard's mutation control shows it kills exactly three tests, it is real,
  and 6 of the 15 blocked facts are permanently blocked by this kernel's
  deliberate absence of `propext` and by the quotient hard rule regardless.
