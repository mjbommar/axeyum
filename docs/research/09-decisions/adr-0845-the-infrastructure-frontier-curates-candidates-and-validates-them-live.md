# ADR-0845: The infrastructure frontier hand-curates candidate rows and re-validates them live against the join, rather than ranking by degree

Status: accepted
Date: 2026-08-30
Index-summary: L2 phase G3 publishes four frozen queues (missing language
infrastructure, missing reusable proof producers, high-leverage theorem
dominators, local dependency-ready leaves) over population
`mathlib-group-defs-v1` (ADR-0820/ADR-0835). Two of the four queues are
EMPTY for this population, each for a stated, data-backed reason; the
other two carry 4 and 1 rows respectively. Every row has a content-hash
`row_id` stable across regeneration, a stated gain kind, raw evidence, and
a preregistered, re-runnable metric.

## Context

`docs/plan/graph-directed-library-roadmap-2026-08-30.md` phase G3 asks for
four queues over the L1 phase G2 graph join
(`artifacts/graph-join/mathlib-group-defs-v1.join.json`), each row showing
top downstream facts, current blockers, estimated cost, destination paths,
and whether the gain is statability, dispatchability, proof, or
independent assurance. Two constraints govern the phase and are repeated
here because they are the exact failure mode this ADR exists to avoid:

1. Graph rank is ADVISORY until its authority is complete
   (`docs/plan/global/50-planning-rules.md`) -- these queues are a
   proposal for humans and coordinators, never an automatic dispatcher.
2. Raw degree never authorizes work -- a declaration with many dependents
   is not thereby worth building; every row must state what the gain
   actually is.

ADR-0835 already measured the population this phase reads: 446
declarations, of which 9 resolve to a ledger fact (all 9 already
`epistemic_status=proved`), 161 resolve to the kernel's own vocabulary
roots (a name-match on one of the 12 trusted inductive carriers), and 27
are "name-coincidence candidates" -- a bare string match against an
UNRELATED fact's evidence, deliberately left unresolved because ADR-0835
refuses to treat name similarity as identity.

## Decision

**Rank-by-degree was tried first and rejected.** In-population in-degree
over the 446 declarations is dominated by Lean/Mathlib-core typeclass and
notation-resolution scaffolding this kernel has no counterpart for and
mostly does not need (`Nat` 194, `OfNat.ofNat`/`instOfNatNat` 85,
`LT.lt`/`instLTNat` 54, `LE.le`/`instLENat` 42-44, `List` 39, ...). A queue
built from this ranking directly would reproduce exactly the failure the
roadmap's own closing line warns against. So:

1. **Candidates are hand-curated in source**
   (`scripts/lib/infrastructure_frontier.py::ROW_CANDIDATES`), each naming
   a specific proposed increment, its claimed gain kind, and a written
   `gain_explanation` that names a MECHANISM (a missing kernel-
   representable structure, a documented recurring cost, an identity
   question needing verification) -- never a raw count. This is
   diffable, reviewable, and git-blamed like any other decision in this
   repository.
2. **Every candidate is RE-VALIDATED against the live join and graph at
   generation time** (`validate_candidate`): its subject declarations
   must still exist in the population, and no Theorem-kind subject may
   have since acquired a fact_id. Generation FAILS LOUDLY (raises,
   non-zero exit) if a candidate's premise no longer holds, rather than
   silently producing a stale or wrong row.
3. **Raw evidence (in-/out-degree, per-dimension resolution, name-
   coincidence membership) is computed fresh and attached to every row**,
   satisfying the roadmap's "all scores must show their raw inputs"
   without letting that evidence stand in as the argument.
4. **A name-similarity presence check (`grep_presence`) is explicitly
   NEVER treated as an identity claim.** One row (`of_decide_eq_true`,
   theorem-dominators) exists specifically because a plain source grep
   finds a same-named kernel prelude primitive that the join's own
   name-coincidence scan cannot see (that scan only reads FACT evidence
   text, not prelude source) -- the row's action is "verify identity
   before doing anything else", not "go prove this", mirroring ADR-0835's
   own refusal to manufacture identity from a bare name match.
5. **Two of the four queues are empty over this population, each for a
   distinct, data-backed, machine-checkable reason** (computed in
   `_empty_reason`, not asserted in prose alone):
   - `proof-producers`: the join's `producers`/`declines` dimensions can
     only see the 9 already-`fact_ids`-resolved declarations (ADR-0835's
     own stated limit), and all 9 are already proved -- there is no open,
     fact-linked cluster in this population for a producer to serve.
   - `dependency-ready-leaves`: 8 Theorem-kind declarations have every
     direct TYPE dependency already available (computed from
     `direct_type_deps` only, never proof/value deps, per phase G1's own
     rule that proof-derived data is forbidden producer input); every one
     is excluded for a stated reason (built-in inductive projection,
     Lean-generated auxiliary, or promoted to another queue because its
     real blocker is architectural or a naming question). The 8
     candidates themselves are published in the artifact's `diagnostics`
     section so the empty reason is independently checkable.
6. **Row ids are content hashes of SUBSTANCE, never of a computed/volatile
   number.** `row_id(queue, population_id, subject, gain_kind)` hashes
   only those four fields; degree, resolved counts, and confidence are
   excluded on purpose so the id survives a graph refresh that shifts
   degree by one but proposes the same increment. `ROW_ID_PURITY` (one of
   seven guards, below) re-derives every row's id from its own recorded
   fields and fails if it does not match.
7. **Every row carries a preregistered metric with a re-runnable
   command**, measured now (`baseline`) so a later reader can re-run the
   same command and see whether it moved -- the falsifiability the
   roadmap phase explicitly asks for.
8. **Seven guards, seven distinct mutation classes, each mutation-verified
   1:1** (`scripts/check-infrastructure-frontier.py`, kill table in
   `scripts/tests/test-infrastructure-frontier-mutations.sh`):

   | Guard | What it catches |
   |---|---|
   | `MISSING_JOIN` | the graph-join artifact this frontier depends on is absent or has no dimensions |
   | `STALE_ARTIFACT` | the committed frontier.json/dashboard.md disagree with a fresh recomputation |
   | `ROW_ID_UNIQUE` | two rows (any queues) share a row_id |
   | `ROW_ID_PURITY` | a row's row_id does not match a hash recomputed from its own (queue, population, subject, gain_kind) |
   | `EMPTY_QUEUE_REASON` | a zero-row queue has no substantive declared empty_reason |
   | `ROW_EVIDENCE_COMPLETE` | a row is missing blockers, a valid gain_kind, a metric command, or both destination paths and a destination note |
   | `CROSS_CHECK_PRESENT` | the artifact has no cross_check section naming the dispatchable-frontier relationship |

9. **Cross-checked against `scripts/check-dispatchable-frontier.py`
   (read-only, out of this lane's edit scope), not silently.** None of
   this population's 446 names is a subject that script reports on (its
   dispatchable/held-out/blocked sets are drawn from unrelated
   `ml430` number-theory mirror families), so no direct disagreement is
   possible; the artifact records this explicitly rather than omitting
   the comparison, and notes the thematic agreement (both independently
   find almost nothing immediately actionable, for different reasons).

## Evidence

Over population `mathlib-group-defs-v1` (446 declarations, ADR-0820):

```
language-infrastructure:   4 rows (Semigroup/mul_assoc, CommMagma/mul_comm,
                            Mul+IsLeftCancelMul/mul_left_cancel, congrArg)
proof-producers:           0 rows (structural: 9/9 fact-linked already proved)
theorem-dominators:        1 row  (of_decide_eq_true -- verify identity first)
dependency-ready-leaves:   0 rows (8 candidates, all excluded for a stated reason)
```

Two independent runs of `scripts/gen-infrastructure-frontier.py` produce
byte-identical `<population>.frontier.json`/`.dashboard.md` (no timestamps
or host-dependent fields). All seven guards each kill exactly their own
fixture when deleted in a scratch copy; deleting any one guard leaves the
good fixture passing and every other guard's bad fixture still failing.

## What this queue set does not capture

It is bounded to the same 446-declaration population ADR-0835 joins, which
is dominated by Lean/Mathlib-core scaffolding; a wider or different
population would need its own join (ADR-0835's own consequence) before
this generator could queue anything from it. The `grep_presence` heuristic
is explicitly non-authoritative (ADR-0835's own refusal to treat name
similarity as identity, applied at the source-text layer instead of the
fact-ledger layer) -- a row built on it names verification as its first
step, never proof work.

## Alternatives

**Rank all 446 declarations by degree and take the top N per queue.**
Rejected: this is exactly the failure the roadmap phase's closing line
warns against, and this population's own top-degree declarations
(`Nat`, `OfNat.ofNat`, `LT.lt`, ...) are overwhelmingly Lean-core notation
plumbing with no independent mathematical content to build.

**Pad empty queues with low-confidence rows to avoid an empty section.**
Rejected per the task's own instruction: an empty queue with a stated,
checkable reason is a real result; a padded one manufactures the
appearance of readiness the population does not have.

**Treat a source-grep name hit as proof of existing coverage and drop the
row entirely.** Rejected: ADR-0835 specifically refuses bare name
similarity as identity; the correct action is a verification row, not a
silent drop (which would hide a possible gap) or a silent build (which
risks duplicating existing work).

## Consequences

G4 (three pilot clusters) can cite a row's `row_id` in a lane brief and
re-run its `preregistered_metric.command` afterward to check whether it
moved, without needing to re-derive the row's evidence by hand. G5 (make
graph selection the ordinary dispatcher) inherits this ADR's structural
rule that a row must state its gain kind and be re-validated at
generation time, not merely computed once and trusted.
