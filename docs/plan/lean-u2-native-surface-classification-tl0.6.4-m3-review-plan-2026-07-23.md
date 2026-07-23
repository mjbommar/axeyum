# Lean U2 TL0.6.4 M3 plan — complete-row independent review and classification acceptance

Status: **preregistered review semantics only; no accepted M2 parent, M3 input
authority, reviewer assignment, review event, attestation, disposition,
TL0.6.4 acceptance, native outcome, pair, performance row, or parity credit
exists**

Date: 2026-07-23

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

Required parent:
[M2.7 variant-merge and M3-handoff plan](lean-u2-native-dependency-tl0.6.4-m2.7-variant-merge-plan-2026-07-23.md),
followed by a future accepted M2.7 result that validates every M2.1-M2.6
authority and closes every applicable case/variant cell.

## 1. Decision boundary

M3 is the independent acceptance review for TL0.6.4's native-surface
classification. It does not discover dependencies, repair the M2 graph,
execute Lean, or infer Axeyum support. It decides whether one immutable,
accepted M2 result actually satisfies the declared classification contract for
every case and every applicable official variant.

The singular rule is:

> Review coverage is exact, not sampled. Every one of the 3,723 case rows and
> every one of the 408,374 applicable case/variant cells must be covered by an
> accountable disposition against the same accepted M2 parent. Automation may
> validate or present rows, but it cannot count as the independent reviewer.

M3 owns:

- frozen entry/success criteria and the exact review-package identity;
- complete case and cell assignment with explicit reviewer independence;
- criterion-by-criterion dispositions, rationale, source pointers, and
  immutable correction requests;
- secondary concurrence for risk-bearing declines, correction overlays,
  equivalence proofs, and intentionally-online routes;
- deterministic acceptance/rejection aggregation and a complete action ledger;
  and
- the bounded decision to accept or reject TL0.6.4 classification.

M3 does not change M0/M1/M2 evidence, resolve a missing provider, convert an
unavailable provider into a decline, waive a required native surface, approve
its own producing work, select representative variants, or create official or
Axeyum outcomes, pairs, performance rows, population completion, axis
completion, terminal gates, or parity credit.

This structure follows current public assurance guidance without outsourcing
Axeyum's acceptance semantics to it. NIST's
[requirements-verification guidance](https://www.nist.gov/itl/csd/secure-systems-and-applications/requirements-verification-tools)
calls out completeness, consistency, correctness, traceability, ambiguity,
understandability, and verifiability as distinct properties. NIST's
[structured-assurance work](https://www.nist.gov/programs-projects/measurement-metrics-and-assurance)
separates claims, arguments, and evidence. NASA's systems-engineering glossary
defines an independent standing review board and review-specific success
criteria, while its
[entrance/exit guidance](https://swehb.nasa.gov/spaces/SWEHBVB/pages/140640427/7.9%2B-%2BEntrance%2Band%2BExit%2BCriteria)
requires review inputs and acceptance criteria to be available before the
decision. These are design references, not evidence that any Axeyum row has
been reviewed.

## 2. Entrance criteria and hard block

M3.1 cannot freeze an input authority until all of the following exist and
validate together:

1. an accepted M2.7 result at one containing revision, with exact parent seals
   for separately accepted M2.1-M2.6 results;
2. exactly eight selection rows, 111 provider variants, 3,723 case rows, and
   408,374 expanded applicable cells under the accepted M2.0 denominator;
3. every provider required by a cell bound to an exact executable, platform,
   configuration, environment, and accepted attempt identity;
4. every cell `closed-supported` or `closed-declined`, with no `not-run`,
   `unresolved`, `provider-unavailable`, invalid, contradictory, orphaned,
   unowned, ambiguous, or incomplete state;
5. every M2.7 node, edge, condition, assurance vector, ownership relation,
   correction, decline, residual resolution, equivalence proof, projection,
   and M3 handoff row present and seal-valid;
6. M1's immutable history and M2.6's four-case editor/RPC correction both
   retained rather than rewritten;
7. every M2 process/evidence root completion-valid under TL0.7, with no retry,
   post-completion mutation, or mixed result revision; and
8. zero native outcome, pair, performance, population, axis, gate, and parity
   credit in the classification package.

The current repository does not satisfy the M3 entry gate: all 111 providers
remain unbound; M2.1 has not executed; M2.2-M2.7 have no accepted input/result
authorities; and node, edge, and closure registries remain empty. Exact M2.0
denominators and zero-credit fields do satisfy their individual invariants,
but cannot seed a review attempt without the other accepted parents.

If any entrance criterion fails, M3 records no review assignment or
disposition. A diagnostic preflight may enumerate failures but is not an M3
attempt and cannot be promoted later.

The current source-first baseline is commit
`e94503faaa2af746eb9646e7b43e4d36fcd2866b`:

| Input | SHA-256 | Current interpretation |
|---|---|---|
| `docs/plan/lean-u2-native-dependency-v1.json` | `46d2c17363bf8e4097d12df20f8ee9ffb86acf647642068d3eacc72e711dd4d6` | accepted M2.0 denominator with empty graph/unbound providers |
| `docs/plan/lean-u2-native-dependency-tl0.6.4-m2.7-variant-merge-plan-2026-07-23.md` | `90cfd4475e5c84378f773f625f88db6fb10ba9b642a91f1d9fec32c8f2a8f96b` | M2.7 preregistration, not an accepted result |
| `docs/plan/lean-complete-parity-v1.json` | `edd78f7218ed0cfbee4bc16e5cec1e63ac117c5b965b33385ad18932e5a9e14e` | pre-M3.0 registry with zero complete populations/axes/pairs/gates |
| `docs/plan/generated/lean-complete-parity.json` | `160ae64ab61495e07aeedc343de9ed6a1ac384651d383cebb6f12b7f37875975` | deterministic projection of that registry |
| `scripts/tests/test_lean_complete_parity.py` | `3b817a5d47f14f1455b0cf5b97fadd03c881afe73ec46774c49841c1e8594bbd` | M3.0 non-crediting regression after this plan was drafted |

These identities document the preregistration boundary only. The plan file
does not self-authorize, and M3.1 must bind future accepted result authorities
rather than treating any hash in this table as observed M2 closure.

## 3. Exact review population

The frozen review denominator expands the accepted M2.0 factoring exactly:

| Case class | Cases | Cells per case | Cell dispositions |
|---|---:|---:|---:|
| eight-selection membership | 3,476 | 111 | 385,836 |
| six-selection membership | 202 | 104 | 21,008 |
| three-selection Lake-only membership | 45 | 34 | 1,530 |
| **Total** | **3,723** | — | **408,374** |

M3 requires two linked review layers:

- one **cell disposition** for each exact `(case_id, variant_id)` pair; and
- one **case disposition** that accounts for every applicable cell, direct and
  transitive surface, correction, decline, residual, and cross-variant delta.

The 3,723 case dispositions do not replace cell review. The 408,374 cell
dispositions do not replace the case-level reconciliation against M0/M1.
Equal selected-case hashes, shared commands, content-addressed graph nodes, or
accepted M2.7 equivalence proofs may reduce presentation cost only. Every
member retains a disposition and reviewer coverage.

Graph-element drill-down rows remain reviewable through their owning cells.
The M3 authority freezes exact counts for cases, cells, owned nodes/edges,
conditions, evidence records, declines, corrections, equivalence members, and
resolved residuals from the accepted M2.7 parent; aggregate counts never
substitute for those rows.

## 4. Reviewer identity, independence, and assignment

Each review identity binds a stable reviewer ID, role, declared competence
scope, assignment revision, and conflict declaration. A human or accountable
named agent session with retained scope and outputs may be a reviewer, but a
generator, validator, test suite, anonymous model invocation, or aggregate
signature alone is not a reviewer identity.

For every assigned cell and case, the primary reviewer must be distinct from
the identities that produced, modified, executed, promoted, or accepted the
corresponding M2 evidence. Repository maintainers may accept the final M3
authority, but maintainer status does not erase row-level conflicts. A reviewer
who discovers a conflict records recusal before inspecting or disposing the
row; reassignment preserves the recusal event.

Assignments are frozen before review as disjoint, exhaustive stable-ID sets or
ranges. Each assignment binds:

- exact case and cell IDs plus their ordered-list digest;
- accepted parent/result and criterion-set identities;
- primary reviewer and any required secondary reviewer;
- allowed review window and immutable event/output roots; and
- zero dispositions at creation.

Every row has exactly one accountable primary reviewer. A second independent
concurrence is mandatory for an accepted decline, correction overlay,
cross-variant equivalence proof, intentionally-online route, or previously
contradictory evidence resolution. The secondary cannot be the primary or an
evidence producer for that row. Ordinary supported cells need one independent
reviewer unless a future authority raises, but never lowers, the rule.

No sampling fraction, random audit, “reviewed by equivalence representative,”
or unowned shared batch satisfies coverage. Deterministic batching is allowed
only when every member is enumerated and each returned disposition expands
losslessly to the original IDs.

## 5. Immutable review package

M3.1 freezes a package before any disposition. At minimum it contains:

- accepted M2.7 result, all M2.1-M2.6 parent authorities, logical seals, exact
  containing revisions, and validation commands;
- the complete case/cell review population and M2.7 ordering;
- direct and transitive graph views with owners, conditions, assurance vectors,
  process/artifact/effect/transcript evidence, and completion identities;
- M0/M1 surface history, M2.6 correction overlay, all resolved residuals,
  reviewed declines, intentionally-online rows, and equivalence proofs;
- per-row claim, argument, evidence, and required-criterion pointers;
- reviewer roster, independence/conflict rules, assignments, and secondary
  concurrence requirements;
- immutable event schemas, completion-last protocol, campaign identity, local
  output root, and append/resume/supersession rules; and
- explicit zero-credit fields and the post-M3 TL0.6.5 boundary.

Presentation artifacts may hyperlink, filter, or group this package but cannot
omit rows or become authority. Reviewers dispose canonical IDs and seals, not
screen positions, line numbers, mutable branch names, or dashboard counts.

Any parent, package, criteria, assignment, code, or rendering change after the
first review event invalidates the attempt. Corrections require a new M2 result
or new M3 authority/attempt as appropriate; historical events remain immutable.

## 6. Criterion vectors and dispositions

Every cell disposition records explicit pass/fail findings for at least:

1. **identity:** case, variant, provider, platform, configuration, environment,
   attempt, and evidence identities agree;
2. **surface:** all required direct/transitive nodes and edges are owned by the
   exact cell and no lexical-only signal is promoted;
3. **assurance:** each edge meets its class-specific static/configured/runtime
   vector without max-state collapse or cross-variant promotion;
4. **conditions:** all branches are registered; taken/not-taken evidence is
   variant-local and complete;
5. **effects:** processes, files, artifacts, ABI/load/init behavior, requests,
   transcripts, outputs, cleanup, and intentionally-online policy are fully
   accounted where applicable;
6. **history:** M0/M1 observations, explicit corrections, and residual
   resolutions remain traceable and non-destructive;
7. **decline:** a decline is stable, scoped, owned, evidence-backed, reviewed,
   and genuinely inapplicable rather than unavailable or unsupported;
8. **consistency:** no contradictory, orphaned, unowned, ambiguous, stale, or
   incomplete evidence remains;
9. **closure:** the M2.7 cell state and aggregate projection recompute exactly;
   and
10. **nonclaim:** the row creates no execution, agreement, performance, or
    parity credit.

Each case disposition additionally checks complete applicable-variant
membership, the supported/declined partition, cross-variant deltas and
equivalence members, M0/M1 reconciliation, correction overlays, residual
history, and stable owner/decline routes.

Terminal row dispositions are:

- `accepted-supported` — all criteria pass for a supported cell;
- `accepted-declined` — all criteria and required secondary concurrence pass
  for an M2-closed declined cell;
- `return-m2-repair` — evidence or classification must be corrected through a
  new M2 authority/result; or
- `invalidate-parent` — the accepted parent or one of its authorities is not
  valid for review.

`recused` and `in-progress` are immutable events, not terminal dispositions.
There is no “accepted with conditions,” “accepted by sampling,” “deferred but
complete,” or waiver state. Free-text rationale accompanies typed criterion
results; prose cannot override them.

## 7. Review execution and evidence

M3 is an offline review of immutable accepted evidence. It starts no Lean,
Lake, compiler, server, official-test, network, tracing, or Axeyum process. If
a reviewer needs new observation, the row becomes `return-m2-repair`; the new
process belongs to a separately preregistered M2 correction, not M3.

An M3 review campaign may span sessions because exact review of 408,374 cells
is intentionally not a sampling exercise. Its append-only event stream binds
assignment, reviewer, row, criterion vector, cited canonical evidence,
rationale, disposition, concurrence, and timestamps/ordinals. Raw reviewer
input is retained. Before each resume, the validator must reproduce the frozen
package/assignment identities and the complete stored prefix. Already-final
rows are not silently replayed. A mistaken pre-completion disposition may be
changed only by an explicit withdrawal/supersession event that retains both
records and recomputes the active projection. Completion is written last after:

- every assignment expands to the exact frozen denominator;
- every required primary and secondary event is present exactly once;
- all referenced parent rows and seals validate;
- all event/list/record seals and deterministic order validate;
- case aggregation recomputes from cell dispositions; and
- the action ledger and acceptance projection agree with every event.

An interrupted campaign with a valid prefix remains incomplete and may resume
under the same frozen authority. A malformed prefix, conflicting active
terminal events, post-completion mutation, or resume under changed inputs is
invalid history and cannot be repaired in place. Missing completion always
means no acceptance.

## 8. Findings, repair, and supersession

M3 judges M2; it never edits M2 in place. Any `return-m2-repair` or
`invalidate-parent` makes the whole M3 attempt non-accepting. The result lists
every finding with exact owner, severity, criterion, affected IDs, evidence,
required action, and target milestone.

Repair follows a new source-first M2 correction plan, authority, implementation,
authorized execution if needed, result, and M2.7 merge. A later M3 attempt
binds the new parent and retains the earlier failed attempt as history. It
cannot copy prior dispositions merely because row content appears unchanged;
it may import them only through a preregistered, identity-complete carry-forward
rule with explicit reviewer reaffirmation and mutation controls.

Accepted dispositions are revocable evidence, not mutable truth. If a parent
or review defect is discovered later, publish a revocation referencing the
original record, reopen TL0.6.4, and transitively invalidate dependent TL0.6.5
pairs or higher claims. Never delete or silently rewrite the accepted history.

## 9. Acceptance projection

An M3 result may accept TL0.6.4 only when:

- one frozen parent/package/criteria/assignment set validates;
- all 408,374 cells have terminal primary dispositions and every risk-bearing
  row has the required independent concurrence;
- all 3,723 case dispositions recompute from exactly their applicable cells;
- every cell is `accepted-supported` or `accepted-declined` and no repair,
  invalidation, conflict, recusal gap, pending event, or unreviewed row remains;
- all corrections, equivalence members, declines, intentionally-online rows,
  residual history, owners, and actions are completely represented;
- review events, completion, result authority, generated projections, and
  containing revision are deterministic and seal-valid; and
- all complete-parity, parity-doc, link, focused mutation, and detached-root
  gates pass at local/tracking/remote equality.

The result reports supported and declined cells separately by case, variant,
surface, provider, platform, configuration, workflow, and assurance dimension.
TL0.6.4 acceptance means only that the official U2 native dependency/surface
classification is complete and independently reviewed for the pinned target.
It does not mean Axeyum executes or matches those rows.

## 10. Required schema and mutation controls

M3.1 must freeze domain-separated package, criterion, reviewer, conflict,
assignment, event, concurrence, finding, action, completion, result, revocation,
and aggregate records. The validator must reject at least:

1. any denominator other than 3,723 cases and 408,374 exact applicable cells;
2. missing, duplicate, extra, reordered, or inapplicable case/variant IDs;
3. a parent lacking accepted M2.1-M2.7 authorities or exact containing seals;
4. any unresolved, unavailable, invalid, contradictory, incomplete, not-run,
   orphaned, unowned, or ambiguous parent row;
5. a review package or criterion change after the first event;
6. assignment gaps, overlap, lossy ranges, digest drift, or unassigned shared
   graph ownership;
7. a primary reviewer who produced or accepted the row's M2 evidence;
8. missing competence/conflict declarations, undisclosed conflict, or a
   disposition after recusal;
9. missing secondary concurrence, same-identity concurrence, or producer
   concurrence on a risk-bearing row;
10. automation, aggregate signatures, sampling, or equivalence representatives
    counted as independent row review;
11. a criterion vector with omitted, unknown, prose-overridden, or internally
    inconsistent fields;
12. accepted support without class-specific assurance or accepted decline from
    `provider-unavailable`, unsupported behavior, missing evidence, or waiver;
13. one variant's evidence or disposition promoted to another variant;
14. M2.6's four-case correction lost, M1 history rewritten, or a residual/
    decline/equivalence member hidden by aggregation;
15. a case disposition that does not exactly recompute from all applicable
    cell dispositions;
16. acceptance with any repair, invalidation, pending, duplicate terminal,
    recusal gap, missing rationale, or open action;
17. missing raw event, malformed append prefix, replay without explicit
    supersession, mixed campaign, post-completion mutation, or stale parent;
18. unstable ordering, domain confusion, row/list/record seal drift, or output
    nondeterminism;
19. a failed/revoked review removed, overwritten, or silently carried forward;
    and
20. any native outcome, pair, performance, population, axis, terminal gate, or
    parity credit created by M3 acceptance.

Mutation tests must reseal outer structures so each semantic invariant, not
only a checksum mismatch, is exercised.

## 11. Source-first sequence and exit

1. **M3.0 plan:** this document freezes review semantics and the current hard
   block. It consumes no parent result and creates no review authority/event.
2. **M3.1 input authority:** after accepted M2.7 only, freeze exact parents,
   package, criteria, roster/conflicts, exhaustive assignments, schemas,
   controls, evidence roots, and zero-credit fields; commit and push.
3. **M3.2 implementation:** implement offline validators, presentation,
   append-only review/concurrence storage, completion-last aggregation,
   mutation tests, and deterministic reports; commit and push before review.
4. **M3.3 review campaign:** verify clean refs and empty roots, then conduct one
   resumable append-only complete-row review with no Lean/external process
   execution and no silent row replay.
5. **M3.4 result:** validate every event and seal, publish all findings/actions,
   accept or reject the attempt, and bind the exact containing revision.

Stop before M3.1 if the accepted M2.7 parent is absent. Stop before review if
the package, criteria, reviewer independence, assignments, or output root is
not exact. Stop without acceptance on any repair/invalidation finding,
coverage gap, missing concurrence, completion failure, mutation failure,
dirty tree, or ref inequality.

M3 exits only with one immutable result that either rejects the exact campaign
with every finding retained, or accepts all 3,723 cases and 408,374 cells under
the criteria above. There is no partial TL0.6.4 acceptance.

## 12. Nonclaims and continuation

This plan does not make M3 executable and does not accept TL0.6.4. Even a
future accepted M3 result completes only the official U2 native-surface
classification boundary. TL0.6.5 must still bind complete official and Axeyum
execution authorities and compare every exact normalized semantic row.

Complete Lean parity additionally requires every U0-U9 population, A0-A11
axis, and G1-G10 terminal gate at one published revision. M3 cannot promote a
classification review into parser, elaborator, tactic, project, editor,
compiler/runtime, bootstrap, `Init`/`Std`, mathlib, trust, performance, or
unqualified parity evidence.
