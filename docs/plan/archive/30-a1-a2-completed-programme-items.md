# A1 and A2 — completed programme items

Moved verbatim out of [`docs/plan/global/20-next-actions.md`](../global/20-next-actions.md)
on 2026-08-17. Both were marked `DONE`, and a "next actions" file should carry
actions that are next.

The move is not cosmetic. `scripts/check-plan-authority.py` budgets the files
`PLAN.md` is generated from at 52,000 bytes, and they had reached 51,958 — **42
bytes of headroom**, which is less than one landed row. A lane that finished a
piece of work could not record it without first evacuating something. Recording
was, briefly, the most expensive step in the loop.

Nothing here is edited; only its location changed.

### A1 — Complete arithmetic deadline and resource enforcement (`DONE`, P0)

Shared deadlines, CAD cancellation, deterministic LRA normalization ceilings,
the DL fallback-reservation repair, exact resume identity, six fresh retained
division runs, and their ledger commits are complete. See the closure note
linked above. The one QF_LIA whole-sweep miss is retained honestly and bounded
by a 3/3 isolated UNSAT reproduction well inside the protocol budget.

### A2 — Rebase and finish credited full-library readiness (`DONE`, P0)

**Why now.** Eleven division samples are useful, but representative general
solving-power remains unmeasured. The topic branch
`agent/smtcomp/full-preparation-live` contains substantial process-free work
based on older July state and must not be merged or launched as-is.

**Completed checkpoint.** The branch audit and R1--R5 process-free topic are
complete. R5 is implemented at `e4bb854bf` with 52 focused tests / 82 subtests,
165 aggregate tests, scoped gates, and a successful real locked/offline build
smoke. Exact topic `2925efea5` was pushed, matched its remote, and passed one
uninterrupted R3-isolated `just check`. Integration review proved the topic was
strictly ahead with no divergence and previewed a conflict-free merge. Merge
`8ed5ad089` then passed the focused post-merge gates and the full combined-main
`just check` with external frontier artifacts and a clean tracked tree. The
exact disposition and gate separation are in the dated A2 audit and R5
implementation result.

**Next slice.** None in A2. Preserve the integrated process-free contract and
move to A3. Do not execute the constructed live operator merely because its
process-free and integration gates are green.

**Exit.** Current-main identity is immutable, readiness and resume gates are
green, the published root is process-free with `launch_authorized=false`, and
an independently reviewed later step authorizes any bounded live execution.

**Stop.** No host/NAS mutation or solver launch from stale refs, red gates, or
an unaccepted root. Follow
[`docs/plan/smtcomp-full-library-workstream/README.md`](docs/plan/smtcomp-full-library-workstream/README.md).
