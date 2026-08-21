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

## A1 arithmetic resource closure (moved from `global/10-status.md`, 2026-08-19)

### A1 arithmetic resource closure

A1 is **DONE**. Resource increment `96ff85930` (merge `14f80a2bf`) resolves the
two measured arithmetic resource defects:

1. ADR-0377 makes arithmetic timeout query-global across sequential exact-real,
   NRA, real-relaxation, NIA-linearization, bounded-blast, and width-ladder
   routes. The same absolute deadline is polled inside solver-local CAD
   polynomial, projection, determinant, exact-division, and rational-cell loops.
   The public QF_NIA `ext-rew-aggr-test` now returns `Unknown(Timeout)` in 0.30 s
   for a 250 ms optimized request instead of 1.10 s; a committed debug regression
   finishes in 0.28 s and requires less than 1 s.
2. Online LRA normalization now has deterministic node, coefficient-work, and
   retained-cache ceilings. Production entry points distinguish deadline expiry
   from resource exhaustion and return `Unknown(Timeout)` or
   `Unknown(ResourceLimit)` rather than constructing a partial theory. The
   existing 1,024-atom front-door cap remains; current `sc-39.base.cvc.smt2`
   declines in 0.10 s at roughly 13 MiB instead of reproducing the historical
   8 GiB abort seen when that cap was experimentally raised.

Focused resource gates are green: deadline 6/6, online-LRA 7/7, CAD 37/37, the
normalization exhausted/near-miss unit, full all-feature solver Clippy, format,
and documentation links. The terminal aggregate solver gate
`CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --all-features --quiet --
--test-threads=2` passed 1,073 library tests and every integration/doctest bin,
including the 397.85-second UFLIA and 286.00-second word-equation differential
tests. `just parity-docs` is independently green at 35 rows, 24 logics, 992
files, 762 decided, 674 oracle-compared, and zero disagreements; its unrelated,
load-sensitive frontier refresh was discarded.

All six required retained lists were rerun fresh from row 1. Results are QF_NIA
34/200 versus 89, QF_LIA 117/200 versus 140, QF_LRA 86/200 versus 146, QF_RDL
105/200 versus 155, QF_IDL 68/200 versus 124, and QF_UFLIA 94/200 versus 180;
all have zero disagreements. The sole lower whole-sweep decision, one QF_LIA
`ex3000...` UNSAT, reproduced 3/3 in isolation at about 8.1 seconds under the
24-second protocol and is classified as load-sensitive sweep timing, not a
semantic loss. The ledger honestly retains 117.

The QF_IDL run exposed and then closed a real fallback-reservation regression.
Commit `4477f2bb9` bounds every probe-front-end phase and uses a measured 12/12
probe/fallback split only for 128–1,024-atom numeric equality gates; a global
12/12 split was rejected after losing five controls. A 171-case QF_IDL/QF_RDL
A/B was monotone. The final full sweep recovers `lpsat-goal-18.smt2` as UNSAT,
retains the BubbleSort gain, adds one SAT graph case, and has no Axeyum loss.

Commit `5ce07c55e` (merge `8ea6a7cad`) also makes parity resume identity
fail-closed: exact committed-list paths are canonical; ambiguous legacy
basenames, duplicate rows, and population drift are rejected. The six accepted
A1 runs were fresh and non-resumed. Full evidence, sidecar hashes, rejected IDL
policies, and gate separation are retained in
[`docs/plan/arithmetic-a1-retained-result-2026-08-06.md`](docs/plan/arithmetic-a1-retained-result-2026-08-06.md).

Disk cleanup preserved every branch and salvaged dirty inactive-worktree deltas
to labelled Git stashes before retiring their checkouts. Reproducible Cargo
artifacts and empty failed-run directories were removed only after ancestry,
cleanliness, and open-file checks. Only clean `main` remains registered; retained
evidence and unrelated temporary projects were untouched.
