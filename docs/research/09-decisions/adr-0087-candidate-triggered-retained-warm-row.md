# ADR-0087: Candidate-Triggered Retained Warm ROW

Status: proposed
Date: 2026-07-10

## Context

ADR-0086 gives each admitted store, constant-array, and array-ITE read a
private scalar owner and retains its exact definition in the incremental CNF.
That closes the ownership and learned-state boundary, but it installs every
definition during observation. The EVM storage-depth sweep localizes the cost:
at depth 32, retained warm definitions take 30.933 ms while frontend scalar ITE
folding takes 0.368 ms. The warm route is no longer rebuilding through the
one-shot dispatcher; it is paying to lower and encode every parent before a SAT
candidate demonstrates that the parent matters.

The canonical array engine already establishes that relaxation-first ROW is
sound (ADR-0072), and its retained-search variant establishes that permanent
valid ROW clauses may be added after a candidate without discarding learned
state (ADR-0081). The incremental warm solver should apply that discipline to
the exact scalar definitions retained by ADR-0086, without introducing a
second SAT or CDCL(T) owner.

This follows the array/UF ownership question in the
[research-question register](../08-planning/research-questions.md) and advances
the deferred warm half of ADR-0030.

## Decision

`IncrementalBvSolver` will retain exact structural-read definition terms at
admission but leave them dormant until a SAT candidate violates them.

- The initial warm CNF contains scoped user roots, existing valid congruence
  lemmas, and previously activated structural definitions. A newly retained
  structural owner is otherwise an unconstrained scalar input.
- After SAT, reconstruction supplies every lowered private owner. Private
  owners not yet present in the AIG receive their sort's deterministic
  well-founded default, producing a total candidate extension.
- The solver evaluates every currently active retained structural equation in
  stable term-ID order. All equations false in that candidate are lowered and
  asserted permanently as one deterministic batch. The same incremental CNF
  and BatSat instance then solve again under the same frame and one-shot
  selectors.
- A structural equation is activated at most once. The existing 512-node and
  256-depth admission limits remain exact; refinement performs at most 256
  candidate-activation rounds, matching the admitted maximum dependency depth.
  Exhausting that limit degrades to a resource `Unknown` rather than accepting
  a partially checked model.
- The user timeout becomes one absolute deadline shared by initial SAT,
  candidate evaluation, definition lowering, and every resumed SAT call. A
  resumed call receives only the remaining duration.
- Only structural equations reachable from active frame roots or the current
  one-shot assumptions are checked. Definitions activated by an earlier scope
  remain harmless permanent lemmas, but inactive pending definitions do not
  create new work.
- Array model projection remains leaf-only. A SAT result is returned only after
  all active structural equations hold in one candidate, direct leaf arrays and
  scalar function tables are projected, and every original active assertion and
  one-shot assumption replays successfully.

The exact retained equations remain those of ADR-0086:

```text
r_select(const(v), j)       = v
r_select(store(a,i,v), j)   = ite(i = j, v, r_select(a,j))
r_select(ite(c,a,b), j)     = ite(c, r_select(a,j), r_select(b,j))
```

## Soundness Argument

The initial formula is a relaxation of the exact definitional extension: fresh
structural owners may take arbitrary scalar values. Therefore UNSAT before all
definitions are active transfers directly to the original query. Every later
refinement adds only a valid total array identity, so UNSAT after refinement
also transfers and existing learned clauses remain valid.

For SAT, deterministic defaults merely complete otherwise absent private
variables for the purpose of testing equations; they are not projected as user
values. A candidate is eligible for projection only when every active retained
equation evaluates to true under one total extension. Induction over the
bounded structural dependency DAG then equates each observed structural owner
with the corresponding array read. Leaf projection realizes direct array
observations, and original-term evaluator replay remains the final acceptance
gate. Missing defaults, failed equation evaluation, exhausted bounds, or failed
replay cannot produce an accepted SAT result.

Permanent activation is scope-safe because a definition constrains only a
private owner to the denotation of its source read; it does not assert any user
root. Failed-assumption cores remain sound: a relaxed-formula core is sufficient
for the stronger exact query, while an activated definition is unconditional
and valid independently of every selector.

## Required Validation Before Acceptance

- A violated store hit activates ROW and changes a relaxed SAT candidate to
  UNSAT without rebuilding the incremental solver.
- A satisfiable miss whose default-completed candidate already obeys ROW
  activates zero structural definitions and replays the original array term.
- Nested store, constant-array, array-ITE, and Bool-element cases activate only
  candidate-false definitions and reach the same replayed verdicts as the eager
  ADR-0086 implementation.
- Push/pop and opposite one-shot assumptions show that activated definitions
  persist, pending inactive definitions do not trigger work, and cores remain
  sound.
- Exact depth/round and node admission controls, plus a shared-deadline timeout
  regression, degrade conservatively.
- The existing 64-seed warm/`check_auto`/Z3 matrix remains disagreement-free,
  with every SAT model replayed.
- Full solver and symbolic-execution tests, EVM tests and differential fuzz,
  strict clippy, warning-denied rustdoc, links, foundational resources, and the
  exact-SHA pre-push gate pass.
- The release EVM storage-depth sweep is regenerated. The result is reported
  honestly; ITE folding remains the default unless the measured warm route wins
  reliably enough to justify a separate policy decision.

## Alternatives

### Keep observation-time permanent definitions

Rejected as the next increment because the depth-32 measurement is roughly 84x
slower than frontend folding after the one-shot-dispatch cost has already been
removed.

### Guard definitions with user selectors

Rejected. Exact private definitions are valid globally, and reinstalling them
per branch would discard the reuse gained by ADR-0086. Only their activation
decision is candidate- and active-root-driven.

### Refine only after original replay fails

Rejected. Replay failure is the final soundness alarm and reports only the
original root, not a deterministic violated private equation. Checking the
retained scalar equations first gives a local valid lemma and keeps replay as an
independent trust gate.

### Embed the canonical array `CdclT` engine

Deferred for broader warm equality/extensionality and array-valued UF parents.
The current retained equations need only monotone root addition, which the
existing incremental CNF already owns.

## Consequences

Warm structural ownership remains persistent while its semantic cost becomes
candidate-driven. Queries that already admit a replayable default extension can
avoid all structural definition CNF; violated paths pay only for equations that
have demonstrated relevance, and that payment is reused by later checks.

The final-check loop becomes multi-solve and must account for one deadline and
an explicit round bound. Structural equality/extensionality, array-valued UF
parents, proof logging for activated ROW, and a policy change for the EVM
frontend remain later decisions.
