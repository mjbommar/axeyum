# ADR-0087: Candidate-Triggered Retained Warm ROW

Status: accepted
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

`IncrementalBvSolver` will retain one exact transitive scalar summary for each
observed structural read, but leave that summary dormant until a SAT candidate
violates it.

- The initial warm CNF contains scoped user roots, existing valid congruence
  lemmas, and previously activated structural summaries. A newly retained
  structural owner is otherwise an unconstrained scalar input.
- Admission expands the bounded store/constant/array-ITE dependency cone into
  one scalar summary and abstracts only its direct array-symbol leaves and
  scalar UF applications. Intermediate structural parents do not receive
  separate CNF definitions unless they are independently observed by a user
  root. The expansion is retained as IR metadata and is not lowered yet.
- After SAT, reconstruction supplies every lowered private owner. Private
  owners not yet present in the AIG receive their sort's deterministic
  well-founded default, producing a total candidate extension.
- The solver evaluates every currently active retained structural summary in
  stable term-ID order. All summaries false in that candidate are lowered and
  asserted permanently as one deterministic batch. The same incremental CNF
  and BatSat instance then solve again under the same frame and one-shot
  selectors.
- A structural summary is activated at most once. The existing 512-node and
  256-depth admission limits remain exact; refinement performs at most 512
  candidate-activation rounds. Exhausting that limit degrades to a resource
  `Unknown` rather than accepting a partially checked model.
- The user timeout becomes one absolute deadline shared by initial SAT,
  candidate evaluation, definition lowering, and every resumed SAT call. A
  resumed call receives only the remaining duration.
- Only structural summaries reachable from active frame roots or the current
  one-shot assumptions are checked. Definitions activated by an earlier scope
  remain harmless permanent lemmas, but inactive pending definitions do not
  create new work.
- Array model projection remains leaf-only. A SAT result is returned only after
  all active structural summaries hold in one candidate, direct leaf arrays and
  scalar function tables are projected, and every original active assertion and
  one-shot assumption replays successfully.

The transitive summary is the recursive closure of the ADR-0086 equations:

```text
expand(select(const(v), j))       = v
expand(select(store(a,i,v), j))   = ite(i = j, v, expand(select(a,j)))
expand(select(ite(c,a,b), j))     = ite(c, expand(select(a,j)),
                                           expand(select(b,j)))
expand(select(symbol, j))         = retained_leaf_owner(symbol, j)
```

For observed read `t` with owner `r_t`, the one dormant equation is
`r_t = expand(t)`. This preserves structural ownership and warm reuse while
avoiding the repeated SAT resumes and per-parent equalities of the initial
one-step prototype.

## Soundness Argument

The initial formula is a relaxation of the exact definitional extension: fresh
structural owners may take arbitrary scalar values. Therefore UNSAT before all
summaries are active transfers directly to the original query. Every later
refinement adds only a valid total array identity, so UNSAT after refinement
also transfers and existing learned clauses remain valid.

For SAT, deterministic defaults merely complete otherwise absent private
variables for the purpose of testing summaries; they are not projected as user
values. A candidate is eligible for projection only when every active retained
summary evaluates to true under one total extension. Induction over the bounded
expansion equates each observed structural owner with the corresponding array
read. Leaf projection realizes direct array observations, and original-term
evaluator replay remains the final acceptance gate. Missing defaults, failed
equation evaluation, exhausted bounds, or failed replay cannot produce an
accepted SAT result.

Permanent activation is scope-safe because a definition constrains only a
private owner to the denotation of its source read; it does not assert any user
root. Failed-assumption cores remain sound: a relaxed-formula core is sufficient
for the stronger exact query, while an activated definition is unconditional
and valid independently of every selector.

## Acceptance Validation

Accepted on 2026-07-10 in `3977f78b` after the required routes passed:

- ten all-feature mechanism/differential tests cover zero-activation replayed
  misses, violated-hit activation, transitive nested-store closure in one
  candidate round, constant/ITE/Bool summaries, push/pop with inactive pending
  metadata, reasserted leaf dependency closure, opposite one-shot assumptions,
  core soundness, zero-timeout classification, and exact node/depth admission;
- the existing eight-shape matrix over 64 seeds remains clean across warm,
  `check_auto`, and direct Z3 routes: 192 comparisons, zero disagreements, and
  every warm SAT model replayed;
- all 816 solver units, 77 symbolic-execution tests, the complete EVM suite and
  its four differential fuzz gates, strict all-target/all-feature clippy,
  warning-denied rustdoc, links, foundational resources, and the exact-SHA
  compile/format/corpus/unit gate pass;
- release EVM remains DISAGREE=0 over 18 cases. At depth 32, candidate-triggered
  transitive summaries take 11.257 ms versus ADR-0086's 30.933 ms, a 2.75x warm
  improvement. Frontend ITE folding still wins at 0.405 ms, so the EVM default
  correctly remains unchanged.

## Alternatives

### Keep observation-time permanent definitions

Rejected as the next increment because the depth-32 measurement is roughly 84x
slower than frontend folding after the one-shot-dispatch cost has already been
removed.

### Activate candidate-violated one-step parent equations

Rejected after implementation and measurement. It is sound, but a depth-32
UNSAT safety query eventually activates the whole chain over repeated SAT
resumes and measured 51.432 ms, worse than ADR-0086's 30.933 ms. One transitive
summary per observed root measured 11.257 ms and preserves the same candidate-
triggered, permanent-valid-lemma contract.

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
avoid all structural summary CNF; violated paths pay only for summaries that
have demonstrated relevance, and that payment is reused by later checks.

The final-check loop becomes multi-solve and must account for one deadline and
an explicit round bound. Building a transitive summary retains bounded scalar
expansion work in the arena, but defers its expensive lowering/CNF cost and
avoids separate intermediate owners. Structural equality/extensionality,
array-valued UF parents, proof logging for activated ROW, and closing the
remaining EVM performance gap remain later decisions.

## Subsequent Decision

[ADR-0088](adr-0088-retained-warm-array-valued-uf-parents.md) closes the scalar-
keyed array-valued UF-parent part of that residual. Applications retain private
array owners, observed reads receive conditional argument/index congruence, and
concrete-equal keys project one full-value result before owner filtering and
original replay. ADR-0089/0090 add structural equality/extensionality, ADR-0091
adds relation flags, ADR-0092 adds direct array-valued UF parameters, and
ADR-0093 adds supported structural array-valued UF parameters. Nested
array-valued application keys, proof logging, and the EVM performance gap
remain.
