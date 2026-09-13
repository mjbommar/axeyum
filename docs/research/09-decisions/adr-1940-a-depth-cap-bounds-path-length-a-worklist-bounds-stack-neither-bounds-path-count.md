# ADR-1940: A depth cap bounds path LENGTH, a worklist bounds STACK, neither bounds path COUNT

Status: accepted
Index-summary: A branching term walker over a `let`-shared DAG costs the number of root-to-leaf PATHS; a depth cap and an explicit worklist each fix a different failure and leave that one untouched, so only a memo counts as protection.
Index-status: accepted
Date: 2026-09-12

## Context

A term arena interns, so a `let`-bound name that is referenced twice is one
node with two parents. A walker that recurses into both children of a binary
operator therefore visits that node once per **path**, not once per node. On a
chain of `d` doublings the arena holds `d + 2` nodes and the walk makes `2^d`
calls.

Three instances came before: `dpll_t::Abstractor` (`c4046c2d6`),
`dpll_lia::ArithAbstractor` (`8860e2a60`) and
`term_identity::identity_normal_form`
([ADR-1936](adr-1936-a-gap-census-reports-attempts-and-marks-an-unfinished-dispatch-unclassified.md)).
**Seventeen more were memoised for this ADR**, across ten modules, and two more
are named below that no memo can fix.

What makes it worth an ADR is not the count. It is that **three standard,
locally correct defences were in place across these sites and not one of them is
a defence against this**:

| defence | what it bounds | sites carrying it |
|---|---|---|
| `depth > 256` / `depth > 1024` | path LENGTH | `lin_form`, `interval_of`, `affine_in`, `accumulate_max_abs` |
| explicit worklist (recursion removed) | STACK | `lra::IntCollector::linearize`, `dl_online::ScanState::linear`, `lia_online::IntRowBuilder::linearize` |
| step counter + deadline | WALL CLOCK, after the fact | `dl_online::ScanState::linear` |
| a `HashMap` cache on the LEAVES | leaf re-materialisation | `abv::RowCtx::memo`, `qinst_egraph::collect_vars`'s `seen` |

The last row is the one that reads most like protection, and it is covered
separately below.

### The measurement

One file family, `(let ((v0 (+ x 1))) (let ((v1 (+ v0 v0))) … (<= v_d 100)))`:
`d + 2` distinct arena nodes, `2^(d+1)` root-to-leaf paths. Release binary, one
pinned core.

| depth | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 30 | 36 | 40 |
|---|---|---|---|---|---|---|---|---|---|---|
| before | 0.33 s | 0.65 s | 1.31 s | 2.61 s | 5.13 s | 10.41 s | unknown | unknown | unknown | unknown |
| after 4 of the route's 7 | — | — | — | 0.28 s | 0.55 s | 1.07 s | 2.13 s | 7.51 s | 18.0 s | 18.0 s |
| after all 7 on the route | — | — | — | 0.01 s | 0.01 s | 0.01 s | 0.01 s | 0.01 s | 0.01 s | 0.01 s |
| z3 4.13.3 | — | — | — | — | — | 0.04 s | 0.05 s | 0.05 s | — | 0.04 s |
| cvc5 1.3.4 | — | — | — | — | — | 0.04 s | 0.04 s | 0.03 s | — | 0.03 s |

A clean factor of two per level in the first row, and the `unknown` at depth 27
is a query both references decide in 40 ms.

### Why the existing guards are not guards

**A depth cap bounds path LENGTH.** `lin_form`, `interval_of` and `affine_in`
each opened with `if depth > 256 { return None; }`, and `accumulate_max_abs`
with `depth > 1024`. At sharing depth 30 every one of the `2^30` calls sits at
depth ≤ 30. The cap is live code, it is correct for the failure it was written
for (a pathologically deep term overflowing the stack), and it fires zero times
on the instance that kills the query.

**An explicit worklist bounds STACK.** This is the sharper half.
`lra::IntCollector::linearize` and `dl_online::ScanState::linear` had **already
been converted** from recursion to an explicit worklist, each carrying a comment
headed *"Why this is an explicit worklist and not native recursion"* and citing
the stack overflow it fixed (`fcc8760d`). The conversion is real and the comment
is true. But an `Enter(t)` pushes both operands, so the number of *work items*
is still the number of paths. The walk no longer dies at depth 3,000; it still
costs `2^30` at depth 30.

Recursion-to-worklist is the textbook remedy for the *other* deep-term failure,
it leaves this one exactly where it was, and the comment explaining it is what
makes the function read as already handled. That is the trap worth naming.

**Fixing most of them is not fixing it.** Seven of the eleven sit on the route
this one query takes, and four of those seven were fixed first. Removing those four moved the cliff by ONE level (row 2 above), because
the cost is a product of doubling factors and four fewer of them is one more
level. A profile taken at that point put the fifth,
`dl_online::ScanState::linear`, at 61.5% of samples, burning
`dl_probe_budget(24 s)` — 18.01 s at every depth from 33 to 40, the flat row
that looks like a plateau and is a budget.

## Decision

1. **A branching walk over `TermId` is protected by a memo keyed on `TermId`, or
   it is not protected.** A depth cap, a node cap, an explicit worklist, a step
   counter and a deadline each bound something else. State in the memo's doc
   comment what it is keyed on and what it is scoped to.

2. **The memo carries an expansion counter and the test asserts the COUNT.** A
   wall-time assertion on a shared box is a coin flip. With the memo the walk is
   linear in distinct nodes, so the counter stays within a small multiple of the
   arena's node count; without it the same input makes `2^d` calls.

   **And the count guard's DEPTH is chosen so the mutation fails FAST.** This is
   not a detail; the first version of
   `lin_form_expands_a_shared_dag_once_per_node` was written at depth 30, and
   when the mutation was actually run — deleting the `memo.map.get` early return
   — the test did not fail. It ran, for ten minutes, until it was killed.
   Asserting a count bought nothing while the depth still made the failure slow.
   At depth 22 the same mutation fails it in **7.54 s** with `expanded 16777215
   nodes for a 25-node DAG`, against a bound of 64. A guard that can only fire
   after an hour is a timeout, not a guard — so pair a fast COUNT guard with a
   slow VERDICT guard, and give them opposite depths on purpose.

3. **A memo's scope is part of its correctness and is written down.** Several of
   the seventeen here are narrower than the arena: `IntervalMemo` and `MaxAbsWalk`
   are valid only while `bounds` is unchanged and are created after its fixpoint;
   `AffineMemo` entries name one variable `v` and live inside one
   `derive_var_bound` call; `IntCollector`'s memo dies with the call because
   `index_of` appends to a `touch_log` whose per-literal order is load-bearing.
   A memo hoisted one level further out in any of those three is wrong.

4. **The end-to-end guard asserts the VERDICT, at a depth that cannot finish
   without the fix.** `shared_let_chain_of_depth_40_is_decided` is `2^41` paths:
   unmemoised it does not return, and the assertion is `sat`, not "it returned".

5. **A census of this shape is a lead generator and is reported as one.** A
   source scan for branching `TermId` walkers with no memo token returned **164**
   candidates at `a25e98639` and 152 after this lane. That is not 164 bugs and
   was never quoted as one. Reachability is a separate, measured question
   (below), and the scan's own blind spots are stated with it.

6. **The instrument for triage is a repro FAMILY, not the scan.** One
   `let`-doubling chain per operator class, swept to the depth where it stops
   being flat, with `perf` on every family that doubles. A family that doubles
   NAMES a live instance and the profile names the function. Over 28 families in
   13 logics this found the instances the scan could not have ranked and the two
   it could not see at all. Final state on the shipped binary: **26 of 28 flat
   to depth 32**, and the two that are not are named below.

## Consequences

### What a scan for this can and cannot see

The first scan written for this counted free-function self-recursion and
explicitly excluded a dot-preceded call. It returned 132 candidates and **missed
both instances that dominated the profile**: `lra::IntCollector::linearize` is a
method (`self.linearize(`), and `dl_online::ScanState::linear` is not recursive
at all. A scan that cannot see a worklist cannot see the form of this defect
that has already survived one round of hardening — which is the form most likely
to be left in place. The corrected scan counts three shapes (free recursion,
`self.` recursion, `while let Some(_) = v.pop()` with ≥ 2 pushes) and finds 164
at the base commit.

Three blind spots are demonstrated, not hypothesised:

1. `self.name(` method recursion — the original regex excluded it.
2. An explicit worklist — no self-call exists to count.
3. A recursion inside `for arg in args { … }` — ONE textual call site that
   branches at runtime. `accumulate_max_abs` is exactly this, and no version of
   the scan lists it; it was found by reading the route the repro took.

So a census of this shape is a floor on the candidate count and gives no
ordering. The ordering comes from the family sweep plus `perf`.

### Real-corpus reachability is narrow, and the fix is priced accordingly

Deep `let` nesting is common; this blowup is not, because it needs each level
referenced at least **twice** along an arithmetic spine. Measured by computing
the exact quantity that governs the walk — `paths(n) = Σ paths(arg)` over
`+`/`-`/`*`, with `let`-bound names resolving to the bound term's value:

| population | files scanned | `let` depth ≥ 25 | `+ - *` paths ≥ 2^20 | max |
|---|---:|---:|---:|---:|
| QF_LIA, whole division | 12,422 of 13,306 | 3,448 | **0** | 39,800 |
| QF_LIA, 200-file board slice | 200 | 55 | **0** | 128 |
| QF_UFLRA, board slice | 197 | 112 | **0** | 36 |
| QF_NRA, board slice | 200 | 46 | **0** | 158,100 |
| QF_NIA / QF_SLIA / QF_UF / QF_UFLIA / QF_IDL slices | 997 | 56 | **0** | ≤ 374 |

Over `and`/`or` spines the picture is the same except in one family: QF_IDL's
`Averest` sorting benchmarks, where `BubbleSort_safe_blmc016.smt2` carries
**8,394,292** and/or paths in 1.4 MB of source — genuine sharing amplification,
not size. Both arms decide it `unsat` in 3.6 s, so even there it is not a cliff.

Two caveats on the metric, because a number without them is misleading.
`max_paths` equals the LEAF COUNT for an unshared spine, so a large value alone
is not blowup — blowup is paths ≫ nodes, and the QF_NRA 158,100 and QF_LIA
39,800 rows are wide flat sums. And the analyser saw 12,422 of QF_LIA's 13,306
files: 47 exceeded its own 20 s per-file budget and the rest were oversized. It
reports them rather than dropping them, because a tool that omits rather than
refuses turns its output into a measurement of the accepted subset.

So this is robustness, not board points: it removes a cliff that a competition
generator or an adversarial input reaches trivially and that today's public
corpora do not. Say that, rather than claiming the fix converts files.

### "No memo can fix this" is a claim, and one of mine was false

Two instances were first reported as output-exponential and therefore not memo
bugs. One of those reports was **wrong, and written without reading the
function**. `abv::RowCtx::abstract_with_array_eq` is a plain structural rebuild,
`TermId -> Option<TermId>`, over an arena that interns — the output is a DAG of
the same size and the exponential is the walk. Memoised, its family went from
4.60 s at depth 30 and doubling to **0.13 s flat to depth 32**.

That is worth recording next to the decision, because "this one is structurally
different" is the most comfortable way to leave an instance in place, and it
reads exactly like the depth cap and the worklist do. The discriminator is
cheap: does the function RETURN a rebuilt term over an interning arena
(memoisable), or does it PUSH one entry per leaf reached into a flat list
(not)?

Two genuinely are not memo bugs:

- `term_walk::collect_top_binary_conjuncts` (61.8% of the `bool_and` family).
  Its contract says it *"deliberately preserves duplicates"*, so `(and v v)`
  over a depth-29 shared DAG genuinely has `2^30` leaves.
- `qinst_egraph::collect_app_candidates` (18.9% plus 68% allocator on
  `quant_lia`, after the `collect_vars` beneath it was memoised). It pushes one
  `(term, indices)` entry per PATH, so the same trigger candidate appears many
  times in `out`.

A visited set would dedupe both outputs, which is a change to what the consumer
sees — a decision about the contract and its call sites, on a Boolean-structure
route and a quantifier-trigger route respectively. This ADR does not cover them;
they need their own evidence.

### A third instance of one specific confusion

A LEAF cache is not a walk memo, and it has now been mistaken for one three
times: `dpll_lia::ArithAbstractor::atom_of` (cached atoms, `8860e2a60`),
`abv::RowCtx::memo` (cached select sites, keyed `(base, index)`), and
`qinst_egraph::collect_vars`'s `seen` (a set of SYMBOLS). Each stops a leaf
being re-materialised and does nothing about the structure above it, which is
where the sharing lives — and each made the enclosing function LOOK cached. When
a walk has a `HashMap` in it, check what the key is.

### Related

- [ADR-1936](adr-1936-a-gap-census-reports-attempts-and-marks-an-unfinished-dispatch-unclassified.md)
  — the same shape in `term_identity::identity_normal_form`, and why a census
  taken through a hung rung measures the dispatcher.
- [ADR-1927](adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md)
  — a rung's refusal is not the query's verdict.
