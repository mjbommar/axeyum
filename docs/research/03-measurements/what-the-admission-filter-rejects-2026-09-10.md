# What the admission filter rejects

**Date:** 2026-09-10
**Lane:** Q3-admission
**Follows:**
[`why-the-instantiation-loop-produces-nothing-2026-09-10.md`](why-the-instantiation-loop-produces-nothing-2026-09-10.md),
category D — the rows where the join found candidate substitutions and nothing
was admitted.
**Population:** `bench-results/parity-losses-20260908/UF.txt` — the 32
declared-status UF files we return `unknown` on and z3 refutes.
**Method:** `AXEYUM_QPROBE=1 AXEYUM_QPROBE_CENSUS=1 target/release/examples/axeyum_cli
<file> --timeout-ms 24000`, one at a time, tree at `d1b4aa5df`.
**Instrument:** `AdmissionCensus` in `crates/axeyum-solver/src/qinst_egraph.rs`
(`ddc21503e`, `d1b4aa5df`).

## The headline

**Category D is not an admission filter making a bad decision. It is four
different things, and the two largest are not filters at all.**

Every rejection point between a joined witness tuple and a term in `ground` now
carries a counter. Across the 32-file slice, 655 of 16,195 per-universal rows
are category D, and every one of them is now attributed:

| dominant reason | rows | share | what it is |
|---|---:|---:|---|
| `rej_unreleased` | 349 | **53.3%** | classified into the deferred pool, which was never released this round |
| `rej_dupother` | 167 | **25.5%** | another universal produced the identical instance term first — **not a loss** |
| `rej_nocontext` | 43 | 6.6% | a non-asserted registration with no replacement context |
| `rej_true` | 39 | 6.0% | `ClauseValue::True` — the shipped entailment filter |
| `rej_flood` | 28 | 4.3% | `budget_flood_slice` truncation |
| `rej_ceiling` | 22 | 3.4% | the admission walk hit `MAX_GROUND_TERMS` |
| `rej_handoff` | 6 | 0.9% | a registration handed to the Slice-3 discovery driver — **not a loss** |
| `rej_seen` | 1 | 0.2% | the identical term was already admitted |
| *unexplained* | **0** | 0.0% | |

Three of the eleven buckets are **zero across the entire slice**:
`rej_expired` (the round deadline never truncated a materialization),
`rej_subst` (`replace_subterms` never refused), and `rej_check`
(`check_quantifier_ground_derivation` never refused a certificate). The
certificate checker — the one filter here that is soundness-critical — declines
nothing on this population. It is not the cause of anything.

The same table by tuple mass rather than by row, because a row is one universal
and a universal can join tens of thousands of tuples:

| reason | tuples | share |
|---|---:|---:|
| `rej_unreleased` | 61,376 | 35.3% |
| `rej_dupother` | 52,722 | 30.3% |
| `rej_flood` | 18,576 | 10.7% |
| `rej_nocontext` | 14,804 | 8.5% |
| `rej_handoff` | 11,465 | 6.6% |
| `rej_true` | 8,953 | 5.1% |
| `rej_ceiling` | 4,981 | 2.9% |
| `rej_seen` | 1,034 | 0.6% |

## Two of the buckets are bookkeeping, not loss

**`rej_dupother` (25.5% of rows, 30.3% of tuple mass) is the census reporting on
the census.** `collect_generated_ground` keys its `derivations` map by
**instance term** and is first-writer-wins. When two universals materialize the
same instance in one round, the second one's certificate is discarded and every
downstream count for that term is credited to the first. The instance is
admitted. The second universal reads `joined>0 admitted=0` and looks starved.

The fixpoint report has always had this collision — it resolves a universal with
`position(|q| q.assertion == certificate.assertion)`, which is also
first-wins — so the census inherits it deliberately rather than disagreeing with
the column printed beside it. What the census adds is that the collision is now
*visible* instead of appearing as an unexplained drop. Before the bucket existed,
121 of 894 D rows had every rejection counter at zero.

The related caveat the probe now prints: **238 universals on this slice share an
assertion term with an earlier universal** (`shared_assertions=`). Their
downstream counts land on the earlier one.

**`rej_handoff` (0.9%) is also not a loss.** A registration with a
positive-replacement context hands its tuples to the Slice-3 discovery driver,
which admits the owner formula with the universal replaced. The tuple did its
job under another name.

Removing both leaves category D at roughly **three quarters** of its nominal
size.

## The dominant real cause: the deferred pool is gated on urgent traffic

`admit_next_source_batch` admits conflict and unit instances first, then:

```rust
let mut admitted = admit_generated_ground(/* urgent + units */);
if admitted.is_empty() {
    /* ... release the deferred pool ... */
}
```

The comment reads *"Once urgent traffic is exhausted, release unresolved clauses
so mutually constraining instances preserve the legacy loop's reach."* The
intent is a **delay**: a held-back candidate is re-materialized and
re-classified every later round, so nothing is dropped.

**On this population it is not a delay. It is a permanent exclusion inside the
budget**, and the per-file release counts are why:

| file | fixpoint ground | deferred releases in the whole run |
|---|---:|---:|
| f02 | 8192 | **1** |
| f12 | 8192 | **1** |
| f23 | 8192 | **1** |
| f24 | 8192 | **1** |
| f26 | 8192 | **1** |
| f01 | 8192 | 3 |
| f19 | 8192 | 3 |
| f11 | 8109 | 32 |
| f15 | 8192 | 33 |
| f31 | 424 | 212 |

On the large files the deferred pool is offered **once**, at the terminal
fixpoint, by which point `MAX_GROUND_TERMS` is already consumed — which is
exactly why `rej_ceiling` appears as a *secondary* count in 369 of the 655 D
rows while dominating only 22. The two interact: the priority gate defers a
candidate until the ground cap has made it unreachable. **23 of the 28 files
that reach a fixpoint end at ground = 8192.**

`f31` (`UF/sledgehammer/TypeSafe/smtlib.1098821.smt2`) is the contrast: ground peaks at 424, urgent
traffic runs dry every round, the pool is released 212 times, and its
`rej_unreleased` is zero.

### Was the rejection right?

Measured, not argued. `AXEYUM_QINST_RELEASE_DEFERRED=1` is an off-by-default
experiment arm that releases the deferred pool in the *same* round as urgent
traffic. Run on the whole 32-file slice under identical conditions:

| arm | decided | files |
|---|---:|---|
| shipped, probe on | 1 of 32 | `Hoare/smtlib.1116374` |
| shipped, **no probe** | 1 of 32 | same |
| released, probe on | **3 of 32** | + `coinductive_list/x2015…2416479`, `Fundamental_Theorem_Algebra/uf.974621` |
| released, **no probe**, run 1 | **3 of 32** | same two |
| released, **no probe**, run 2 | **3 of 32** | same two, file-for-file identical |

**Two files flip to `unsat`. Nothing is lost — no file goes the other way, in
any arm.** The flip holds with the census off, so it is not an artifact of
probing, and it repeats exactly across two independent runs, which matters on a
loop this sensitive.

The two files are
`UF/20170428-Barrett/cdt-cade2015/nada/afp/coinductive_list/x2015_09_10_17_09_42_195_2416479.smt_in.smt2`
and `UF/sledgehammer/Fundamental_Theorem_Algebra/uf.974621.smt2`.

**So the rejection was wrong, on this population, and the fix is a priority
change rather than a bigger budget.** That is the distinction category D was
separated out for: unlike a cap, this is a decision made per round, and making
it differently decides files.

### The loss direction, and what it does NOT cover

Both gates run with the flag forced on:

| gate | tests | result |
|---|---:|---|
| `--test corpus_regression --features full` | 2 | green (control also green) |
| `--test progress_frontier --features full -- --test-threads=1` | 12 | green (control also green) |

**`corpus_regression` cannot detect this class of loss and must not be quoted as
if it could.** `corpus/regression/` skips `unknown`, so a file going
`unsat → unknown` stays green — the exact hole
`tests/quant_skolem_egraph_routing.rs` was written to close for the previous
finding. The capability ratchet is the gate that can see it, and it is the one
to trust here.

**Not run:** any measurement of the flag over a corpus wider than these two
gates and the 32-file slice. The population that would settle a shipping
decision is every UF/UFLIA benchmark we currently decide, and that did not run.
Reported as did not run, not as absence of loss.

## The entailment filter is 94.5% free and 5.5% not

The brief asks specifically whether a `ClauseValue::True` drop is the good kind
of redundant or the bad kind. The two are separable mechanically.

`IncrementalEmatchSession::equality` returns `Undetermined` for any term it has
not registered. So a clause is normally only `True` over terms the e-graph
already holds — and dropping such an instance costs nothing twice over: the
ground conjunction already entails it, so the final refutation check cannot
weaken; and it introduces no term, so no later trigger loses a match.

But the classifier has two **term-blind** routes to `True`: a syntactic `t = t`
(returned before any registration lookup), and a disjunction made true by one
literal, which says nothing about the other literals' terms. A drop on those
routes is still entailed — it still cannot help the refutation — but it *does*
cost the loop a term it might have matched a trigger against.

Measured over the slice: **760,070 entailment drops, of which 41,758 (5.5%)
contain a term the e-graph has never registered.**

So: the redundancy is overwhelmingly the correct kind. 94.5% of the filter's
work is provably free. The remaining 5.5% is not a lost *clause* — the ground
set already entails it — it is a lost *term*, and it belongs to the
term-availability question (category B of the previous measurement), not to the
admission question. **DO NOT rebuild the entailment filter.** If the 5.5% is
worth anything it is worth it as a term source, next to
`invent_starved_trigger_terms`, which already exists for exactly that job.

## Re-measured: the three flood constants

`scripts/check-config-registry-staleness.py` flags `FLOOD_THROTTLE_MIN_GROUND`,
`FLOOD_ROUND_ADMISSION_CAP` and `FLOOD_EAGER_GENERATION_MAX` as resting on a
2026-08-01 measurement that predates `d910fa590` and `09e9cffab` (2026-09-09).
Neither commit changed a **value**; both reorganised the code that consumes
them into `RelevancePolicy` / `budget_flood_slice`. The checker's instruction is
to re-take the measurement, not to move the date, so here it is, on the current
tree and on this population:

| | measured 2026-09-10 |
|---|---|
| deferred pool releases, whole slice | **878** |
| of those, at or past `FLOOD_THROTTLE_MIN_GROUND` (2048) | **262** (29.8%) |
| of those, also past `FLOOD_ROUND_ADMISSION_CAP` (256), so the slice acted | **243** |
| files whose throttle ever engaged | **25 of 32** |
| candidates kept eagerly at generation ≤ `FLOOD_EAGER_GENERATION_MAX` (1) | **96,631** |
| deeper-generation candidates ranked and truncated | **396,202** |

Read: the throttle sees **70.2% fewer releases than exist** — most of this
population's deferred releases happen below ground = 2048 and are the historical
dump-everything admission. Where it does engage it almost always acts (243 of
262). The eager exemption covers **19.6%** of what the slice classifies, so
`FLOOD_EAGER_GENERATION_MAX = 1` is protecting a fifth of the flood-regime
traffic from the cap, not a rounding error.

## Method notes, including one that refutes a number in the previous document

**The census does not perturb the loop.** It is gated on a *second* environment
variable, `AXEYUM_QPROBE_CENSUS`, precisely so `AXEYUM_QPROBE=1` alone keeps
reproducing the historical probe and the two can be differenced. Same tree, same
box, same 32 files, one at a time:

| | A | B | C | D | E |
|---|---:|---:|---:|---:|---:|
| `AXEYUM_QPROBE` only | 4.3% | 68.5% | 9.6% | 4.5% | 13.0% |
| with the census | 4.5% | 69.0% | 8.3% | 4.0% | 14.2% |

**But those shares do not match the previous document's**, which reported
A 4.6% / B 41.1% / C 25.5% / D 15.6% / E 13.1% on the same 32 files. The census
is not the cause — the control arm above rules it out. Two candidates remain,
and the first is confirmed:

1. **The tree moved.** That document reports the slice at **0 of 32** decided
   and describes `318930806` as the fix that takes it to 1 of 32. Every run
   here decides **1 of 32** (`Hoare/smtlib.1116374`). So its table was measured
   *before* the fix the same document announces.
2. **Run conditions.** It ran four at a time; these runs are serial. A join that
   returns `None` from an internal deadline check is scored as *starved*, so
   contention inflates category C at B's and D's expense. Not isolated here —
   listed as the remaining candidate, not as a finding.

**Row counts move ±25% run to run**; shares do not. Four runs of the same 32
files gave 20,613 / 19,253 / 18,782 / 16,195 rows with A between 4.3% and 4.5%,
D between 4.0% and 4.6%. **Quote the shares, never the row counts**, and do not
compare an absolute D count across runs.

**`starved_joins` and `joined` are different units** in the shipped probe:
`joined` counts tuples, `starved_joins` counts *rounds*. The A–E classification
compares them, so it is a comparison across units. Left as it is here so the two
documents' buckets remain the same buckets, but it is a real defect in the
classifier.

**Another lane was building on this box during the experiment arm.** Row counts
are load-sensitive; verdicts are not, and verdicts are what the experiment turns
on.

## What to do next

1. **Ship the deferred-pool release as a policy decision, not this flag.**
   `AXEYUM_QINST_RELEASE_DEFERRED` is an experiment switch, and an environment
   variable is the wrong home for an admission policy — `RelevancePolicy`
   already exists as the object that owns exactly this kind of choice
   (`d910fa590`). The measured behaviour is worth +2 of 32 with no measured
   loss; the route in is a `RelevancePolicy` field with an arm, so the A/B is
   reproducible from a test rather than a shell, and a wider corpus run before
   the shipped arm changes.

2. **Do not rebuild the entailment filter.** 94.5% of its drops are provably
   free. Its 5.5% term-introducing tail is a term-availability question and
   belongs next to `invent_starved_trigger_terms`, not here. **DO NOT BUILD** a
   smarter `ClauseValue::True` test.

3. **Do not treat `rej_dupother` as a loss.** A quarter of category D by row and
   30% by tuple mass is one universal being credited for another's identical
   instance. Any future work that reads `admitted=0` per universal — including a
   fairness or scheduling change — has to subtract this first or it will chase a
   number that is not describing what it appears to describe.

4. **Fix the classifier's unit mismatch before the next slice of this work.**
   `joined` counts tuples and `starved_joins` counts rounds, and the A–E
   buckets compare them. Category C and category D are separated by a
   quantity measured in different units from the one that defines them.

5. **Re-measure the previous document's A–E table on the current tree.** Its
   B/C/D shares were taken before `318930806`, which the same document
   announces. The headline (86.6% of rounds admit nothing) survives — this run
   gives 85.8% — but the four-way split that the next three work items are
   prioritised from does not.
