# ADR-2114: the model finder is not what cannot represent datatypes — the GROUND closure is, and the message names the wrong engine

Status: accepted
Index-summary: [ADR-2090]'s `AUFDTLIRA` give-up census recorded **17 "mbqi declined an unsupported DATATYPE fragment"** and named that as the reason the division's model finder never gets to build a model. **The premise does not survive the control.** Traced over **134 files** (the 55 ADR-2090 cores plus the 79 undecided originals, 24 s, pinned cores on an idle s7, `AXEYUM_QPROBE` throughout): MBQI's refutation loop **did not run on 132 of 134**, and on **127** the reason is a purely syntactic quantifier shape guard that mentions no datatype (125 of them `nested-binder-in-matrix` and/or `quantifier-below-top-level`, 2 `multi-binder-prefix`) — SPARK VCs are alternating and non-prenex, and the rung takes only single-binder prenex. 17 rows do print a datatype wording, and on **16 of 17** MBQI's loop had already been bypassed: the sentence is produced by a ground sub-solve inside e-matching (`decide_instantiation`, `auto.rs:13388`) and acquires its "mbqi declined" prefix at `auto.rs:2473`. **The control refuses the datatype reading of that**: the loop also did not run on **116 of the 117** rows with NO datatype wording, so "MBQI never got to build a model" is a fact about the ladder, not about datatypes; the narrow claim that survives is that the message names an engine that did not produce it. Constructs are classified by SORTS, not names (`field_sort_expands`/`datatype_expansion_is_exact` are invisible in a `declare-datatypes` form), 134 of 134 joined, **38 disagreements all one way** ("predicted a refusal, observed none" — the ladder ended before the Ackermann pass) and **0** the other. Two buckets: `W1` refuses a field sort, and that sort is `(Array Int <datatype>)` on **86 of 86** occurrences; `INEXACT` is a datatype-typed field at a UF boundary. The reference: z3 refutes **44 of 55 cores GROUND** (both quantifier engines off) and **MBQI decides 0 of 55**; on the 13 datatype-refused rows **12 of 13 are GROUND**, so the gap is real and quantifier-free. z3's model finder contains **zero** occurrences of `datatype`/`constructor` (control `sort`=68) and builds **no universe** — measured, not only read: `-v:10` under `smt.ematching=false` emits 0 universe/model-finder lines across all 13, against a non-vacuous control of 27 to 47,758 total lines. **No datatype lever is built**: the wording is the printed blocker on 13 of 55 CORES but only **4 of the 79 undecided ORIGINALS** — a reference-minimised core population over-reports this bucket by more than 3×, which no census in `bench-results/` currently distinguishes — and the 13 split across two designs while 127 of 134 die upstream of any theory question. What ships is the mislabelled sentence, corrected as a byte-identical-prefix suffix so the four committed censuses that read it keep working, with 4 tests and a 4-guard mutation suite (first three measured: **each killed exactly one test, three different ones**; `--check-anchors` `suites=141 anchors=1069 stale=0`). §4 names and sizes the representation the `INEXACT` bucket would need — recursive tag/field expansion to the datatype's own nesting depth, terminating because **0 of 134 files declares a recursive datatype and the deepest nest is 5** — so the next lane need not re-derive it.
Index-status: accepted
Date: 2026-09-15

## Context

[ADR-2090] censused the minimal unsat cores of all seven Tier 1 divisions and
found `AUFDTLIRA` running opposite to intuition: it has the **cleanest core
shape in the population** — 54 of 55 cores carry the negated goal, median
`minimal` 2, median `suffix_need` 11 — and the **second-worst ceiling at 3 of
55**. Its give-up census recorded, among the 193 rows we fail on,

    17  mbqi declined an unsupported DATATYPE fragment (three distinct wordings)

and this lane was dispatched to find, per core, which construct triggers that
decline, what z3's model finder does with the construct, and what the minimal
thing we would have to represent is.

**The premise does not survive measurement.** MBQI does not decline a datatype
construct. On the cores that print those wordings, MBQI's refutation loop
mostly never runs at all, and the sentence is produced by wrapping an error
that came back from the **quantifier-free** closure.

## Decision

**The `AUFDTLIRA` datatype decline is a GROUND-closure refusal wearing a
quantifier engine's name, and no datatype lever is built.**

Three things are decided here.

1. **The give-up sentence is corrected in place.** `mbqi declined an
   unsupported fragment: …` now carries a note when MBQI's refutation loop
   never ran, which is **16 of the 17** rows that print it. The sentence up to
   and including the original message is byte-identical, so the four committed
   censuses that read it keep working.
2. **No datatype capability lever is built**, on [ADR-2090]'s own rule. The
   bucket is real and the reference confirms it is ground-convertible (§5), but
   it is **4 of the 79 undecided originals**, it splits across two different
   designs, and it sits behind a shape guard that stops 127 of 134 files before
   any theory question is asked.
3. **The representation is named and sized anyway** (§4), because the next lane
   should not re-derive it: recursive tag/field expansion to the datatype's own
   nesting depth, reusing the child slots `unfold_traversals` already creates —
   terminating, because 0 of 134 files declares a recursive datatype and the
   deepest nest is 5.

## 1. What the message actually reports

The string is assembled in `crates/axeyum-solver/src/auto.rs`. As it stood
before §6's correction:

```rust
Err(SolverError::Unsupported(message)) => {
    refused_fragment = true;
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: format!("mbqi declined an unsupported fragment: {message}"),
    })
}
```

It wraps **any** `Err(Unsupported)` coming back from `prove_unsat_by_mbqi`. It
is not a claim that MBQI examined a datatype, and it is not a claim that MBQI
ran.

(Line numbers below are as of this ADR's own commit; §6's change moved them, so
grep the identifier rather than trusting the number if the file has moved on.)

`prove_unsat_by_mbqi_inner` (`auto.rs:12862`) hands the whole query to
`prove_unsat_by_ematching` at **five** shape guards before its refutation loop
is reached — `auto.rs:12896` `forall-arity`, `:12903`
`nested-binder-in-matrix`, `:12913` `quantifier-below-top-level`, `:12921`
`no-top-level-universal`, `:12937` `multi-binder-prefix`; the loop itself is
entered at `:12940`. And `prove_unsat_by_ematching` decides its instantiated
query with a plain ground solve, `auto.rs:13482`:

```rust
let result = check_auto(arena, &instantiation.assertions, config)?;
```

`instantiation.assertions` is quantifier-free. The `?` carries an
`Err(Unsupported)` from the ground ladder straight back out through
`prove_unsat_by_ematching` and `prove_unsat_by_mbqi_inner` to the sentence
above (`auto.rs:2488`), where it acquires the "mbqi declined" prefix.

The distinction is measurable rather than inferred, because `AXEYUM_QPROBE`
exists for exactly this — `mbqi_shape_probe`'s own doc comment (`auto.rs:12740`)
says the rung's `qtrace` line "cannot distinguish 'the MBQI refutation loop ran
and failed' from 'a shape guard fired and the call was e-matching all along'".
On
`AUFDTLIRA/…/O512-022__stacks__stacks.ads_84_58_index_check`, whose give-up
reads `mbqi declined an unsupported fragment: congruence over a datatype
argument whose expansion is not exact`:

    [mbqi-census] assertions=5 qf=1 prenex1=2 prenexN=0 nested=1 other=1
    [mbqi-shape]  exit=nested-binder-in-matrix single_binder_universals=0 ground=0

MBQI's loop never ran. The refusal is in the ground closure and the label names
an engine that did not produce it.

## 1a. And the control says how to read that

134 files traced on an idle s7 — the 55 [ADR-2090] `AUFDTLIRA` cores and the 79
undecided originals — at 24 s on four pinned physical-core pairs, sharded
round-robin so no shard is a prefix of a path-sorted list. `AXEYUM_QPROBE=1`
throughout.

| | n | share |
|---|---:|---|
| MBQI's refutation loop **did not** run | **132** | 98.5 % |
| it ran | 2 | 1.5 % |

| `mbqi_exit`, distinct | n |
|---|---:|
| `nested-binder-in-matrix` + `quantifier-below-top-level` | 44 |
| `quantifier-below-top-level` | 43 |
| `nested-binder-in-matrix` | 38 |
| `NONE` (the rung was never reached) | 5 |
| `multi-binder-prefix` | 2 |
| **`refutation-loop`** | **2** |

**127 of 134 files are rejected by a purely syntactic quantifier shape guard
that mentions no datatype.** These are SPARK verification conditions of the
form `(not (forall … (=> … (forall …))))` — alternating and non-prenex — and
`prove_unsat_by_mbqi_inner` accepts only a single-binder prenex universal.

17 of 134 rows do print a datatype wording (W1 9, W2/W3 folded 8 — exactly
[ADR-2090]'s "17", here inside one division). On **16 of those 17** MBQI's loop
had already been bypassed.

**But the control refuses the obvious reading.** On the 117 rows with NO
datatype wording the loop also did not run, **116 of 117**. So "MBQI did not get
to build a model" is a statement about the LADDER, not about datatypes: the
datatype rows are not special in that respect, and a census that printed only
the datatype half would have reported a datatype cause for a shape problem.
That is the error this lane was dispatched to commit, and the control is the
only thing that stops it.

The narrow claim that does survive the control is the one in §1: **the message
names an engine that did not produce it, 16 times out of 17.**

## 2. The construct, classified by SORTS rather than by names

The three wordings are decided by sorts, not by names:
`register_datatype` (`datatype_native.rs:1497`) refuses a field sort that
`field_sort_expands` (`:1549`) rejects, and `datatype_expansion_is_exact`
(`:1576`) — the precondition guarding the refusals at `:904` and `:963` — is
"every field sort of every constructor expands". Neither predicate is visible
in the text of a `declare-datatypes` form without resolving sort names, so a
name-matching census would measure the SPARK naming convention rather than the
refusal. `dtshape.py` parses instead, resolving `let` rather than expanding it
(CLAUDE.md records a lane's `let`-expander reaching 63.4 GB on this corpus).

The classifier agrees with the binary on the wording, and its disagreements run
one way only — 134 of 134 joined, 0 unmatched:

| predicted × observed | n |
|---|---:|
| `NONE` × `NONE` | 79 |
| `INEXACT` × `NONE` | 27 |
| `W1` × `NONE` | 11 |
| `W1` × `W1` | 9 |
| `INEXACT` × `INEXACT` | 8 |

**38 disagreements, all of them "predicted a refusal, observed none", and 0 in
the direction "observed a wording the classifier did not predict."** The 38 are
rows whose ladder ended before the Ackermann validation pass ran at all, which
is a statement about reach, not about the classifier. The asymmetry is printed
rather than summarised away, because a classifier only ever compared against
itself is the un-failable checker this repository keeps deleting.

**The two buckets, and what each one actually is.** W2 and W3 are folded: the
Ackermann validation loop checks result sort then argument sort *per function*
over a `BTreeMap`, so which of the two fires first is `FuncId` order, not a
property of the file, and a census separating them would be reporting an
iteration order.

- **`INEXACT` (W2/W3, 8 observed, 35 predicted)** — a datatype with a
  *datatype-typed field* reaching a UF argument or result.
  `datatype_expansion_is_exact` is false because `build_sym_vars`
  (`datatype_native.rs:1649`) gives such a field no expansion variable, so
  the encoded equality is a relaxation and a weaker congruence antecedent would
  be a stronger axiom — a wrong `unsat`.
- **`W1` (9 observed, 20 predicted)** — `register_datatype` refuses the field
  sort outright. Its refused sort is `(Array Int <datatype>)` on **86 of 86**
  occurrences over the 55 cores: SPARK's array-of-records, and nothing else.

**Sizing the only repair `INEXACT` could take.** Expanding a datatype-typed
field recursively, into its own tag and fields, is exact if it terminates.
Whether it terminates is a property of the corpus, so it was measured
(`nesting-depth.py`): over all 134 files **0 declare a recursive datatype** and
the deepest field nest is **5** (cores: 6 at depth 0, 26 at 1, 8 at 2, 7 at 3,
5 at 4, 3 at 5). So the unrolling terminates on every file in the division and
leaves no relaxation. `W1` is a different shape and depth unrolling does not
reach it — an array-of-datatype field's expansion variable would carry datatype
content into the residual, which `refuse_if_datatype_survives` must then refuse.

**"0 recursive" is a strong negative, so it carries a positive control.** An
empty result from a detector nobody has shown to fire is indistinguishable from
a broken detector. Run over `repro/control-recursive.smt2`
(`lst = nil | cons(car Int, cdr lst)`) and `repro/ground.smt2` (a depth-1
record nest), `nesting-depth.py` separates them — `depth RECURSIVE 1`,
`depth 1 1` (`census/nesting-control.txt`).

## 3. What the references do with the construct

Read from the shipped sources, with a positive control on every negative.

**z3 has no datatype code in its model finder at all.** `grep -c -i datatype`
and `-i constructor` over `src/smt/smt_model_finder.cpp` and
`src/smt/smt_model_checker.cpp` return **0** on both files, against a control
of `sort` = 68 and 5. Instantiation sets hold **terms pulled from the e-graph**
by sort (`smt_model_finder.cpp:1226-1242`), and the only sort-driven population
is gated on `m.is_uninterp(s)` (`:1700-1706`), which a datatype sort is not.
There is **no finite datatype universe and no depth bound** anywhere in it;
datatype *values* are manufactured lazily only during model completion
(`model/datatype_factory.cpp:99`, `:129`).

**z3's ground datatype theory needs no expansion variables, so it has nothing
to refuse.** `theory_datatype.cpp:140` `assert_is_constructor_axiom` asserts
`n = c(acc_1 n, …)`; `:167` `assert_accessor_axioms` asserts the converse for a
constructor term. A **datatype-typed field is handled by recursion**:
`internalize_term` at `:329-378` carries the comment "*we must create a theory
variable for each argument that has sort datatype*" and the loop at `:372-378`
gives the nested field's enode its own theory var and its own axioms. Equality
on the nested datatype is the e-graph's equality on constructor terms and
congruence over a UF is the e-graph's own congruence, so nothing is weakened
and nothing has to be refused. An **array-of-datatype field** is likewise not
encoded: `:358-363` projects the array to `default`, and `:923-1003` walks its
`select`-parents, **only for the acyclicity check** — array equality stays with
`theory_array`. The only global datatype obligation is one occurs check,
`:1009` `occurs_check`, called at `:765` and guarded by `m_util.is_recursive(s)`.

**cvc5 does build a finite universe of constructor terms, but only for FMF.**
`RepSet::complete` (`src/theory/rep_set.cpp:131-165`) drives a `TypeEnumerator`
to exhaustion; for a datatype that is `DatatypesEnumerator`, which enumerates
`APPLY_CONSTRUCTOR` terms **by iterative deepening on term size** —
`theory/datatypes/type_enumerator.h:58` `unsigned d_size_limit;`, incremented
at `type_enumerator.cpp:339-348`. It is gated by an exact cardinality
computation, `expr/dtype.cpp:384-403` (sum over constructors of the product
over fields, recursing into datatype fields, `Cardinality::INTEGERS` on
recursion), under the `fmfTypeCompletionThresh` default of **1000**
(`quant_bound_inference.cpp:45-63`). FMF's own files contain no datatype code:
`full_model_check.cpp` and `first_order_model_fmc.cpp` return 0 for both
`datatype` and `TypeEnumerator` against a `TypeNode` control of 16 and 4; the
enumeration happens strictly upstream in `RepSet::complete`.

**So the brief's hypothesis is half right, and the half it gets right is the
half that does not apply.** "A finite universe per datatype sort with
constructor terms up to a depth bound" is exactly cvc5's FMF device, and it is
**not** what makes either reference's ground datatype reasoning work — z3 has
no such thing and decides these benchmarks anyway. Neither reference ever
weakens datatype equality, which is why neither ever has to refuse Ackermann
congruence.

## 4. The minimal representation, named

The brief asked for "a finite universe per datatype sort with constructor terms
up to a depth bound? selector interpretation as a partial function over that
universe?". Measured against the two references, the first is cvc5's FMF device
and the second is neither's.

**What our ground theory actually lacks is not a universe. It is exact equality
on a datatype-typed field**, and the smallest thing that supplies it, for this
corpus, is:

> **Recursive tag/field expansion of a datatype-typed field, to the datatype's
> own finite nesting depth.**

The child slot this needs already exists. `unfold_traversals`
(`datatype_native.rs:452`) already rewrites a `select` into a datatype-typed
field to a fresh child variable and records it in
`links[(parent, ctor, field)]`, and `project_slot` (`:2083`) already projects
that child recursively when reconstructing a model. What is missing is that the
link is created **only for a traversed field**, the child is left
**unconstrained**, and `build_dt_eq` never compares through it. Materialising a
child for every datatype-typed field to a bounded depth, and emitting the
recursive equality between the two children at each compared constructor, makes
`build_dt_eq` exact — and the measurement above says it terminates, because 0 of
134 files declares a recursive datatype and the deepest nest is 5.

That is a bounded, sound and well-located change. **It is not the change this
lane ships, and §5 says why.**

For `W1` the answer is different, and both references agree on it: an
array-of-datatype field should not be encoded by the datatype layer at all.
z3 leaves array equality to `theory_array` and touches the array only to project
it to `default` and its `select`-parents for the acyclicity check
(`theory_datatype.cpp:358-363`, `:923-1003`). A tag/field expansion has no
corresponding move, which is why `field_sort_expands` refuses it, and why depth
unrolling does not reach it.

## 5. What the reference says about the bucket, and why no datatype lever is built

The datatype refusal is a real capability gap and it is a GROUND one. z3 on the
same 55 cores, four configurations each, 60 s, pinned:

| z3 attribution | n |
|---|---:|
| `GROUND` — refuted with `smt.ematching=false smt.mbqi=false` | **44** (80.0 %) |
| `EMATCHING` | 11 |
| `MBQI` | **0** |

and on exactly the 13 rows we refuse on a datatype construct, **12 of 13 are
`GROUND`**. So on those rows no quantifier reasoning is needed at all, and a
ground datatype theory that did not weaken equality would reach them. The
fourth configuration is why this is an attribution and not a guess: without the
both-off control every ground-refutable row reports "decided by either engine",
which is exactly what this lane's own first two-file probe printed before the
control existed.

**And it is still not the bucket to build for.** Three measurements against it:

1. **The datatype wording is the printed blocker on 13 of the 55 CORES but only
   **4 of the 79 undecided ORIGINALS**. The core population over-reports this
   bucket by more than 3×, for [ADR-2090] §8's reason: taking the reference's
   minimal core removes the material the ladder was using, so a different rung
   ends the run. **A blocker census run on reference-minimised cores is not a
   census of the division**, and [ADR-2090]'s "17 mbqi datatype declines" is a
   core-population number.
2. **The 13 split across two designs, not one.** 7 are `W1` — array-of-datatype
   — which depth unrolling does not reach and which both references handle by
   leaving equality to the array theory. Only **5** are the `INEXACT` bucket
   that §4's recursive expansion fixes.
3. **127 of 134 files never reach any datatype question**, dying at an MBQI
   quantifier shape guard. That is the largest bucket in this division by an
   order of magnitude, it is not a datatype change, and it belongs to the
   quantifier lane rather than this one.

So no datatype lever is built, on [ADR-2090]'s own rule: a lane that measures
its target and finds it small says so rather than manufacturing a lever for it.
§4 names the representation and sizes it so the next lane does not have to
re-derive either.

## 6. What does ship

The defect this lane actually found: the give-up sentence names the wrong
engine. `auto.rs` now carries a loop-entry flag through
`prove_unsat_by_mbqi_reporting` and appends a correction when MBQI's refutation
loop never ran. The sentence up to and including the original message is
**byte-identical**, because four committed censuses under `bench-results/`
match on that prefix and on the ADR-0022 sentences inside it; nothing branches
on `UnknownReason::detail`, so it cannot move a verdict.

Four tests and a four-guard mutation suite (`mbqi-loop-entry-note`). Measured on
the first three guards: baseline green at 4 tests, **each guard killed exactly
one test, three different ones**; `--check-anchors` reports `suites=141
anchors=1069 stale=0`.

## Consequences

- **[ADR-2090]'s `AUFDTLIRA` give-up bucket is re-attributed.** Its 17 "mbqi
  datatype declines" are 17 ground-closure refusals relabelled in transit, and
  they are a core-population artefact at more than 3× the rate of the real
  files. Any lane sizing work off that line should read §1 and §5 first.
- **A blocker census must state whether it ran on cores or on originals.** This
  one ran on both and they disagree by 3×, which no census in
  `bench-results/` currently distinguishes.
- **The next `AUFDTLIRA` lever is a quantifier SHAPE change, not a datatype
  change**: 127 of 134 files are refused by `nested-binder-in-matrix` /
  `quantifier-below-top-level` before any theory question is asked. SPARK VCs
  are alternating and non-prenex; MBQI accepts only single-binder prenex.
- **If the datatype side is taken up later, §4 names the representation** — a
  recursive tag/field expansion to the datatype's own nesting depth, reusing
  the `links` child slots that `unfold_traversals` already creates — and §2
  sizes it: 0 recursive datatypes over 134 files, max depth 5, and `W1`'s
  `(Array Int <datatype>)` is a separate design that this does not reach.
- **The brief's hypothesised representation is cvc5's FMF device, not the thing
  that makes ground datatype reasoning work.** z3 builds no datatype universe
  at all — measured, not only read: over all 13 datatype-refused cores,
  `-v:10` under `smt.ematching=false` emits 0 lines mentioning
  universe/model-finder/instantiation-set against a non-vacuous control of 27
  to 47,758 total lines.

[ADR-2090]: adr-2090-the-cores-are-small-and-findable-and-we-do-not-decide-them.md
