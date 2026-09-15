# Lane: dt-quant-trace — the AUFDTLIRA datatype decline is a GROUND refusal wearing a quantifier label

<!-- plan-section: lane-status -->

**MBQI's refutation loop runs on 2 of 134 AUFDTLIRA files** (`WIP`,
dt-quant-trace, 2026-09-15, [ADR-2114]). [ADR-2090]'s give-up census recorded
*"17 mbqi declined an unsupported DATATYPE fragment (three distinct wordings)"*
and this lane was dispatched to find which construct triggers the decline.
**The premise does not survive the control.**

Traced 134 files on an idle s7 — the 55 [ADR-2090] `AUFDTLIRA` cores and the 79
undecided originals — at 24 s on four pinned physical-core pairs, `AXEYUM_QPROBE`
on throughout, shards round-robin so no shard is a prefix of a path-sorted list.
MBQI's refutation loop **did not run on 132 of 134**, and on **127** the reason
is a purely syntactic quantifier shape guard (`nested-binder-in-matrix`,
`quantifier-below-top-level`) that mentions no datatype: these are SPARK VCs of
the form `(not (forall … (=> … (forall …))))` and the rung takes only a
single-binder prenex universal.

17 rows do print a datatype wording, and on **16 of 17** MBQI's loop had already
been bypassed — the sentence was produced by a ground sub-solve inside
e-matching (`decide_instantiation`, `auto.rs:13388`, `check_auto` on a
quantifier-free query) and picked up its "mbqi declined" prefix on the way out
at `auto.rs:2473`. **But the control refuses the datatype reading**: on the 117
rows with no datatype wording the loop also did not run, 116 of 117. So "MBQI
did not get to build a model" is a fact about the ladder, not about datatypes.
The narrow claim that survives is that the message names an engine that did not
produce it, 16 times of 17.

The construct is classified by SORTS, not names (`dtshape.py`), because the
three refusals are decided by `field_sort_expands`
(`datatype_native.rs:1549`) and `datatype_expansion_is_exact` (`:1576`) and
neither is visible in the text of a `declare-datatypes` form. 134 of 134 joined
against the binary, 0 unmatched, 38 disagreements **all** in the direction
"predicted a refusal, observed none" (the ladder ended before the Ackermann pass
ran) and **0** the other way.

Two buckets. `W1` (9 observed, 20 predicted) refuses a field sort, and that sort
is `(Array Int <datatype>)` on **86 of 86** occurrences — SPARK's array of
records, the one shape z3 also declines to encode. `INEXACT` (W2/W3 folded, 8
observed, 35 predicted) is a datatype-typed field reaching a UF boundary.
Sizing: over all 134 files **0 declare a recursive datatype** and the deepest
nest is **5**, so a recursive field expansion would terminate and be exact.

Reference reading, with a positive control on every negative: z3's model finder
has **zero** occurrences of `datatype`/`constructor` (`smt_model_finder.cpp`,
control `sort`=68) and no depth bound — it handles a nested datatype field by
recursion in the e-graph (`theory_datatype.cpp:372-378`) and never weakens
datatype equality, which is why it never has to refuse congruence. A finite
universe of constructor terms exists only in cvc5, only for FMF, by iterative
deepening on term size (`rep_set.cpp:131-165`, `type_enumerator.h:58`).

Detail in [ADR-2114]; artifacts under `bench-results/dt-quant-trace-20260915/`.

[ADR-2090]: ../../research/09-decisions/adr-2090-the-cores-are-small-and-findable-and-we-do-not-decide-them.md
[ADR-2114]: ../../research/09-decisions/adr-2114-aufdtlira-what-the-model-finder-cannot-represent.md

<!-- plan-section: landed-changes -->

| 2026-09-15 | `175ed2e8b` | `dtshape.py`: the datatype construct that refuses is decided by SORTS, so the classifier parses rather than greps; `let` resolved, not expanded. 55 cores + 79 originals classified, joined against ADR-2090's own traced give-ups 55 of 55. |
| 2026-09-15 | `db7132eff` | The 134-file traced census with `AXEYUM_QPROBE`, the z3 four-configuration attribution runner (the fourth arm is the both-engines-off CONTROL, without which every ground-refutable row reports "decided by either engine"), and the nesting-depth sizing: 0 recursive datatypes, max depth 5, W1's refused sort `(Array Int <datatype>)` 86 of 86. |
