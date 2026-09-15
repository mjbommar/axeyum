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
e-matching (`decide_instantiation`, `auto.rs:13482`, `check_auto` on a
quantifier-free query) and picked up its "mbqi declined" prefix on the way out
at `auto.rs:2488`. **But the control refuses the datatype reading**: on the 117
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
deepening on term size (`rep_set.cpp:131-165`, `type_enumerator.h:58`). That it
builds no universe here is measured, not only read: `-v:10` under
`smt.ematching=false` emits **0** universe/model-finder lines across all 13
datatype-refused cores, against a non-vacuous control of 27 to 47,758 lines.

**The number that decides the lane is on the ORIGINALS, not the cores.** Four
z3 configurations per file — the fourth being the both-engines-off control,
without which every ground-refutable row reports "decided by either engine":
z3 refutes **44 of 55 cores** and **39 of the 79 undecided originals (49.4 %)
GROUND**, and **MBQI decides 0 of 134**. So `AUFDTLIRA`'s gap is substantially
a ground capability gap — but of the **4** original rows we refuse on a
datatype construct only **1** is `GROUND`, so a perfect ground datatype theory
converts **at most 1 of 79**. **No datatype lever is built** ([ADR-2090]'s own
rule). What ships is the mislabelled give-up sentence, corrected as a suffix on
a byte-identical prefix, with 4 tests and a 4-guard mutation suite where each
guard kills exactly one of four distinct tests.

Verdict invariance is measured, not argued: the 134 files re-run on a freshly
built post-change binary give **0 verdict changes of 134 and 0 flips**, with
non-vacuity in **both** directions — 15 of the 16 wrapper rows carry the
correction, 0 in the base arm, and the **1** row whose refutation loop genuinely
ran correctly carries none. The checker was wrong before the code was: its first
version demanded the correction on a row that never entered the quantified arm
at all, and the population is now the rows that came through the wrapper.

Gates: clippy `-D warnings` exit 0; the four DT suites **24 / 6 / 3 / 5** and the
`dt_*` gate suites **20 / 11 / 12 / 10**, 0 failed; `dispatch_rung_refusal_declines`
6/6; `route_trace` 13/13; `config_registry::tests` 18/18; `progress_frontier`
12/12 rc 0, no REGRESSION; fmt 0; hygiene PASS; links ok. The `--lib` sweep is
**1827 passed, 3 failed**, and all four failures across the run are wall-clock
budget tests on a box at load 86-90 — **all four re-checked and all four re-pass** rather than assumed, and
`quantified_route_trace::decider_agrees_with_the_verdict` settled by running
**both binaries interleaved at load ~8: base 1/1 pass, this branch 1/1 pass**.
Its failing assertion is the test's own `decided >= 4` non-vacuity guard; the
misattribution assertion above it passed in every run.

Not committed, deliberately: `progress_frontier` rewrote the five
`bench-results/frontier/*.json` baselines with a saturated box's reference frame,
including `lia_cuts` recording **35 → 26** while declaring itself
`"comparable": false` at `load_start 37.27`. The five files were restored.

Detail in [ADR-2114]; artifacts under `bench-results/dt-quant-trace-20260915/`.

[ADR-2090]: ../../research/09-decisions/adr-2090-the-cores-are-small-and-findable-and-we-do-not-decide-them.md
[ADR-2114]: ../../research/09-decisions/adr-2114-aufdtlira-what-the-model-finder-cannot-represent.md

<!-- plan-section: landed-changes -->

| 2026-09-15 | `175ed2e8b` | `dtshape.py`: the datatype construct that refuses is decided by SORTS, so the classifier parses rather than greps; `let` resolved, not expanded. 55 cores + 79 originals classified, joined against ADR-2090's own traced give-ups 55 of 55. |
| 2026-09-15 | `db7132eff` | The 134-file traced census with `AXEYUM_QPROBE`, the z3 four-configuration attribution runner (the fourth arm is the both-engines-off CONTROL, without which every ground-refutable row reports "decided by either engine"), and the nesting-depth sizing: 0 recursive datatypes, max depth 5, W1's refused sort `(Array Int <datatype>)` 86 of 86. |
| 2026-09-15 | `8793f1387` | z3's engine attribution on the 55 cores, and the measured answer to "what does the model finder build for the datatype sorts": nothing — 0 universe/model-finder lines under `-v:10` with e-matching off, control 27 to 47,758 lines. |
| 2026-09-15 | `75b716b95` | `mbqi declined an unsupported fragment: …` names the engine that refused and names the wrong one on 16 of the 17 rows that print it. A loop-entry flag through `prove_unsat_by_mbqi_reporting` appends a correction; the sentence up to the original message is byte-identical so the four committed censuses keep working; nothing branches on `UnknownReason::detail`. 4 tests, 4 mutation guards, each killing exactly one distinct test. |
| 2026-09-15 | `e75f85413` | [ADR-2114]: no datatype lever is built — of the 4 undecided ORIGINALS we refuse on a datatype construct, 1 is ground-convertible. §4 names and sizes the representation anyway so the next lane need not re-derive it. |
| 2026-09-15 | `3d8435c2f` | The same four z3 configurations on the 79 undecided ORIGINALS, which is the measurement the cores could not give: 39 GROUND (49.4 %), 16 EMATCHING, 0 MBQI, 24 z3 cannot refute either. Half the gap is ground — but only 1 of the 4 datatype-refused originals is, so the bucket converts at most 1 of 79. |
| 2026-09-15 | `d53c89e8e` | Verdict invariance measured rather than argued: 0 verdict changes of 134, 0 flips, non-vacuity in both directions. The checker was wrong before the code was — it demanded the correction on a row that never entered the quantified arm. |
