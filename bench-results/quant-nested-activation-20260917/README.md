# A13-QUANT (ADR-2149): the per-core split of `inactive_dropped`, and the lever sweep

ADR-2113's 53 reference-minimal `UFLIA` cores (`uflia-cores.list`, the same
population as ADR-2120 §7, ADR-2130 §6, ADR-2133 and QUANT-REACH-DIFF),
24 s / 8 GiB, s6 physical pairs `5,13` and `6,14`, timing by
`$EPOCHREALTIME`. Every number here is derived from a committed TSV by a
committed script; nothing is typed.

- `census-run.sh <cores.list> <outdir> <pin> <bin> <arm> [budget_s]` — one
  binary, one environment arm (`off` = every lever variable UNSET, the shipped
  arm byte for byte; `on` = `AXEYUM_QINST_POSITIVE_PATH=1`; `nested1`,
  `nested2`, `nested2-on`, `nested2-composed` as named in the script), with
  `AXEYUM_QTRACE`/`AXEYUM_QPROBE`/`AXEYUM_QPROBE_CENSUS` on.
- `split.py <outdir>…` — parses the `QPROBE universal[…]` and
  `QPROBE nested-discovery` lines into one row per (core, arm), summed over
  every loop exit. `--self-test` checks a fixture with trailing content (the
  `re.M` trap QUANT-REACH-DIFF's classifier fell into; the mutant without
  `re.M` fails it) and the three pinned caps against the source.
- `render.py split.tsv` — the per-core table and the pooled totals below.
- `sweep-table.py <sweep-root> [run…]` — the sweep table with the mover
  threshold: a core moves between two arms only if it decides in EVERY run of
  one arm and in NO run of the other.
- `split.tsv` — the census, binary `faa6cac11`
  (`smtcomp_cli-2149-d2`, sha256 `c0189eec…`), arms `off` and `on`.
- `collect-sweep.py <sweep-root>` — every `run-summary.tsv` into one table,
  each row labelled `complete` or `partial` by its arm's `DONE` marker.
- `sweep.tsv` — the sweep's per-(core, arm, run) verdicts, binary
  `smtcomp_cli-2149-d5` (sha256 `9c715f6b…`, the Rust of `26c81da53`).

The raw captures (`raw/*.out`, `raw/*.err`, ~100 MB per arm) are on the NAS
under `/nas3/data/axeyum/harness/a13-quant-2149/{census,sweep}/`, not
committed, matching ADR-2120 §7e's precedent; `census-run.sh` regenerates
them.

## The census: `inactive_dropped` split by the first refusal on the path

`rej_nocontext` (= `inactive_dropped`) is charged to `InertReason`:
`crossed-binder` (the path entered another universal's body below the owner's
prefix), `negative` (a tracked negative position — effectively existential),
`untracked` (a connective the level in force refuses: everything but
`and`/`or` at level 0, the `ite` condition and boolean `=`/`xor` at level 1).
First cause wins.

| arm | cores | unsat | cores printing a table | regs context / crossed / negative / untracked | handoff | poscap | nocontext crossed / negative / untracked | cores with crossed drops | discovered | checker-refused | cores hitting cap regs / rebuilds / positive |
|---|---:|---:|---:|---|---:|---:|---|---:|---:|---:|---|
| `off` | 53 | 15 | 37 | 4,762 / 54 / 0 / 1,029 | 131,229 | 2,328,593 | 17,685 / 0 / 2,520,232 | 5 | 4,344 | 2,713 | 11 / 0 / 2 |
| `on` | 53 | 15 | 36 | 11,990 / 178 / 44 / 2 | 935,313 | 13,687,328 | 1,611,516 / 231,040 / 57,014 | 9 | 10,677 | 17,600 | 26 / 2 / 19 |

Read:

1. **Shipped arm: the crossed-binder class is 0.7 % of the drops** (17,685 of
   2,537,917) on 5 cores. ADR-2120's connective class is 99.3 %, because a
   `=>` above a binder is charged to the `=>`.
2. **At `AXEYUM_QINST_POSITIVE_PATH=1` it is 1.6 M tuples on 9 cores** — and
   the contextful tuples fare no better: 13.7 M are cut by
   `MAX_POSITIVE_TUPLES_PER_ROUND` (256), 17,600 are handed off and refused
   by the checker because they bind a variable to itself, the
   256-registration discovery cap is hit on 26 cores and the 4,096
   positive-instance cap on 19.
3. **37 of 53 cores print a table on the shipped arm** (ADR-2120 §7a had 18):
   the table now prints at every loop exit. The 16 without are 12 decided on
   an earlier rung (`q:mbqi-quick`, `q:bool-skeleton`), 1 decided by the
   loop's own `unsat` return (`sledgehammer_Hoare_smtlib.1175889`), and 3
   sledgehammer cores whose loop never reaches an exit.

### Per core

| core | off: verdict | off: nocontext crossed / negative / untracked | off: handoff | off: caps hit (regs/rebuilds/positive) | on: verdict | on: nocontext crossed / negative / untracked | on: handoff | on: caps hit (regs/rebuilds/positive) |
|---|---|---:|---:|---|---|---:|---:|---|
| `boogie_AdvancedTypes_InternalSubClass..ctor-orderStrength_1` | unknown | 0 / 0 / 105051 | 2424 | 1/0/0 | unknown | 0 / 275 / 0 | 4170 | 2/0/0 |
| `boogie_Arrays_Q3-noinfer` | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `boogie_AssignToRepField_AssignToRepField.N` | unknown | 0 / 0 / 158 | 220 | 0/0/0 | unknown | 0 / 0 / 0 | 220 | 0/0/0 |
| `boogie_BasicMethodology_SubClass..ctor` | unknown | 0 / 0 / 774 | 0 | 0/0/0 | unknown | 0 / 0 / 0 | 0 | 0/0/0 |
| `boogie_Cast_Cast.R_System.Object_System.Int32` | unknown | 0 / 0 / 7260 | 5120 | 1/0/0 | unknown | 0 / 3990 / 0 | 27784 | 2/0/1 |
| `boogie_Chunker11c_Chunker.SpecSharp.CheckInvariant_System.Boolean` | unknown | 0 / 0 / 149790 | 71832 | 2/0/1 | unknown | 0 / 4462 / 0 | 128495 | 3/0/2 |
| `boogie_DefaultLoopInv0_A.M-modifiesOnLoop-noinfer` | unknown | 0 / 0 / 69257 | 1238 | 1/0/0 | unknown | 0 / 0 / 0 | 1238 | 1/0/0 |
| `boogie_ExposeVersion_D..ctor-level_2` | unknown | 0 / 0 / 1190 | 3977 | 1/0/0 | unknown | 0 / 2720 / 0 | 10584 | 2/0/1 |
| `boogie_Interval_Cell.Shift_System.Int32` | unknown | 0 / 0 / 14550 | 342 | 0/0/0 | unknown | 0 / 23433 / 0 | 52064 | 1/1/1 |
| `boogie_Spouse_Person..ctor` | unknown | 0 / 0 / 104353 | 2728 | 1/0/0 | unknown | 0 / 19424 / 0 | 63658 | 2/0/1 |
| `boogie_loopinv1_LoopInv1.Test1a_F_notnull-infer_eh` | unknown | 0 / 0 / 0 | 1512 | 1/0/0 | unknown | 0 / 14801 / 0 | 35956 | 2/0/1 |
| `grasshopper_instantiated_delete_check_heap_access_53_12` | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `grasshopper_instantiated_insertion_sort_postcondition_of_insertion_sort_63_1` | unsat | 0 / 0 / 0 | 0 | 0/0/0 | unsat | 0 / 0 / 0 | 0 | 0/0/0 |
| `grasshopper_uninstantiated_merge_loop_check_heap_access_60_6` | unknown | 0 / 0 / 0 | 0 | 0/0/0 | unknown | 0 / 0 / 0 | 0 | 0/0/0 |
| `simplify2_front_end_suite_javafe.PrintSpec.012` | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `simplify2_front_end_suite_javafe.ast.ImportDeclVec.015` | unknown | 522 / 0 / 464816 | 5352 | 2/0/0 | unknown | 380131 / 73310 / 0 | 72636 | 3/0/1 |
| `simplify2_front_end_suite_javafe.ast.LabelStmt.011` | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `simplify2_front_end_suite_javafe.ast.MethodDecl.005` | unknown | 0 / 0 / 2556 | 0 | 0/0/0 | unknown | 207 / 0 / 0 | 2041 | 1/0/0 |
| `simplify2_front_end_suite_javafe.ast.ParenExpr.006` | unknown | 0 / 0 / 7224 | 0 | 0/0/0 | unknown | 0 / 0 / 0 | 1948 | 1/0/0 |
| `simplify2_front_end_suite_javafe.ast.StandardPrettyPrint.008` | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `simplify2_front_end_suite_javafe.ast.TypeModifierPragmaVec.013` | unknown | 11899 / 0 / 260406 | 26900 | 1/0/1 | unknown | 238731 / 39564 / 0 | 97212 | 2/0/2 |
| `simplify2_front_end_suite_javafe.ast.VariableAccess.001` | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `simplify2_front_end_suite_javafe.filespace.HashTree.001` | unknown | 0 / 0 / 29856 | 0 | 0/0/0 | unknown | 0 / 15009 / 0 | 81317 | 1/0/1 |
| `simplify2_front_end_suite_javafe.filespace.ZipTree.005` | unknown | 0 / 0 / 18363 | 425 | 0/0/0 | unknown | 0 / 0 / 0 | 13801 | 1/0/1 |
| `simplify2_front_end_suite_javafe.parser.Parse.005` | unknown | 232 / 0 / 11816 | 992 | 1/0/0 | unknown | 3712 / 0 / 0 | 3290 | 2/0/0 |
| `simplify2_front_end_suite_javafe.parser.TagConstants.001` | unknown | 0 / 0 / 1976 | 0 | 0/0/0 | unknown | 0 / 0 / 0 | 16 | 0/0/0 |
| `simplify2_front_end_suite_javafe.reader.CachedReader.003` | unknown | 0 / 0 / 999 | 0 | 0/0/0 | unknown | 0 / 0 / 0 | 10164 | 1/0/1 |
| `simplify2_front_end_suite_javafe.tc.EnvForLocals.007` | unknown | 0 / 0 / 810 | 0 | 0/0/0 | unknown | 0 / 0 / 0 | 8552 | 1/0/1 |
| `simplify2_front_end_suite_javafe.tc.FlowInsensitiveChecks.017` | unknown | 0 / 0 / 0 | 0 | 0/0/0 | unknown | 0 / 0 / 0 | 0 | 0/0/0 |
| `simplify2_front_end_suite_javafe.tc.TypeSig.001` | unknown | 0 / 0 / 31004 | 0 | 0/0/0 | unknown | 0 / 0 / 0 | 18028 | 1/0/1 |
| `simplify2_front_end_suite_javafe.tc.TypeSigVec.005` | unknown | 5000 / 0 / 950752 | 2056 | 0/0/0 | unknown | 942980 / 15894 / 0 | 70014 | 1/0/1 |
| `simplify2_front_end_suite_javafe.tc.Types.035` | unknown | 0 / 0 / 36252 | 0 | 0/0/0 | unknown | 0 / 0 / 0 | 1713 | 1/0/0 |
| `simplify2_front_end_suite_javafe.test.SuperlinksTest.004` | unknown | 0 / 0 / 17134 | 0 | 0/0/0 | unknown | 9849 / 0 / 0 | 9220 | 1/0/1 |
| `simplify2_small_suite_getRootInterface` | unknown | 32 / 0 / 42184 | 3117 | 1/0/0 | unknown | 921 / 0 / 0 | 5670 | 2/0/0 |
| `simplify_javafe.ast.CatchClauseVec.66` | unknown | 0 / 0 / 0 | 2707 | 0/0/0 | unknown | 0 / 0 / 0 | 2707 | 0/0/0 |
| `simplify_javafe.ast.LexicalPragmaVec.219` | unknown | 0 / 0 / 0 | 29 | 0/0/0 | unknown | 0 / 0 / 0 | 29 | 0/0/0 |
| `simplify_javafe.ast.NewInstanceExpr.271` | unknown | 0 / 0 / 35020 | 0 | 0/0/0 | unknown | 5437 / 0 / 0 | 21175 | 1/0/1 |
| `simplify_javafe.ast.StandardPrettyPrint.322` | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `simplify_javafe.ast.TypeDeclElemPragma.373` | unknown | 0 / 0 / 11496 | 0 | 0/0/0 | unknown | 0 / 4072 / 0 | 70656 | 0/1/1 |
| `simplify_javafe.ast.UnaryExpr.424` | unknown | 0 / 0 / 73440 | 0 | 0/0/0 | unknown | 0 / 8580 / 0 | 68214 | 1/0/1 |
| `simplify_javafe.parser.TokenQueue.576` | unsat | 0 / 0 / 65381 | 2 | 0/0/0 | unsat | 0 / 0 / 57014 | 49506 | 1/0/1 |
| `simplify_tohtml.Java2Html.832` | unknown | 0 / 0 / 0 | 256 | 0/0/0 | unknown | 29548 / 0 / 0 | 3235 | 1/0/0 |
| `sledgehammer_FFT_smtlib.898060` | unknown (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unknown (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `sledgehammer_Fundamental_Theorem_Algebra_smtlib.1057395` | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `sledgehammer_Fundamental_Theorem_Algebra_smtlib.1462528` | unknown (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unknown (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `sledgehammer_Fundamental_Theorem_Algebra_smtlib.972059` | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `sledgehammer_Hoare_smtlib.1175889` | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `sledgehammer_Hoare_smtlib.581330` | unknown (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unknown (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `sledgehammer_Hoare_smtlib.993567` | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `sledgehammer_QEpres_smtlib.1065390` | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `sledgehammer_QEpres_smtlib.1120322` | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 | unsat (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `sledgehammer_QEpres_smtlib.1237382` | unknown | 0 / 0 / 3718 | 0 | 0/0/0 | unknown (no table) | 0 / 0 / 0 | 0 | 0/0/0 |
| `tokeneer_auditlog_init-31` | unknown | 0 / 0 / 2646 | 0 | 0/0/0 | unknown | 0 / 5506 / 0 | 0 | 0/0/0 |

## The sweep

One binary (`smtcomp_cli-2149-d5`, built at `26c81da53`'s Rust — the lever
as committed; sha256 `9c715f6b…`), six environment arms, 24 s / 8 GiB, s6
physical pairs `5,13` / `6,14` (run 1, then run 3) and `1,9` / `3,11` (run 2).
**Runs 1 and 2 are complete for all six arms (636 rows). Run 3 was stopped by
the coordinator's wrap-up at 32 of 53 `off` rows and 28 of 53 `on` rows, and
its other four arms did not start**; `sweep.tsv` labels each row `complete`
or `partial`. A core MOVES only if it decides in every run of one arm and in
no run of the other, so with two complete runs the threshold below is 2/2
against 0/2 — one recheck short of the brief's 3/3, and stated as such.

Arms: `off` = every lever variable unset (the shipped arm); `on` =
`AXEYUM_QINST_POSITIVE_PATH=1` (ADR-2120); `nested1` / `nested2` = this
lever alone at that level; `nested2-on` = level 2 + ADR-2120's level 1;
`nested2-composed` = those two + `AXEYUM_QINST_GROUND_SESSION=2` (ADR-2130),
the composition QUANT-COMPOSE sized.

| arm | runs | decided per run | sat/unsat flips |
|---|---:|---|---:|
| `off` | 2 (+ 32 of 53 in run 3) | 15 / 16 (+ 9 of 32) | 0 |
| `on` | 2 (+ 28 of 53 in run 3) | 15 / 15 (+ 8 of 28) | 0 |
| `nested1` | 2 | 15 / 15 | 0 |
| `nested2` | 2 | 15 / 15 | 0 |
| `nested2-on` | 2 | 15 / 15 | 0 |
| `nested2-composed` | 2 | 16 / 16 | 0 |

Movers against `off` at the 2/2-vs-0/2 threshold:

| core | arm | `off` | arm | class |
|---|---|---|---|---|
| `boogie_Cast_Cast.R_System.Object_System.Int32` | every arm | unknown, unsat (run 3: unknown) | unknown, unknown | UNSTABLE — the ±1 the three ADRs' OFF arms already spread |
| `simplify2_front_end_suite_javafe.reader.CachedReader.003` | `nested2-on`, `nested2-composed` | unknown, unknown (run 3: **unsat** at 4.0 s) | unsat, unsat | UNSTABLE — `off` decides it in run 3; it sits on the clock (15–16 s of 24 in the census) |
| `simplify_javafe.ast.TypeDeclElemPragma.373` | `nested2-composed` | unknown, unknown (run 3: unknown) | unsat, unsat | **STABLE-GAIN at 2/2 vs 0/3** — the one gain, on the composed arm only |
| `simplify_javafe.parser.TokenQueue.576` | `nested2-on`, `nested2-composed` | unsat, unsat (run 3: unsat) | unknown, unknown | **STABLE-LOSS at 0/2 vs 3/3** — see below |

`nested1` and `nested2` alone move nothing: 15/15 against `off`'s 15/16.

**The `TokenQueue.576` loss is an interaction, and it is located.** The core
is `unsat` by `q:mbqi` in 4 s at `off`, at `on`, at `nested1`, at `nested2`,
and at `on + nested1` (local probe, pinned, 6.1 / 7.2 s) — and `unknown` at
24 s at `on + nested2`. So level 2's opaque-binder ingestion loses it only
when ADR-2120's level 1 is also armed. A refinement that kept the GROUND
subterms of a quantifier body (only bound-variable-carrying subterms opaque)
was built, passed the 22 tests, and did **not** rescue it (`unknown` at 24 s
on the same probe); it is not committed, and the code the sweep ran is the
code on the branch. The core's z3 refutation is one instance
(QUANT-REACH-DIFF: `z3_uniq=1`, MATCHED-REJECTED); which term under a binder
that one instance needs at `on` is the next single question.

**Ship decision: `AXEYUM_QINST_NESTED_ACTIVATION` stays `0`; ADR-2149 stays
`proposed`.** No arm meets the criterion on this population: alone the lever
moves nothing, composed it has one stable gain against one stable loss. The
pinned `UFLIA` / `AUFDTLIRA` A/B, the `UFNIA` control and the held-out draws
**did not run** — the composed arm's 1 gain / 1 loss does not clear the bar
that would have started them, and the coordinator paused the campaign before
run 3 completed.
