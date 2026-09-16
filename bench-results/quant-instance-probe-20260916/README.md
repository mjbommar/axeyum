# QUANT-INSTANCE-PROBE: selection vs. ground refutation, on ADR-2113's 53 cores

ADR-2113 measured that on its 53 reference-minimal UFLIA cores z3 refutes
every one E-matching-only (median 108 ms) using a **median of 6** used
instantiations, while our engine admits a **median of 1,473** per core. ADR-2120
(activation by assignment), ADR-2124 (incremental ground closure) and
ADR-2130 (session-hosted arithmetic) each removed a block and moved one
core, but the verdicts did not move as a population. The question those four
ADRs left unreconciled: is the block **instance SELECTION** (our 1,473 drown a
ground solver that would refute z3's 6 at once) or **ground REFUTATION** (even
handed exactly z3's instances, our quantifier-free ladder does not refute the
set)? This lane runs the experiment that separates them: extract z3's own
used instantiations from its proof, hand them to our engine as plain ground
assertions with every quantifier removed, and see whether it refutes or not.

## Method

1. **Extract** (`scripts/z3-proof-instances.py`): for each of the 53 cores,
   run `z3 :produce-proofs (get-proof)` and walk the proof for every
   `((_ quant-inst t1..tn) F)` step. `quant-inst` is a leaf proof rule --
   like `asserted` -- so its single argument `F` IS the step's conclusion,
   always `(or (not <quantified-formula>) <body[t]>)`; the tool recovers
   `body[t]`, the one ground consequence a caller can `assert` directly.
   **Positive control, all 53 of 53, not just one**: the raw occurrence
   count of `(_ quant-inst ..)` matches ADR-2113's own `proof_qinst` column
   (`ref-cores.tsv`) exactly on every core, 0 mismatches.
2. **Build the ground-only file** (`build-ground-only.py`): original ground
   assertions (quantified `assert`s stripped by
   `scripts/strip-quantified-assertions.py`) plus z3's recovered instances,
   `(set-logic QF_UFLIA)`. Checked with plain z3 for completeness.
3. **Run ours** (release `smtcomp_cli`, `--trace`, 24 s / 8 GiB `ulimit -v`,
   s6 pinned physical core pairs `1,9`/`3,11`, through
   `scripts/ledger-run-one.sh`, `sweep_id=quant-instance-probe`,
   `arm=z3-instances`).
4. **Second arm** (`build-ground-from-dump.py`, `arm=admitted-instances`):
   the same construction from OUR OWN admitted instance set, dumped via
   `AXEYUM_QGROUNDDUMP` on the unmodified original core (gen>=1 rows are
   admitted instances; gen=0 rows are the original ground assertions and are
   skipped to avoid double-asserting).

## The two headline counts

**Count 1 -- extraction completeness (does z3's own proof reconstruct into a
file our engine is even given a fair shot at?).** Of 53 cores, z3-checking
the reconstructed ground-only file finds **7 complete** (confirmed `unsat` by
z3 itself -- every used instantiation was recovered), **41 incomplete**
(z3 says `sat`: some instance z3's proof used was NOT recovered), and 5
degenerate (zero ground bodies recoverable at all). The gap is not random: of
1,021 raw recovered instance bodies across all 53 cores, **472 (46 %)** still
carry an unresolved outer bound variable (`?p_!N`) from a NESTED
instantiation -- the exact `rej_nocontext`/context-dependent-activation
mechanism ADR-2113 §4b already named as UFLIA's dominant blocker, now
independently reconfirmed from the opposite direction: it is hard for US to
even RECONSTRUCT z3's own refutation outside its own proof-search session,
for the identical structural reason it is hard for OUR e-matching loop to use
a nested instance once found.

**Count 2 -- on the 7 cores where the ground truth is clean, does our ground
checker refute it?** **6 of 7 (86 %)**. Handed z3's own minimal instantiation
set as plain ground assertions -- no quantifiers, no e-matching, no
selection problem left to solve -- our existing dispatch ladder (`euf-online`,
`uf-arithmetic`) reaches `unsat` in every case but one, each in well under a
second except one 12.1 s case. The one miss
(`UFLIA_sledgehammer_FFT_smtlib.898060`) exhausts the WHOLE ladder (26
attempts, 107 ms, every rung DECLINES rather than times out) and is a
distinct, narrow ground-refutation gap, not evidence against the general
capability.

**This is the answer the lane was dispatched to find: on the population
where it is measurable at all, the block is predominantly SELECTION, not
ground refutation.** Our ground checker can close the SAME refutation z3
finds, using z3's OWN instances, on 6 of 7 cores. The reason it does not do
so on its own is that its e-matching loop never gets to try: it spends its
budget on `rej_nocontext` (ADR-2113 §4b) and, even where it does admit
instances, admits ~250x too many of the wrong ones to find the needed 6
before the interleaved ground check's clock runs out.

## The second arm, and why its own headline number is a tooling artifact, not a result

Of 29 admitted-instance ground-only files built (53 minus 24 cores that
produced no usable dump: 16 where our own run never reached a give-up point
at all -- `AXEYUM_QGROUNDDUMP` writes nothing until then -- and 8 where a
dump existed but held zero `gen>=1` rows), **16 of 29 (55 %) fail immediately
at PARSE**, before the solver is ever invoked. Every one of the 16 is the
exact same typed error:

```
give-up kind=Error detail=parse error: unsupported: unknown identifier `!qsk_4`
```

(and `!qu_N`, `!q.?x_.N` variants). These are OUR OWN internal Skolem
constants -- `quant_skolemize.rs:64-65` documents them: *"Symbols are
declared through `declare_internal*` under reserved `!qsk`/`!qskf`/`!qu`
prefixes"* -- declared only inside the live solving session and never
written back to the original query as a `declare-fun`. When
`AXEYUM_QGROUNDDUMP` renders a ground TERM that mentions one of these names
and this lane's `build-ground-from-dump.py` re-asserts it in a FRESH file
with no matching declaration, `crates/axeyum-smtlib/src/parse.rs:16570`
correctly refuses it as an unknown identifier. **This is a mirror of the
z3-side not-ground finding above (Count 1): both arms' extraction gaps are
the same underlying shape -- a term that only makes sense inside the
producing session's own context cannot be serialized as a standalone ground
fact.** It is a gap in this lane's OWN reconstruction tooling, not a
measurement of whether our ground checker can refute our own instances, and
is named here rather than left to read as a negative result.

**Of the 13 files that DID parse**, our engine decided **4** (1 `unsat` --
`grasshopper_instantiated_insertion_sort`, 710 ms, using its own 2,828
admitted instances directly -- and 3 `sat`) and **8 gave up `unknown`**. Of
those 8, **5 ran to the full ~25 s budget** (`bound_by=none`/`dl-online`,
genuinely clock-exhausted, not declined) and 3 gave up sooner (608 ms,
3.1 s, 13.6 s) on a typed decline further down the ladder. This smaller,
cleaner subset IS consistent with the "large admitted set drowns the ground
checker" half of the hypothesis, though at n=13 it is suggestive rather than
conclusive on its own -- Count 2 above is the stronger, cleanly-controlled
result.

## The dominant typed reason, named with `file:line`

Two blocks, same shape, one on each side of the pipeline:

- **z3 side** (why 46 % of z3's own recovered instances are not directly
  usable): `crates/axeyum-solver/src/qinst_egraph.rs:6834`
  (`batch.rejects.inactive_dropped += tuples.len()`, field doc at
  `:5119-5120`) -- re-verified at THIS lane's HEAD rather than copied from
  ADR-2113's own citation, which named `:6196-6215`/`:4597-4599` and has
  since drifted (ADR-2120/2124/2130 landed on this file in between). A
  universal nested under a disjunction/implication is compiled and matched
  but its tuples are discarded outright because no `PositiveContext`
  licenses the instance. ADR-2113 §4b's finding, independently reconfirmed
  here from the reconstruction side.
- **our side** (why 55 % of our own admitted-instance ground-only files
  cannot even be re-parsed): `crates/axeyum-solver/src/quant_skolemize.rs:64-65`
  declares internal `!qsk_`/`!qskf_`/`!qu_` symbols with no standalone
  `declare-fun`, and `crates/axeyum-smtlib/src/parse.rs:16570` is the exact
  line that refuses them once this lane's tooling serializes one bare. This
  is new to this lane -- not previously documented -- and is the dominant
  reason the SECOND arm's own raw numbers read worse than the first: it is a
  reconstruction gap in `build-ground-from-dump.py`, addressable by also
  emitting `declare-fun` lines for referenced internal symbols, not
  attempted here.

## Table

53 cores. `z3 raw/uniq/unmatch` = z3-proof-instances.py's raw quant-inst
count / unique GROUND bodies recovered / applications whose conclusion did
not match the expected `(or (not F) body)` shape. `ground-only build` = 0 ok,
else the builder's exit code. `z3-ground` = plain z3 on the z3-instance
ground-only file (`unsat` = COMPLETE reconstruction). `ours(z3-inst)` =
our engine on that same file: verdict/decided_by/elapsed. `admitted rows` =
gen>=1 rows in our own `AXEYUM_QGROUNDDUMP` (0 = our run never reached a
give-up point, so no file was built). `ours(admitted)` = our engine on the
admitted-instance ground-only file.

<!-- BEGIN-TABLE -->
| core | z3 raw/uniq/unmatch | ground-only build | z3-ground | ours(z3-inst) v/decided_by/ms | admitted rows | ours(admitted) v/decided_by/ms |
|---|---:|---|---|---|---:|---|
| UFLIA_boogie_AdvancedTypes_InternalSubClass..ctor-orderStrength_1 | 11/4/1 | 0 | sat | unknown/none/25032ms | 1772 | unknown/none/25033ms |
| UFLIA_boogie_Arrays_Q3-noinfer | 2/2/0 | 0 | **unsat** | **unsat**/uf-arithmetic/12120ms | 0 | NA |
| UFLIA_boogie_AssignToRepField_AssignToRepField.N | 31/8/1 | 0 | sat | sat/uf-arithmetic/509ms | 102 | unknown/none/108ms |
| UFLIA_boogie_BasicMethodology_SubClass..ctor | 292/120/1 | 0 | sat | unknown/none/1211ms | 988 | unknown/none/109ms |
| UFLIA_boogie_Cast_Cast.R_System.Object_System.Int32 | 3/3/0 | 0 | sat | sat/uf-arithmetic/109ms | 32 | unknown/none/7616ms |
| UFLIA_boogie_Chunker11c_Chunker.SpecSharp.CheckInvariant | 2/1/1 | 0 | sat | sat/uf-arith-online/110ms | 1229 | unknown/none/25032ms |
| UFLIA_boogie_DefaultLoopInv0_A.M-modifiesOnLoop-noinfer | 96/28/1 | 0 | sat | sat/uf-arith-lazy-overbound/2511ms | 0 | NA |
| UFLIA_boogie_ExposeVersion_D..ctor-level_2 | 14/4/1 | 0 | sat | sat/uf-arithmetic/708ms | 208 | unknown/none/109ms |
| UFLIA_boogie_Interval_Cell.Shift_System.Int32 | 38/14/1 | 0 | sat | sat/uf-arith-lazy-overbound-pre-lia/209ms | 18 | unknown/none/25032ms |
| UFLIA_boogie_Spouse_Person..ctor | 13/6/1 | 0 | sat | sat/uf-arith-lazy-overbound-pre-lia/310ms | 2058 | unknown/none/25034ms |
| UFLIA_boogie_loopinv1_LoopInv1.Test1a_F_notnull-infer_eh | 143/89/2 | 0 | sat | unknown/none/1311ms | 271 | unknown/none/25134ms |
| UFLIA_grasshopper_instantiated_delete_check_heap_access_53_12 | 5/5/0 | 0 | **unsat** | **unsat**/euf-online/109ms | 0 | NA |
| UFLIA_grasshopper_instantiated_insertion_sort_postcondition | 34/32/2 | 0 | sat | sat/uf-arith-lazy-overbound-pre-lia/110ms | 2828 | **unsat**/uf-arith-lazy-overbound/710ms |
| UFLIA_grasshopper_uninstantiated_merge_loop_check_heap_access_60_6 | 17/14/3 | 0 | sat | sat/uf-arith-lazy-overbound-pre-lia/110ms | 5663 | unknown/none/608ms |
| UFLIA_simplify2_front_end_suite_javafe.PrintSpec.012 | 2/2/0 | 0 | sat | sat/uf-arithmetic/110ms | 0 | NA |
| UFLIA_simplify2_front_end_suite_javafe.ast.ImportDeclVec.015 | 54/21/4 | 0 | sat | unknown/none/110ms | 475 | unknown/none/2211ms |
| UFLIA_simplify2_front_end_suite_javafe.ast.LabelStmt.011 | 1/1/0 | 0 | sat | sat/uf-arith-online/109ms | 0 | NA |
| UFLIA_simplify2_front_end_suite_javafe.ast.MethodDecl.005 | 24/24/0 | 0 | sat | unknown/none/409ms | 0 | NA |
| UFLIA_simplify2_front_end_suite_javafe.ast.ParenExpr.006 | 1/0/1 | BUILD-FAIL-4 | NA | NA | 295 | unknown/none/13621ms |
| UFLIA_simplify2_front_end_suite_javafe.ast.StandardPrettyPrint.008 | 0/0/0 | BUILD-FAIL-4 | NA | NA | 0 | NA |
| UFLIA_simplify2_front_end_suite_javafe.ast.TypeModifierPragmaVec.013 | 29/10/0 | 0 | sat | unknown/none/110ms | 973 | unknown/none/1111ms |
| UFLIA_simplify2_front_end_suite_javafe.ast.VariableAccess.001 | 3/3/0 | 0 | sat | sat/uf-arith-online/110ms | 0 | NA |
| UFLIA_simplify2_front_end_suite_javafe.filespace.HashTree.001 | 17/6/0 | 0 | sat | sat/uf-arithmetic/1711ms | 621 | unknown/none/109ms |
| UFLIA_simplify2_front_end_suite_javafe.filespace.ZipTree.005 | 7/7/0 | 0 | sat | sat/uf-arithmetic/108ms | 0 | NA |
| UFLIA_simplify2_front_end_suite_javafe.parser.Parse.005 | 23/23/0 | 0 | sat | sat/uf-arith-lazy-overbound-pre-lia/110ms | 342 | unknown/none/110ms |
| UFLIA_simplify2_front_end_suite_javafe.parser.TagConstants.001 | 1/1/0 | 0 | sat | sat/uf-arith-online/809ms | 0 | NA |
| UFLIA_simplify2_front_end_suite_javafe.reader.CachedReader.003 | 7/7/0 | 0 | sat | sat/uf-arithmetic/109ms | 1028 | sat/uf-arith-lazy-overbound/4614ms |
| UFLIA_simplify2_front_end_suite_javafe.tc.EnvForLocals.007 | 8/8/0 | 0 | sat | sat/uf-arith-lazy-overbound/1411ms | 0 | NA |
| UFLIA_simplify2_front_end_suite_javafe.tc.FlowInsensitiveChecks.017 | 8/8/0 | 0 | sat | unknown/none/610ms | 0 | NA |
| UFLIA_simplify2_front_end_suite_javafe.tc.TypeSig.001 | 3/3/0 | 0 | sat | sat/uf-arithmetic/111ms | 3899 | unknown/none/3110ms |
| UFLIA_simplify2_front_end_suite_javafe.tc.TypeSigVec.005 | 13/5/0 | 0 | sat | sat/uf-arithmetic/12019ms | 690 | unknown/none/109ms |
| UFLIA_simplify2_front_end_suite_javafe.tc.Types.035 | 10/8/2 | 0 | sat | sat/uf-arithmetic/1411ms | 296 | sat/uf-arith-lazy-overbound/109ms |
| UFLIA_simplify2_front_end_suite_javafe.test.SuperlinksTest.004 | 6/6/0 | 0 | sat | sat/uf-arithmetic/111ms | 4129 | sat/uf-arith-lazy-overbound/17126ms |
| UFLIA_simplify2_small_suite_getRootInterface | 17/17/0 | 0 | sat | sat/uf-arith-lazy-overbound-pre-lia/108ms | 0 | NA |
| UFLIA_simplify_javafe.ast.CatchClauseVec.66 | 28/5/2 | 0 | sat | sat/uf-arithmetic/12019ms | 193 | unknown/none/307ms |
| UFLIA_simplify_javafe.ast.LexicalPragmaVec.219 | 18/8/0 | 0 | sat | unknown/none/107ms | 66 | unknown/none/110ms |
| UFLIA_simplify_javafe.ast.NewInstanceExpr.271 | 2/1/1 | 0 | sat | sat/uf-arith-online/107ms | 4 | sat/uf-arith-online/109ms |
| UFLIA_simplify_javafe.ast.StandardPrettyPrint.322 | 1/0/1 | BUILD-FAIL-4 | NA | NA | 0 | NA |
| UFLIA_simplify_javafe.ast.TypeDeclElemPragma.373 | 3/1/0 | 0 | sat | sat/uf-arith-online/107ms | 150 | unknown/none/109ms |
| UFLIA_simplify_javafe.ast.UnaryExpr.424 | 6/2/0 | 0 | sat | sat/uf-arith-online/107ms | 0 | NA |
| UFLIA_simplify_javafe.parser.TokenQueue.576 | 3/1/2 | 0 | sat | sat/uf-arithmetic/107ms | 444 | unknown/none/110ms |
| UFLIA_simplify_tohtml.Java2Html.832 | 4/3/1 | 0 | sat | sat/uf-arith-online/107ms | 981 | unknown/none/109ms |
| UFLIA_sledgehammer_FFT_smtlib.898060 | 2/2/0 | 0 | **unsat** | unknown/none/107ms | 0 | NA |
| UFLIA_sledgehammer_Fundamental_Theorem_Algebra_smtlib.1057395 | 5/5/0 | 0 | **unsat** | **unsat**/euf-online/108ms | 0 | NA |
| UFLIA_sledgehammer_Fundamental_Theorem_Algebra_smtlib.1462528 | 6/4/1 | 0 | sat | unknown/none/107ms | 0 | NA |
| UFLIA_sledgehammer_Fundamental_Theorem_Algebra_smtlib.972059 | 2/2/0 | 0 | **unsat** | **unsat**/euf-online/106ms | 0 | NA |
| UFLIA_sledgehammer_Hoare_smtlib.1175889 | 4/4/0 | 0 | **unsat** | **unsat**/euf-online/107ms | 0 | NA |
| UFLIA_sledgehammer_Hoare_smtlib.581330 | 20/4/3 | 0 | sat | unknown/none/106ms | 0 | NA |
| UFLIA_sledgehammer_Hoare_smtlib.993567 | 2/2/0 | 0 | **unsat** | **unsat**/uf-arithmetic/106ms | 0 | NA |
| UFLIA_sledgehammer_QEpres_smtlib.1065390 | 2/2/0 | 0 | sat | sat/uf-arithmetic/108ms | 0 | NA |
| UFLIA_sledgehammer_QEpres_smtlib.1120322 | 3/0/0 | BUILD-FAIL-4 | NA | NA | 0 | NA |
| UFLIA_sledgehammer_QEpres_smtlib.1237382 | 1/0/0 | BUILD-FAIL-4 | NA | NA | 105 | unknown/none/109ms |
| UFLIA_tokeneer_auditlog_init-31 | 17/13/0 | 0 | sat | sat/uf-arith-lazy-overbound-pre-lia/107ms | 984 | unknown/none/110ms |
<!-- END-TABLE -->

(Full core paths, per-file solver captures, and the raw extraction JSON are
under `extract/`, `ground/`, `admitground/`, `dumpadmit/dump-summary.tsv`,
and `runs/` in this directory; the outcome ledger row is
`bench-results/ledger/quant-instance-probe.tsv`.)

## Verified not-wrong

`ours(z3-inst)` never claims `unsat` on a core where the z3-ground check says
`sat` (0 of 48 disagreements) -- the six `unsat` agreements above are z3 and
our engine agreeing independently on the SAME ground file, not a
self-consistency check.

## What could not be extracted / not attempted

- **Nested instantiation chains are not resolved.** `z3-proof-instances.py`
  recovers a per-occurrence ground consequence; when the substituted term
  itself still mentions an outer, not-yet-closed quantifier's bound variable
  (z3's own `?p_!N` naming), that occurrence is reported separately
  (`not_ground`) and dropped rather than chased through the enclosing
  `quant-intro`/`quant-inst` pair that would close it. Resolving this fully
  needs enough of z3's `quant-intro` proof-rule semantics to be reimplemented
  to track schema variables across the DAG -- out of scope here, and it is
  the reason Count 1 is 7 of 53 rather than higher.
- **The admitted-instance arm's Skolem-name gap was found but not fixed** --
  see the dominant-typed-reason section above; `build-ground-from-dump.py`
  would need to also emit `declare-fun` lines for every internal
  `!qsk_`/`!qskf_`/`!qu_` symbol it references, with the right sort, which
  this lane did not attempt.
- **cvc5 was not run** as a third extraction source; the brief allowed it as
  a fallback for cores where z3 proof extraction fails, and z3 proof
  extraction did not fail on any of the 53 (all produced a proof), so the
  fallback was never needed.
