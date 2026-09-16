# QUANT-REACH-DIFF: which of z3's instances we never produce, and where

Four lanes removed candidate blocks on ADR-2113's 53 reference-minimal UFLIA
cores (z3 refutes each E-matching-only in ~108 ms with ~6 instances) without
moving the population: trigger alternatives (ADR-2113), incremental ground
closure (ADR-2124), activation-by-assignment (ADR-2120), arithmetic hosting
(ADR-2130). QUANT-INSTANCE-PROBE showed our ground checker refutes 6 of 7
cores when handed z3's OWN instances directly, so the block is not ground
refutation. ADR-2133 showed a generation ladder over our accumulated ground
set reaches its check on 31 of 53 cores and refutes at NONE — the refutation
is absent from our ground set at every generation, not buried in it. This
lane classifies every z3-used instance on all 53 cores against our
admitted/rejected/never-produced ground set, to say exactly where it is
lost.

## Method

For each core: z3's used instantiations are re-extracted from a fresh
`z3 :produce-proofs` run (`scripts/z3-proof-instances.py`, ~30 s budget, s4
pinned physical pair `6,7`); our side is `AXEYUM_QGROUNDDUMP` +
`AXEYUM_QPROBE` + `AXEYUM_QPROBE_CENSUS` on the ORIGINAL quantified core,
SHIPPED DEFAULT configuration (no lever overrides), same 24 s / 8 GiB budget
ADR-2120/2133 used. `classify.py`'s `classify_core` then sorts every unique
z3 ground instance body into one of four classes — full method and its
documented limits are in `classify.py`'s module docstring; the short version:

- **ADMITTED** — the body is in our own admitted (`gen>=1`) ground set,
  compared as a normalized string (commutative-arg sort + Skolem collapse).
- **MATCHED-REJECTED** — not admitted, but every one of z3's substitution
  arguments is a term SOMEWHERE in our ground set (checked against the
  flattened SUBTERM set of every dumped row, not row equality — see "Two
  bugs" below), and the run's rejection census shows nonzero evidence. Named
  reason is the CORE's dominant `rej_*` field (a core-level, not per-tuple,
  attribution — no per-substitution-tuple log exists in the shipped binary
  and this lane writes no Rust).
- **NEVER-MATCHED** — not admitted; either `trigger-did-not-fire` (arguments
  present, no rejection evidence) or `missing-term` (some argument never
  entered our ground set at all, at any generation).
- **NESTED** — z3's own recovered instance body still carries an unresolved
  outer bound variable (`z3-proof-instances.py`'s `not_ground` list) — a
  nested instantiation neither z3's proof nor this lane's extraction
  resolves without chasing the enclosing `quant-intro`/`quant-inst` pair.

**Host note.** The brief pins s6 physical pairs `1,9`/`3,11`. This session's
worktree exists only on s4 (`ssh s6 ls .../worktrees/agent-a178bf3df2d094f76`
→ no such directory; s6 has its own full checkout at the same path, just not
this agent's worktree). Ran on s4 instead, pinned physical pair `6,7`
(`/sys/.../thread_siblings_list` confirms 6-7 share one physical core on this
12600K), recorded in `qrd-run-ours.sh`'s own header rather than silently
substituted.

## Two bugs this lane's own classifier shipped and caught, not assumed away

Both are recorded here rather than quietly fixed, per CLAUDE.md's "ask what
it would print if it were broken" — each produced exactly that signature.

1. **Argument presence checked whole `GROUND` rows, not subterms.** The
   first full run put 100% of non-admitted, non-nested instances in
   `missing-term` (0 `MATCHED-REJECTED`, 0 `trigger-did-not-fire`), with
   `missing=[...]` naming BARE DECLARED SYMBOLS like `this`. Checked: a
   symbol like `this` is essentially never dumped as its OWN row —
   `AXEYUM_QGROUNDDUMP` records asserted/derived FORMULAS, not every
   e-graph leaf — so a top-level-row-only check reads it as absent even
   though it is trivially present as a leaf of a larger asserted term. Fixed
   in `classify.py` (`flatten_subterms`): presence is checked against every
   subterm of every dumped row. Regression tests:
   `test_bare_leaf_inside_a_larger_row_is_present` /
   `test_genuinely_absent_leaf_is_still_missing`.
2. **`UNIVERSAL_RE` was missing `re.M`.** Exactly the trap
   `bench-results/uflia-trace-20260915/silent-split.py`'s own docstring
   warns about: without `re.M`, Python's `$` anchors to the end of the WHOLE
   string, so `.*$` matches only when a `QPROBE universal[...]` line happens
   to be the very LAST line of the capture. Caught directly: `grep` found
   nonzero `rej_nocontext` on 26 of 53 `.err` captures, yet
   `MATCHED-REJECTED` was 0 on all 53 — the "empty result from a tool never
   pointed at your subject" signature. The two-line unit test fixture
   originally in this file could not have caught it (its target line WAS
   the last line before the final newline, which the buggy regex can still
   match); `test_a_non_final_line_is_still_parsed` adds a fixture with
   trailing content after the target line and fails without `re.M`.

A third, purely computational bug (not a correctness bug) is recorded in
`classify.py`'s `flatten_subterms` docstring: two earlier implementations
re-canonicalized or re-rendered each subtree at every recursion level
(`O(depth × size)` per row), and neither finished a 53-core sweep in a
bounded session on the real dumps (measured: 10 of 53 cores in 34 minutes,
killed). The shipped version renders each subterm exactly once
(`O(size)`), plus a documented `HUGE_ROW_CHARS = 20000` skip for the rare
row (232 of 1651 on one core) that is itself a multi-generation instance
chain 100+ KB long — z3's own substitution arguments are declared constants
or modest compound terms (ADR-2113's own median is 6 instantiations/core),
never that large, so the skip costs no real recall.

## The histogram, pooled over 53 cores

1,025 unique z3-used ground instance bodies classified (denominator =
`z3_uniq` per core, i.e. deduped ground bodies from z3's own proof, NOT the
raw `quant-inst` occurrence count, which is higher):

| class | count | share |
|---|---:|---:|
| ADMITTED | 11 | 1.1% |
| MATCHED-REJECTED | 169 | 16.5% |
| NEVER-MATCHED | 369 | 36.0% |
| NESTED | 476 | 46.4% |
| **TOTAL** | **1,025** | |

**NESTED's 46.4% matches QUANT-INSTANCE-PROBE's own finding almost exactly**
(46% of z3's recovered instances carry an unresolved outer bound variable) —
independent corroboration that this is a real, stable proportion of the
population, not an artifact of this lane's extraction.

MATCHED-REJECTED reason breakdown (core-dominant `rej_*`, summed):

| reason | count | mechanism |
|---|---:|---|
| `rej_nocontext` | 101 | matched, discarded: universal compiled under a disjunction/implication, `active: false` |
| `rej_seen` | 27 | tuple already admitted via another substitution (arguably not a loss) |
| `rej_true` | 26 | instance already semantically redundant (also not a loss) |
| `rej_flood` | 14 | per-round admission cap (`FLOOD_ROUND_ADMISSION_CAP`) |
| `rej_poscap` | 1 | positive-context admission cap |

NEVER-MATCHED reason breakdown:

| reason | count |
|---|---:|
| `missing-term` | 236 |
| `trigger-did-not-fire` | 133 |

## Per-core histogram

53 cores, `z3_uniq` = deduped z3 ground bodies, `no_dump` = our engine never
wrote an `AXEYUM_QGROUNDDUMP` block for this core (the e-matching/flood loop
never ran — a different dispatch rung decided the core first, see Worked
Example 2). Full table: `histogram.tsv`.

<!-- BEGIN-TABLE -->
| core | z3_uniq | no_dump | ADMITTED | MATCHED-REJECTED | NEVER-MATCHED | NESTED |
|---|---:|---|---:|---:|---:|---:|
| UFLIA_boogie_AdvancedTypes_InternalSubClass..ctor-orderStrength_1 | 10 | False | 0 | 4 | 0 | 6 |
| UFLIA_boogie_Arrays_Q3-noinfer | 2 | True | 0 | 0 | 2 | 0 |
| UFLIA_boogie_AssignToRepField_AssignToRepField.N | 30 | False | 1 | 0 | 7 | 22 |
| UFLIA_boogie_BasicMethodology_SubClass..ctor | 291 | False | 1 | 0 | 119 | 171 |
| UFLIA_boogie_Cast_Cast.R_System.Object_System.Int32 | 3 | False | 0 | 3 | 0 | 0 |
| UFLIA_boogie_Chunker11c_Chunker.SpecSharp.CheckInvariant | 1 | False | 0 | 1 | 0 | 0 |
| UFLIA_boogie_DefaultLoopInv0_A.M-modifiesOnLoop-noinfer | 95 | False | 0 | 26 | 2 | 67 |
| UFLIA_boogie_ExposeVersion_D..ctor-level_2 | 13 | False | 0 | 0 | 4 | 9 |
| UFLIA_boogie_Interval_Cell.Shift_System.Int32 | 37 | False | 1 | 13 | 0 | 23 |
| UFLIA_boogie_Spouse_Person..ctor | 12 | False | 0 | 6 | 0 | 6 |
| UFLIA_boogie_loopinv1_LoopInv1.Test1a_F_notnull-infer_eh | 135 | False | 0 | 0 | 89 | 46 |
| UFLIA_grasshopper_instantiated_delete_check_heap_access_53_12 | 5 | True | 0 | 0 | 5 | 0 |
| UFLIA_grasshopper_instantiated_insertion_sort_postcondition | 32 | False | 1 | 0 | 31 | 0 |
| UFLIA_grasshopper_uninstantiated_merge_loop_check_heap_access_60_6 | 14 | False | 0 | 14 | 0 | 0 |
| UFLIA_simplify_javafe.ast.CatchClauseVec.66 | 26 | False | 0 | 0 | 5 | 21 |
| UFLIA_simplify_javafe.ast.LexicalPragmaVec.219 | 18 | False | 0 | 0 | 8 | 10 |
| UFLIA_simplify_javafe.ast.NewInstanceExpr.271 | 1 | False | 0 | 1 | 0 | 0 |
| UFLIA_simplify_javafe.ast.StandardPrettyPrint.322 | 0 | True | 0 | 0 | 0 | 0 |
| UFLIA_simplify_javafe.ast.TypeDeclElemPragma.373 | 3 | False | 0 | 1 | 0 | 2 |
| UFLIA_simplify_javafe.ast.UnaryExpr.424 | 6 | False | 0 | 2 | 0 | 4 |
| UFLIA_simplify_javafe.parser.TokenQueue.576 | 1 | False | 0 | 1 | 0 | 0 |
| UFLIA_simplify_tohtml.Java2Html.832 | 3 | False | 0 | 0 | 3 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.PrintSpec.012 | 2 | True | 0 | 0 | 2 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.ast.ImportDeclVec.015 | 50 | False | 0 | 21 | 0 | 29 |
| UFLIA_simplify2_front_end_suite_javafe.ast.LabelStmt.011 | 1 | True | 0 | 0 | 1 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.ast.MethodDecl.005 | 24 | False | 0 | 16 | 8 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.ast.ParenExpr.006 | 0 | False | 0 | 0 | 0 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.ast.StandardPrettyPrint.008 | 0 | True | 0 | 0 | 0 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.ast.TypeModifierPragmaVec.013 | 29 | False | 1 | 9 | 0 | 19 |
| UFLIA_simplify2_front_end_suite_javafe.ast.VariableAccess.001 | 3 | True | 0 | 0 | 3 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.filespace.HashTree.001 | 17 | False | 0 | 6 | 0 | 11 |
| UFLIA_simplify2_front_end_suite_javafe.filespace.ZipTree.005 | 7 | False | 0 | 0 | 7 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.parser.Parse.005 | 23 | False | 0 | 0 | 23 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.parser.TagConstants.001 | 1 | False | 0 | 1 | 0 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.reader.CachedReader.003 | 7 | False | 2 | 5 | 0 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.tc.EnvForLocals.007 | 8 | False | 0 | 6 | 2 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.tc.FlowInsensitiveChecks.017 | 8 | False | 0 | 0 | 8 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.tc.TypeSig.001 | 3 | False | 0 | 3 | 0 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.tc.TypeSigVec.005 | 13 | False | 1 | 4 | 0 | 8 |
| UFLIA_simplify2_front_end_suite_javafe.tc.Types.035 | 8 | False | 0 | 7 | 1 | 0 |
| UFLIA_simplify2_front_end_suite_javafe.test.SuperlinksTest.004 | 6 | False | 2 | 4 | 0 | 0 |
| UFLIA_simplify2_small_suite_getRootInterface | 17 | False | 0 | 3 | 14 | 0 |
| UFLIA_sledgehammer_FFT_smtlib.898060 | 2 | True | 0 | 0 | 2 | 0 |
| UFLIA_sledgehammer_Fundamental_Theorem_Algebra_smtlib.1057395 | 5 | True | 0 | 0 | 5 | 0 |
| UFLIA_sledgehammer_Fundamental_Theorem_Algebra_smtlib.1462528 | 5 | True | 0 | 0 | 4 | 1 |
| UFLIA_sledgehammer_Fundamental_Theorem_Algebra_smtlib.972059 | 2 | True | 0 | 0 | 2 | 0 |
| UFLIA_sledgehammer_Hoare_smtlib.1175889 | 4 | True | 0 | 0 | 4 | 0 |
| UFLIA_sledgehammer_Hoare_smtlib.581330 | 17 | True | 0 | 0 | 4 | 13 |
| UFLIA_sledgehammer_Hoare_smtlib.993567 | 2 | True | 0 | 0 | 2 | 0 |
| UFLIA_sledgehammer_QEpres_smtlib.1065390 | 2 | True | 0 | 0 | 2 | 0 |
| UFLIA_sledgehammer_QEpres_smtlib.1120322 | 3 | True | 0 | 0 | 0 | 3 |
| UFLIA_sledgehammer_QEpres_smtlib.1237382 | 1 | False | 0 | 0 | 0 | 1 |
| UFLIA_tokeneer_auditlog_init-31 | 17 | False | 1 | 12 | 0 | 4 |
<!-- END-TABLE -->

(Core paths truncated to basename minus `.smt2.core.smt2` for width; full
names and every classified row are under `diff/<core>.smt2.core.smt2.tsv`.)

## Three worked examples

### 1. MATCHED-REJECTED / `rej_nocontext` — `UFLIA_boogie_AdvancedTypes_InternalSubClass..ctor-orderStrength_1`

**Quantifier** (core file line 165, the standard array write/read axiom):
`(forall ((?A Int)(?o Int)(?f Int)(?v Int)) (= (select2 (store2 ?A ?o ?f ?v) ?o ?f) ?v))`.

**z3's instance**: `(= (select2 (store2 Heap_0_ this inv_ InternalSubClass) this inv_) InternalSubClass)`
— substitution `A=Heap_0_, o=this, f=inv_, v=InternalSubClass`.

**Our engine's classification**: `MATCHED-REJECTED`, core-dominant reason
`rej_nocontext` (105,051 rejections of this type pooled over this core's
per-universal census — the largest single reject bucket by a wide margin;
this is a CORE-LEVEL attribution, not proven for this exact tuple, since no
per-substitution-tuple log exists — see Method).

**The mechanism, at `file:line`**: a universal compiled under a disjunction
or implication (this core's own negated goal nests several `forall`s inside
`and`/`=>` chains — e.g. the `?v_9`/`?v_10` bindings at line 167) is
registered as `active: false` by `collect_nested_registrations`
(`crates/axeyum-solver/src/qinst_egraph.rs:1844`, recursive helper `:1893`).
It is still matched — the tuples are found — but every matched tuple for
such a universal is discarded outright: `batch.rejects.inactive_dropped +=
tuples.len()` at `crates/axeyum-solver/src/qinst_egraph.rs:7294`. z3 and
cvc5 instead give the quantifier its own SAT literal and instantiate only
once the solver assigns it true (ADR-2113 §4b); we have no such notion.

**The recovery mechanism already exists and ships OFF.** ADR-2120 built
exactly this: `AXEYUM_QINST_POSITIVE_PATH` (activation-by-assignment) hands
off a matched-but-context-gated tuple as an entailed positive replacement
instead of discarding it — `batch.rejects.inactive_positive_capped` at
`qinst_egraph.rs:7291` is the capped/admitted counterpart of the same
decision point. Measured in ADR-2120 §7a: turning it ON recovers 660,992
tuples pooled over 16 cores where the OFF arm discarded them all — but
verdicts did not move, because the downstream ground closure was still the
blocker on that population (ADR-2120 §7e). This lane's own `rej_nocontext`
figure (101 of 169 MATCHED-REJECTED instances, 60%) says the LEVER's target
population is not empty on the population this lane classified either.

### 2. NEVER-MATCHED / `missing-term` — `UFLIA_boogie_Arrays_Q3-noinfer`

**Quantifier** (core file line 49, the same array axiom as example 1):
`(forall ((?A Int)(?o Int)(?f Int)(?v Int)) (= (select2 (store2 ?A ?o ?f ?v) ?o ?f) ?v))`.

**z3's instance**: `(= (select2 (store2 B o F (+ (select2 B o F) y)) o F) (+ (select2 B o F) y))`
— substitution `A=B, o=o, f=F, v=(+ (select2 B o F) y)`.

**Our engine's classification**: `NEVER-MATCHED` / `missing-term` — every
one of z3's four substitution arguments, including the compound term
`(+ (select2 B o F) y)`, is absent from our ground set, because **our
engine never wrote a ground dump for this core at all** (`no_dump=True`).

**The stage, verified by direct run**: `route decided_by=q:mbqi-quick
bound_by=q:mbqi-quick total_ms=0 attempts=9` — the bounded first-refusal
MBQI rung (`mbqi_first_refusal`, called at
`crates/axeyum-solver/src/auto.rs:2437`) decides the whole query BEFORE the
e-matching/flood engine ever runs. `run_egraph_quantified_fallback`, the
call that would enter `qinst_egraph.rs` and start accumulating a ground set,
sits at `crates/axeyum-solver/src/auto.rs:2440` — three lines later, never
reached. The comment at `auto.rs:2414-2429` documents WHY this ordering is
deliberate (a fast MBQI refutation should not be starved by a budget the
e-graph "reliably consumes every second it is given"), so this is not a bug
— it is a REAL, working shortcut for this exact 2-instance core (z3 itself
needs only these 2 instances too). The reach gap here is an ARTIFACT of
`no_dump` cores being counted as `missing-term` by this classifier, not
evidence our e-matching loop tried and failed to build these terms.

**A second, compounding gap this core still demonstrates (derived, not
run).** Even on a core WHERE the e-matching loop does run, this SAME
quantifier's shipped trigger differs structurally from z3's. Replicating
both sides' documented selection algorithms by hand
(`trigger_derive.py`, since no live profiler output is available on this
host — see the file's own docstring for why) on this quantifier's body:

| | trigger |
|---|---|
| ours (`select_triggers`, `qinst_egraph.rs:9765`; candidates from `collect_app_candidates:10095`) | `(select2 (store2 ?A ?o ?f ?v) ?o ?f)` — first pre-order full-cover candidate, no ranking |
| z3 (`pattern_inference.cpp`'s `filter_bigger_patterns`+`pattern_weight_lt`, cited in ADR-2113 §4a; replicated in `select_trigger_z3`) | `(store2 ?A ?o ?f ?v)` — smaller, minimal, more general |

Ours requires the WHOLE `select2`-wrapped term to appear literally in the
ground set before this universal's trigger fires at all; z3's fires on any
`store2` application. This is ADR-2113 §4a's finding (a single, unranked
trigger vs. both references' ranked/minimal one) made concrete on one axiom.

### 3. NEVER-MATCHED / `trigger-did-not-fire` — `UFLIA_simplify2_front_end_suite_javafe.tc.FlowInsensitiveChecks.017`

**Quantifier** (core file line 3443, subtype transitivity, with an EXPLICIT
user multi-pattern):
`(forall ((?t0 Int)(?t1 Int)(?t2 Int)) (! (=> (and (subtypes ?t0 ?t1) (subtypes ?t1 ?t2)) (subtypes ?t0 ?t2)) :pattern ((subtypes ?t0 ?t1) (subtypes ?t1 ?t2)) ))`.

**z3's instance**: `(or (subtypes T_javafe.ast.Expr T_java.lang.Object) (not (subtypes T_javafe.ast.Expr T_javafe.ast.ASTNode)) (not (subtypes T_javafe.ast.ASTNode T_java.lang.Object)))`
— substitution `t0=T_javafe.ast.Expr, t1=T_javafe.ast.ASTNode, t2=T_java.lang.Object`.

**Our engine's classification**: `NEVER-MATCHED` / `trigger-did-not-fire`.
**This is the sharpest of the three examples, and it is NOT a trigger-selection
difference**: the quantifier carries a USER `:pattern` annotation, so
`user_trigger_groups` (`qinst_egraph.rs:9649`) reads it and
`usable_trigger_groups` (`:9689`) installs it verbatim — we use the EXACT
SAME two-term multi-pattern z3 does. Directly checked against this core's
own ground dump: `(subtypes T_javafe.ast.ASTNode T_java.lang.Object)`
appears once; `(subtypes T_javafe.ast.Expr T_javafe.ast.ASTNode)` — the
SECOND pattern term — appears **zero times**, in any generation.

**The stage, at `file:line`**: a multi-pattern universal's tuples come from
joining matches across every group in `quantifier.pattern_groups`
(`qinst_egraph.rs:5767`, consumed at `:7677` `if
quantifier.pattern_groups.len() <= 1`, joined at `:7690`). The join can only
produce a tuple if BOTH pattern terms exist as ground facts to unify on the
shared variable `?t1`; here one never does.

**This example also exposes a real limit of this lane's own classifier**,
recorded rather than hidden: the `missing-term` vs `trigger-did-not-fire`
split checks presence of the LEAF substitution symbols
(`T_javafe.ast.Expr`, `T_javafe.ast.ASTNode`, `T_java.lang.Object` — all
three are bare declared constants, trivially present somewhere as leaves),
not the COMPOUND pattern-term `(subtypes T_javafe.ast.Expr
T_javafe.ast.ASTNode)` the join actually needs. By that finer standard this
row is really `missing-term` at the pattern-subterm level, not
`trigger-did-not-fire` — the coarse leaf check is a real, documented
imprecision in the 53-core aggregate histogram above (see `classify.py`'s
module docstring on lower/upper bounds), not a claim that trigger selection
is the mechanism here.

## The block, named, and the recoverable count

**The dominant class over all 53 cores is NESTED (46.4%), and it is the same
wall QUANT-INSTANCE-PROBE already found from the reconstruction side**: a
nested/context-dependent instantiation is either (a) impossible for THIS
lane's tooling to even name as a flat ground assertable term outside z3's
own proof-search session (the true NESTED class, 476), or (b) nameable but
discarded by our own engine at the exact SAME structural point —
`collect_nested_registrations` (`qinst_egraph.rs:1844`) marking the
universal `active: false`, then `inactive_dropped`
(`qinst_egraph.rs:7294`) or `inactive_positive_capped` (`:7291`) throwing
away what was matched — which is most of MATCHED-REJECTED's `rej_nocontext`
(101) and `rej_poscap` (1) rows, **102 of 169 (60.4%)**.

**Our engine DOES register instance-produced/nested universals for matching
at all** — `AXEYUM_NESTED_QUANT` defaults ON
(`crate::quant_skolemize::nested_quantifiers_enabled`,
`quant_skolemize.rs:142`; discovery site `qinst_egraph.rs:1642`, doc at
`:1365-1366`) — so the block named here is NOT "nested universals are never
matchable." It is specifically the ACTIVATION step: a nested universal is
matched and its tuples are computed, and then thrown away because our
engine has no notion of "this universal is currently entailed true," the
exact gap ADR-2113 §4b named and ADR-2120 already built a fix for
(`AXEYUM_QINST_POSITIVE_PATH`) — which ships OFF.

**The smallest change that recovers the largest counted class: turn ON
`AXEYUM_QINST_POSITIVE_PATH`.** It recovers the 102 `rej_nocontext`/
`rej_poscap` MATCHED-REJECTED instances this lane counted directly (60.4%
of that class), on top of the 660,992-tuple pooled recovery ADR-2120 already
measured. ADR-2120 §7e is explicit that this alone did not flip verdicts on
its own 53-core sweep, because the downstream ground closure was still the
blocker there — so this is a NECESSARY, not sufficient, recovery: it moves
real counted instances from discarded to admitted, and per QUANT-INSTANCE-PROBE
our ground checker already refutes 6 of 7 cores once handed a complete
instance set, so closing this gap is on the path to a verdict change even
though it is not proven to close one alone here.

**A second, smaller and independently actionable recovery: `missing-term`
(236) is not one shape.** Two of the three examples above show it is NOT a
single mechanism: Arrays_Q3-noinfer's `missing-term` rows are an artifact of
`mbqi-quick` deciding the core before e-matching ever runs (not a true reach
failure — z3 needs only 2 instances here too, and our engine already
decides this core correctly via a different route); FlowInsensitiveChecks'
`trigger-did-not-fire` row is arguably `missing-term` at the
pattern-subterm level once the leaf-check imprecision is accounted for. A
genuine, generation-level reach gap (our accumulated ground set never
reaching the generation z3's refutation needs) is exactly what ADR-2133 §
"Reach, not selection, on 22 of 35" already measured and is not re-derived
here; this lane's contribution is confirming, at the INSTANCE level and
with worked mechanism citations, that REACH — not selection, not ground
refutation — is the dominant remaining wall, and naming the one lever
(`AXEYUM_QINST_POSITIVE_PATH`) that is already built, already ships OFF, and
already recovers a measured, counted slice of it.

## Artifacts

- `classify.py` — the classifier (z3-side extraction reuse, canonicalization,
  the four-class decision function `classify_core`), with its own module
  docstring covering the method and its documented lower/upper-bound limits.
- `qrd-run-ours.sh` — the 53-core sweep on our side (shipped default config).
- `qrd-classify-all.py` — end-to-end driver (fresh z3 extraction + our
  already-collected dumps → per-core diff TSVs + histograms).
- `qrd-reclassify.py` — re-runs classification from ALREADY-collected data
  (no z3/solver re-invocation) when only the classification LOGIC changed;
  this is what let both bugs above get fixed and re-measured in minutes
  rather than the ~70-minute full sweep.
- `trigger_derive.py` — derives (not live-profiles; see its own docstring
  for why no live profiler output was available on this host) each side's
  shipped trigger-selection algorithm on one `forall` body.
- `diff/<core>.smt2.core.smt2.tsv` — one row per unique z3 instance body,
  per core: class, reason, detail, body, params.
- `histogram.tsv`, `histogram-summary.tsv`, `reason-summary.tsv` — the
  tables above, machine-readable.
- `runs-ours/run-summary.tsv` — per-core verdict/route/elapsed from the
  solver sweep. The raw captures (`runs-ours/dump/`, `runs-ours/raw/`,
  ~131 MB) are deliberately NOT committed, matching ADR-2120 §7e's
  precedent for the same kind of artifact; `qrd-run-ours.sh` regenerates
  them.
- `scripts/tests/test_quant_reach_diff_classify.py` — 17 unit tests on
  synthetic fixtures, no subprocess, no corpus dependency; includes
  regression tests for both bugs named above.

## What was not attempted

- **Per-instance (not core-level) rejection attribution.** The shipped
  binary's `AXEYUM_QPROBE_CENSUS` counters are per-universal, per-round
  aggregates; a true per-substitution-tuple rejection log would need new
  Rust instrumentation, which this lane's brief forbids. The three worked
  examples substitute hand-verified per-quantifier attribution (matching
  the exact source `forall` and, for #3, the exact pattern-term) where the
  53-core histogram's `MATCHED-REJECTED` reason is necessarily core-level.
- **Chasing z3's `quant-intro`/`quant-inst` DAG to resolve NESTED bodies
  fully.** QUANT-INSTANCE-PROBE already named this as out of scope (needs
  re-implementing enough of z3's schema-variable tracking to close the DAG);
  this lane's NESTED count (476) is the same structural gap, not a new one.
- **A live trigger profiler.** This host's z3 (4.13.3) rejects `-tr:*`
  (trace macros compiled out of this release build), and neither side prints
  its selected pattern under `smt.qi.profile`/`AXEYUM_QPROBE` in a form this
  lane's tooling could capture without new Rust. `trigger_derive.py`
  replicates both documented algorithms by hand instead, with the
  limitation stated in its own docstring.
