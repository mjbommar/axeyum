# ADR-2113: UFLIA does not fail to FIND the instance — it finds instances for universals it is not allowed to USE, and `rej_nocontext` is 100 % of the rejections

Status: proposed
Index-summary: UFLIA is **58 behind** cvc5 and the standing story is that our e-matching cannot find what z3's finds. Traced against z3 and cvc5 on [ADR-2090]'s 53 reference-minimal UFLIA cores, that story is **wrong in both halves**. The reference half: **all 53 cores are E-MATCHING-ONLY** — `z3 smt.mbqi=false` refutes 53 of 53, median 108 ms — and z3's own proofs name a **median of 6** instantiations against the 23 it makes; cvc5 agrees on 53 of 53. Our half: on the 19 cores whose per-universal probe runs at all, **444 of 500 universals (88.8 %) admit NO instance for the entire run** while the loop produces **4.3 M trigger joins and admits a median of 1,473 instances per core** (0.87 % of joins) against z3's median of 6 used. The decisive split — which no aggregate count can make and which this lane built `silent-split.py` to make — is that **NEVER-MATCHED is ZERO of 478** and **ALL-REJECTED is 429 of 478 (89.7 %)**, with **100.0 % of 2,139,815 rejections a single reason, `rej_nocontext`**: a universal nested under a disjunction or implication, compiled and matched, whose every tuple is *"joined and then discarded outright"* because `A ∨ (∀y. B(y))` does not entail `B(t)` and we hold no positive-replacement context for it. The fix is NOT prenexing — refuted with code: z3's `pull_nested_quantifiers` defaults to false, its `quantifier_hoister` has no caller under `src/smt`, and cvc5's default is the OPPOSITE (miniscoping). Both instead give the nested universal **its own SAT literal** and instantiate it only once the solver assigns that literal true (`smt_internalizer.cpp:647-666` + `smt_context.cpp:1473-1486`; `cnf_stream.cpp:539-556` + `theory_quantifiers.cpp:173-183`), so the missing mechanism is a **boolean-assignment guard on quantifier activation** — half of which this repository already has in `q:bool-skeleton` and the online CDCL(T) session, connected to nothing. The brief's premise does not survive either: **UFLIA has ZERO e-matching fixpoint give-ups** (the "12 fixpoints" is a cross-division count), its buckets are the interleaved ground check consuming the clock (12), `q:mbqi` ResourceLimit (8) and a watchdog (6). Two design claims are cited `file:line` on both sides. The lever this lane built and measured — trigger ALTERNATIVES, `AXEYUM_QINST_TRIGGER_ALTERNATIVES`, because z3 (`pattern_inference.cpp:458-467`) and cvc5 (`inst_strategy_e_matching.cpp:277-302`) keep several per quantifier and we kept exactly one — is **sound, tested, deterministic, and aimed at the bucket the census measures at ZERO**; it ships **OFF** and its A/B is reported as a measured number rather than an assumed one. The next lane's target is named with its denominator: make the nested universal's instances usable, not make more triggers.
Index-status: proposed
Date: 2026-09-15

## Context

UFLIA: we decide **86 of 200** on `bench-results/ledger/t1-UFLIA-db31113fa.tsv`;
cvc5 decides 142–144 and z3 139 on the six-division head-to-head. **58 behind.**

[ADR-2090] closed assertion *selection* as an axis and left the question sharper
than it found it: handed z3's own minimal unsat core, we return `unknown` on 193
of 230 rows, **15 of 53 for UFLIA** — the assertions already ARE the core and the
engine worked hard on them. It named the give-up strings but not the mechanism.

The brief for this lane proposed three candidate mechanisms: our trigger
selection does not fire where z3's does; our instantiation is bounded before the
needed term exists; or the ground checker cannot close what the instances imply.
It framed the population around **12 e-matching fixpoints** ("more rounds cannot
help").

**That framing does not survive contact with UFLIA.** The 12 is a count across
seven divisions. Re-derived on this branch over the 53 UFLIA cores, UFLIA has
**zero** fixpoint give-ups. So the first job was to find out what UFLIA's
give-ups actually are, and then what is underneath them.

## Decision

1. **The located cause is `rej_nocontext`, at a denominator of 2,139,815 and a
   share of 100.0 %.** UFLIA's e-matching finds instances; it finds them for
   universals whose instances are not entailed, and discards every one. This is
   recorded as the division's blocker, superseding "our triggers do not fire".
2. **The trigger-alternative lever ships OFF.** It is built, sound, tested,
   deterministic and reference-aligned — and the census measures its target
   bucket (NEVER-MATCHED) at **0 of 478**. It is kept as a measured lever with a
   working self-check rather than deleted, because an A/B that reports zero with
   an instrument proven able to tell the arms apart is evidence, and an
   un-run lever is not.
3. **No lever is built for `rej_nocontext` in this lane.** The fix is a
   **boolean-assignment guard on quantifier activation** (§4b) — not a
   preprocessing rewrite, which is the obvious hypothesis and is refuted with
   code on both references. It reaches across the dispatch ladder into
   `q:bool-skeleton` and the online CDCL(T) session, which is wider than this
   lane's diff is scoped to. The next lane gets the measurement, the two-sided
   source comparison, and the denominator.

## 1. The reference half: these cores are E-matching-only and cost z3 six instances

`bench-results/uflia-trace-20260915/ref/ref-cores.tsv`, four arms per core, on
pinned s6 cores. All 53 are cores [ADR-2090] produced and re-checked.

| arm | result |
|---|---|
| `z3 -st smt.qi.profile=true` | **53/53 unsat**, median **108 ms**, max 406 ms |
| `z3 -st smt.mbqi=false` | **53/53 unsat** |
| `z3 :produce-proofs` | 53/53 proofs |
| `cvc5 --stats` | **53/53 unsat** |

**Not one of these cores needs model-based instantiation.** E-matching alone
decides every one, which removes MBQI from the explanation entirely — and we
route 4 of the 53 into `q:mbqi` *datatype declines* and 8 more into `q:mbqi`
ResourceLimit.

Sizes, from z3's own numbers and its own proof:

| | med | p75 | p90 | max |
|---|---:|---:|---:|---:|
| instantiations **made** (`:quant-instantiations`) | 23 | 117 | 271 | 11,113 |
| instantiations **used** (`quant-inst` rules in the proof) | **6** | 17 | — | 292 |

`max-generation` is 1 on 16 cores, 2–3 on 25, and **≥ 4 on 11**: the needed
instance is typically built from a term an earlier instance introduced, ten
levels deep on one core. So nested instantiation depth is real — but it is not
our blocker: our matcher is already incremental in the same way z3's MAM is.
`IncrementalEmatchSession` carries `candidate_patterns: BTreeMap<usize,
BTreeSet<ENodeId>>` --- *"exact top applications added or reached since each
pattern's last scan"* (`qinst_egraph.rs:5466`) --- and a `merge_paths:
PatternPathIndex` that re-queues patterns a congruence merge affected, which is
what z3 does at `mam.cpp:4005-4024` (`relevant_eh` -> `add_candidate`) and
`:4032-4047` (`add_eq_eh` -> `process_pc`/`process_pp`). Neither side re-scans
everything each round. **The census confirms it from the other end: joins are in
the millions, so matching against newly introduced terms is plainly happening.**

**z3 over-produces about 4× as well** (23 made, 6 used). The gap is not that z3
is frugal.

**Stated at one denominator, because the obvious comparison is a category
error.** Our 37,414 is a SUM over 19 cores; z3's 6 is a per-core MEDIAN, and
putting them side by side compares a total with a middle value. Per core, ours
is a **median of 1,473 instances admitted** (min 105, max 5,663) against z3's
**median 23 made and 6 used**. Two orders of magnitude at a matched denominator,
not four.

`proof-instances.py` names the instances rather than counting them: it expands
z3's `let` chain, because the substituted terms arrive abbreviated (`(+ ?x55 y)`)
and reporting the abbreviation would name a z3 internal rather than a term of the
query. Its parser is iterative — a recursive one dies on the interpreter's stack
before reaching the first `quant-inst` on this population — and its expander is
depth-bounded, because an unbounded expander on a truncated proof is how a lane
reaches 63 GB.

## 2. Our half: 88.8 % of universals never produce an instance, and it is not triggers

`ref/census-cores.tsv` (53 cores) and `ref/census-originals.tsv` (the same 53
files unreduced), 24 s, `AXEYUM_TRACE=1 AXEYUM_QPROBE=1`, pinned s6 cores.

**The cores.** 38 of 53 undecided, median **19.4 s** against **226 ms** on the 15
we refute; 9 of the 38 give up under 2 s and 17 run ≥ 20 s — a refusal and an
exhausted clock behind the same `unknown`, in roughly a quarter/half split.

| terminal route × give-up | n |
|---|---:|
| `q:egraph` ResourceLimit | 14 |
| `q:mbqi` ResourceLimit | 8 |
| — Watchdog | 6 |
| `q:bool-skeleton` ResourceLimit | 3 |
| `q:mbqi` Incomplete | 2 |
| `q:egraph` Incomplete | 2 |
| others | 3 |

Verbatim and unbucketed, because sizing a bucket by its LABEL is how a census
reports one cause where the raw details hold four:

    14  quantified solve time budget exhausted after MBQI and the finite-model finder
    12  e-matching: instantiation time budget exhausted mid-round (the interleaved
        ground check did not decide the set inside the deadline)
     6  watchdog fired before the worker thread returned
     4  mbqi declined an unsupported fragment: term #N has sort (Uninterpreted K)
     1  e-matching instantiation stopped after 216 rounds
     1  combined theories: eager Ackermann elimination would emit 398,989 congruence constraints

**Zero fixpoints.** The brief's "more rounds cannot help" bucket does not exist
in this division.

**The scale.** 19 of 53 cores printed a per-universal probe at all — the other 34
exit on a time budget before the probe block, which sits behind
`if admitted.is_empty()` (`qinst_egraph.rs:2553`), and are **not zeros**. On
those 19:

| | |
|---|---:|
| universals | 500 |
| universals that admitted **nothing all run** | **444 (88.8 %)** |
| universals with **no trigger at all** | **1 (0.2 %)** |
| trigger joins | 4,307,703 |
| instances admitted, summed | 37,414 (**0.87 %** of joins) |
| instances admitted, **median per core** | **1,473** (min 105, max 5,663) |
| instances z3 **uses**, median per core | **6** |

On the **original** files rather than the cores, 0 of 53 decided and admitted
instances pin near `MAX_GROUND_TERMS` (7,500–8,174) within 3–7 rounds: the flood
regime, reached in seconds.

## 3. The split that decides it, and it is not the one anybody was looking for

Three situations produce `admitted=0` and have **opposite** remedies. Counting
silent universals cannot separate them; `silent-split.py` does, from the
per-universal probe rows, over the 19 shaped cores:

| class | n | share |
|---|---:|---:|
| FIRED (admitted ≥ 1) | 48 | 10.0 % |
| **NO-TRIGGER** (`patterns=0`) | **1** | **0.2 %** |
| **NEVER-MATCHED** (`patterns>0, joined=0`) | **0** | **0.0 %** |
| **ALL-REJECTED** (`joined>0, admitted=0`) | **429** | **89.7 %** |

**NEVER-MATCHED is zero.** Not one silent universal is silent because its trigger
failed to match. Every one produced joins and none became an instance.

And the reason is a single one:

| reject reason | count | share |
|---|---:|---:|
| **`rej_nocontext`** | **2,139,815** | **100.0 %** |
| every other reason | 0 | 0.0 % |

`rej_nocontext` is `AdmissionRejects::inactive_dropped`
(`qinst_egraph.rs:4597-4599`), whose own doc says it exactly:

> The universal is a non-asserted registration with NO context. Its tuples are
> joined and then discarded outright — nothing downstream sees them.

The drop is at `qinst_egraph.rs:6196-6215`: a `CompiledUniversal` with
`active == false` and `context == None`. It is **correct**. A universal nested
under a disjunction or an implication is not an assertion, and `A ∨ (∀y. B(y))`
does not entail `B(t)`, so admitting the bare instance would be unsound. The
machinery for the legitimate move exists — `PositiveContext` and the Slice-3
discovery driver turn a matched tuple into the entailed positive replacement
`owner ⊨ owner[∀y.B := B(t)]` — and on this population it is **absent on 429 of
478 universals**, so 2.1 M matched tuples are discarded.

**That is where UFLIA's e-matching budget goes.** The loop is not failing to find
instances. It is spending its clock finding instances for universals it may not
use, and then timing out in the interleaved ground check over what little it
kept.

## 3a. And the terms z3 substitutes ARE in our ground set

The brief asks for *"the instance z3 needed that we never produced -- name it."*
**On this division there is no such instance, and that is the answer.**

`ground-membership.py` takes our `AXEYUM_QGROUNDDUMP` -- the whole accumulated
ground set at the loop's exit -- and asks, for every term `proof-instances.py`
pulled out of z3's own `quant-inst` rules, whether we ever built it.

<!-- MEMBERSHIP-RESULT -->

This separates the two situations that produce identical `unknown`s and need
opposite fixes: *we never build it* (no cap, budget or ranking can reach it) and
*we build it and do not use it* (a selection or admission problem). The UF lane's
2026-09-10 note found the first on 10 of 16 files. **UFLIA is the other one.**

**How this file's first answer was wrong, and what it would have published.**
The first version compared each substituted term against a `GROUND` ROW. A
`GROUND` row is a whole asserted CONJUNCT, not a term. So it returned **ABSENT on
100 % of arguments on every core** -- including bare declared constants
(`nullObject`, `this`, `J`) which cannot be missing: `nullObject` occurs 215 times
inside one 34-row dump. Read at face value that table says *"we never construct
the term z3 needs"*, which is this lane's headline with the sign flipped. A
100 % ABSENT that includes a constant is the signature of a comparison that never
matches. The test is now containment over the rendered ground set at identifier
boundaries, and it carries a **non-vacuity control** -- a synthetic symbol that
cannot occur -- because a containment test over a multi-megabyte corpus drifts
toward answering PRESENT for everything, and then the zero on the other side
means nothing. Both failure directions are now guarded and `CAN-ANSWER-ABSENT` is
printed on every row.

**PRESENT is strong, ABSENT is a lower bound.** The dump holds whatever the run
accumulated before its deadline, and this pass ran unpinned while the A/B held
this lane's cores. Load can only make a run build FEWER terms, so it can only
move rows from PRESENT to ABSENT -- which makes a PRESENT column measured under
load a conservative reading, and an ABSENT column not a proof of anything.

## 4. Two design claims, `file:line` on both sides

### 4a. Trigger alternatives: both references keep several, we kept one

| | |
|---|---|
| z3 | `pattern_inference.cpp:458-467` (`candidates2unary_patterns`) makes **every** surviving full-cover candidate its own single-pattern; `:718` attaches them all via `update_quantifier(q, new_patterns.size(), …)`. `filter_bigger_patterns` (`:391-396`) keeps the minimal ones, `pattern_weight_lt` (`:399-408`) ranks *more free variables, then smallest size*, and `filter_looping_patterns` (`:288-307`) drops self-re-matching candidates. |
| cvc5 | `inst_strategy_e_matching.cpp:277-302` registers a separate `Trigger` per single pattern term — its own comment is *"add all considered single triggers"* — under the default `triggerSelMode = MIN` (`quantifiers_options.toml:428-449`). Multi-triggers are capped at one (`:329-336`). |
| **ours** | `qinst_egraph.rs:5594` called `select_triggers` and wrapped it in a **one-element `vec!`**; `select_triggers` (`:8684`) returns the **first** candidate covering every variable in pre-order — no size ranking, no minimality filter, no loop filter, no alternatives. |

The matcher could always hold alternatives: `CompiledUniversal::pattern_groups`
(`:4782`) unions the alternatives' tuple sets, and user `:pattern` annotations
already produce several. Its own doc named the gap — *"Auto trigger selection
produces exactly one alternative."*

**This claim is true and it is not the blocker.** It can only move a
NEVER-MATCHED universal, and NEVER-MATCHED is 0 of 478. The lever is built
anyway (§5) and measured, so the zero is a measurement.

### 4b. The nested universal: they gate it on a SAT LITERAL, we gate it on a syntactic context computed once

**This lane's first hypothesis here was that both references PRENEX — hoist the
inner universal to a top-level quantified clause before instantiation. That is
refuted, with code, and the truth is sharper.** Recording the refutation because
the hypothesis is the obvious one and the next lane would have spent its time on
it: z3's `pull_nested_quantifiers` defaults to **false**
(`preprocessor_params.h:35`, `smt_params_helper.pyg:31`) and merges quantifiers
nested in another quantifier's *body*, not out of a disjunction; z3's NNF
skolemizes existentials only and rebuilds a positive `forall` in place
(`nnf.cpp:759-812`, default mode `skolem` at `nnf_params.pyg:6`); its
`quantifier_hoister` has **no caller under `src/smt` or `src/solver`** — every
call site is QE or Datalog (`qsat.cpp`, `nlqsat.cpp`, `qe.cpp`, `hnf.cpp`,
`dl_rule.cpp`); and `asserted_formulas.cpp:284-308`, the whole default
preprocessing list, contains **no hoisting step at all**. cvc5's default is the
*opposite* — miniscoping, `miniscopeQuant = CONJ_AND_FV`
(`quantifiers_options.toml:14-32`) — and its `prenexQuant = SIMPLE`
(`:46-61`) takes the enclosing quantifier as its first argument
(`quantifiers_rewriter.cpp:1918-1931`), so an assertion with no enclosing
quantifier is never prenexed, and one carrying a user pattern is excluded outright
(`:2568-2583`).

What they actually do is the same thing as each other, and we do not do it:

| | |
|---|---|
| z3 | `internalize_quantifier` gives the quantifier **its own boolean variable** and flags it: `bool_var v = mk_bool_var(q); … d.set_quantifier_flag(); m_qmanager->add(q, generation);` (`smt_internalizer.cpp:647-666`). Instantiation starts **only when the SAT solver assigns that literal true** — `if (get_assignment(v) == l_true) { … assign_quantifier(…); }`, with the comment *"All universal quantifiers have positive polarity in the input formula. So, we can ignore quantifiers assigned to false"* (`smt_context.cpp:1473-1486`), reaching `m_qmanager->assign_eh(q)` at `:1868-1871`. |
| cvc5 | A `FORALL` under an `OR` falls through the CNF stream's connective cases to `convertAtom` (`cnf_stream.cpp:539-556`), so it gets its own SAT literal inside the clause; when the solver asserts it, `preNotifyFact` routes it to `getQuantifiersEngine()->assertQuantifier(atom, polarity)` (`theory_quantifiers.cpp:173-183`). |
| **ours** | `collect_nested_registrations` compiles a universal under a disjunction as an INACTIVE `CompiledUniversal` (`active: false`, `qinst_egraph.rs:4794`) whose usability is decided **once, statically, from the syntax**: present exactly when a `PositiveContext` could be computed. It is matched anyway, and every matched tuple is **discarded outright** at `:6196-6215`, counted as `inactive_dropped` (`:4597-4599`). **100.0 % of 2,139,815 rejections on this population.** |

**So the missing mechanism is not a rewrite. It is a boolean-assignment guard on
quantifier activation.** For `A ∨ (∀y. B(y))`, both references let the SAT solver
decide `A` false, which forces the quantifier's literal true, and *under that
assignment* `B(t)` is entailed — no context is needed and nothing is dropped. We
have no notion of "this universal is currently asserted true", so a nested
universal is permanently in the worst of both states: matched (paying the full
join cost — 2.1 M tuples here) and never usable.

The asymmetry is not that their matcher is better. **Their matcher is asked the
question only when the answer is usable; ours is asked it 2.1 M times and throws
every answer away.**

## 5. The lever, and why it ships OFF

`AXEYUM_QINST_TRIGGER_ALTERNATIVES`, shipped `1`, byte for byte today's
behaviour: `select_trigger_groups` short-circuits at `≤ 1` to the single call the
compile loop used to inline, so the OFF path does not run one line of the new
selection.

At a cap above 1 it makes every full-cover candidate its own alternative; drops a
candidate that properly contains another full-cover candidate (exact, because the
arena hash-conses — if `b` is inside `a` and both cover every variable, every
ground match of `a` carries a match of `b`, so `a` proposes a subset at strictly
higher cost); orders by `witness_size` then `TermId`, which is total because
`TermId`s are dense in insertion order; truncates to the cap; and falls back to
`select_triggers` when there is no full-cover candidate.

**Soundness is unconditional and not a property of the ordering.** A trigger's
only output is a substitution; every admitted instance is
`replace_subterms(body, x ↦ t)` and `∀x. B ⊨ B[x := t]` for *every* ground `t`.
Alternatives can cost time and change which refutation is found first; they
cannot produce a wrong `unsat`.

**Two defects this lane's own tests caught, recorded because each would have
passed every verdict check.**

- The containment filter was **inverted**: written
  `is_proper_subterm(arena, other, candidate)`, it dropped the CONTAINED
  candidate and kept the CONTAINER — the opposite of both references, keeping the
  deepest pattern, which matches least often. A worse trigger loses *decisions*,
  not soundness, so only a test asserting the surviving `TermId` rather than the
  count could fire. One did.
- The soundness fixtures were **vacuous**. `∀x. f(g(x)) = a` has two full-cover
  candidates, but they are NESTED, so the containment filter collapses them to
  one and a raised cap compiles exactly the shipped pattern. Every "a raised cap
  did not refute the satisfiable query" assertion would have compared the shipped
  arm with itself. Both fixtures now use INCOMPARABLE candidates, and
  `a_raised_cap_proposes_both_incomparable_candidates` is the control: 2 groups
  at cap 4, 1 at cap 1.

`TriggerAlternativeCapGuard` is a thread-local in the shape of
`GroundBudgetGuard`, because the process cap resolves once into a `OnceLock` and
a lever whose ON arm is reachable only by re-launching the binary has no
in-process soundness test. **It does not cross a thread boundary**, and
`smtcomp_cli` solves on a watchdog worker thread — so the A/B uses the
environment variable, and `the_guard_does_not_cross_a_thread_boundary` is that
reason written as a failing condition rather than a comment.

<!-- AB-RESULT: filled from `ref/ab-summary.txt` and `ref/recheck-movers.tsv`. -->

## 6. What this lane measured about its own instruments

Three of them were wrong first, each in a way that reads as a finding.

- **`probe-shape.py`** printed `NA` for `silent` and `0` for `joined`,
  `starved`, `admitted` — all four read from one segment set, so a row with no
  measurement read as *"no join was found"*. All four now print `NA` together.
- **`silent-split.py`** matched `(.*)$` without `re.M`, so `$` anchored to the
  end of the WHOLE input and every file came back `NO-PROBE-ROWS` — an empty
  result from an instrument pointed straight at its subject.
- **`silent-split.py` again**: with `AXEYUM_QPROBE=1` alone every `rej_*` field
  prints `0`, because `AdmissionCensus::enabled` is
  `qprobe_enabled() && census_enabled()` — including `census_admitted=0` on a
  universal that admitted 148 instances. Reading that as "rejected for no
  recorded reason" attributes a cause to a measurement nobody took. It now
  decides from the DATA whether the census ran and prints `REASONS-UNMEASURED`;
  the uncensused output is kept at `ref/silent-nocensus.shard*.txt`.
- **`ab-self-check.sh`** failed on its first run, correctly: its hand-written
  two-candidate fixture is refuted by `q:mbqi-quick` at attempt 9 of the ladder,
  so the e-matching compile loop never runs and no probe line exists. A
  self-check that had defaulted to "no line means no difference" would have
  reported PASS.

## Consequences

- **The next lane's target is `rej_nocontext`, not triggers**, with a
  denominator: 429 of 478 universals, 100.0 % of 2,139,815 rejections, on 18
  shaped cores of 53. **Do not spend the lane on prenexing** — §4b refutes that
  route with code on both references. The two routes worth sizing are
  (a) **gate quantifier activation on a boolean assignment**, which is what both
  references do and which this repository already has half of: `q:bool-skeleton`
  (ADR-2025) computes exactly the assignment that would license a nested
  universal, and `OnlineQuantifierClauseSession` already holds a live CDCL(T)
  session over the ground set. Nothing connects either to
  `CompiledUniversal::active`; and (b) widen where a `PositiveContext` is
  computed at compile time, which is bounded and testable and reaches a subset of
  what (a) reaches. Size (b) first, build (a).
- **A second, independent finding for whoever takes (a):** the interleaved ground
  check calls `check_auto` over the WHOLE accumulated ground set from scratch
  (`qinst_egraph.rs:3416` via `quantifier_qf_check`), every round inside the
  cadence window and at power-of-two rounds beyond it; the one retained
  accelerator, `OnlineQuantifierClauseSession`, abstracts every arithmetic atom
  to a fresh boolean (`euf_egraph.rs:2163-2180`), so on UFLIA it structurally
  cannot see the LIA half of a refutation, and while it stays alive it
  *suppresses* the arithmetic-aware per-round check (`:2365`). That is the
  mechanism behind this division's second-largest give-up, *"the interleaved
  ground check did not decide the set inside the deadline"* (12 of 38). It is not
  measured further here.
- **`AXEYUM_QINST_TRIGGER_ALTERNATIVES` stays OFF** and is not re-measured on
  this population without a reason; its bucket is zero here. It may still matter
  on a division whose silence IS unmatched triggers — `universals-without-triggers-2026-09-10.md`
  measured UF's category A at 728 triggerless universals, a different shape
  entirely — and the lever is now there to measure that with.
- **`silent-split.py` is the reusable instrument**, not the numbers: any division
  can be asked the NEVER-MATCHED / ALL-REJECTED question, and no other tool here
  answers it.
- MBQI is removed from UFLIA's explanation: `smt.mbqi=false` refutes 53 of 53.
  Time spent in `q:mbqi` on this division (8 ResourceLimit + 2 Incomplete of 38)
  is time spent on a rung the reference does not need.

[ADR-2050]: adr-2050-the-eleven-are-four-causes-and-the-largest-is-one-refused-atom.md
[ADR-2090]: adr-2090-the-cores-are-small-and-findable-and-we-do-not-decide-them.md
