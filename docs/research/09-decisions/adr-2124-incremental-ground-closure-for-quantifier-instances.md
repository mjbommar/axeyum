# ADR-2124: incremental ground closure for quantifier instances — one gate, `online_clauses.is_none()`, puts every arithmetic file in the re-solve regime

Status: proposed
Index-summary: [ADR-2120] §7 located the quantified divisions' block at the **ground closure over the instance set**, and this lane found the whole mechanism is ONE `if`. The interleaved cold ground check fires behind `online_clauses.is_none()` (`qinst_egraph.rs`), so the retained CDCL(T) session and the from-scratch re-solve are **alternatives, not companions**: when the session exists the loop updates it, and when it does not, every due round re-solves the WHOLE accumulated ground set. `OnlineQuantifierClauseSession::new` builds its encoder without opaque abstraction, so one integer comparison anywhere in the ground set refuses the session — which is why UFLIA (and AUFDTLIRA, UFDTLIRA, AUFLIRA) are in the re-solve regime for their entire run. **Sizing, before code:** on ADR-2120's 53 reference-minimal UFLIA cores the check ran on 45 of 53, **493 calls**, median 11 and max 29 per core, over sets whose per-core maximum has median 1,356 and max **8,019** terms; 33 of 53 died on the clock and 32 of those had run it. Asserting each term ONCE is 71,127 against a linear-growth estimate of 437,373 re-solved — **6.1x**. On the Tier 1 ledger the quantifier route's own last decline names the interleaved check on **108 of 1,400**, **101** of them ending `unknown` (UFNIA 44/200, UFLIA 28/200, AUFDTLIRA 18/200, AUFLIRA 6/200, UF 4/200, UFDTLIRA 1/200). Level 1 (`AXEYUM_QINST_GROUND_SESSION=1`) abstracts the unencodable Boolean-position term to a free propositional variable so the session exists; the abstraction is a **weakening** (it only adds models) and, independently, the session's `Unsat` is **never the verdict** — it is re-established by `replay_online_refutation` over the same ground set with the ordinary cold route. **A certificate hole is closed in the same change**: the `CandidateFixpointStep::Refuted` exit returned `unsat` with NO instance-set certificate while the two cold-check exits beside it both collect one — invisible while the session declined every arithmetic file, load-bearing the moment it stops.
Index-status: proposed
Date: 2026-09-16

## 1. Context — three lanes, one block, and it was never where it was looked for

[ADR-2113] located `UFLIA`'s blocker at `rej_nocontext`. [ADR-2114] located
`AUFDTLIRA`'s at MBQI's shape guards. [ADR-2120] built the activation fix, and
its 53-core census refuted its own premise in the most useful way available: with
activation ON, on 53 cores **z3 refutes each E-matching-only in a median 108 ms**,
660,992 tuples were handed off, 41,230 instances were admitted, **87.9 % of z3's
own substituted terms were already in our ground set** — and **the verdict moved
on 0 of 53**.

So the instances are found, they are sufficient, and they are not the block. What
ADR-2120 §7 named instead was the **ground closure**: `quantifier_qf_check`
re-solves the whole accumulated ground set from scratch each time it is due, and
`OnlineQuantifierClauseSession` declines to exist on any ground set carrying an
arithmetic atom.

This lane's contribution is that those are not two facts. They are one.

## 2. The mechanism, at `file:line`

### 2.1 Ours — the gate is a single `if`

`crates/axeyum-solver/src/qinst_egraph.rs`:

| what | where |
|---|---|
| the interleaved cold check's **gate** | `prove_quantified_unsat_via_egraph_impl`, `if online_clauses.is_none() { … if interleaved_check_due(round) { … } }` |
| the cold check itself | `fn quantifier_qf_check(…)` → `check_auto(arena, ground, &remaining)` — a **fresh full solve of the whole `ground`** |
| the session's construction | `OnlineQuantifierClauseSession::new_with_limits` |
| **the decline site** | `let top = encoder.encode(arena, assertion, &mut clauses)?;` — the `?` on an encoder built `EufEncoder::new(&atom_terms).with_bool_apply_atoms()` and **no** `.with_opaque_bool_atoms(true)` |
| what the encoder does there | `euf_egraph.rs` `Encoder::encode`, arm `None => return None` — reached for any Boolean-sorted application with no connective arm: an arithmetic comparison, a `distinct`, an `is_int`, a datatype tester |
| the session's refutation exit | `scoped_candidate_fixpoint_step` → `CdcltOutcome::Unsat` → `replay_online_refutation` → `CandidateFixpointStep::Refuted` |
| the loop's handling of it | `CandidateFixpointStep::Refuted => …` in `prove_quantified_unsat_via_egraph_impl` |

**Read the gate and the decline site together and the regime is forced.** The
session and the cold check are alternatives. One integer comparison in the ground
set — and a `UFLIA` ground set has one in its first round — makes
`OnlineQuantifierClauseSession::new` return `None`, `online_clauses` stays `None`
for the whole run, and the loop pays a full cold re-solve of a monotonically
growing set on every due round. Nothing in the loop ever tries again.

This is the repository's oldest pattern, and it already has a documented fix in
the same tree: `axeyum-cnf`'s `IncrementalSat` and `IncrementalCnf` (ADR-0009)
exist because the BV path had it too.

### 2.2 z3 — the instance is internalized into the live context

Verified against the checked-out clone (`scripts/VERSION.txt` → `5.1.0.0`).

| what | where |
|---|---|
| the instantiation | `src/smt/qi_queue.cpp:199` `void qi_queue::instantiate(entry & ent)` |
| the lemma it builds | `src/smt/qi_queue.cpp:274-289` — `(or (not q) s_instance)` |
| **the hand-off** | `src/smt/qi_queue.cpp:336` `m_context.internalize_instance(lemma, pr1, gen);` |
| the receiver | `src/smt/smt_context.h:1781` `void internalize_instance(expr*, proof*, unsigned)` — guards on `inconsistent()` and forwards |
| into the live clause DB | `src/smt/smt_internalizer.cpp:288` `context::internalize_assertion` → `:1716` `mk_root_clause` → `:1460` `context::mk_clause`, which reads `m_scope_lvl` / `m_base_lvl` at `:1544-1546` and pushes into `m_lemmas` + the watch lists at `:1566-1568` |
| **the search is not restarted** | `src/smt/smt_context.cpp:4106` `bounded_search`, `:4174-4176` `case FC_CONTINUE: break;` — the same `while` loop simply continues |
| the quantifier module's return path | `src/smt/smt_context.cpp:4264` `m_qmanager->final_check_eh(true)`, `:4277-4278` `case FC_CONTINUE: return FC_CONTINUE;` |
| the theories that stay live across it | `src/smt/theory_arith.h:87` (`push_scope_eh`/`pop_scope_eh` at `:656-657`, bodies `theory_arith_core.h:3349`/`:3368`); `src/smt/theory_datatype.h:31` (`theory_datatype.cpp:735`/`:742`); `src/smt/theory_array_full.h:26` (`pop_scope_eh` at `theory_array_full.cpp:1097`, `push_scope_eh` inherited from `theory_array.h:64`) |

**Two corrections to the shape this was expected to have.** There is no
`context::add_clause` in this version — grep over `smt_context.{h,cpp}` returns
nothing, and `internalize_instance` is the single hand-off point. And no
`context::internalize*` is defined in `smt_context.cpp` at all; they all live in
`smt_internalizer.cpp`.

### 2.3 cvc5 — the instance is a lemma into the running prop engine

Verified against the checked-out clone (`cmake/version-base.cmake:2` →
`CVC5_LAST_RELEASE "1.3.4"`, `CVC5_IS_RELEASE "false"`).

| what | where |
|---|---|
| the instantiation | `src/theory/quantifiers/instantiate.cpp:92` `Instantiate::addInstantiation`, `:103` `addInstantiationInternal` |
| **the emit** | `src/theory/quantifiers/instantiate.cpp:339` / `:343` `d_qim.addPendingLemma(lem, id, p, …)` |
| the buffer | `src/theory/inference_manager_buffered.cpp:49` `addPendingLemma`, `:110` `doPendingLemmas`, `:180` `lemmaTheoryInference` → `:187` `trustedLemma` |
| the channel | `src/theory/theory_inference_manager.cpp:252` `trustedLemma` → `:273` `d_out.trustedLemma(tlem, id, p)` |
| **into the live engine** | `src/theory/theory_engine.cpp:1610` `TheoryEngine::lemma`, `:1659` `d_propEngine->assertLemma(id, tlemma, p);`, `:1683` `d_lemmasAdded = true;` |
| CNF into the running SAT solver | `src/prop/prop_engine.cpp:182` `assertLemma` → `:225` → `:265` → `:296` `d_cnfStream->convertAndAssert(node, removable, negated)` |
| the SAT→theory direction, same theories | `src/theory/theory_engine.cpp:1230` `assertFact`, `:1056` `assertToTheory` |
| it runs inside `check()` on the same context | `src/theory/quantifiers/theory_quantifiers.cpp:167-170` `postCheck` → `getQuantifiersEngine()->check(level)`; `src/theory/quantifiers_engine.cpp:187` `check`, `:266` `checkInternal`, `:455-457` the module effort loop, `:440-443` early return the moment a lemma was sent; `src/theory/theory_engine.cpp:444` `while (d_factsAsserted && !d_inConflict && !d_lemmasAdded)` |

**One correction.** `Instantiate::addInstantiation` does not call
`OutputChannel::lemma` or `TheoryEngine::lemma` directly; it goes through
`d_qim.addPendingLemma` and the buffered manager, as tabulated.

**Neither solver ever re-solves the ground part.** In both, the instance is a new
clause in the one context that already holds it.

## 3. Sizing — measured before any code was written

Artifacts: `bench-results/quant-ground-incremental-20260916/SIZING-ledger.txt`,
`SIZING-cores.txt`. Commit `6480135e6`.

### 3.1 Per division — the population this can move

Source: `bench-results/ledger/t1-<DIV>-db31113fa.tsv`, binary `db31113fa`, 200
benchmarks per division.

| division | n | unsat | unknown | qGROUND | qGROUND & unknown | bound by a `q:` route |
|---|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 200 | 119 | 81 | 18 | **18** | 198 |
| AUFLIRA | 200 | 178 | 22 | 6 | **6** | 185 |
| QF_NIA (unquantified control) | 200 | 6 | 116 | 0 | **0** | 0 |
| UF | 200 | 68 | 106 | 4 | **4** | 193 |
| UFDTLIRA | 200 | 138 | 56 | 1 | **1** | 192 |
| UFLIA | 200 | 86 | 114 | 34 | **28** | 197 |
| UFNIA | 200 | 33 | 146 | 45 | **44** | 165 |
| **total** | **1400** | 628 | 641 | **108** | **101** | 1130 |

`qGROUND` is "the quantifier route's OWN last decline detail names the
interleaved ground check". **It is not the `terminal()` reason and the difference
is written down on purpose.** `terminal()` as
`bench-results/quant-activation-20260915/core-census.py:96` defines it takes the
last decline of ANY route, and on every one of these rows that is a downstream
`fd:` route inheriting the same clock and printing the same generic string
("quantified solve time budget exhausted after MBQI and the finite-model
finder"). Reading that as the cause would attribute 0 of 1,400 to the ground
check and would be wrong in the direction that makes this lane look unnecessary.

`QF_NIA` is in the table as the control it is: an unquantified division, 0 of
200, which is what a correct query must return there.

### 3.2 Per core — what the check actually did

Source: `bench-results/quant-activation-20260915/cores/cores.tsv`, the ON arm, 53
rows.

| | |
|---|---|
| `qf-check` ran on | **45 of 53** |
| total calls | **493** |
| calls per core, where it ran | min 1, **median 11**, mean 11.0, **max 29** |
| per-core largest ground set handed to it | min 2, **median 1,356**, mean 1,581, **max 8,019** |
| terms re-solved, upper bound (calls × max) | 874,747 |
| terms re-solved, linear-growth estimate | **437,373** |
| terms if each were asserted **once** | **71,127** |
| ratio | **6.1x** |
| cores that died on the clock (`on_reason == budget`) | **33 of 53** |
| …that had run `qf-check` at least once | **32 of 53** |

The ground set GROWS across a core's calls, so `calls × max` over-counts and
`calls × 1` under-counts. Both bounds are printed in the artifact; the 6.1x is
the linear-growth estimate between them and is labelled as one.

**One absence is stated rather than zeroed.** ADR-2120 did not commit
`cores/raw/`, so per-core `qf-check` WALL TIME is not recoverable from the
ledger. Calls and set size are. Time is measured in this lane's own probe (§6).

## 4. The change

### 4.1 The lever

`GROUND_SESSION_LEVEL` in `config_registry.rs`, env override
`AXEYUM_QINST_GROUND_SESSION`, thread guard `GroundSessionLevelGuard`.
**Shipped at 0**, which is byte for byte the historical behaviour: the encoder is
built `with_opaque_bool_atoms(false)` and a Boolean-position term it has no arm
for still refuses the whole construction.

At level 1:

1. `OnlineQuantifierClauseSession::new_with_limits` builds the encoder
   `.with_opaque_bool_atoms(true)`, so the unencodable Boolean-position term
   becomes a free propositional variable and the session **exists** on an
   arithmetic ground set.
2. The encoder's variable for every term it abstracted is carried into the
   session as `opaque_variables`, so a later instance naming the SAME comparison
   reuses the SAME variable.
3. `online_opaque_clause_atom` admits those shapes as clause literals, and
   `ensure_atom` routes them to `ensure_opaque_variable` →
   `WarmNativeCdclT::add_variable` (new) rather than to `add_theory_variable`.

### 4.2 Two guards at level 1, both because an existing session SUPPRESSES the cold check

- **A ground set with no theory atom at all is declined.** Such a session is a
  pure Boolean skeleton: it refutes nothing the cold route's own skeleton would
  not, and keeping it would trade a real check for a vacuous one. Without this
  guard the lever would be a pure loss on files whose ground part is all
  arithmetic.
- **A Boolean CONNECTIVE is never abstracted.** `collect_clause_literals` splits
  on `or` and `not` only, so an `and`, an `=>`, an `ite` or an `xor` still
  arrives as a literal. Abstracting one is sound (weaker always is) but drops the
  clause structure while its subterms stay separately constrained. Those shapes
  keep the historical `Unsupported` → session-disabled → cold-route behaviour.

### 4.3 Why `WarmNativeCdclT::add_variable` is not `add_theory_variable` minus a line

`NativeTheoryAdapter::register_atom_variable` (`native_cdclt.rs:362`) **asserts**
that a variable is claimed at most once and pushes it onto `var_for_atom`, so an
atom index is allocated whether or not the theory can represent the term. A
caller that claimed one and then failed to give the theory a matching atom would
leave `var_for_atom` one longer than the theory's own atom list and every later
index off by one — a silent misattribution of asserted literals, which is a
wrong-answer defect. `add_variable` never touches the map.

### 4.4 The certificate hole, found and closed here

`CandidateFixpointStep::Refuted` returned `Ok(CheckResult::Unsat)` with **no
`*certificate`**. The two cold-check exits beside it — the ground-ceiling exit and
the interleaved-cadence exit — both do
`*certificate = collect_ground_derivations(arena, anchor, &ground, &ground_derivations)`.

It is the same certificate over the same facts: `scoped_candidate_fixpoint_step`
reaches `Refuted` only through `replay_online_refutation`, which re-establishes
the refutation over that very `ground` with the ordinary cold route. Before this
lane the gap was nearly invisible, because the session declined every arithmetic
file and the exit was reachable only on `EUF`-only ground sets. At level 1 it
becomes the main refutation route on `UFLIA` — so a lever that shipped without
this fix would have converted certified refutations into bare ones.

## 5. Soundness

**The abstraction is a weakening.** Replacing an atom by a free propositional
variable only ADDS models: every model of the original extends to one of the
skeleton by giving the variable the atom's truth value. So the skeleton is
weaker, an `unsat` of it transfers back to the original, and a `sat` of it says
nothing. Structural sharing keeps one variable per distinct hash-consed `TermId`,
so a repeated or negated occurrence stays consistent — which is what makes the
abstraction useful, not what makes it sound.

**Second and independent: the session's `Unsat` is never the verdict.**
`scoped_candidate_fixpoint_step` reaches `Refuted` only through
`replay_online_refutation`, an ordinary cold quantifier-free refutation over the
same ground set. The session picks WHEN to look; the cold route still says
whether the refutation is real.

**There is no retraction, so the stale-clause hazard has no mechanism.**
`add_checked_batch` calls `unwind_to_root()` before inserting and every insertion
is `add_permanent_clause` at root; `ground` is only ever appended to. A learned
clause is therefore derived from permanent root clauses and stays entailed by
them. The fixture below is written so that removing the `unwind_to_root` — the
one place that discipline lives — kills it.

### Fixtures

`crates/axeyum-solver/src/qinst_egraph.rs` (in-crate, the session's own surface):

| fixture | what it refutes |
|---|---|
| `ground_session_level_1_hosts_an_arithmetic_ground_set_level_0_refuses` | both halves: level 0 still refuses byte for byte, level 1 hosts. A test showing only level 1 working would pass if level 0 had silently started working too, and then the A/B's OFF arm would not be the shipped behaviour |
| `ground_session_level_1_never_manufactures_an_unsat_on_a_satisfiable_set` | **the stale-clause fixture.** Three batches of checked instances over a satisfiable arithmetic ground set, each arriving after the previous solve put decisions on the trail. Carries an independent `check_auto` control that the set really is satisfiable |
| `ground_session_level_1_reuses_one_variable_per_abstracted_term` | one variable per abstracted term across the construction boundary, and that it never enters the theory's atom map or the candidate-equality proposal |
| `ground_session_level_1_declines_a_ground_set_with_no_theory_atom` | the vacuous-session guard |

`crates/axeyum-solver/tests/quant_ground_session_soundness.rs` (query level, both
levels on every fixture):

| fixture | what it refutes |
|---|---|
| `SAT_ABSTRACTED_COMPARISONS` | an abstraction that is not a weakening — one that asserted the abstracted variable on the comparison's syntactic shape, or collapsed a polarity |
| `SAT_DISTINCT_COMPARISONS_NOT_COLLAPSED` | an abstraction keyed on anything coarser than the `TermId` (the operator, the sort, the right-hand constant): both comparisons collapse to one variable and the query becomes `v ∧ ¬v` |
| `SAT_MANY_ROUNDS` | the root-level insertion discipline end to end |
| `UNSAT_EUF_INSTANCE`, `UNSAT_EUF_INSTANCE_BESIDE_ARITHMETIC` | **positive controls.** A suite of satisfiable queries passes trivially against an engine that decides nothing |
| `the_two_levels_never_disagree_on_a_decided_verdict` | the ship gate as an assertion, with a `compared >= 2` guard so a differential that compared nothing cannot pass |

## 6. Measurement

_(Filled in by the 53-core probe and the divisional A/B; see §8.)_

## 7. Decision

_(Filled in with the ship decision.)_

## 8. What this lane did not do

_(Filled in.)_

[ADR-2113]: adr-2113-uflia-the-instance-we-never-produce.md
[ADR-2114]: adr-2114-aufdtlira-what-the-model-finder-cannot-represent.md
[ADR-2120]: adr-2120-quantifier-activation-by-assignment.md
