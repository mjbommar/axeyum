# ADR-2124: incremental ground closure for quantifier instances — one gate, `online_clauses.is_none()`, puts every arithmetic file in the re-solve regime

Status: proposed
Index-summary: [ADR-2120] §7 located the quantified divisions' block at the **ground closure over the instance set**, and this lane found the mechanism: `online_clauses.is_none()` selects between TWO interleaved-check sites that differ by **seven rounds** — the no-session branch re-solves the whole accumulated ground set on rounds 0-6 and then on 7, 15, 31, …, while a live session skips to the exponential schedule alone. (An earlier draft of this ADR said a live session suppresses the check outright; **38 of 53 cores ran an identical number of cold checks in both arms**, which suppression cannot produce, and §2.1.1 records the correction.) `OnlineQuantifierClauseSession::new` builds its encoder without opaque abstraction, so one integer comparison anywhere in the ground set refuses the session — which is why UFLIA (and AUFDTLIRA, UFDTLIRA, AUFLIRA) are in the re-solve regime for their entire run. **Sizing, before code:** on ADR-2120's 53 reference-minimal UFLIA cores the check ran on 45 of 53, **493 calls**, median 11 and max 29 per core, over sets whose per-core maximum has median 1,356 and max **8,019** terms; 33 of 53 died on the clock and 32 of those had run it. Asserting each term ONCE is 71,127 against a linear-growth estimate of 437,373 re-solved — **6.1x**. On the Tier 1 ledger the quantifier route's own last decline names the interleaved check on **108 of 1,400**, **101** of them ending `unknown` (UFNIA 44/200, UFLIA 28/200, AUFDTLIRA 18/200, AUFLIRA 6/200, UF 4/200, UFDTLIRA 1/200). Level 1 (`AXEYUM_QINST_GROUND_SESSION=1`) abstracts the unencodable Boolean-position term to a free propositional variable so the session exists; the abstraction is a **weakening** (it only adds models) and, independently, the session's `Unsat` is **never the verdict** — it is re-established by `replay_online_refutation` over the same ground set with the ordinary cold route. **A certificate hole is closed in the same change**: the `CandidateFixpointStep::Refuted` exit returned `unsat` with NO instance-set certificate — and it is one of a MATCHED PAIR, because the session's OTHER refutation exit (the batch path) already collected one through the identical replay over the identical ground set, with a comment saying why it is certifiable. Three of four sites were right.
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
| the session's refutation exits, **both of them** | (a) the batch path: `add_checked_batch` → `Some(CdcltOutcome::Unsat)` → `replay_online_refutation` → `return Ok(CheckResult::Unsat)`, which **already collected the certificate**; (b) the fixpoint path: `scoped_candidate_fixpoint_step` → `CdcltOutcome::Unsat` → `replay_online_refutation` → `CandidateFixpointStep::Refuted`, which **did not** |
| the interleaved check with a LIVE session | a second site: `if online_clauses.is_some() && round + 1 >= instantiation_cadence() && (round + 1).is_power_of_two()` — see §2.1.1 |

**Read the gate and the decline site together and the regime is forced.** One
integer comparison in the ground set — and a `UFLIA` ground set has one in its
first round — makes `OnlineQuantifierClauseSession::new` return `None`,
`online_clauses` stays `None` for the whole run, and the loop takes the cold
branch every time. Nothing in the loop ever tries again.

### 2.1.1 What the gate actually selects — and the correction this lane had to make to itself

The first version of this ADR said the session and the cold check are
"alternatives, not companions", and that when the session exists the loop never
re-solves. **That is wrong, and the probe's own numbers are what exposed it**:
38 of 53 cores ran an IDENTICAL number of cold checks in both arms, which a
clean alternation could not produce. Reading further down the loop found the
reason, and the true statement is narrower.

There are **two** interleaved-check sites, one per branch:

| branch | site | cadence | rounds it fires on |
|---|---|---|---|
| no session | inside `if online_clauses.is_none()`, guarded by `interleaved_check_due(round)` = `round < instantiation_cadence() \|\| (round + 1).is_power_of_two()` | per-round then exponential | **0,1,2,3,4,5,6**, 7, 15, 31, 63, … |
| live session | a separate `if online_clauses.is_some() && round + 1 >= instantiation_cadence() && (round + 1).is_power_of_two()` | exponential only | 7, 15, 31, 63, … |

`instantiation_cadence()` is `MAX_INSTANTIATION_ROUNDS = 8`. So the difference
the lever buys **by cadence alone is exactly rounds 0–6: seven per-round cold
re-solves**, and from round 7 onward the two regimes run the identical
exponential schedule.

That is not the whole difference, and the probe shows why: the heaviest core goes
from **30 cold checks to 15**, which is more than seven. A live session also
changes what each round DOES — `scoped_candidate_fixpoint_step` proposes
candidate equalities to the matcher on a round that admitted nothing — so the two
arms diverge in their round SEQUENCES and the call counts diverge with them. The
cadence difference is the floor; the sequence divergence is the rest, and it can
go either way (11 of 53 cores spend MORE time in the check at level 1).

**Both halves of that are worth stating because the first version of this ADR
stated neither.** A reader who took "alternatives, not companions" at face value
would over-predict the saving by the whole exponential tail, which is where the
ground sets are largest.

This is still the repository's oldest pattern, and it already has a documented
fix in the same tree: `axeyum-cnf`'s `IncrementalSat` and `IncrementalCnf`
(ADR-0009) exist because the BV path had it too.

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
`*certificate`**.

**The argument for the repair is stronger than "the cold exits do it", and the
strongest form was found by reading rather than assumed.** The session has TWO
refutation exits, not one. The batch path — `add_checked_batch` returns
`Some(CdcltOutcome::Unsat)`, `replay_online_refutation` confirms — **already
collected the certificate**, with a comment saying exactly why:

> *"The online CDCL(T) session found the conflict, but `replay_online_refutation`
> re-established it against `ground` — so this is a ground refutation by the same
> instances as every other exit, and is certifiable."*

The fixpoint path reaches `Refuted` through the identical `replay_online_refutation`
over the identical `ground`, and collected nothing. So this was not a design
question at all: it was one of a matched pair, written and justified, with the
other half missing. Two cold-check exits (the ground ceiling and the
interleaved cadence) make it four sites, three of which were right.

Before this lane the gap was nearly invisible, because the session declined every
arithmetic file and the fixpoint exit was reachable only on `EUF`-only ground
sets. At level 1 the session exists on `UFLIA` — so a lever that shipped without
this fix would have turned certified refutations into bare ones on exactly the
division it targets.

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

**There is no retraction, so the stale-clause hazard has no mechanism** — and
this lane's own mutation is what established it rather than the reading that
motivated the brief. `ground` is only ever appended to and every insertion is
`add_permanent_clause`, so a learned clause is derived from permanent root
clauses and stays entailed by them. Removing `add_checked_batch`'s
`unwind_to_root()` — the call that *looks* like the guard against inserting
under a live trail — **killed nothing** (§5.1). `NativeIncrementalCdcl::add_clause`
(`crates/axeyum-cnf/src/proof_sat/incremental.rs:486`) calls `between_solves()`
itself, unconditionally, before touching the database: a clause is always
registered into an unassigned solver whether or not the caller asked. What the
session's own call buys is stated in that method's own doc comment
(`incremental.rs:515-520`) and is **liveness, not soundness** — it closes the
previous solve's theory epoch so `EufTheory::add_atom_at_root`, reached from
`ensure_atom` before the batch's first `add_clause`, accepts a registration
instead of refusing it.

### Fixtures

`crates/axeyum-solver/src/qinst_egraph.rs` (in-crate, the session's own surface):

| fixture | what it refutes |
|---|---|
| `ground_session_level_1_hosts_an_arithmetic_ground_set_level_0_refuses` | both halves: level 0 still refuses byte for byte, level 1 hosts. A test showing only level 1 working would pass if level 0 had silently started working too, and then the A/B's OFF arm would not be the shipped behaviour |
| `ground_session_level_1_never_manufactures_an_unsat_on_a_satisfiable_set` | three batches of checked instances over a satisfiable arithmetic ground set, each arriving after the previous solve left a trail. Carries an independent `check_auto` control that the set really is satisfiable |
| `ground_session_level_1_reuses_one_variable_per_abstracted_term` | one variable per abstracted term across the construction boundary, and that it never enters the theory's atom map or the candidate-equality proposal |
| `ground_session_level_1_declines_a_ground_set_with_no_theory_atom` | the vacuous-session guard |

`crates/axeyum-solver/tests/quant_ground_session_soundness.rs` (query level, both
levels on every fixture):

| fixture | what it refutes |
|---|---|
| `SAT_ABSTRACTED_COMPARISONS` | an abstraction that is not a weakening — one that asserted the abstracted variable on the comparison's syntactic shape, or collapsed a polarity |
| `SAT_DISTINCT_COMPARISONS_NOT_COLLAPSED` | an abstraction keyed on anything coarser than the `TermId` (the operator, the sort, the right-hand constant): both comparisons collapse to one variable and the query becomes `v ∧ ¬v` |
| `SAT_MANY_ROUNDS` | the accumulate-across-rounds path end to end |
| `UNSAT_EUF_INSTANCE`, `UNSAT_EUF_INSTANCE_BESIDE_ARITHMETIC` | **positive controls.** A suite of satisfiable queries passes trivially against an engine that decides nothing |
| `the_two_levels_never_disagree_on_a_decided_verdict` | the ship gate as an assertion, with a `compared >= 2` guard so a differential that compared nothing cannot pass |

### 5.1 Mutations — and the one that SURVIVED is the more useful result

`scripts/tests/mutation_controls.py qinst-ground-session`, filter
`--lib ground_session` (baseline **4 tests**, so every kill count below is
against that denominator):

| guard removed | outcome |
|---|---|
| an abstracted atom never reaches the `EUF` theory | **killed 1** — `..._never_manufactures_an_unsat_on_a_satisfiable_set` |
| one variable per abstracted term, reused across occurrences | **killed 1** — `..._reuses_one_variable_per_abstracted_term` |
| a session with no theory atom is declined, not kept | **killed 1** — `..._declines_a_ground_set_with_no_theory_atom` |
| level 1 actually turns the abstraction on | **killed 3** |

`--check-anchors` over the whole file: **151 suites, 1,103 anchors, stale=0**.

**The fifth mutation SURVIVED, and its survival is a finding about the code, not
about the fixtures.** Removing `add_checked_batch`'s `unwind_to_root()` — the
call the brief and this lane both read as the guard against inserting a
permanent clause under a live trail — killed nothing. The reason is that the
hazard has no mechanism at that layer: `NativeIncrementalCdcl::add_clause`
(`crates/axeyum-cnf/src/proof_sat/incremental.rs:486`) calls `between_solves()`
**itself, unconditionally**, before touching the database, so a clause is always
registered into an unassigned solver whether or not the caller asked.

What the session's own call buys is written in that method's own doc comment
(`incremental.rs:515-520`) and is **liveness, not soundness**: it closes the
previous solve's theory epoch so `EufTheory::add_atom_at_root` — reached from
`ensure_atom` before the batch's first `add_clause` — accepts a registration
instead of refusing it. That is measured by a second suite,
`qinst-online-session-epoch`, against a fixture whose batch registers a real
`EUF` atom. The `ground_session` fixtures structurally cannot measure it: their
instances abstract to opaque variables, and an opaque variable needs no epoch.

The statement that survives is therefore narrower and true: **there is no
retraction, so no learned clause can go stale**, and the root discipline that
makes that so lives one layer down and is not this session's to lose.

### 5.2 Verification

Everything below ran with a **nonzero** test count, which is checked because a
feature-gated suite compiles to nothing and exits 0.

| gate | result |
|---|---|
| `--test quant_ground_session_soundness` (`--features full`) | **3 passed, 0 failed** |
| `--lib ground_session` (`--features full`) | **4 passed, 0 failed** |
| `--lib config_registry::` | **18 passed, 0 failed** — three of them failed on the first attempt and each named a real omission (unsorted entry, a `dated` basis naming a document that did not yet exist, and an admission-class bound with no crossing record; the last was a misclassification, and the lever is `OnExceed::Truncate`) |
| the 55 quantified suites (`quantified_route_trace`, `quantifier_trigger_alternatives`, `quantifier_positive_path`, and every `tests/*` matching `quant\|mbqi\|egraph\|inst`) | **54 green.** `quantified_route_trace` is treated separately below |
| the **23** `dispatch/reason:` suites, read out of `hooks/pre-push` rather than retyped | **all green**, this lane's new suite among them |
| `--features z3 --test qf_uflra_differential_fuzz` | **1 passed, 0 failed** |
| `--features z3 --test qf_lia_differential_fuzz` | **4 passed, 0 failed** |
| `clippy -p axeyum-solver -p axeyum-bench --all-targets --features full -- -D warnings` | clean |
| `cargo check --workspace --all-targets`, default features | clean |
| `cargo fmt --all --check` | clean |
| `check-config-registry-staleness.py` | **PASS**, 0 unexplained |
| `check-suite-gating.py` | **PASS**, the new suite gated |
| `check-merge-hygiene.sh`, `check-links.sh` | PASS / all links ok |

**`quantified_route_trace` is load-sensitive and is reported as such rather than
as green or red.** It failed once in the battery and, on re-runs, gave 6/6 green,
then 2 failed, then 3 failed — **a varying failure set at fixed code**, which a
deterministic regression cannot produce. The assertion that fires is the suite's
own non-vacuity guard:

> *"only 3 quantified corpus files were decided; with fewer than 4 this gate
> cannot distinguish a correct attribution from an absent one"*

— a statement about how many corpus files finished inside their budget, not about
attribution. Those runs were on s4 at **load average 42–44 on 16 cores**, with a
second lane's `nra_differential_fuzz` and its own mutation sweep on the same box.
It is re-run on a quiet box and the load each run saw is printed beside its
result.

### 5.3 Three red gates, and none of them is this lane — measured, not argued

Three gates came back red and each is reported with the control that attributes
it, because a red gate is not evidence until you check its own query.

**(a) `-p axeyum-solver --lib --features full -- --skip reconstruct::` — 3 failed,
then 2, then 1, then 0.** The failing set VARIES at fixed code, which a
deterministic regression cannot produce. Four arms, and the load each run saw:

| tree | `--test-threads` | load | failed |
|---|---|---:|---|
| **this lane, serialized** | **1** | 6.3 → 3.6 | **0 of 1576** |
| this lane | default | 9.5 → 30 | 1 (`pathological_overbound_stays_terminal_under_every_policy`) |
| this lane | default | 72 → 92 | 1 (same) |
| **this lane, its 4 new fixtures SKIPPED** | default | 30 → 72 | **3** |
| this lane, its 4 new fixtures SKIPPED | default | 92 → 6.3 | 0 |
| **main** (snapshot `e85bb86f0`) | default | 15.5 → 7.3 | 0 |
| **main** | default | 107 → 5.3 | **1 (the same test)** |
| main | default | 5.3 → 4.4 | 0 |
| main | default | 4.4 → 3.9 | 0 |

Three things fall out and each rules out a different explanation. **Serialized,
this tree is 1576 / 0** — so nothing is deterministically broken. **Main flakes on
the same test** — so it is not this diff. And **removing this lane's four fixtures
made it WORSE, not better** (3 failures against 1) — so it is not this lane's
fixtures crowding the pool either. What remains is what the numbers show: two
`auto::tests::*overbound*` tests and one `euf_egraph` timeout test are
concurrency- and load-sensitive on this box, on main and on this branch alike.

**(b) `cargo test --workspace --lib`, default features — 1 failed at load ~90, 0
failed at load 10.7 → 23.4.** Every binary green on the quiet run.

**(c) `--test quantified_route_trace` — 1 of 3 red at load 8–18 on this tree, and
1 of 3 red on MAIN at load 9–10, the same test both times
(`decider_agrees_with_the_verdict`).** Its assertion is the suite's own
non-vacuity guard, *"only 3 quantified corpus files were decided; with fewer than
4 this gate cannot distinguish a correct attribution from an absent one"* — a
statement about how many files finished inside a budget. Pre-existing.

**`progress_frontier` is green twice** (12 passed, 0 failed, pinned to the P-cores,
`--test-threads=1`): no REGRESSION.

## 6. Measurement

### 6.1 The 53-core probe — the cores move, and nothing flips

53 UFLIA cores, one binary at two env values, both arms `--trace` +
`AXEYUM_QTRACE=1`, **interleaved per file on the same pinned core** (s6 physical
pairs 1,9 / 3,11 / 5,13 / 6,14), 24 s, 8 GiB.
Artifacts: `bench-results/quant-ground-incremental-20260916/cores/`.

| | OFF | ON |
|---|---:|---:|
| decided | 15 | **16** |
| verdict moved | — | **1** |
| …GAIN (`unknown` → decided) | — | **1** |
| …LOSS (decided → `unknown`) | — | **0** |
| …**FLIP** (`sat` ↔ `unsat`) | — | **0** |

The mover is `UFLIA_simplify_javafe.ast.TypeDeclElemPragma.373`: `unknown` at
`fd:bounded-completeness-unsat=budget` becomes `unsat` at `q:mbqi-quick=decided`,
and its interleaved-check cost drops from **12.7 s over 27 calls to 0.7 s over
1**.

**The seconds, and they are smaller than one core suggested.**

| | OFF | ON |
|---|---:|---:|
| the check ran on | 45 of 53 | 45 of 53 |
| calls | 513 | **450** |
| total seconds in it | 452.4 | **404.0** |

**48.4 s removed — 10.7 % of what OFF spent there, 3.8 % of the whole 24 s × 53
budget.** It is not evenly spread: **20 cores gain (57.3 s, max 12.6 s), 11 cores
LOSE (−9.1 s, worst −6.2 s), 22 are unchanged**. And the session suppresses the
cold check on only **13 of 53** — on 38 the call count is identical. The
mechanism fires where the loop is *starved* (no instance admitted, so the
candidate fixpoint runs), not on every round.

**The regime change is larger than the seconds.** How each arm ENDED:

| | budget | decided | incomplete |
|---|---:|---:|---:|
| OFF | 29 | 15 | 9 |
| ON | **24** | **16** | **13** |

Five cores move out of "died on the clock" into an **honest fixpoint** — seven ON
rows now say *"e-matching instantiation reached fixpoint without refuting after N
rounds"*, which OFF could not reach because it ran out of budget first. The
detail naming the interleaved ground check drops from 13 rows to **8**. A file
that reports a fixpoint is a file whose next blocker is the instance SET, not the
clock; that is a different lane's problem and it is now visible.

### 6.2 Datatypes are hosted, not declined — and that is a deliberate deviation

The brief anticipated that the session could not host `theory_datatype` and
asked for a **typed decline** on datatype ground sets, plus a sizing of what that
excludes. It is not needed, and declining would have been the worse design.

A datatype tester is `Op::DtTest(ctor)`, a Bool-sorted application with no
connective arm — exactly the shape level 1 abstracts, by the same weakening
argument as an integer comparison and with no datatype reasoning required. There
is no sub-case to decline. Measured on an `AUFDTLIRA` file from the Tier 1
list (`O512-022__infoflow__infoflow.adb_181_22_overflow_check___00`,
2026-09-16): the interleaved cold check runs **39 times OFF and 24 times ON**, so
the session is built and is suppressing checks on a datatype ground set.

What keeps the degenerate case out is the **vacuous-session guard**, not a
per-theory decline: a ground set whose atoms are *all* abstracted has no theory
atom and the session refuses, so it cannot displace the cold check for nothing.
`AUFDTLIRA` and `UFDTLIRA` are both in the divisional A/B, which measures this
directly rather than sizing an exclusion that does not exist.

### 6.3 The six-division A/B — −4 over 1,200, and five of the losses are stable

One binary at two env values, arms back to back on the SAME file on the SAME
pinned s6 core with the arm ORDER alternating per file, 24 s / 8 GiB, four shards
over physical pairs 1,9 / 3,11 / 5,13 / 6,14, files interleaved ACROSS divisions
so a partial read is a fair sample of all six rather than a prefix of one.

| division | n | A (shipped) | B (level 1) | delta | A rc≠0 | B rc≠0 |
|---|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 200 | 119 | 118 | −1 | 0 | 0 |
| AUFLIRA | 200 | 178 | 177 | −1 | 0 | 0 |
| UF | 200 | 90 | 90 | +0 | 3 | 3 |
| UFDTLIRA | 200 | 144 | 142 | −2 | 0 | 0 |
| UFLIA | 200 | 85 | 85 | +0 | 0 | 0 |
| UFNIA | 200 | 54 | 54 | +0 | 0 | 0 |
| **total** | **1200** | **670** | **666** | **−4** | 3 | 3 |

**Verdict disagreements (`sat` on one arm, `unsat` on the other): 0 of 1,200.**
The nonzero exit statuses are 3 on *each* arm, so the lever created none.

**The re-check is what the decision rests on.** Every one of the 8 raw movers, 3
passes per arm, arms alternating within the row, on one pinned core with nothing
else on it:

| | count |
|---|---:|
| STABLE-GAIN | **1** |
| STABLE-LOSS | **5** |
| UNSTABLE | 2 |

The single stable gain is `UFLIA/simplify/javafe.ast.TypeDeclElemPragma.373` —
`unknown` 3/3 on the shipped arm, `unsat` 3/3 at level 1 — and it is the **same
file the 53-core probe moved**, which is the only agreement between the two
populations in this whole measurement. Every stable loss is the same shape in
reverse: `unsat` 3/3 shipped, `unknown` 3/3 at level 1.

The raw column would have misled: two raw gains re-check as one stable and one
ambient, six raw losses as five stable and one ambient.

### 6.4 The self-check could not use a verdict fixture, and says so

ADR-2120's lever was a CAPABILITY lever — level 1 refutes a five-line query level
0 returns `unknown` on, so a fixture separates the arms by verdict. This one is a
REGIME lever: it changes nothing about what the loop can conclude, only whether
the accumulated ground set is re-solved on the loop's first seven rounds. Every
query small enough to be a self-check fixture decides before the difference can
show, and the one place the arms separated on the 53-core probe is a 24-second
core.

So the hard gate is a direct observation that the variable ARRIVED, taken from
the binary's own `; config digest=` line: the two arms must resolve DIFFERENT
configurations, arm B's line must NAME the override, and arm A's must not. That
is not a behaviour ambient load could imitate. It additionally refuses if the
arms DECIDE the control query differently.

## 7. Decision

**The lever ships OFF (`GROUND_SESSION_LEVEL = 0`), and the ship criterion was
not met by a wide margin.**

| criterion | result |
|---|---|
| 0 verdict flips (`sat` ↔ `unsat`) | **MET** — 0 of 1,200, and 0 of 53 on the cores |
| 0 stable losses | **NOT MET** — **5** |
| net decided over 1,200 | **−4** |

**What the lever does buy, measured, is real but small and the losses swamp it.**
On the 53 cores it removed 48.4 s of 452.4 s of ground re-solve (10.7 %), moved
five cores out of "died on the clock" into an honest fixpoint, and produced one
gain that survives a 3× re-check on both populations. On the divisions it also
produced five losses that survive the same re-check. **The single stable gain and
the five stable losses are the same mechanism seen from both sides**: skipping the
first seven per-round cold checks returns budget to the instantiation loop on a
file whose refutation needs more rounds, and removes a refutation from a file
whose ground set was already refutable in those rounds.

**The held-out draw was not run.** It confirms a lever that has passed its A/B;
with 5 stable losses there is nothing to confirm, and drawing a blind population
to score a lever that is not shipping spends the population for nothing.

## 8. What this lane did not do

**The certificate repair has no fixture, and that is now MEASURED rather than
suspected.** §4.4's fix is correct by construction — the `Refuted` exit is reached
only through `replay_online_refutation`, and its sibling exit collects the same
certificate on the same facts — but reaching it requires the candidate-equality
fixpoint to produce a session `Unsat` on a query small enough to be a fixture,
and this lane did not build one. The mutation suite
`qinst-session-refutation-certificate` removes the repair and runs the whole
`quant_instance_set_cert::` surface against it: **9 tests ran and SURVIVED**. So
nothing in the instance-set certificate surface notices the repair being taken
away, and **nobody should read its presence in the diff as evidence that a later
change could not silently undo it.**

**The `unwind_to_root()` call is covered by nothing either.** The second mutation
suite, `qinst-online-session-epoch`, aims the removal at a fixture whose batch
registers a real `EUF` atom (`instance_provenance`, 1 test) and it **SURVIVED**
too. So the liveness purpose §5.1 attributes to that call is read off
`incremental.rs:515-520`'s own doc comment, not off a test.

**The session still falls back rather than growing its theory.** Level 1 hosts an
arithmetic ground set by ABSTRACTING the arithmetic, not by hosting
`CombinedIncrementalLia` (`combined_theory_lia.rs`, which already implements
`TheorySolver` and is what `uflia_online` drives). That is the real incremental
CDCL(T)-with-arithmetic session, and the reason it is not here is a bounded,
named piece of work: its interface pairs are computed **once up front** from the
full atom set (`CombinedIncrementalLia::build`), and `LiaTheory` is constructed
over a fixed combined layout, so an instance introducing a new integer term has
nowhere to go. `TheorySolver::take_new_atoms` is the growth hook the trait already
has; `EufTheory::add_atom_at_root` is the pattern. A lane that adds
`add_atom_at_root` to `LiaTheory` and re-derives the partition incrementally gets
a session that can REFUTE on arithmetic rather than only decline to re-solve.

**The one thing that would make the saving larger is not this lever.** The probe
shows the session suppressing the cold check on 13 of 53 cores and leaving the
call count identical on 38. The loop only consults the session when a round
admits NOTHING (`admitted.is_empty() && candidate_equalities_enabled` guards
`scoped_candidate_fixpoint_step`); on a productive round the cold check is
skipped anyway because `online_clauses` is `Some`. So the remaining cost is on
rounds where the session exists, is consulted, returns `Sat`, and the loop then
still pays a cold check later. Widening that is a cadence question and belongs to
whoever owns `interleaved_check_due`.

[ADR-2113]: adr-2113-uflia-the-instance-we-never-produce.md
[ADR-2114]: adr-2114-aufdtlira-what-the-model-finder-cannot-represent.md
[ADR-2120]: adr-2120-quantifier-activation-by-assignment.md
