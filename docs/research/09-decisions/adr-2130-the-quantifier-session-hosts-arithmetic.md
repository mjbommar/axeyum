# ADR-2130: the quantifier session hosts arithmetic — the theory arrives, 366 atoms move into it, and the verdict does not

Status: proposed
Index-summary: [ADR-2124] made `OnlineQuantifierClauseSession` exist on an arithmetic ground set by **abstracting** the arithmetic; this lane made it **host** the arithmetic, so its `unsat` can be a Farkas conflict rather than only a congruence one. **Sizing first:** 77 of ADR-2124's 101 ground-check rows are arithmetic-bearing (AUFDTLIRA 18/18, AUFLIRA 6/6, UFLIA 28/28, UFNIA 24/44, UFDTLIRA 1/1, UF 0/4), 53 of them carry a comparison in a GROUND position and 24 acquire one only through an instance; `dt-only` is **0 of 108**, so the typed datatype decline the brief asked for excludes nothing. The lever engages and it is measured, not assumed: on ADR-2113's 53 UFLIA cores, level 1 abstracts **366 atoms on 20 cores** and level 2 abstracts **0** — at least 365 of them `IntLt`/`IntLe`/`IntGt`/`IntGe` becoming real constraints. **And the verdict does not move.** Paired probe, 24 s, interleaved per file on one pinned core: OFF 15 decided, ON 17, 2 raw gains, 0 losses, **0 flips**; the 3x re-check makes that **1 STABLE-GAIN, 1 ambient**, and the stable one is `TypeDeclElemPragma.373` — **the same single file ADR-2124's abstraction moved**. Hosting arithmetic adds **zero net movers over abstracting it** on this population. It ships **OFF**. Three corrections land with it: `TheorySolver::take_new_atoms` is **not** the hook for this route and using it would have been a wrong-answer defect (the warm route registers driver-side); **ADR-2125 built no bound trail to reuse** (its lever is `off` and its subject is the offline cube loop — the retraction here needs no trail at all, because `IntSimplexEngine::sync` re-derives the bounds from the live set); and **ADR-2124's own premise is false on this population** — the shipped arm reached the session site on 45 cores and BUILT a session on **26**, not on 0.
Index-status: proposed
Date: 2026-09-16

## 1. Context

[ADR-2124] located the quantified divisions' remaining block precisely:
`OnlineQuantifierClauseSession::new` builds its encoder without opaque
abstraction, so one integer comparison anywhere in the ground set refuses the
session. Its lever made the session exist by **abstracting** the arithmetic
atom to a free propositional variable, measured cores +1/0 and divisions −4,
and shipped OFF. Its named next increment is this lane, verbatim:

> The session still abstracts rather than hosting arithmetic. …
> That lane gets a session that can refute on arithmetic rather than only
> decline to re-solve.

An abstracted atom only adds models. The session can decline to re-solve
through one; it can never **refute** through one. This lane builds the other
half.

## 2. Sizing — before any code

Artifacts: `bench-results/quant-session-arith-20260916/SIZING-ledger.txt`,
script `sizing-ledger.py`. Commit `59f5687f0`.

### 2.1 The ceiling

| population | n | arith | arith in GROUND position | arith only under a quantifier | dt-only | euf-only |
|---|---:|---:|---:|---:|---:|---:|
| qGROUND | 108 | 84 | 58 | 26 | 0 | 24 |
| **qGROUND & `unknown`** | **101** | **77** | **53** | **24** | **0** | 24 |
| ADR-2113's 53 UFLIA cores | 53 | 41 | 37 | 4 | 0 | 4 |

Per division on the 101: AUFDTLIRA 18/18, AUFLIRA 6/6, UF 0/4, UFDTLIRA 1/1,
UFLIA 28/28, UFNIA 24/44.

**The ceiling is 77 of 101 (76.2 %).** The 24 `euf-only` rows are the share
ADR-2124's abstraction already reaches and hosting cannot improve — 20 UFNIA and
4 UF — and they are the honest denominator correction rather than a rounding
error.

**24 of the 77 are arithmetic-only-under-a-quantifier**, so their ground set
acquires a comparison only through an admitted instance. That is precisely the
atom that must be accepted AFTER construction, and it is a quarter of the
ceiling rather than a corner case. The other 53 refuse the session at round 0.

**Datatypes: `dt-only` is 0 of 108.** The brief asked for a typed decline on
datatype ground sets plus a sizing of what it excludes. It excludes nothing:
there is no file in this population whose only refusing atom is a datatype
tester — every AUFDTLIRA and UFDTLIRA row here is arithmetic-bearing as well.
ADR-2124 §6.2 reached the same conclusion from the other direction.

### 2.2 ADR-2124's population is re-derived here, not quoted

The script behind ADR-2124's `SIZING-ledger.txt` was never committed — its
README lists only the output — so its 108/101 was not falsifiable in-tree.
`sizing-ledger.py --self-check` reproduces that table on **7 of 7** divisions
and fails if it stops doing so.

**The reading that works is narrow and was not the first one tried.** The
predicate is the last `q:`-prefixed decline **that carries a nonempty detail**.
Five natural readings of the ADR's own one-line definition give five different
populations:

| reading | qGROUND / unknown |
|---|---|
| last `q:` decline **with a nonempty detail** | **108 / 101** ✓ |
| last `q:` decline, empty details included | 27 / 20 |
| last `q:egraph` decline | 136 / 136 |
| any `q:` decline | 319 / 300 |
| first `q:` decline | 0 / 0 |

## 3. The mechanism, at `file:line`

### 3.1 z3 — the instance's new arithmetic atom is internalized at the current level, and deleted on pop

Verified against the checked-out clone (`scripts/VERSION.txt` → `5.1.0.0`).

| what | where |
|---|---|
| the hand-off | `src/smt/qi_queue.cpp:336` `m_context.internalize_instance(lemma, pr1, gen);` |
| receiver | `src/smt/smt_context.h:1781` |
| → assertion → recursion | `src/smt/smt_internalizer.cpp:288`, `:308-310`, `:449`, `:455-456` |
| **theory-atom dispatch** | `src/smt/smt_internalizer.cpp:519`, and the call at **`:580-581`** `th->internalize_atom(n, gate_ctx)` |
| `theory_arith::internalize_atom` | `src/smt/theory_arith_core.h:1275` |
| **new column (theory var)** | `src/smt/theory_arith_core.h:100-101`, `m_columns.push_back(column())` at `:106` |
| **new tableau row** | `src/smt/theory_arith_core.h:349`, `:358-360` |
| **new bound atom** | `src/smt/theory_arith_core.h:1328` `alloc(atom, bv, v, k, kind)` |
| the level is stamped into the enode | `src/smt/smt_internalizer.cpp:1082-1083` (`m_scope_lvl`) |
| **undo on pop**: atoms / bounds / vars+rows | `theory_arith_core.h:3391` `del_atoms`, `:3392` `del_bounds`, `:3393` `del_vars`; row deletion `:3540`; the nine per-variable `shrink`s at `:3525-3532` |
| watermarks taken on push | `theory_arith_core.h:3349`, `:3353-3358` |

There is **no base-level assertion anywhere on this path**: no `at_base_level`,
no `get_scope_level() > 0` guard in `internalize_atom` or `mk_var`. Relevancy
does not defer internalization — it only gates whether an *assigned* literal is
queued to the theory (`smt_context.cpp:307-308`). So z3 accepts the new atom at
the current level and throws the whole column/row/atom/enode away on backjump.

**Three corrections to ADR-2124 §2.2, which this lane had to make before it
could rely on the citations.**

1. **§2.2 is wrong about `m_lemmas`.** It says the instance clause "pushes into
   `m_lemmas` + the watch lists at `:1566-1568`". The instance path reaches
   `mk_clause` through `mk_root_clause` (`smt_internalizer.cpp:1716`) with the
   default `k = CLS_AUX` (`smt_context.h:988`); `is_lemma(CLS_AUX)` is false
   (`smt_clause.h:47-48`), so control takes the `else` at **`:1587`
   `m_aux_clauses.push_back(cls)`**, and the watch calls are at `:1588-1589`.
   This matters materially: aux clauses are **not** reinit-marked and **are**
   deleted on pop (`smt_context.cpp:2560`), so the instance clause has SAT-level
   lifetime, not permanent lifetime. ADR-2124's "the instance is a new clause in
   the one context that already holds it" is directionally right and understates
   this.
2. **§2.2 cites `:1544-1546` as if it were live on this path.** On the instance
   path `lemma == false`, so `iscope_lvl` is forced to `0` and `save_atoms` is
   false; the `m_scope_lvl`/`m_base_lvl` read is a no-op there.
3. Its other z3 citations verified good.

### 3.2 cvc5 — preregistration creates the arith variable, and it is PERMANENT

Verified against the checked-out clone (`cmake/version-base.cmake:2` → `1.3.4`).

| what | where |
|---|---|
| a theory literal is minted → notify | `src/prop/cnf_stream.cpp:217-222`, `:296`, `:300` |
| eager preregistration (the default) | `src/prop/theory_preregistrar.cpp:75`, `:78-83`; default `EAGER` at `src/options/prop_options.toml:98`, `:102` |
| → `TheoryEngine::preRegister` | `src/theory/theory_engine.cpp:287`, `:291`, `:324` |
| → the visitor → the theory | `src/theory/term_registration_visitor.cpp:204-205` `th->preRegisterTerm(current)` |
| `TheoryArith::preRegisterTerm` | `src/theory/arith/theory_arith.cpp:106`, `:174` |
| `TheoryArithPrivate::preRegisterTerm` → `setupAtom` | `src/theory/arith/linear/theory_arith_private.cpp:1504`, `:1515-1517`, `:1427` |
| **new arith variable** | `src/theory/arith/linear/theory_arith_private.cpp:1550`, allocation at `:1571` |
| **new tableau row** | `src/theory/arith/linear/theory_arith_private.cpp:1383-1386` |
| …in NON-context-dependent storage | `src/theory/arith/linear/partial_model.h:108`, `:111`; `constraint.h:1007` |
| the `isSetup` memo is NOT context-dependent | `src/theory/arith/linear/theory_arith_private.h:195` |
| but the "already preregistered" memos ARE | `term_registration_visitor.h:44`, `:50`; `theory_arith_private.h:299` |
| **so registration is REPLAYED on backjump** | `src/prop/theory_preregistrar.cpp:87`, `:96-119`; driven from `src/prop/minisat/core/Solver.cc:704` |
| `TheoryEngine::assertFact` | `src/theory/theory_engine.cpp:1230`, `:1288-1291` |

**ADR-2124 §2.3 has no citation for preregistration at all** — it tabulates the
lemma→CNF→SAT direction and the `assertFact` return direction, and the hop where
a brand-new arithmetic atom acquires its `ArithVar` is simply absent. That is
the hop this ADR is about, and it is where the two reference solvers differ:
**z3 deletes the column on pop; cvc5 keeps it and replays the registration.**

### 3.3 Ours

| what | where |
|---|---|
| the gate that selected the schedule | `qinst_egraph.rs`, `online_clauses.is_none()` in `prove_quantified_unsat_via_egraph_impl` |
| the two schedules, now named | `GroundCheckSchedule`, `ground_check_split_round()` |
| the decline site | `OnlineQuantifierClauseSession::new_with_limits`, the `?` on `encoder.encode` |
| **where a new atom is registered** | `OnlineQuantifierClauseSession::ensure_atom` → `WarmNativeCdclT::add_theory_variable` (driver side) + `EufLiaSessionTheory::add_atom_at_root` (theory side) |
| the composite theory | `crates/axeyum-solver/src/qinst_session_theory.rs` |
| the interface pairs computed ONCE up front | `combined_theory_lia.rs:686-687`, in `build` at `:663` |

**`TheorySolver::take_new_atoms` is not the hook for this route, and using it
would have been a wrong-answer defect.** The brief named it. It is polled by the
core at a propagation fixpoint *inside* a solve, so it cannot hand an index back
to a caller that is still building the clause the variable belongs to — the
adapter's own doc says exactly this (`native_cdclt.rs:340-352`). The warm route
uses the driver-side channel instead. This theory's `take_new_atoms` returns `0`
always, with a fixture pinning it: a nonzero count would make the driver append
a **second** SAT variable for an atom that already has one, and every later atom
index would be off by one.

## 4. The change

### 4.1 `EufLiaSessionTheory` — two theories, one atom index space

`EUF` and `LIA` side by side, sharing one atom index space. No mapping is
needed, because both sub-theories were already written to tolerate an atom they
cannot represent: `EufTheory` stores `None` sides for a non-equality atom
(`euf_egraph.rs:477-479`) and `LiaTheory` classifies a non-`LIA` atom as
`AtomKind::Unsupported` (`lia_online.rs:111-113`). So composite atom `i` is
`EUF` atom `i` **and** `LIA` atom `i`, and a conflict core from either half is
already in composite indices. An integer equality is registered in both and seen
by both, which is where that is wanted.

**It is deliberately not `CombinedIncrementalLia`.** That type already
implements `TheorySolver` and already does a real Nelson–Oppen combination, and
the brief named it. It is unusable for a set that grows after construction, for
a structural reason: `build` computes the interface pairs once up front
(`combined_theory_lia.rs:686-687`) and constructs both sub-theories over a
*combined* atom list interleaving three synthetic atoms per pair (`:713-730`).
A new atom can propose a new pair, so the combined index space is not
append-only in the original atoms — and every clause already in the session's
SAT database was built against the old indices. The pairs also carry
`structural_clauses` (`:781`) that a growing session would have to insert into a
clause database mid-search.

Side-by-side composition avoids all of it and propagates **no** interface
equalities. That is an incompleteness, and it is free **for this caller
specifically**: the session's `Sat` is never a verdict, and its `Unsat` is
re-established by `replay_online_refutation` over the same ground set with the
cold route before it becomes the answer. A combination that misses a conflict
costs a refutation; it cannot manufacture one.

### 4.2 `new_with_opaque_apps`, not `new` — and the difference decides everything

A UFLIA comparison almost always mentions an Int-sorted UF application
(`(< (f a) 5)`). Plain `LiaTheory::new` cannot build a row for one, so the atom
lands as `AtomRow::None` and the theory hosts it as a **no-op** — an arithmetic
theory that refuses exactly the arithmetic this lane exists for. The opaque-app
constructor treats each Int-sorted application as its own integer variable: an
over-approximation of the model space (it forgets that `a = b` forces
`f(a) = f(b)`), so it can only lose conflicts, never invent one. Its own doc
calls it an UNSAT-oriented UFLIA hook, and its stated cost — a satisfiable
opaque abstraction is model-incomplete — is zero here.

### 4.3 The ground set needed its own pass, and it is the larger half

The session's atoms come from `collect_euf_atoms`, which collects only the
shapes congruence owns. A comparison in the **original** assertions is therefore
not an atom, `Encoder::encode` reaches its abstraction arm, and the arithmetic
sub-theory never sees it no matter what later instances do. Level 2 appends the
ground set's order atoms in a second pass, after the EUF atoms and with its own
`seen` set so the existing atom indices do not move.

Per §2.1 this reaches 53 of the 77 arithmetic-bearing files; only 24 acquire a
comparison solely through an instance. **This was found by the code not working,
not by reading it.**

### 4.4 The inert `EUF` slot is conditional, or levels 0 and 1 would change

Historically a Boolean-position term the congruence closure has no opinion about
reached `EufTheory::add_atom_at_root`, was **refused**, and the refusal disabled
the whole session — which is what level 0 does and what ADR-2124's arm A
measured. Accepting an inert slot unconditionally would keep the session alive
on files where the shipped build abandons it, and every A/B against those arms
would be measuring two changes at once. The slot is offered only when the
session hosts arithmetic **and** the atom is one the arithmetic can constrain.

### 4.5 Growth is a REBUILD, and this ADR does not claim otherwise

`LiaTheory` freezes three things at construction that an appended atom would
have to reach into: the simplex tableau, for which `simplex::Incremental`
exposes **no row- or column-append method at all**; the warm decider's literal
table, whose own doc says the key table *"must not change for the life of the
decider"* (`lra/warm.rs:381-383`); and the theory's **owned clone of the arena**,
which carries `BoolNot` nodes at ids the caller's arena does not have, so it
cannot be replaced by a newer clone of the caller's.

Rebuilding sidesteps all three, and it is correct for a reason that is the whole
argument for this design: **the simplex's imposed bounds are derived, not
accumulated.** `IntSimplexEngine::sync` (`lia_online.rs:359-388`) reconciles
them against the live set on every check and its own doc calls the result *"a
pure function of `live` — no hidden coupling to call order"*. A fresh engine with
no bounds imposed and the same assignments reaches the same state on its next
check.

The rebuild runs once per admitted **batch**, not per atom. The Boolean search,
the clause database, the learned clauses and the `EUF` e-graph all stay warm
across it; the arithmetic tableau does not. A real
`simplex::Incremental::add_row` is the named next increment.

### 4.6 The two schedules are named and registered

`online_clauses.is_none()` selected between two inline conditions seven hundred
lines apart, and what that selection does was stated **wrongly** in the source,
in the config-registry entry, and in ADR-2124's first draft, all at once: the
claim was that a live session SUPPRESSES the cold check. It does not. The two
schedules are now `GroundCheckSchedule::PerRoundThenExponential` and
`ExponentialOnly`, both arms of `due` written in terms of
`ground_check_split_round()`, so the seven-round gap is structural rather than
two conditions that happen to line up. The registry entry is
`MAX_INSTANTIATION_ROUNDS`, whose justification is now dated and names the
symbols — it previously cited `qinst_egraph.rs:1677-1682` for a function that
had not been there for some time.

## 5. Soundness

**The retraction of an arithmetic bound on backjump needs no bound trail, and
the brief's expectation that it would was wrong in a useful way.** ADR-2125 did
not build one to reuse: its subject is the OFFLINE lazy-SMT cube loop, its lever
`AXEYUM_LRA_WARM_CUBE` ships `off`, and the bound trail it was confused with is
older (ADR-1701 / ADR-2122) and lives on `LraTheory` — the **real** theory — not
`LiaTheory`. `LiaTheory` has no bound undo at all, and does not need one: §4.5's
`sync` re-derives the imposed bounds from the live set, and `LiaTheory::pop`
(`lia_online.rs:1787-1795`) unassigns every atom back to the `push` marker. So
the forwarded `pop` **is** the retraction.

That is load-bearing, and it is what the mutation suite aims at.

### Fixtures

`crates/axeyum-solver/src/qinst_session_theory.rs` (8):

| fixture | what it refutes |
|---|---|
| `hosting_refutes_an_arithmetic_conflict_the_euf_half_cannot_see` | the capability, with its negative half: the `EUF`-only arm must ACCEPT both comparisons, or the fixture is not measuring the arithmetic. Also that the core is in COMPOSITE indices and is non-empty |
| `pop_retracts_an_arithmetic_bound_a_backjump_undid` | **the soundness fixture.** Each comparison is feasible alone, so an `Ok` means the popped bound is gone and an `Err` means a branch the search abandoned is still constraining the theory |
| `hosting_never_manufactures_a_conflict_on_a_satisfiable_assignment` | a satisfiable assignment across a push/pop cycle |
| `a_rebuild_replays_the_root_assignments_into_the_new_sub_theory` | a rebuild that forgot a root-level bound |
| `a_flush_with_no_pending_atom_is_a_no_op` | an unconditional rebuild, which would pay an arena clone every round |
| `the_euf_only_arm_hosts_no_arithmetic_and_never_rebuilds` | levels 0 and 1 silently acquiring a `LIA` half |
| `take_new_atoms_is_always_zero_because_the_driver_registers` | the double-registration defect §3.3 describes |
| `only_order_atoms_are_pulled_back_from_the_abstraction` | an equality pulled out of the abstraction by a second route |

`crates/axeyum-solver/src/qinst_egraph.rs` (4 new):

| fixture | what it refutes |
|---|---|
| `ground_session_level_2_hosts_the_comparison_level_1_abstracts` | all three levels, with the opaque count asserted at 1 AND 2 — a level 2 that had quietly kept abstracting would still be `Some` and pass every liveness check |
| `ground_session_level_2_refutes_an_arithmetic_ground_set_level_1_cannot` | both arms: level 1 must report `Sat`, level 2 `Unsat` |
| `the_two_ground_check_schedules_differ_by_exactly_the_leading_rounds` | derives the differing set by RUNNING both schedules, with a non-vacuity guard; a literal `{0..6}` would have measured the maintainer's memory |
| `the_historical_helper_agrees_with_the_named_schedule` | the two conditions drifting apart again |

`crates/axeyum-solver/tests/quant_session_arith_certificate.rs` (3): the
certificate invariant — see §7.

## 6. Measurement

### 6.1 The lever engages — and this had to be measured before any A/B

Artifacts: `qsa-engage-l{0,1,2}.txt`, `engagement-compare.py`. 53 cores, 12 s.

| | site reached | session built | hosting | abstracted |
|---|---:|---:|---:|---:|
| level 0 (shipped) | 45 of 53 | **26** | 0 | 0 |
| level 1 (ADR-2124) | 45 of 53 | 44 | 0 | **366 on 20 cores** |
| level 2 (this lane) | 45 of 53 | 44 | **44** | **0** |

**366 atoms moved out of the abstraction and into the arithmetic theory**, and
at least 365 are `IntLt`/`IntLe`/`IntGt`/`IntGe`. (The `shapes` histogram is
truncated to six operators, so the arithmetic subcount is a lower bound, not an
equality.) The per-core arithmetic is visible in the atom count:
`filespace.ZipTree` goes `atoms=45 abstracted=7` at level 1 to
`atoms=52 abstracted=0` at level 2 — exactly the seven `IntLt` atoms becoming
real constraints.

`engagement-compare.py` exits 1 when nothing moved, so a lever that was built
but never engaged cannot report as a clean null.

**8 of 53 cores printed no session line at all**: the loop exited before the
construction site was reached. That is an ABSENCE and is reported as one. It is
the one load-sensitive number here and this capture ran on s4 at load ~51; the
structural per-core counts are not load-sensitive.

### 6.1.1 ADR-2124's premise is false on this population

ADR-2124 reads as if one integer comparison anywhere in the ground set refuses
the session, so UFLIA takes the cold branch for its entire run. Measured
directly: the **shipped** arm reached the site on 45 cores and **built a session
on 26 of them**. It refuses on 19 of 45, not on 45 of 45.

**Corroborated on a second, independent run.** The 24 s paired probe of §6.2 —
different host, different budget, idle box — reports the shipped arm building a
session on **24 of 53** (`cores/cores.tsv`, `off_built`). Two runs at two
budgets on two hosts both say the shipped arm builds a session on roughly half
this population, which is not what "one integer comparison refuses it" predicts.

The reason is that the round-0 ground set is the *quantifier-free subset*, and
on most of these Boogie/Simplify-family files that subset is EUF-only: their
arithmetic is encoded through uninterpreted functions over `Int` (`intLess`,
`intAtMost`, `boolAnd`, `anyEqual`), so there is no comparison for the encoder
to refuse. This does not make ADR-2124's lever wrong — its measured effect was
the schedule change, not the abstraction — but it does mean its stated mechanism
over-attributes.

### 6.1.2 What the self-check caught before any probe ran

The construction-site counter first reported `opaque_variables.len()` as "atoms
abstracted". That map is `encoder.term_var` minus the theory atoms, so it also
holds every **Tseitin gate**: on the first real core it was pointed at the map
held 18 entries — `BoolAnd:9, BoolNot:5, BoolOr:3, BoolConst:1` — and **none was
an abstraction**. ADR-2124's own unit test pins that map at 1 on a fixture with
no connectives in it, so the conflation never surfaced there. The trace now
reports `abstracted=` (the encoder's `opaque_atoms`) and `gates=` separately,
plus a `shapes=` histogram, because a bare count cannot distinguish a lever that
met no arithmetic from one that failed to host the arithmetic it met.

The self-check also failed twice for two different reasons, and only the second
was the solver's. The first assertion was simply **wrong** — it required level 0
not to build a session, which it legitimately does whenever the ground set is
EUF-only. Without the self-check, a 20-minute paired probe would have run on an
unrepresentative core and reported a clean null.

### 6.2 The 53-core paired probe — 1 stable gain, 0 losses, 0 flips

One binary at two env values, both arms `--trace`, **interleaved per file on the
same pinned core** (s6, physical pairs 1,9 / 3,11 / 5,13 / 6,14), 24 s, 8 GiB,
box otherwise idle (load 0.03). Artifacts: `cores/`.

| | OFF (shipped) | ON (level 2) |
|---|---:|---:|
| decided | 15 | **17** |
| verdict moved | — | 2 |
| …GAIN | — | 2 |
| …LOSS | — | **0** |
| …**FLIP** | — | **0** |

**The re-check is what the decision rests on.** Both raw movers, 3 passes per
arm, arms alternating within the pass, on one pinned core with nothing else on
it:

| | count |
|---|---:|
| STABLE-GAIN | **1** |
| STABLE-SAME (the raw gain was ambient) | **1** |
| STABLE-LOSS | 0 |
| FLIP | 0 |

The stable gain is `UFLIA_simplify_javafe.ast.TypeDeclElemPragma.373` —
`unknown` 3/3 shipped, `unsat` 3/3 at level 2 — and it is **the same single file
ADR-2124's level 1 moved**. `UFLIA_boogie_Cast_Cast.R_System.Object_System.Int32`
re-checks `unknown` 3/3 on both arms.

So **hosting arithmetic adds zero net movers over abstracting it** on this
population.

The first version of the re-check extracted verdicts with a `sed` over the trail
JSON and reported `none` for every `unknown` arm and for one core the probe had
seen decide. It was replaced by `route_trace_reader.py` — the rule this lane's
own summariser docstring states and the re-check script initially violated.
`recheck-summarize.py` exits 2 if every run fails to parse, so an extractor
failure cannot read as a population of undecided runs.

### 6.3 The ground re-solve

| | OFF | ON |
|---|---:|---:|
| the check ran on | 45 of 53 | 45 of 53 |
| calls | 529 | **471** |
| total seconds in it | 451.1 | **401.8** |

**49.3 s removed — 10.9 % of what OFF spent there.** That is ADR-2124's
schedule effect, reproduced; it is not attributable to hosting.

### 6.4 The ON arm's terminal reasons

| n | route = reason |
|---:|---|
| 21 | `fd:bounded-completeness-unsat=budget` |
| 13 | `q:mbqi-quick=decided` |
| 8 | `fd:bounded-completeness-unsat=incomplete` |
| 3 | `q:egraph=incomplete` |
| 3 | `q:mbqi-quick=budget` |
| 2 | `q:egraph=decided` |
| 1 each | `q:bool-skeleton=decided`, `q:mbqi-quick=incomplete`, `q:mbqi=decided` |

Twelve rows still end on *"e-matching: instantiation time budget exhausted
mid-round (the interleaved ground check did not decide the set inside the
deadline)"*, and six reach an honest fixpoint (*"reached fixpoint without
refuting after 6 / 74 / 75 / 80 / 265 rounds"*). The ground check remains the
named blocker on a dozen of these cores **with the arithmetic hosted**, which is
the finding §7 turns into a decision.

## 7. Decision

**The lever ships OFF (`GROUND_SESSION_LEVEL = 0`), and the divisional A/B was
not run.**

| criterion | result |
|---|---|
| 0 verdict flips | **MET** — 0 of 53 |
| 0 stable losses | **MET** — 0 |
| ≥ 5 cores moved | **NOT MET** — 1 stable gain, and it is the file level 1 already moved |

The brief's stop rule is explicit: below five movers, stop and do not run the
divisions. That is the right call for a second reason the measurement supplies —
ADR-2124's level 1 produced 5 **stable losses** on 1,200 divisional rows from
the schedule change alone, and level 2 inherits that schedule change whole.
Running six divisions to rediscover those losses plus one gain would spend
around six hours of pinned-core time to confirm an arithmetic that moved nothing
on the population it was sized for.

**What this does establish, and it is worth more than the lever.** The session
can now host a theory beside its e-graph; 366 arithmetic atoms became real
constraints on 20 of 45 cores with zero flips and zero stable losses; and the
verdict did not move. That is a clean negative result about **where the block
is**, not about whether the code works. On this population the refutations these
files need are not the ones a Farkas core over the round-0 ground set supplies —
twelve of them still die naming the interleaved ground check, with the
arithmetic hosted.

**The held-out draw was not run.** It confirms a lever that has passed its A/B;
there is nothing to confirm, and drawing a blind population to score a lever
that is not shipping spends the population for nothing.

## 8. What this lane did not do

**The certificate repair still has no query fixture, and the source invariant
that replaced it is a weaker thing honestly labelled.** ADR-2124 §8 measured
that removing the `CandidateFixpointStep::Refuted` certificate collection left
all 9 `quant_instance_set_cert::` tests SURVIVING. Reaching that exit needs the
candidate-equality fixpoint to produce a session `Unsat` on a query small enough
to be a fixture; ADR-2124 did not find one and neither did this lane.
`quant_session_arith_certificate.rs` instead asserts the property the repair is
an instance of — **every unsat exit of `prove_quantified_unsat_via_egraph_impl`
that refutes BY THE INSTANCE SET assigns the certificate first** — over the
function's own source, with non-vacuity controls on the body it read and on both
exit counts. It is **not** a behavioural check and must not be quoted as one.

**Its first honest run was itself a finding, and it corrected ADR-2124's count.**
Written first over *every* unsat exit, it failed: the function has **seven**
`return Ok(CheckResult::Unsat)` exits, not the four ADR-2124 counted
(*"two cold-check exits … make it four sites, three of which were right"*), and
two of them assign no certificate.

Those two are not defects, and the test was too strong rather than the code
being wrong: they are `if try_closed_universal_refutations(…)?` and
`if try_targeted_quantifier_refutations(…)?` — **delegated** routes that run
before the instantiation loop and refute a quantifier directly, producing no
instances at all. An instance-set certificate for one of them would be empty,
and an empty certificate asserted as evidence is worse than no claim.

So the population is **derived from the source**, not listed: an exit whose
guard calls a `try_…` helper is delegated and carries its own evidence; the
other five refute by the accumulated ground set and must carry the certificate.
Both counts are asserted, so neither a new delegated route nor a new loop exit
can join the wrong population silently — and in particular, if the guard window
ever stops reaching those conditions, every delegated exit would silently join
the demanding population, which the delegated-count assertion catches.

**The divisional A/B, the movers' 3x on six divisions, and the held-out draw
were not run**, per §7.

**The new differential seed class was not built.** The brief asked for
quantifier-free UFLIA sets assembled incrementally (atoms pushed in rounds) and
compared against z3 on the whole set. That is the check that would catch a
wrong-`unsat` from the growth path on shapes no committed corpus contains, and
it is the most valuable thing left undone here.

**Interface equalities are not propagated** between the two sub-theories (§4.1),
and **growth rebuilds the arithmetic tableau** rather than appending to it
(§4.5). A `simplex::Incremental::add_row` / `add_column` is the named next
increment, and the cvc5 shape in §3.2 is the model for it: keep the column,
replay the registration.

[ADR-2113]: adr-2113-uflia-the-instance-we-never-produce.md
[ADR-2124]: adr-2124-incremental-ground-closure-for-quantifier-instances.md
[ADR-2125]: adr-2125-a-warm-simplex-basis-across-sat-decisions.md
