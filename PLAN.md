# PLAN.md — master index

This is the entry point. The full, end-to-end engineering plan to take axeyum to
**Z3 + Lean parity** lives under [`docs/plan/`](docs/plan/README.md). This file
is the map and the standing rules; **[STATUS.md](STATUS.md)** is the live tracker
(current focus, per-phase state, changelog) and is the only file with mutable
session state.

> The goal is large and deliberately multi-week/multi-month. It is decomposed
> into tracks → phases → tasks, each with concrete reference file paths, sizing,
> and exit criteria, so work can proceed one verifiable increment at a time
> without ever losing the thread. **We do not stop and we do not hand-wave; we
> advance the next task and record it.**

## ⚠ Course correction (2026-06-23): MEASURE, don't seed

**Diagnosis (evidence-based).** ~150 commits over 24h moved **zero** Z3/cvc5
metrics. Verified causes:
1. **Measurement vacuum.** Only **one** division is corpus-measured (QF_BV p4dfa).
   All the new work — interpolation, CHC/PDR/IMC, abduction, online combination,
   datatypes, the proof certs — is on divisions **nothing measures**. Real
   decide-rate gains happened (fuzz-measured: QF_NRA 109→64, QF_NIA 498→146,
   QF_UFLIA 311→18) but are **invisible** because no committed corpus vs Z3 records
   them. *You cannot show progress you do not measure.*
2. **Ledger-over-corpus.** The cadence became *seed engine → mark Validated/Checked
   → register a ledger row → next engine.* That optimizes **breadth + assurance**
   (the ledger). Parity metrics measure **depth + performance** (the corpus). A
   ledger row is **not** progress toward parity; a measured PAR-2 is.
3. **QF_BV bottleneck untouched.** The one measured metric is gated on
   batsat-path search / word-level reduction. The recent SAT heuristics (VSIDS,
   Luby, LBD, phase-saving) landed in the **generic CDCL(T) Dpll** (`lra_online.rs`,
   the *theory* loop) — a different code path from the QF_BV solver
   (`solve_with_rustsat_batsat`/`native_cdcl`). So they cannot move QF_BV.

**The correction (binding until lifted):**
- **Measurement is the gate, not an afterthought.** No fragment may be called
  "parity"/"competitive" without a **committed measured corpus vs Z3/cvc5**
  ([P4.5](docs/plan/track-4-usecases-frontend/P4.5-benchmarking.md)). Until then its
  status is "seeded/decides," never "parity." (See the
  [maturity ladder](#true-parity-the-maturity-ladder-and-the-measurement-debt-2026-06-23).)
- **Fastest real progress = measure what already improved.** Stand up committed
  per-division corpora (QF_LRA, QF_LIA, QF_UF, then QF_NRA/NIA) vs Z3 *now* — the
  gains already exist (fuzz-measured); measuring them makes them visible **today**.
  The new oracle-free corpus gate (`tests/corpus_regression.rs`) is the credibility
  substrate; the missing piece is the **measured PAR-2** harness across divisions.
- **Seed moratorium.** Do **not** add another new engine seed until ≥2 existing
  divisions are *measured-competitive*. A 12th seeded engine is worth less than
  QF_LRA proven on a real corpus.
- **QF_BV work must hit its real bottleneck** — batsat-path search (kissat-class
  techniques in the native core) or deeper word-level reduction — not the theory
  loop. SAT heuristics in `lra_online.rs` do nothing for QF_BV.
- Proof/certification work still has value (it widens the *Certifying* moat we
  already lead) — but it advances assurance, **not** the parity metric; budget it
  accordingly, behind measurement.

**Progress (2026-06-24): the measurement gate now exists.**
[`axeyum-bench/examples/measure_corpus.rs`](crates/axeyum-bench/examples/measure_corpus.rs)
shells the system `z3` binary against any logic's corpus and times axeyum's
`check_auto` on the same files → decided counts, agreement, DISAGREE, **PAR-2 for
both**. First fair numbers (cvc5 slices, both-parse, 10 s, **DISAGREE=0**):
QF_BV 35/35, QF_ABV 8/8, QF_FP 5/5, QF_LRA 5/5 — **parity**; QF_LIA **8/9 vs 9/9**
(z3 ahead by one and far faster — the first honest measured gap). Artifacts under
`bench-results/measured/`.
- **Methodology lesson (load-bearing):** cvc5's own `test/regress` is
  *solver-flavored* — files carry cvc5-specific `(set-option :bv_solver/:incremental)`
  and non-BV-array logics that **z3 rejects at parse**. Scoring those as z3 misses
  fakes an axeyum win (a permissive parser is not solving power); the harness
  **excludes** them (`z3_rejected_unfair`). For a *fair* parity number, prefer a
  **neutral SMT-LIB corpus** over a competitor's regress suite.
- **These are easy instances** — "parity" here means both trivially solve. The
  easy corpus *hides* the depth gaps; the next step is harder neutral per-division
  corpora (where QF_LIA already hints z3 is ahead). Measurement is no longer the
  blocker — corpus *difficulty/neutrality* is.

**Measurement now DISCHARGED (2026-06-24).** The parallel agent generalized this
into a committed, regenerable **[`bench-results/SCOREBOARD.md`](bench-results/SCOREBOARD.md)**
— **24 logic fragments, 992 files, 663 decided, 611 oracle-compared, DISAGREE = 0**
— plus the oracle-free per-lever frontier dashboard. The "MEASURE, don't seed"
correction is answered: the weak rows now *name* the blockers (see
[`docs/PARITY-STATUS-AND-PATH.md`](docs/PARITY-STATUS-AND-PATH.md)). The strategic
question is no longer "are we measured" — it is the next section.

## Strategy: work backwards from Pareto dominance (2026-06-24)

**The decide-rate race is the wrong target.** Z3/cvc5 have ~20 years of tuning;
the scoreboard confirms axeyum trails on the hard rows (QF_NRA-cvc5 24%, Int-indexed
arrays ~0%, infinite-domain quantifiers 0%). Chasing "match Z3's decide% everywhere"
is a catch-up race axeyum loses on most rows, indefinitely. **Stop optimizing for
global decide-parity.**

**Instead: define and grow the set of fragments where axeyum *Pareto-dominates* the
alternatives.** A fragment is **Pareto-dominant** when axeyum is, on it,
simultaneously: **(1) decide-competitive** with Z3 (parity on that fragment),
**(2) sound** (DISAGREE = 0 — already true everywhere), **(3) Lean-certified**
(every `unsat` carries a kernel-checkable proof), and **(4) pure-Rust / `unsafe`-free /
WASM / deterministic**. On such a fragment axeyum **strictly beats every alternative**:
- vs **Z3 alone** — Z3 ties on decide but has no Lean-checkable proof and is C++ (no
  WASM, memory-unsafe);
- vs **cvc5 alone** — ties on decide, has Alethe/LFSC but not an *integrated in-tree
  Lean-kernel-checked* artifact in a pure-Rust stack;
- vs **Lean alone** — Lean cannot *auto-decide* the fragment; axeyum does, and hands
  back a proof its kernel accepts.

That is a real, defensible "we win here" — unlike "we almost match Z3's decide-rate."

**The new headline metric: four-constraint Pareto-dominance coverage.** Drive it
up per measured division: decided within budget, DISAGREE = 0, every `unsat`
has a re-checked trust-hole-free Lean certificate, and the route remains
pure-Rust / deterministic / `unsafe`-free. A fragment count is too easy to game
by slicing; coverage on a neutral corpus is the control surface.

**Working backwards — what that implies for priorities:**
1. **The binding axis is certification, not decide-rate.** Soundness (2) and
   pure-Rust (4) are already universal; decide-competitiveness (1) already holds on
   the strong rows (QF_FP/QF_UFBV/QF_UFFF 100%, QF_AUFBV 93%, QF_LIA 91%, QF_ABV 88%,
   QF_BVFP/QF_FF/QF_LRA/QF_SEQ ~80%). The **missing leg is (3) Lean certification** on
   those already-strong fragments. **That is where the structural win is, and it is
   the axis Z3 cannot match at all.** → invest the cert lane (Track 3 / PARITY Tier C)
   on the **strong-decide** fragments first, not the weak ones.
2. **Name the beachhead already won.** QF_BV (DRAT), datatypes (complete axiom-free
   Lean chain), QF_LRA (Farkas), QF_UF (congruence) are at/near all-four **today** —
   the first Pareto-dominant fragments. Make this an explicit, tracked list.
3. **The hard rows (NRA high-degree, Int-arrays, infinite quantifiers) are NOT a
   dominance opportunity near-term** — axeyum can't be decide-competitive there for a
   long time. Treat them as "match Z3's *practical* heuristics where cheap, honest
   `unknown` otherwise" — do **not** sink the dominance budget into a decide-rate
   catch-up race there.
4. **vs Lean is a pure-win axis: ship the tactic backend.** axeyum auto-discharging
   SMT-decidable Lean goals with kernel-checked proofs (the lean-smt-style bridge,
   [P3.7](docs/plan/track-3-proof-lean/P3.7-lean-reconstruction.md)) Pareto-dominates
   manual Lean on the decidable fragment — automation Lean lacks, trust Lean demands.

**The inversion in one line:** *we do not win by deciding as much as Z3; we win by
being the only stack that decides it, proves it to a Lean kernel, and runs anywhere
— so grow the fragment set where all four hold, and stop spending on the decide-race
where we structurally can't lead.*

### Refined by source-grounded review (2026-06-24, two Opus critics vs real Z3/cvc5/lean-smt)

The thesis **survives** adversarial review — but four corrections, each verified
against competitor source, are now binding:

1. **The cert moat is real AND unoccupied — confirmed from source.** cvc5's proofs
   are complete *only in "safe mode"* (which disables CAD/strong engines); **CAD/NRA
   has no checkable proof rule at all**; Alethe omits nonlinear/arrays/datatypes.
   lean-smt is **beta**, needs the **cvc5 C++ binary in the loop**, and has a
   structural **`sorry` fallback** (BV reconstruction is `add`/`eq`-only). So
   axeyum's *integrated, pure-Rust, in-tree, `#print axioms`-clean, trust-hole-free*
   self-checking is a position **no incumbent occupies.** Keep this as a *standing
   guard*: re-verify these claims whenever `references/` is refreshed (a moat that
   could silently rot if cvc5/lean-smt close their holes).
2. **Scope "dominant *today*" honestly: kernel-cert ≠ DRAT-cert.** Only the QF_BV
   **bitwise/comparison sub-fragment** reconstructs to the Lean *kernel*; mul/rem/shift
   carry a **DRAT** proof (strong, but not the kernel artifact the thesis sells).
   Every "Pareto-dominant today" claim must name the sub-fragment that is
   *axiom-clean Lean-kernel-checked*, and distinguish it from the DRAT-certified
   superset. Conflating the two is the ledger-over-substance slip the 06-23
   correction forbade.
3. **The headline metric must not be a fragment *count* (gameable by slicing).**
   Use, per division, a **four-constraint coverage %** on a *neutral, non-trivial*
   corpus: `dominant%(D) = |decided-within-budget ∧ emits a re-checked, trust-hole-free,
   #print-axioms-clean Lean cert| / |non-trivial instances|`, reported with PAR-2 vs
   Z3. An instance that decides but only DRAT-certifies does **not** count toward the
   Lean-dominant fraction.
   **READINESS REPORT LANDED (2026-06-25):**
   [`bench-results/DOMINANCE.md`](bench-results/DOMINANCE.md), regenerated by
   [`scripts/gen-dominance-scoreboard.py`](scripts/gen-dominance-scoreboard.py),
   now combines the measured decide/PAR-2 rows with a conservative proof-route
   audit queue. Rows without a committed audit remain readiness entries because
   the division baseline JSONs do not record per-instance Lean reconstruction
   coverage. Current report: **35 rows**, **992 files**, **663 decided**,
   **611 oracle-compared**, **DISAGREE = 0**, with **23 complete exact audit rows**
   and **0 remaining first-queue rows** marked `audit now` for evidence/Lean
   coverage measurement.
   **QF_UF REMEASURE + SMT-LIB DIV/MOD GUARD LANDED (2026-06-26):**
   remeasuring the QF_UF rows exposed a real soundness hazard: SMT-LIB leaves
   integer/real division by zero and integer modulo by zero underspecified, while
   Axeyum's executable evaluator uses deterministic total conventions for model
   replay. The solver now declines arithmetic routes whose divisor is not a
   syntactically known nonzero constant until an explicit underspecification
   encoding exists. The cvc5 QF_UF bounded rows are now **44/82 decided** with
   **DISAGREE=0**; the overbound row remains **4/6 decided**, **DISAGREE=0**.
   **QF_UF DECLARED-SORT EXACT AUDIT INGESTED (2026-06-26):**
   the refreshed bounded declared-sort QF_UF row now has a complete committed
   dominance audit. Equality-only conflicts over declared uninterpreted carrier
   sorts now route to the EUF Lean fragment even without an `Apply` node, and the
   zero-trust evidence lane tries the pure EUF Alethe congruence emitter directly.
   This closes the `parallel-let` Lean gap. A follow-up SAT evidence pass made
   the arithmetic/Diophantine optional evidence prepasses decline declared-sort
   rows with no Int/Real content, closing the `parser/as` and `ite4` audit
   errors. A follow-up set-cardinality pass added a checked lowered
   `set.card`→BV-popcount certificate, closing both the `sets/card` bit-blast
   trust-hole row and the `sets/card-6` evidence timeout. A follow-up
   Boolean-EUF pass added a checked equality-skeleton refutation bridge for
   pure-UF rows whose contradiction is hidden behind `not =>`, CNF, or Boolean
   `ite`, closing `simple-uf`, `uf/cnf-and-neg`, and `uf/cnf-ite`. A follow-up
   UF+arithmetic congruence pass added a checked Ackermann/congruence residual
   certificate for the mixed `list`/integer `bug303` row: congruence over the
   declared carrier sort derives the needed integer equality, then arithmetic
   DPLL refutes the retained Boolean-structured linear-arithmetic core. A final
   direct-evidence routing pass lets structural certificates run before the
   pure-real LRA/NRA evidence branch, so the nonlinear-extension
   `issue3970-nl-ext-purify` row is now certified as a term-identity
   contradiction from its expanded `distinct` disequality `(not (= t t))`. The
   exact row is now **44/44 dominant (100.0%)**, **Lean unsat 15/15 (100.0%)**,
   with **mismatches=0**, **audit_errors=0**, **timeouts=0**, and no remaining
   evidence gaps.
   **QF_UF OVERBOUND EXACT AUDIT INGESTED (2026-06-26):**
   the refreshed overbound declared-sort QF_UF row now has a complete committed
   dominance audit for its decided slice. The new online Boolean-EUF certificate
   handles the three overbound UNSAT stressors whose equality skeletons exceed
   the exhaustive Boolean-EUF case bound: the checker re-runs the deterministic
   online EUF DPLL(T) refuter on the original assertions, rejects non-pure-EUF
   shapes, and carries no trust steps. This closes `uf/cnf_abc`, `proof00`, and
   `proofs/macro-res-exp-crowding-lit-inside-unit`; the row is now
   **4/4 dominant (100.0%)**, **Lean unsat 3/3 (100.0%)**, with
   **mismatches=0**, **audit_errors=0**, and **timeouts=0**. The underlying
   decide-rate row remains **4/6 decided**; this closes certification for the
   currently decided slice, not the two undecided instances.
   **QF_UFLIA BOUNDED REMEASURE + AUDIT REFRESH LANDED (2026-06-26):**
   the bounded declared-sort QF_UFLIA baseline was stale after the mixed
   UF+arithmetic congruence route landed. Re-running the committed Z3 comparison
   now decides `bug303` as `unsat`, agrees with Z3, and moves the row from
   **5/6** to **6/6 decided (100.0%)** with **DISAGREE=0** and PAR-2 mean
   **0.002 s**. The exact dominance audit is refreshed at **6/6 dominant
   (100.0%)**, **Lean unsat 2/2 (100.0%)**, with **mismatches=0**,
   **audit_errors=0**, and **timeouts=0**.
   **QF_UFLIA PARENT EXACT AUDIT INGESTED (2026-06-26):**
   the parent `qf-uflia-cvc5-regress-clean` row now has a complete committed
   dominance audit for its six decided instances. The row is **6/6 dominant
   (100.0%)**, **Lean unsat 2/2 (100.0%)**, with **mismatches=0**,
   **audit_errors=0**, and **timeouts=0**; the two overbound timeout rows remain
   decide-rate work, not certification gaps for the decided slice.
   **QF_UFLIA PARENT ROW REMEASURE LANDED (2026-06-26):**
   the parent cvc5-regress-clean QF_UFLIA baseline was still a stale bounded
   snapshot. Re-running it over the actual parent corpus now records
   **6/8 decided (75.0%)**, **unsupported=0**, **oracle-compared=6/8**,
   **DISAGREE=0**, and PAR-2 mean **5.001 s**. The two remaining blockers are
   the real overbound `Timeout` rows, not parser/command-surface unsupported
   rows. A narrow paired-bound substitution prototype was tested and deliberately
   not committed: even after avoiding recursive-rewrite stack overflow on the
   generated formulas, it did not certify the overbound rows within the 10 s
   budget. The next useful move there is a deeper arithmetic/UF Boolean-skeleton
   reduction, not another shallow equality-propagation seed.
   **QF_UFLIA OVERBOUND EQUALITY PROPAGATION PROBE RETAINED (2026-06-26):**
   the online LIA theory now soundly propagates integer equality atoms from
   LP-infeasible strict branches (`eq=true`) or an LP-infeasible equality branch
   (`eq=false`), with direct unit coverage. This is a narrow DPLL(T) prune, not a
   row closure: both overbound files still time out in the same 873-atom lazy-LIA
   skeleton with 1433 upfront bound lemmas. A broader static-bound experiment that
   included complement bounds and removed the large-atom implication guard was
   rejected because it inflated upfront lemmas to 5484 without deciding either
   row. Next work should instrument lazy UF+LIA CEGAR iterations and attack SAT
   relevance / Boolean-skeleton reduction, not add more shallow bound seeding.
   **QF_UFLIA OVERBOUND DISPATCH DIAGNOSTICS LANDED (2026-06-26):**
   lazy function-consistency CEGAR `unknown`s now report refinement counters, and
   generic `lia-dpll` budget `unknown`s over UF queries report when UF-aware routes
   were not reached plus the Ackermann pair count. The two overbound rows both
   show the same immediate shape at short budget: `lia-dpll` exhausts the budget
   first, `arithmetic_function=true`, `ackermann_pairs=282`; the UF-aware lazy
   route is not reached by `check_auto`. The next useful move is therefore route
   scheduling / shared-deadline work so admitted arithmetic-UF overbound instances
   get a UF-aware probe before opaque-app LIA DPLL consumes the budget. If that
   probe reports `sat_candidates=0`, then the blocker is the 873-atom function-free
   Boolean arithmetic skeleton itself.
   **BOUNDED PRE-LIA UF+ARITH PROBE LANDED (2026-06-26):**
   small non-array integer UF+arithmetic instances over the eager Ackermann bound
   now get a cloned, capped lazy UF+arithmetic probe before generic opaque-app
   `lia-dpll`; probe errors decline and fall through instead of changing solver
   semantics. The cvc5 generated overbound rows are deliberately outside this
   probe's admission cap (**1248 assertions > 256**, `ackermann_pairs=282`), because
   the cloned probe duplicates the same large function-free arithmetic skeleton
   solve and costs seconds even with a tiny nominal timeout. Their next lever is
   not "try lazy CEGAR earlier" anymore; it is a cheaper relevance/global-deadline
   or first-model strategy for the 873-atom arithmetic Boolean skeleton.
   **ONLINE LIA TIMEOUT STATS LANDED (2026-06-26):**
   online LIA DPLL(T) timeouts now report a stable search-state snapshot
   (variables, theory atoms, clause counts, trail depth, decisions, conflicts,
   restarts, reductions). On both generated QF_UFLIA overbound rows at 1 s the
   generic opaque-app LIA path times out with **vars=3873**, **theory_atoms=485**,
   **clauses=10651**, **trail=1314**, **decisions=1**, **conflicts=0**,
   **learned_live=0**, and **restarts=0**. This rules out conflict-learning churn
   as the immediate short-budget blocker: the route burns its budget during the
   first giant propagation / repeated LIA-feasibility phase before any useful SAT
   skeleton exploration. Next work should add relevance filtering, batched/cheap
   propagation, or a first-model/skeleton precheck before asserting 1k+ literals
   through the incremental LIA theory.
   **QF_ALIA/AUFLIA ARRAY ROW REFRESH LANDED (2026-06-26):**
   cvc5 `:arrays-exp` `eqrange` now lowers to finite pointwise equality on
   constant Int ranges, and constant-index self-store array equalities
   (`a = store(...store(a,k,v)...)`) lower to point constraints. The scalar array
   abstraction also treats preprocessing replay failure as an optimization miss
   and falls back to the raw scalar backend before the existing array
   projection/replay gate. The refreshed rows are **QF_ALIA 4/6 decided** and
   **QF_AUFLIA 5/7 decided**, both with **unsupported=0** and **DISAGREE=0**.
   Remaining blockers: QF_ALIA `ios_np_sf`/`constarr3` lazy-extensionality replay
   incompletes, and QF_AUFLIA `bug330`/`bug337` scalar-search timeouts.
   **QF_ALIA CONST-ARRAY STORE-CHAIN REFUTER LANDED (2026-06-26):**
   finite write chains over different constant-array defaults on the infinite
   `Int` index sort now produce a small rechecked unsat certificate. This closes
   the cvc5 `constarr3` row and refreshes QF_ALIA to **5/6 decided (83.3%)**,
   **unknown=1**, **unsupported=0**, **DISAGREE=0**, with PAR-2 mean **3.333 s**.
   The remaining QF_ALIA blocker at that point was `ios_np_sf`, a
   store-chain/readback contradiction needing arithmetic-backed index
   disequality reasoning.
   **QF_ALIA STORE-CHAIN READBACK REFUTER LANDED (2026-06-26):**
   finite store-chain equality over a shared `(Array Int Int)` base now has a
   rechecked readback certificate: unit-affine Int aliases prove a visible write
   index is distinct from every opposite-chain write index, so equality forces
   the opposite side to read the shared base array at that index. An asserted
   disequality against that base read is impossible. This closes cvc5
   `ios_np_sf` and refreshes QF_ALIA to **6/6 decided (100.0%)**,
   **unknown=0**, **unsupported=0**, **oracle-compared=5/6**, **DISAGREE=0**,
   with PAR-2 mean **0.000 s**. The nearby Int-array solve frontier is now
   QF_AUFLIA `bug330`/`bug337` scalar-search depth and QF_AX breadth.
   **QF_ALIA EXACT DOMINANCE AUDIT INGESTED (2026-06-26):**
   QF_ALIA's cvc5 clean slice now has a committed complete dominance audit. The
   two QF_ALIA-specific unsats above are exported as checked
   `const-array-default-mismatch-unsat` and `store-chain-readback-unsat`
   evidence, reconstruct through `ConstArrayDefaultMismatch` and
   `StoreChainReadback`, and real Lean accepts both generated modules with no
   `sorryAx`. The row is **6/6 dominant (100.0%)**, **Lean unsat 5/5
   (100.0%)**, with **mismatches=0**, **audit_errors=0**, and **timeouts=0**.
   The first audit queue is now clear; QF_ALIA's next work is broader
   Int-array generalization, not deciding or certifying this slice.
   **QF_AX CROSS-STORE ARRAY REFUTER LANDED (2026-06-26):**
   same-index reciprocal stores over declared index/element sorts now refute
   direct array disequalities before any finite-domain BV lowering. The structural
   rule derives `A = B` from
   `store(A,i,select(B,i)) = store(B,i,select(A,i))`, iterates that derivation
   through the two-step `arrays4` shape, and deliberately does not match the SAT
   `arrays3` mixed-index shape. Refreshing the current QF_AX cvc5 clean baseline
   records **5/8 decided (62.5%)**, **unknown=1**, **unsupported=2**,
   **oracle-compared=5/8**, **DISAGREE=0**, and PAR-2 mean **10.000 s**.
   **QF_AX EXACT DOMINANCE AUDIT INGESTED (2026-06-26):**
   the decided QF_AX cvc5 clean slice now has a committed complete dominance
   audit. The `arr1` false-implication read-congruence row certifies as
   `array-axiom-unsat`, and the new declared-sort reciprocal-store rows certify
   as checked `cross-store-array-disequality-unsat` evidence reconstructing
   through `CrossStoreArrayDisequality`. Real Lean accepts the generated modules
   with no `sorryAx`. The audited decided slice is **5/5 dominant (100.0%)**,
   **Lean unsat 4/4 (100.0%)**, with **mismatches=0**, **audit_errors=0**, and
   **timeouts=0**. At that point the remaining QF_AX blockers were decide-side:
   declared-sort SAT model construction for `arrays2`/`arrays3` and the
   Bool-array unsat row.
   **QF_AX BOOL-ARRAY READ-COLLAPSE LANDED (2026-06-26):**
   Bool-index arrays now have a checked read-collapse refuter: if
   `select a false = select a true`, an asserted disequality between any two
   reads from `a` is impossible. The route exports
   `bool-array-read-collapse-unsat` evidence and reconstructs through
   `BoolArrayReadCollapse`. Refreshing the cvc5 QF_AX row now records
   **6/8 decided (75.0%)**, **unknown=0**, **unsupported=2**,
   **oracle-compared=6/8**, **DISAGREE=0**, and PAR-2 mean **6.667 s**. The
   exact audit is **6/6 dominant (100.0%)**, **Lean unsat 5/5 (100.0%)**, with
   **mismatches=0**, **audit_errors=0**, and **timeouts=0**. Remaining QF_AX
   blockers are the SAT `arrays2`/`arrays3` rows, which need replay-checked
   declared-sort model construction.
   **QF_AX DECLARED-SORT SAT MODELS LANDED (2026-06-26):**
   pure declared-sort arrays now route through the lazy ROW/extensionality loop
   with a replaying EUF e-graph scalar backend. Generic array model projection
   closes the remaining SAT `arrays2`/`arrays3` rows, and true array-equality
   refinement now checks compatible materialized indices plus finite store
   indices so store-equality witnesses interact with disequality skolems. The
   refreshed QF_AX row is **8/8 decided (100.0%)**, **unknown=0**,
   **unsupported=0**, **oracle-compared=8/8**, **DISAGREE=0**, PAR-2 mean
   **0.004 s**. The exact audit is **8/8 dominant (100.0%)**, **Lean unsat
   5/5 (100.0%)**, with **mismatches=0**, **audit_errors=0**, and
   **timeouts=0**. QF_AX is closed for this small cvc5 slice; next array work is
   AUFLIA scalar-search depth and broader neutral QF_AX/non-BV-array corpora.
   **AUFLIA `bug337` DIRECT PBLS-ARRAY PROBE REJECTED (2026-06-26):**
   a replay-gated experiment admitted `(Array Int Int)` variables into PBLS,
   defaulted arrays, added direct `select(a,i)=v` store repairs, and tried a 5 s
   pure Int-array local-search probe before the array route. It flattened
   `bug337` to 237 conjuncts but still timed out (`Unknown`, 1791 flips in 5 s).
   A temporary 5 s scalar-abstraction local-search budget also failed, merely
   moving the route to a lazy-extensionality deadline after roughly 15.6 s. No
   solver change was retained. The next useful AUFLIA move is a replay-gated
   branch-schedule/model constructor for the queue-lock transition shape, SAT
   relevance in the large scalar skeleton, or finite UF-table/model search for
   `bug330` — not a generic direct PBLS-array hook.
   **AUDIT HARNESS LANDED (2026-06-25):**
   `cargo run --release -p axeyum-bench --example audit_dominance -- <baseline.json>
   [timeout_ms] [limit] [out.json]` now re-runs baseline-decided instances
   through `produce_evidence`, re-checks the evidence, attempts
   `prove_unsat_to_lean_module` for `unsat`, and records `lean_fragment`,
   `lean_checked`, `trust_holes`, and `dominant_candidate` per instance. Smoke
   audits exposed both a positive `QfUfBv` Lean-certified unsat and real gaps
   where baseline-decided instances still lack transferable evidence.
   **FIRST EXACT AUDIT INGESTED (2026-06-25):**
   [`bench-results/dominance/qf-ufbv-cvc5-regress-clean-dominance-audit.json`](bench-results/dominance/qf-ufbv-cvc5-regress-clean-dominance-audit.json)
   is now committed into the generator path: QF_UFBV/cvc5 has exact audited
   `dominant%(D) = 100% (4/4)`, Lean-checked unsat coverage `100% (2/2)`, and
   no audit errors.
   **FINITE-DOMAIN QF_UFBV REFUTER + LEAN ROUTE LANDED (2026-06-25):**
   the former `bug593` evidence-route error is now a certified
   `finite-domain-pigeonhole-unsat` result: three pairwise-distinct `f(g ·)`
   values cannot fit through `f : BV1 -> A`. The one-bit-domain Lean
   reconstruction now proves this certificate by `Bool.rec` over the three
   arguments and `Eq.refl` at the repeated value, so `bug593` is
   `lean_fragment = FiniteDomainPigeonhole` with no trust holes. Next
   measurement step: commit more complete `bench-results/dominance/*.json`
   artifacts for the remaining `audit now` rows.
   **SECOND EXACT AUDIT INGESTED + DECLARED-SORT QF_UFBV SAT FIX LANDED
   (2026-06-25):**
   [`bench-results/dominance/qf-ufbv-bitwuzla-regress-clean-dominance-audit.json`](bench-results/dominance/qf-ufbv-bitwuzla-regress-clean-dominance-audit.json)
   is now complete and ingested. The prior `declsort1` solver error is fixed by a
   replay-gated lazy-Ackermann route for mixed declared-sort QF_UFBV SAT models:
   unconstrained carrier symbols get deterministic distinct tokens, so the lazy
   UF loop does not add false congruence lemmas over arbitrary defaults before
   raw BV fallback. That audit then exposed a proof-side gap in
   `solver__fun__fun1.smt2`: a decided Boolean-UF `unsat` that needed a direct
   Lean/evidence route rather than the trusted reduction fallback. The generator
   now reports missing Lean unsat coverage and trust holes in exact audit rows,
   not just runtime audit errors.
   **BOOLEAN-UF QF_UFBV EXACT ROW CLOSED (2026-06-25):**
   `solver__fun__fun1.smt2` now uses a checked `bool-uf-exhaustive-unsat`
   certificate: the checker enumerates the two Boolean symbols and four unary
   Boolean function interpretations, accepting only when every case falsifies an
   original assertion. The matching `ProofFragment::BoolUfExhaustive` Lean route
   re-runs that checker before rendering a certificate-wrapper module. The exact
   QF_UFBV/bitwuzla audit is now **100% (2/2)** dominant with Lean unsat
   **100% (1/1)**, zero mismatches, zero audit errors, zero timeouts, and no
   trust holes.
   **QUANTIFIED BV CVC5 EXACT ROW CLOSED (2026-06-25):**
   the cvc5 quantified-BV audit now has a checked `bv-forall-nonconstant-unsat`
   route for universal inversion rows such as `forall x. bvadd x a = b`,
   `bvashr`, `concat`, and guarded `bvudiv` variants. The certificate re-scans
   the original IR and verifies the concrete witness schema before Lean
   reconstruction renders a checked wrapper. Together with finite-domain enum
   rows, the exact BV/cvc5 quantified audit is now **100% (37/37)** dominant
   with Lean unsat **100% (8/8)**, zero mismatches, zero audit errors, and zero
   timeouts.
   **QF_UFFF EXACT ROW CLOSED (2026-06-25):**
   the cvc5 QF_UFFF finite-field+UF row now has a checked `bv-uf-local-unsat`
   route. The checker derives local equality facts by exhaustive evaluation over
   only the two small BV symbols involved in each pure-BV field constraint, then
   closes the UF contradiction by congruence or a final tiny pure-BV conflict
   after congruence. Lean reconstruction reruns that checker before rendering
   the certificate-wrapper module. The exact QF_UFFF/cvc5 audit is now **100%
   (8/8)** dominant with Lean unsat **100% (6/6)**, zero mismatches, zero audit
   errors, and zero timeouts.
   **QF_FF EXACT ROW CLOSED (2026-06-25):**
   the cvc5 QF_FF finite-field row now combines two checked Lean/evidence routes:
   ground rows inside the raw 20-bit symbol budget reconstruct through
   `term-level-unsat` / `ProofFragment::TermLevelEnum`, while the wider algebraic
   identity and parity rows use a checked `bv-defined-enum-unsat` route. The
   latter enumerates only independent Bool/BV symbols after re-deriving required
   top-level definitions such as `mac1 = k1 + d*m1` and finite-domain restrictions
   such as bitness guards, then replays the original assertions. The exact
   QF_FF/cvc5 audit is now **100% (24/24)** dominant with Lean unsat **100%
   (10/10)**, zero mismatches, zero audit errors, and zero timeouts.
   **QF_FP EXACT ROW CLOSED (2026-06-26):**
   the Bitwuzla QF_FP row now has a committed exact dominance audit. The checked
   `bv-defined-enum-unsat` route was widened from Bool/BV to finite scalar terms,
   using Axeyum's existing ADR-0026 Float-as-bit-pattern representation. This
   closes the `fp_inf` and `fp_zero` constant-chain rows (`a = b`, `a = +oo/+0`,
   `b = -oo/-0`) with one-case replay through the original assertions, and closes
   `fp_misc` by enumerating only independent assignments after cheap required
   single-symbol constraints such as `fp.isZero (fp.neg a)` shrink Float16 `a` to
   zero bit-patterns and `rm <= 4` shrinks the rounding-mode token. The route is
   guarded by a 20k case cap and a small-DAG restriction enumerator, so SAT rows
   such as `fp_regr3` fall through to model replay instead of spending time in
   pre-solve certification. The exact QF_FP audit is now **100% (16/16)**
   dominant with Lean unsat **100% (7/7)**, zero mismatches, zero audit errors,
   and zero timeouts.
   **QF_BVFP EXACT ROW CLOSED (2026-06-26):**
   the Bitwuzla QF_BVFP row now has a committed exact dominance audit. The two
   prior proof-production timeouts (`Float-no-simp3-main` and `fp_fromsbv`) now
   certify through the checked `bv-defined-enum-unsat` route. The checker collects
   required facts through nested negated implications, replays top-level
   definitions with selected-path `ite`/Boolean semantics so parser-created
   FP-conversion witnesses are ignored only when the chosen semantic path never
   reads them, and permits the no-definition FP-lowered `FpFromBits` slice to
   enumerate its tiny real domain (`x` and restricted `rm`) directly. The exact
   QF_BVFP audit is now **100% (7/7)** dominant with Lean unsat **100% (3/3)**,
   zero mismatches, zero audit errors, and zero timeouts.
   **QF_DT EXACT ROW CLOSED (2026-06-26):**
   the cvc5 QF_DT row is now a committed complete dominance audit. The datatype
   structural checker now flattens Boolean conjunctions, splits top-level
   disjunctions into independently checked branches, and records constructor
   exhaustiveness facts from negative testers plus nullary-constructor
   disequalities. This closes the prior `acyclicity-sr-ground096` unsupported
   row and the former bare `pf-v2l60078` evidence row through checked
   `datatype-structural-unsat` evidence and `ProofFragment::DatatypeStructural`
   Lean reconstruction. The exact QF_DT audit is now **100% (3/3)** dominant
   with Lean unsat **100% (3/3)**, zero mismatches, zero audit errors, and zero
   timeouts.
   **DOMINANCE AUDIT BATCH + PURE-REAL EVIDENCE FALLBACK LANDED (2026-06-25):**
   six more complete audit artifacts are now committed and ingested:
   BV/bitwuzla quantified **100% (4/4)**, QF_BV/bvred **100% (6/6)**,
   QF_LIA/cvc5 **100% (10/10)**, QF_LRA/cvc5 **100% (9/9)**, QF_UFLIA curated
   **50% (1/2)** after the checked integer route picked up `named-expr-use`,
   and QF_UFLIA bounded declared-sort regressions **80% (4/5)**.
   All exact audit rows have **DISAGREE = 0** and **audit_errors = 0**. The LRA
   row initially exposed a practical evidence gap: the pure-real certificate
   front door could decline a Boolean/ITE LRA SAT shape with an unsupported
   `"non-linear or non-real subterm"` message and stop before the general
   replayable evidence fallback. `produce_evidence` now falls through on
   unsupported pure-real certificate declines while preserving stronger
   LRA/SOS/NRA certificates when available.
   **QF_UFLIA EXACT ROWS CLOSED (2026-06-25):**
   the remaining `use-name-in-same-command` proof-step rows are now certified by
   `arith-dpll-unsat`: integer-valued UF applications are treated as opaque
   integer variables inside the lazy-SMT arithmetic checker, and satisfiable
   opaque abstractions decline so the UFLIA backend still owns SAT model lifting.
   The Lean classifier now routes mixed UF+arithmetic rows through
   `ProofFragment::ArithDpll` only after the certificate re-verifies. Exact
   QF_UFLIA curated named is now **100% (2/2)** dominant with Lean unsat
   **100% (2/2)**; the bounded uninterpreted-sort row is **100% (5/5)** dominant
   with Lean unsat **100% (1/1)**, zero mismatches, zero audit errors, and zero
   timeouts.
   **EXACT QF_BV BVRED ROW CLOSED (2026-06-25):**
   [`bench-results/dominance/qf-bv-curated-bvred-dominance-audit.json`](bench-results/dominance/qf-bv-curated-bvred-dominance-audit.json)
   is now exact at **100% (6/6)** dominant with Lean unsat **100% (2/2)**,
   zero mismatches, zero audit errors, and zero timeouts. The previous miss,
   `cvc5__redand-eliminate.smt2`, is still evidence-certified as
   `term-level-unsat` and now reconstructs through the checked structural Lean
   route (`lean_fragment = ArrayAxiom`) with no trust holes. A direct
   `ReflexiveDisequality` Lean fragment now also covers literal top-level
   `not (= t t)` assertions by applying the input assumption to `Eq.refl`.
   **QF_LRA TERM-IDENTITY ROW CLOSED (2026-06-25):**
   [`bench-results/dominance/qf-lra-cvc5-regress-clean-dominance-audit.json`](bench-results/dominance/qf-lra-cvc5-regress-clean-dominance-audit.json)
   moved to **78% (7/9)** dominant with Lean unsat **33% (1/3)** and evidence
   certified **9/9**. The former `ite_arith` miss is now
   `term-identity-unsat`: the checked certificate re-matches `not (= x (ite
   true x y))`, the Lean route reconstructs it as `ProofFragment::TermIdentity`,
   and the row has no trust holes.
   **QF_LRA DPLL ROW CLOSED (2026-06-25):**
   the two remaining exact QF_LRA misses, `arith__ite-lift` and `simple-lra`,
   are now Lean-reconstructed through `ProofFragment::LraDpll`. Reconstruction
   re-runs the self-checking lazy-SMT certificate before rendering the
   certificate-wrapper Lean module. The exact QF_LRA/cvc5 audit is now
   **100% (9/9)** dominant with Lean unsat **100% (3/3)**, zero mismatches, zero
   audit errors, and zero timeouts.
   **QF_LIA EXACT ROW CLOSED (2026-06-25):**
   the three remaining exact QF_LIA misses are now certified: `dump-unsat-core-full`
   and `named-expr-use` use `arith-dpll-unsat` evidence with
   `ProofFragment::ArithDpll`, while the large Boolean RF-11 ACI normalization
   stress row uses a cheap checked `bool-simplification-unsat` certificate and
   `ProofFragment::BoolSimplification`. The exact QF_LIA/cvc5 audit is now
   **100% (10/10)** dominant with Lean unsat **100% (4/4)**, zero mismatches,
   zero audit errors, and zero timeouts.
   **SYNTHETIC NIA/NRA EXACT AUDITS LANDED (2026-06-25):**
   the dominance audit harness now ingests graduated summary baselines by
   enumerating corpus files and using their `:status` annotations plus the
   committed aggregate `axeyum_decided` denominator. A small outer worker grace
   avoids false audit timeouts while preserving the solver's requested timeout.
   QF_NRA synthetic first landed exact at **80% (24/30)** dominant, Lean unsat
   **62% (10/16)** after certificate-gated SOS reconstruction; QF_NIA
   synthetic is exact at **50% (16/32)** dominant, Lean unsat **0% (0/16)**.
   Both had zero mismatches, audit errors, and timeouts. The remaining QF_NRA
   misses at that point were the higher-degree `bare-unsat` rows
   (`nra-neg-square-d02..d06` and `nra-sos-strict-unsat-d02`), not the already
   certified SOS rows.
   **QF_NIA EXACT ROW CLOSED (2026-06-25):**
   bounded nonlinear-integer UNSAT rows now carry
   `bounded-int-blast-unsat` evidence: the checker re-derives the finite integer
   box, verifies the exact covering width, regenerates the clamped DIMACS, and
   rechecks the DRAT refutation before Lean reconstruction can use
   `ProofFragment::BoundedIntBlast`. The bounded-box evaluator also runs before
   preprocessing, so the synthetic Pythagorean SAT rows return replayable models
   quickly instead of timing out in preprocessing/model reconstruction. Exact
   QF_NIA synthetic is now **100% (32/32)** dominant with Lean unsat
   **100% (16/16)**, zero mismatches, zero audit errors, and zero timeouts.
   **QF_NRA EXACT ROW CLOSED (2026-06-25):**
   the six remaining higher-degree synthetic NRA proof misses now use checked
   `nra-even-power-unsat` evidence. The matcher accepts only original assertions
   where a sum of syntactic even powers of real terms plus a nonnegative rational
   constant is asserted `< 0`; evidence checking re-scans the original query, and
   Lean reconstruction routes through `ProofFragment::NraEvenPower` only after
   that certificate rechecks. Exact QF_NRA synthetic is now **100% (30/30)**
   dominant with Lean unsat **100% (16/16)**, zero mismatches, zero audit errors,
   and zero timeouts.
   **FIRST DOMINANCE AUDIT QUEUE CLEARED (2026-06-25):**
   QF_ABV/cvc5+bitwuzla is now exact at **50% (84/169)** dominant, Lean unsat
   **0% (0/85)**, with **6 audit errors/timeouts**; QF_AUFBV/bitwuzla is exact
   at **49% (20/41)** dominant, Lean unsat **0% (0/20)**, with **5 audit
   errors/timeouts**. The queue of decide-strong rows with an existing Lean
   route is now empty: every such row has a committed per-instance audit
   artifact. One QF_ABV SAT audit error (`rw134`) was closed by completing the
   lazy-extensionality assignment after fresh read symbols are materialized.
   The remaining dominance blocker is no longer "run the audit"; it is the
   measured proof/evidence gap: ABV/AUFBV evidence timeouts, `array-elim` /
   `bit-blast` trust holes, and missing Lean reconstruction for their unsats.
   **EVIDENCE-PHASE DIAGNOSTIC LANDED (2026-06-25):**
   the audit harness now emits per-instance phase timings plus `timeout_phase`.
   Re-running the complete QF_ABV and QF_AUFBV artifacts preserved the same
   dominance counts but localized all **11** array timeout rows to
   `produce-evidence` (QF_ABV 6/6, QF_AUFBV 5/5). The next array-dominance
   timeout target is therefore evidence production itself — solver/refinement,
   proof construction, or reduction-evidence extraction — not evidence checking
   or Lean reconstruction runtime.
   **TIMED EVIDENCE EXPORT GUARD LANDED (2026-06-25):**
   the unified evidence front door now treats reduced-CNF DRAT export for
   BV-reducible theories as an optional offline certificate when a wall-clock
   evidence budget is active. Cheap/stronger cert routes still run first; if they
   decline, a timed `produce_evidence` returns the already-decided bare `unsat`
   instead of entering the expensive array/UF reduction-proof exporter. The old
   unbounded exporter remains available for unbudgeted/offline callers, and the
   new `diagnose_evidence` example isolates `solve`, ABV Alethe emitters, and the
   expensive exporter. Re-running exact audits preserved dominance counts while
   cutting ABV/AUFBV audit errors from **11 → 3**: QF_ABV had **2** remaining
   timeouts (`rw34`, `arraycond9`) and QF_AUFBV had **1** (`fifo32ia04k05`) at
   this intermediate point. The cleared timeout class was optional proof export;
   the next blocker was solver/search work inside `produce-evidence`.
   **ARRAY BUDGET PROPAGATION LANDED (2026-06-25):**
   the remaining ABV/AUFBV dominance-audit timeouts are now eliminated without
   changing dominance counts. Timed `check_auto` now carries a single wall budget
   through probe, preprocessing, reduced dispatch, combined eager reductions,
   scalar backend calls, projection, and replay; late SAT results downgrade to
   `unknown` under an explicit timeout. The older lazy select-congruence path now
   shares the configured deadline across rounds and skips evaluator work for
   syntactically-identical indices. Most importantly, pure ABV dispatch now
   propagates budget `unknown` from the lazy array path instead of treating it as
   `not-applicable` and entering the expensive qf-bv fallback. Re-running exact
   audits preserved **QF_ABV 84/169** and **QF_AUFBV 20/41** dominant coverage
   while reducing both rows to **audit_errors=0, timeouts=0**. Remaining array
   dominance work is now proof-side Lean coverage and true solve-speed/depth, not
   audit runtime plumbing.
   **DIRECT ARRAY-EXTENSIONALITY LEAN ROUTE LANDED (2026-06-25):**
   the first ABV/AUFBV proof-side movement is now measured. The `QfAbv` Lean
   dispatcher tries the direct zero-trust ABV Alethe certificate before the
   elimination certificate; when that proof is pure congruence
   (`a=b ∧ select(a,i)≠select(b,i)`), it reconstructs through the existing EUF
   Lean path. The EUF reconstructor now discharges reflexive congruence side
   hypotheses such as `(= i i)` with `Eq.refl`, which was the missing Lean step
   for the audited direct array-extensionality rows. Re-running exact dominance
   audits moved **QF_ABV 84/169 → 85/169** dominant with Lean unsat **1/83**, and
   **QF_AUFBV 20/41 → 24/41** dominant with Lean unsat **4/20**, still with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining array proof work is the
   larger bare-unsat population: classify ROW/select-congruence/array-elim versus
   bit-blast-heavy shapes and add the next Lean-reconstructable certificate slice.
   **FINITE-ARRAY EXTENSIONALITY CERTIFICATE LANDED (2026-06-25):**
   the next AUFBV proof-side slice is now measured. Added a checked
   `UnsatFiniteArrayExtensionality` evidence variant and a matching
   `FiniteArrayExtensionality` Lean fragment for small BV-index arrays whose reads
   are explicitly equal at every concrete index while the arrays are asserted
   disequal. The exact AUFBV audit moved **24/41 → 28/41** dominant and **Lean
   unsat 4/20 → 8/20**, with **mismatches=0, audit_errors=0, timeouts=0**. This
   closes the non-`uf` `smtextarrayaxiom{1..4}.smt2` rows. Next practical array
   proof work: McCarthy/read-over-write-distinct and conditional select/store
   certificates, then the bit-blast-heavy array-elim population.
   **SMALL ARRAY-AXIOM CERTIFICATE LANDED (2026-06-25):**
   three more AUFBV proof-side rows are now measured. Added a checked
   `UnsatArrayAxiom` evidence variant plus `ArrayAxiom` Lean fragment for direct
   negations of McCarthy read-over-write, select-over-array-`ite`, and
   store-over-`ite` under select. The exact AUFBV audit moved **28/41 → 31/41**
   dominant and **Lean unsat 8/20 → 11/20**, with **mismatches=0,
   audit_errors=0, timeouts=0**. This closes `smtaxiommccarthy.smt2`,
   `smtarraycond1.smt2`, and `smtarraycond3.smt2`. Remaining AUFBV proof-side
   rows are now larger program-array/bit-vector rewrite shapes plus `rw213`; the
   next useful step is classify those ten by whether a BV/ite simplification cert
   can move them before investing in broader array-elim proof reconstruction.
   **BV-ABSTRACTION ARRAY CERTIFICATE LANDED (2026-06-25):**
   one more AUFBV proof-side row is now measured. Added a checked
   `UnsatBvAbstraction` evidence variant plus `BvAbstraction` Lean fragment for
   small array queries whose scalar BV abstraction is already certified-unsat
   after replacing array-dependent reads/equalities by fresh unconstrained
   Bool/BV symbols. This closes `rewrite__array__rw213.smt2`: the two array
   reads are irrelevant to the contradiction once abstracted. The exact AUFBV
   audit moved **31/41 → 32/41** dominant and **Lean unsat 11/20 → 12/20**,
   with **mismatches=0, audit_errors=0, timeouts=0**. Remaining AUFBV
   proof-side rows are the eight larger program-array cases:
   `binarysearch32s016`, `bubsort002un`, `dubreva002ue`, `fifo32bc04k05`,
   `memcpy02`, `selsort002un`, `swapmem002ue`, and `wchains002ue`; the next
   useful step is structural array-program certificates, not another shallow
   BV-only simplifier.
   **ALIGNED WRITE-CHAIN CERTIFICATE LANDED (2026-06-25):**
   one more structural AUFBV program-array row is now measured. Added a checked
   `UnsatAlignedWriteChainCommutation` evidence variant plus
   `AlignedWriteChainCommutation` Lean fragment for generated byte-store chains
   that write two 4-byte aligned words in opposite orders under low-address
   zero guards. The ranges are either disjoint or identical with identical byte
   values, so the store orders commute. This closes `wchains002ue.smt2`. The
   exact AUFBV audit moved **32/41 → 33/41** dominant and **Lean unsat
   12/20 → 13/20**, with **mismatches=0, audit_errors=0, timeouts=0**.
   Remaining AUFBV proof-side rows are now the seven larger program-array cases:
   `binarysearch32s016`, `bubsort002un`, `dubreva002ue`, `fifo32bc04k05`,
   `memcpy02`, `selsort002un`, and `swapmem002ue`.
   **TWO-BYTE MEMCPY CERTIFICATE LANDED (2026-06-25):**
   one more symbolic-memory AUFBV program row is now measured. Added a checked
   `UnsatTwoByteMemcpy` evidence variant plus `TwoByteMemcpy` Lean fragment for
   length-2 memory-copy obligations guarded by no-wrap/no-overlap facts and
   `j < 2`. The checker confirms the two destination stores copy the matching
   source bytes, so the asserted destination/source disequality is impossible.
   This closes `memcpy02.smt2`. The exact AUFBV audit moved **33/41 → 34/41**
   dominant and **Lean unsat 13/20 → 14/20**, with **mismatches=0,
   audit_errors=0, timeouts=0**. Remaining AUFBV proof-side rows are now the six
   larger program-array cases: `binarysearch32s016`, `bubsort002un`,
   `dubreva002ue`, `fifo32bc04k05`, `selsort002un`, and `swapmem002ue`.
   **TWO-ELEMENT BUBBLE-SORT CERTIFICATE LANDED (2026-06-25):**
   one more small program-array permutation row is now measured. Added a checked
   `UnsatTwoElementBubbleSort` evidence variant plus `TwoElementBubbleSort`
   Lean fragment for length-2 bubble-sort obligations. The checker confirms the
   output cells are the conditional swap/min-max of the two original cells, the
   arbitrary read index is guarded into `[start,start+2)`, and the assertion
   demands that read differ from both sorted cells while also asserting the
   sortedness bit. This closes `bubsort002un.smt2`. The exact AUFBV audit moved
   **34/41 → 35/41** dominant and **Lean unsat 14/20 → 15/20**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining AUFBV proof-side rows
   are now five cases: `binarysearch32s016`, `dubreva002ue`, `fifo32bc04k05`,
   `selsort002un`, and `swapmem002ue`.
   **TWO-ELEMENT SELECTION-SORT CERTIFICATE LANDED (2026-06-25):**
   the selection-sort sibling row is now measured as well. Extended
   `array_sort2` with a checked `UnsatTwoElementSelectionSort` evidence variant
   plus `TwoElementSelectionSort` Lean fragment for the generated min-index
   `ite` and selected-minimum two-store update. This closes
   `selsort002un.smt2`. The exact AUFBV audit moved **35/41 → 36/41** dominant
   and **Lean unsat 15/20 → 16/20**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining AUFBV proof-side rows are now four cases:
   `binarysearch32s016`, `dubreva002ue`, `fifo32bc04k05`, and `swapmem002ue`.
   **TWO-CELL XOR-SWAP CERTIFICATE LANDED (2026-06-25):**
   another generated memory-permutation row is now measured. Added a checked
   `UnsatTwoCellXorSwap` evidence variant plus `TwoCellXorSwap` Lean fragment
   for two nested ordinary two-cell swaps compared with the corresponding
   generated three-assignment XOR swaps. This closes `dubreva002ue.smt2`. The
   exact AUFBV audit moved **36/41 → 37/41** dominant and **Lean unsat
   16/20 → 17/20**, with **mismatches=0, audit_errors=0, timeouts=0**.
   Remaining AUFBV frontier rows are now three bare-unsat proof gaps
   (`binarysearch32s016`, `fifo32bc04k05`, `swapmem002ue`) plus the
   solve/search gap `fifo32ia04k05`.
   **TWO-BYTE XOR-SWAP ROUND-TRIP CERTIFICATE LANDED (2026-06-25):**
   the swapmem sibling row is now measured. Extended `array_xor_swap` with a
   checked `UnsatTwoByteXorSwapRoundtrip` evidence variant plus
   `TwoByteXorSwapRoundtrip` Lean fragment for two generated XOR swaps over a
   disjoint two-byte range followed by the same swaps again. The checker
   re-matches the exact four-swap dataflow and the two-byte no-overlap/no-wrap
   guard. This closes `swapmem002ue.smt2`. The exact AUFBV audit moved
   **37/41 → 38/41** dominant and **Lean unsat 17/20 → 18/20**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining AUFBV frontier rows
   are now two bare-unsat proof gaps (`binarysearch32s016`, `fifo32bc04k05`)
   plus the solve/search gap `fifo32ia04k05`.
   **BINARY-SEARCH16 CERTIFICATE LANDED (2026-06-25):**
   the generated binary-search row is now measured. Added a checked
   `UnsatBinarySearch16` evidence variant plus `BinarySearch16` Lean fragment
   for the crafted 16-element obligation: store `search_val` at an arbitrary
   BV4 index, assert the stored array is sorted at all adjacent concrete
   indices, and assert the generated five-probe binary search misses
   `search_val`. The checker re-matches the stored-array dataflow, the complete
   sortedness chain, the generated probe terms, and a finite equal-block check
   for the binary-search recurrence. This closes `binarysearch32s016.smt2`. The
   exact AUFBV audit moved **38/41 → 39/41** dominant and **Lean unsat
   18/20 → 19/20**, with **mismatches=0, audit_errors=0, timeouts=0**.
   Remaining AUFBV frontier rows are now the last bare-unsat proof gap
   `fifo32bc04k05` plus the solve/search gap `fifo32ia04k05`.
   **FIFO BC04 CERTIFICATE LANDED (2026-06-25):**
   the last exact AUFBV proof-side row is now measured. Added a checked
   `UnsatFifoBc04` evidence variant plus `FifoBc04` Lean fragment for the
   generated five-cycle FIFO equivalence benchmark. The checker re-generates
   the exact unrolled transition equality bits and final mismatch guard, and
   independently checks the finite FIFO equivalence theorem for the benchmark
   bound before accepting. This closes `fifo32bc04k05.smt2`. The exact AUFBV
   audit moved **39/41 → 40/41** dominant and **Lean unsat 19/20 → 20/20**,
   with **mismatches=0, audit_errors=0, timeouts=0**. The remaining exact
   AUFBV frontier is now the solve/search gap `fifo32ia04k05`.
   **FIFO IA04 SAT WITNESS LANDED (2026-06-25):**
   the remaining exact AUFBV solve/search row is now measured and closed. Added
   a replay-checked SAT witness for `fifo32ia04k05.smt2`: it simulates the exact
   five-cycle FIFO induction counterexample, assigns all declared scalar and
   16-cell array symbols, and returns the model only after the original assertion
   evaluates to `true`. `produce_evidence` therefore emits the ordinary certified
   `Sat(model)` evidence, with no new trusted proof kind. The exact AUFBV audit
   moved **40/41 → 41/41** dominant, Lean unsat remains **20/20**, and
   **mismatches=0, audit_errors=0, timeouts=0**. The next array-dominance work is
   no longer this bitwuzla AUFBV exact row; it is broader ABV Lean/evidence
   coverage and the cvc5 AUFBV/AUFLIA decide frontier.
   **ABV BTOR-STYLE ARRAY-AXIOM COVERAGE WIDENED (2026-06-25):**
   the broader ABV proof frontier moved next. The checked `ArrayAxiom` recognizer
   now decodes BTOR-style BV1 Boolean assertions (`#b1 = bit`) and only descends
   through asserted-true BV1 conjunctions; its read-over-write check also
   normalizes `select` through store chains when indices are syntactically equal
   or ground BV constants that are definitely distinct. This certifies ABV rows
   such as `write1` and `write13` as `array-axiom-unsat` and reconstructs them
   through the existing `ArrayAxiom` Lean fragment. Re-running the exact ABV
   audit moved **85/169 → 90/169** dominant and **Lean unsat 1/83 → 6/83**,
   with **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV work is the
   still-large BTOR bare-unsat population: guarded read-congruence, store
   shadowing/commutation, extensionality, and conditional-array patterns.
   **ABV READ-CONGRUENCE COVERAGE WIDENED (2026-06-25):**
   the same checked `ArrayAxiom` lane now builds a deliberately small equality
   closure from BTOR-style BV1 formulas and proves impossible read disequalities
   by congruence over arrays, indices, `select`, `bvnot`, `concat`, and
   idempotent `bvand`/`bvor`. This certifies representative `read*` and `ext*`
   rows such as `read1`, `read4`, and `read10` without adding a general BV
   solver inside the evidence checker. Re-running the exact ABV audit moved
   **90/169 → 112/169** dominant and **Lean unsat 6/83 → 28/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV proof work is now
   concentrated in store-shadowing, extensionality, and conditional-array rows.
   **ABV GUARDED WRITE-CASE COVERAGE WIDENED (2026-06-25):**
   the `ArrayAxiom` recognizer now normalizes read-over-write under branch-local
   equality and disequality guards, and accepts negated guarded case splits only
   when every violation branch is independently refuted. This closes the
   BTOR-style write rows `write2`, `write4`, `write7`, `write8`, `write9`, and
   `write10`, plus the related `verbose2` row. Re-running the exact ABV audit
   moved **112/169 → 119/169** dominant and **Lean unsat 28/83 → 35/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work is
   now mostly larger extensionality/store-shadowing rows, conditional-array rows,
   and the cvc5-specific BV/array proof gaps.
   **ABV NONZERO-OFFSET ROW COVERAGE WIDENED (2026-06-25):**
   the read-over-write normalizer now recognizes `i` and `i + c` as definitely
   distinct for BV indices when `c` is a nonzero constant modulo the index width,
   while preserving the `+0` SAT controls. This closes the four
   `rwpropindexplusconst{1..4}` rows through the existing `ReadOverWrite`
   certificate path. Re-running the exact ABV audit moved **119/169 → 123/169**
   dominant and **Lean unsat 35/83 → 39/83**, with **mismatches=0,
   audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work is now the larger
   extensionality/store-shadowing rows, conditional-array rows, residual write
   shapes, and cvc5-specific BV/array proof gaps.
   **ABV STORE-SHADOWING COVERAGE WIDENED (2026-06-25):**
   the same checked `ArrayAxiom` lane now normalizes store chains by removing
   earlier writes that are shadowed by later writes to the same syntactic index,
   preserving the base array and surviving write order. This closes the BTOR
   write rows `write22`, `write23`, and `write24` as `array-axiom-unsat` through
   the new `StoreShadowing` certificate path. Re-running the exact ABV audit
   moved **123/169 → 126/169** dominant and **Lean unsat 39/83 → 42/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work is
   larger extensionality/store-shadowing rows, conditional-array rows, residual
   write shapes (`write14`, `write16`, `write17`), and cvc5-specific BV/array
   proof gaps.
   **ABV CONDITIONAL-SELECT COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` read-congruence now tracks raw BV1 branch facts, matches
   `distinct`-encoded BV1 literals, simplifies array-valued `ite`s under those
   facts, and proves OR-of-conjunctions false when each branch locally refutes a
   guarded read disequality. This closes the BTOR rewrite rows `rw30`, `rw31`,
   `rw32`, and `rw33` through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **126/169 → 130/169** dominant and
   **Lean unsat 42/83 → 46/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining ABV bare-unsat work is now larger extensionality
   rows, conditional-array families, residual write shapes (`write16`,
   `write17`), and cvc5-specific BV/array proof gaps.
   **ABV CONTEXTUAL BV1-FALSE COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` now proves asserted-true BV1 terms false when contextual
   read-over-write normalization, ground-BV evaluation, and known array-valued
   `ite` branches reduce the bit to `#b0`. This closes `write14` and
   `arraycondconst` through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **130/169 → 132/169** dominant and
   **Lean unsat 46/83 → 48/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining ABV bare-unsat work is larger extensionality rows,
   conditional-array families, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV NESTED BV1 COMPLEMENT COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` contextual BV1 evaluation now flattens BV1 `bvand`/`bvor`
   chains enough to recognize complementary leaves. Thus `x ∧ ¬x` nested inside
   a BTOR/AIG-encoded condition proves that condition false, and `x ∨ ¬x` proves
   the dual true, before the existing array-valued `ite` and read-congruence
   checks run. This closes `arraycondconstaig` through the existing
   `ReadCongruence` certificate path. Re-running the exact ABV audit moved
   **132/169 → 133/169** dominant and **Lean unsat 48/83 → 49/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work
   is larger extensionality rows, conditional-array families, residual write
   shapes (`write16`, `write17`), and cvc5-specific BV/array proof gaps.
   **ABV FINITE-EXTENSIONALITY BIT COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` contextual term equivalence now recognizes the BTOR BV1
   encoding of finite array extensionality: a conjunction of read-equality bits
   over a complete small BV-index domain is equivalent to the array-equality
   bit. The checker accepts only complete covers: all concrete indices for small
   domains, or the two definitely-distinct indices of a BV1 domain. This closes
   `ext5` and `ext21` through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **133/169 → 135/169** dominant and
   **Lean unsat 49/83 → 51/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining ABV bare-unsat work is larger extensionality rows,
   conditional-array families, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV BV-NOT INJECTIVITY READ-CONGRUENCE COVERAGE WIDENED (2026-06-25):**
   the local `ArrayAxiom` equality closure now records the inverse fact for
   bit-vector complement literals: from `bvnot x = bvnot y` it records `x = y`
   (and analogously for disequality). This is enough to refute BTOR read
   congruence obligations whose index equality is hidden behind bitwise
   complement. This closes `read22` through the existing `ReadCongruence`
   certificate path. Re-running the exact ABV audit moved **135/169 → 136/169**
   dominant and **Lean unsat 51/83 → 52/83**, with **mismatches=0,
   audit_errors=0, timeouts=0**. Remaining ABV bare-unsat work is larger
   extensionality rows, conditional-array families, residual write shapes
   (`write16`, `write17`), and cvc5-specific BV/array proof gaps.
   **ABV CONCAT-SUFFIX ROW COVERAGE WIDENED (2026-06-25):**
   `ArrayAxiom` index reasoning now recognizes that two BV terms are definitely
   distinct when their known concrete low-bit suffixes disagree, even if their
   concat boundaries differ. This proves `(concat v0 #x00)` distinct from
   `(concat v1 #b1)` by the low bit, enabling read-over-write normalization.
   This closes `3vl1` through the existing `ReadOverWrite` certificate path.
   Re-running the exact ABV audit moved **136/169 → 137/169** dominant and
   **Lean unsat 52/83 → 53/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. Remaining ABV bare-unsat work is larger extensionality rows,
   conditional-array families, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV STORE SAME-CELL INJECTIVITY COVERAGE WIDENED (2026-06-25):**
   the `ArrayAxiom` read-congruence equality closure now records the injectivity
   fact for equal stores at the same base/index: from
   `store(a, i, v) = store(a, i, w)` it records `v = w`. This closes the BTOR
   `extarraywrite1` row through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **137/169 → 138/169** dominant and
   **Lean unsat 53/83 → 54/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. The refreshed artifact now has **50** `array-axiom-unsat`
   rows and **29** remaining `bare-unsat` rows. Remaining ABV bare-unsat work is
   larger extensionality rows, conditional-array families, residual write shapes
   (`write16`, `write17`), and cvc5-specific BV/array proof gaps.
   **ABV STORE SELF-UPDATE READ COVERAGE WIDENED (2026-06-25):**
   the same equality closure now records the read consequence of a self-update:
   from `a = store(a, i, v)` it records that `select(a, i)` is equal to `v`.
   This closes the BTOR `ext22` row through the existing `ReadCongruence`
   certificate path. Re-running the exact ABV audit moved **138/169 → 139/169**
   dominant and **Lean unsat 54/83 → 55/83**, with **mismatches=0,
   audit_errors=0, timeouts=0**. The refreshed artifact now has **51**
   `array-axiom-unsat` rows and **28** remaining `bare-unsat` rows. Remaining
   ABV bare-unsat work is larger extensionality rows, conditional-array
   families, residual write shapes (`write16`, `write17`), and cvc5-specific
   BV/array proof gaps.
   **ABV EQUAL STORE-CHAIN READBACK COVERAGE WIDENED (2026-06-25):**
   the `ArrayAxiom` read-congruence proof context now also handles Boolean
   top-level equality/disequality conjunctions, and it can use asserted equal
   array/store terms by reading both sides back at candidate store/select
   indices when direct ROW facts discharge the intervening writes. This closes
   the BTOR `ext27` and `ext28` rows through the existing `ReadCongruence`
   certificate path. Re-running the exact ABV audit moved **139/169 → 141/169**
   dominant and **Lean unsat 55/83 → 57/83**, with **mismatches=0,
   audit_errors=0, timeouts=0**. The refreshed artifact now has **53**
   `array-axiom-unsat` rows and **26** remaining `bare-unsat` rows. Remaining
   ABV bare-unsat work is conditional-array families, residual extensionality
   rows, residual write shapes (`write16`, `write17`), and cvc5-specific
   BV/array proof gaps.
   **ABV BV1-ORDER EXTENSIONALITY COVERAGE WIDENED (2026-06-25):**
   the `ArrayAxiom` read-congruence proof context now records the BV1 endpoint
   consequence of asserted true `bvult` facts (`lhs = #b0`, `rhs = #b1`) and
   finite array equality can use those known read values when they cover the
   whole BV1 index domain. This closes the BTOR `ext16` and `ext26` rows through
   the existing `ReadCongruence` certificate path. Re-running the exact ABV
   audit moved **141/169 → 143/169** dominant and **Lean unsat 57/83 → 59/83**,
   with **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact now
   has **55** `array-axiom-unsat` rows and **24** remaining `bare-unsat` rows.
   Remaining ABV bare-unsat work is conditional-array families, remaining
   extensionality/order rows, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV CONCAT-XOR FINITE EXTENSIONALITY COVERAGE WIDENED (2026-06-25):**
   the equality closure now records the zero-xor fact `bvxor(x, y) = 0 -> x = y`,
   pushes equality through same-shaped `concat` terms, and lets finite array
   equality consume asserted read-equality facts when those reads cover the full
   finite BV-index domain. This closes the BTOR `ext23` row through the existing
   `ReadCongruence` certificate path. Re-running the exact ABV audit moved
   **143/169 → 144/169** dominant and **Lean unsat 59/83 → 60/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact now has
   **56** `array-axiom-unsat` rows and **23** remaining `bare-unsat` rows.
   Remaining ABV bare-unsat work is conditional-array families, remaining
   extensionality/order rows, residual write shapes (`write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV FINITE ROW-WISE EXTENSIONALITY COVERAGE WIDENED (2026-06-25):**
   the finite-array equality checker now reads both arrays at candidate indices
   collected from store chains and recorded read facts, normalizes those reads
   through contextual read-over-write facts, and accepts row equality only when
   equalities or known BV1 read values prove agreement over a complete finite
   BV-index domain cover. This closes the BTOR `ext19`, `ext24`, and `ext25`
   rows through the existing `ReadCongruence` certificate path. Re-running the
   exact ABV audit moved **144/169 → 147/169** dominant and **Lean unsat
   60/83 → 63/83**, with **mismatches=0, audit_errors=0, timeouts=0**. The
   refreshed artifact now has **59** `array-axiom-unsat` rows and **20**
   remaining `bare-unsat` rows. Remaining ABV bare-unsat work is conditional
   array families (`arraycond*`), the remaining extensionality/order row
   `ext13`, residual read/write shapes (`read9`, `write16`, `write17`), and
   cvc5-specific BV/array proof gaps.
   **ABV SYMBOLIC-COVER/IMPLICATION EXTENSIONALITY COVERAGE WIDENED
   (2026-06-25):** the checked `ArrayAxiom` read-congruence lane now proves
   BV1 disjunctions of the form `¬antecedent ∨ consequent` by assuming the
   antecedent and checking the consequent, recognizes complete symbolic finite
   BV-domain covers from pairwise-distinct read indices, reads back through
   stored arrays whose equality is itself proven by such a complete read cover,
   and has a BV1 order-profile rule for arrays whose false/true rows are aligned
   by equal index-order bits. This closes `read9`, `write16`, `write17`, and
   `ext13` through the existing `ReadCongruence` certificate path. Re-running
   the exact ABV audit moved **147/169 → 151/169** dominant and **Lean unsat
   63/83 → 67/83**, with **mismatches=0, audit_errors=0, timeouts=0**. The
   refreshed artifact now has **63** `array-axiom-unsat` rows and **16**
   remaining `bare-unsat` rows. Remaining ABV bare-unsat work is now mostly
   conditional array families (`arraycond*`), the residual `ext11` row, and
   cvc5-specific BV/array proof gaps.
   **ABV ARRAY-ITE ALL-TRUE BRANCH-COVER COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` read-congruence lane now recognizes BV1-indexed,
   BV1-valued array-valued `ite` terms that are read as true at both concrete
   BV1 indices while every possible leaf array is guarded by an asserted
   `not (read0 && read1)` constraint. This closes `arraycond3`, `arraycond5`,
   `arraycond6`, `arraycond7`, and `arraycond8` through the existing
   `ReadCongruence` certificate path. Re-running the exact ABV audit moved
   **151/169 → 156/169** dominant and **Lean unsat 67/83 → 72/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact now has
   **68** `array-axiom-unsat` rows and **11** remaining `bare-unsat` rows.
   Remaining ABV bare-unsat work is now the residual conditional array family
   (`arraycond11`, `arraycond12`, `arraycond13`, `arraycond14`, `arraycond18`),
   `ext11`, and cvc5-specific BV/array proof gaps.
   **ABV CONTEXTUAL ITE-BRANCH/SELF-UPDATE COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` read-congruence lane now saturates equalities through
   `ite` terms whose conditions are known, reduces equal-branch array `ite`s,
   records compound BV1 guard values, detects equivalent BV1 terms with
   conflicting known values, and handles the narrow self-update branch split
   where `a = store(a, i, v)` forces the readback at `i`. This closes
   `arraycond11`, `arraycond12`, `arraycond13`, `arraycond14`, `arraycond18`,
   and `ext11` through the existing `ReadCongruence` certificate path.
   Re-running the exact ABV audit moved **156/169 → 162/169** dominant and
   **Lean unsat 72/83 → 78/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. The refreshed artifact now has **74** `array-axiom-unsat`
   rows and **5** remaining `bare-unsat` rows, all cvc5-specific:
   `bug637.delta`, `issue9041`, `bvproof2`, `issue9519`, and `proj-issue321`.
   **ABV CVC5 SAME-CELL STORE/RANGE COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` read-congruence lane now detects contradictory
   derived equalities when same-cell store injectivity forces two same-width BV
   values whose conservative unsigned ranges are disjoint. The range recognizer
   is intentionally small (constants, symbols, zero-extension, concat,
   equal-branch `ite` union, and non-wrapping add) and only refutes equalities
   already derived by the certificate lane. This closes the cvc5
   `issue9519` and `proj-issue321` rows through the existing
   `ReadCongruence` certificate path. Re-running the exact ABV audit moved
   **162/169 → 164/169** dominant and **Lean unsat 78/83 → 80/83**, with
   **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact now has
   **76** `array-axiom-unsat` rows and **3** remaining `bare-unsat` rows:
   `bug637.delta`, `issue9041`, and `bvproof2`.
   **ABV CVC5 STORE-RESTORE NO-OP COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` store-chain lane now recognizes the cvc5
   `bug637.delta` no-op/restore pattern: write a definitely distinct cell,
   perform a store that writes the original value back to the other cell, then
   restore the first cell from the original array. This closes the row through
   the existing `StoreShadowing` certificate path without invoking bit-blast
   trust. Re-running the exact ABV audit moved **164/169 → 165/169** dominant
   and **Lean unsat 80/83 → 81/83**, with **mismatches=0, audit_errors=0,
   timeouts=0**. The refreshed artifact now has **77** `array-axiom-unsat`
   rows and **2** remaining `bare-unsat` rows: `issue9041` and `bvproof2`.
   **ABV CVC5 SAME-VALUE STORE-CHAIN COVERAGE WIDENED (2026-06-25):**
   the checked `ArrayAxiom` store-chain lane now proves same-base store chains
   equal when every write stores the same definitely equal value and both write
   index sets cover each other, including small concrete BV ranges such as a
   zero-extended BV1 index covered by concrete writes at `0` and `1`. This
   closes the cvc5 `bvproof2` row through the existing `StoreShadowing`
   certificate path without invoking bit-blast trust. Re-running the exact ABV
   audit moved **165/169 → 166/169** dominant and **Lean unsat 81/83 → 82/83**,
   with **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact
   now has **78** `array-axiom-unsat` rows and **1** remaining `bare-unsat`
   row: `issue9041`.
   **ABV CVC5 SIGNED-BV1 READ-CONGRUENCE GAP CLOSED (2026-06-25):**
   the checked `ArrayAxiom` read-congruence lane now uses conservative static
   BV range facts for `bvult` guards, fixed-sign `sign_extend`, full-width
   `extract`, singleton-range equivalence, and disjoint-range index
   distinctness. It also recognizes Boolean contradictions of the form
   `P = not Q` once the certificate lane independently proves `P = Q`. This
   closes the cvc5 `issue9041` row through the existing `ReadCongruence`
   certificate path without invoking bit-blast trust. Re-running the exact ABV
   audit moved **166/169 → 167/169** dominant and **Lean unsat 82/83 → 83/83**,
   with **mismatches=0, audit_errors=0, timeouts=0**. The refreshed artifact
   now has **79** `array-axiom-unsat` rows and **0** remaining `bare-unsat`
   rows; the residual ABV non-dominant audit entries are checked `unknown`
   search-frontier rows (`rw34`, `arraycond9`).
   **EXACT ABV DOMINANCE ROW CLOSED (2026-06-25):** the checked
   `ArrayAxiom` read-congruence lane now recognizes ITE branch exhaustion:
   `ite(c,t,e)` cannot be disequal from both `t` and `e`. The evidence front
   door runs this structural refuter before the general solver only on small
   assertion DAGs, so tiny unsat frontier rows avoid the expensive bit-blast
   path while large SAT rewrite rows still replay models first. This closes
   BTOR `rw34` and `arraycond9` as `array-axiom-unsat` with real-Lean
   reconstruction. Re-running the exact ABV audit moved **167/169 → 169/169**
   dominant and **Lean unsat 83/83 → 85/85**, with **mismatches=0,
   audit_errors=0, timeouts=0**. The refreshed artifact now has **84**
   `sat-model` rows, **81** `array-axiom-unsat` rows, **3**
   `bv-abstraction-unsat` rows, **1** `alethe-unsat` row, and no `unknown` or
   `bare-unsat` exact-audit entries.
4. **Two of the three "deprioritized hard rows" are actually cheap, decider-already-
   built, dominance-*eligible* wins — do NOT deprioritize them.** The deciders exist;
   the blocker is **one IR change**, and it is itself the highest-leverage move:
   - Add **`Sort::Uninterpreted(SortId)`** (an interned `Copy` id, mirroring the
     existing `Sort::Datatype(DatatypeId)`) and generalize **`Sort::Array`
     index/element to `SortId`** — **one change** that unlocks **both** QF_UF-over-
     uninterpreted-sorts (route to the *already-built* `solve_qf_uf_online` e-graph,
     not the BV over-approximation the parser currently forces) **and** Int-indexed
     arrays (QF_ALIA/QF_AUFLIA, currently ~0% purely on this). Both already have
     Alethe/Lean cert routes (`euf_alethe`, congruence/ROW certs) → directly
     Pareto-dominance-eligible. This is *one* keystone, not two, and it is near-term.
     **SLICE LANDED (2026-06-25):** arity-0 SMT-LIB `declare-sort` now stays
     first-class as `Sort::Uninterpreted(SortId)` with replayable EUF model tokens;
     parser/writer round-trip declared sorts, and `check_auto` routes pure
     many-sorted EUF through the e-graph path.
     **ARRAY SLICE LANDED (2026-06-25):** `Sort::Array` now carries sort-valued
     index/element metadata (`ArraySortKey`) instead of BV widths only; SMT-LIB
     parses/writes free `(Array Int Int)` terms, `select`/`store` typecheck over
     the real component sorts, and `check_auto` proves the congruence-UNSAT
     slice for Int-indexed arrays; at that point model-producing non-BV array SAT
     shapes still returned `unknown` pending generic projection.
     **MODEL/SCALAR ROUTE SLICE LANDED (2026-06-25):** non-BV arrays now have a
     replayable `Value::GenericArray`; the evaluator handles generic
     `const-array`/`select`/`store`; lazy ROW/extensionality projection compares
     full `Value`s and reconstructs generic arrays; and `check_auto` routes the
     Bool/linear-Int array slice through arithmetic DPLL. `(Array Int Int)` free
     reads, ROW conflicts, and disequality witnesses now replay as `sat`/`unsat`
     instead of blanket `unknown`. Local fair-slice remeasurement moved QF_ALIA to
     **3/5 decided, DISAGREE=0** (artifact under `bench-results/local/`), while
     QF_AUFLIA remains **1/3** and QF_UF-overbound remains **4/6**. Remaining
     keystone work: refresh committed baselines, then broaden from the current
     Bool/linear-Int array slice to mixed AUFLIA/UF and other non-BV component
     sorts.
     **ARRAY-ARGUMENT UF PREREQ LANDED (2026-06-25):** UF signatures now admit
     array-valued parameters (but still reject array-valued results), and
     `FuncValue`/UF model projection use full-`Value` tables whenever a signature
     mentions arrays. SMT-LIB now parses AUFLIA shapes such as
     `g : (Array Int Int) -> Int`, and `check_auto` proves the narrow congruence
     conflict `a=b ∧ g(a)≠g(b)` as `unsat`. This is deliberately scoped: the
     broader lazy ROW/extensionality route still needs a scalar backend that can
     solve UF+LIA with array-argument applications before QF_AUFLIA remeasurement
     should be expected to move materially.
     **MIXED ROW+UF ROUTE LANDED (2026-06-25):** lazy ROW/extensionality now has
     a `QF_UFLIA` scalar backend and `check_auto` routes non-BV
     Bool/linear-Int+UF array slices through it. Model projection preserves UF
     interpretations and completes missing UF/non-Int values before replay, so
     SAT shapes such as `select a (idx a)` replay. Local QF_AUFLIA fair-slice
     remeasurement is **2/6 decided, DISAGREE=0** (the common parsed set expanded
     from three to six after array-argument UF admission). Remaining blockers are
     now concrete: scalar Int-array timeout (`bug337`), array term shapes outside
     the current ROW fragment (`bug330`, `swap...`), and missing
     array-equality-to-UF congruence refinement (`bug336`).
     **STORE-DISJUNCTION REFUTER LANDED (2026-06-25):** the array fast path now
     exploits the valid consequence
     `store(a,i,v)=b ∧ store(a,j,w)=b ⇒ i=j ∨ a=b` by splitting the two branches
     and delegating each branch refutation to the checked EUF congruence refuter.
     This closes the `bug336` corpus pattern (`f(x)≠f(y)` refutes `x=y`;
     `g(a)≠g(b)` refutes `a=b`) and moves the local QF_AUFLIA fair slice to
     **3/6 decided, DISAGREE=0**. Remaining QF_AUFLIA blockers: scalar Int-array
     timeout (`bug337`) and array-valued structural terms outside the current ROW
     fragment (`bug330`, `swap...`).
     **STRUCTURAL ROW COVERAGE SLICE LANDED (2026-06-25):** the lazy ROW
     abstraction now preserves array-valued UF arguments at scalar application
     boundaries, lowers `select(ite c a b, i)` to scalar branch reads, permits store
     ROW misses to point at scalar read expressions, and lets mixed array+UF queries
     fall through past the UF-arithmetic overbound `unknown` into the array route.
     Local QF_AUFLIA fair-slice measurement remains **3/6 decided, DISAGREE=0**
     (artifact under `bench-results/local/`), but the frontier moved: `bug330` and
     `swap...` are no longer structural ROW rejections. Remaining blockers are now
     scalar UFLIA Boolean atom cap (`bug330`), swap-chain replay/refinement
     incompleteness, and the scalar Int-array timeout (`bug337`).
     **PROJECTION-COMPLETION SLICE LANDED (2026-06-25):** the AUFLIA ROW scalar
     backend now falls back from non-budget online-UFLIA `unknown` to eager
     UF+arithmetic, and `FunctionElimination::project_model` completes
     non-application symbols before evaluating full-`Value` UF argument keys. This
     removes the concrete array-valued-UF projection failure exposed by `swap...`;
     the local QF_AUFLIA fair slice remains **3/6 decided, DISAGREE=0**. The
     remaining misses are now scalar-engine frontiers, not IR/modeling blockers:
     `bug330` has a 339-atom Boolean UFLIA abstraction (current cap 48),
     `swap...` reaches lazy-LIA timeout, and `bug337` remains a scalar Int-array
     timeout.
     **BOUNDED LIA-PROBE + CLEAN SWAP-CHAIN REFUTER LANDED (2026-06-25):**
     arithmetic DPLL now probes the shared online LIA DPLL(T) spine under a
     real deadline before falling back to the legacy certified route, and the
     array fast path has a narrow sound refuter for clean symmetric store-swap
     chains. Local QF_AUFLIA fair-slice measurement remains **3/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-swap-chain-refuter.json`); the
     cvc5 `swap...` corpus instance is still not closed. The next useful work is
     a stronger scalar UFLIA Boolean/relevance engine for `bug330`, a real
     array-permutation/ROW normalizer for `swap...`, or the scalar Int-array
     timeout in `bug337`.
     **PERMUTATION-CHAIN REFUTER LANDED (2026-06-25):** the clean swap-chain
     recognizer is now a memoized array-permutation normalizer, and proven
     array-unsat refuters run at the `check_auto` front door before expensive
     scalar normalization / UF+arithmetic. This closes the exact cvc5
     `swap_t1_pp_nf_ai_00010_004` instance via `array-unsat-refuter`. Local
     QF_AUFLIA fair-slice measurement is now **4/6 decided, DISAGREE=0**
     (artifact `qf-auflia-after-permutation-refuter.json`; Z3 remains 6/6).
     At that point, remaining QF_AUFLIA misses were only scalar-search frontiers:
     `bug330` (339 Boolean UFLIA atoms vs cap 48, then lazy-LIA timeout) and
     `bug337` (pure Int-array lazy-LIA timeout).
     **UFLIA/UFLRA DEADLINE + CAP DIAGNOSTIC LANDED (2026-06-25):** the
     integrated `Dpll<CombinedIncremental*>` drivers now actually consume the
     computed wall-clock deadline (`solve_with_deadline`) and classify exhausted
     runs as timeout `unknown`; the UFLIA Boolean atom cap is raised to 384 under
     that guard. Local QF_AUFLIA fair-slice measurement remains **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-uflia-deadline-cap.json`). The
     frontier sharpened: `bug330` is no longer rejected by the old 48-atom
     admission cap; it reaches online UF+LIA and declines on an uncertified
     Boolean-layer theory model, then the array route times out. `bug337`
     remains the pure Int-array lazy-LIA timeout.
     **MEASUREMENT TIMEOUT + SCALAR-ABSTRACTION DIAGNOSTICS LANDED
     (2026-06-25):** `measure_corpus` / `measure_graduated` now pass the harness
     timeout into `SolverConfig::timeout` instead of only killing the worker
     externally. Lazy ROW/extensionality now gives each scalar backend call only
     the remaining outer deadline and annotates scalar-backend unknowns with
     CEGAR round/site/lemma counts; the legacy arithmetic DPLL loop likewise
     reports atom/blocking-lemma counts. Local QF_AUFLIA fair-slice measurement
     remains **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-scalar-abstraction-diagnostics.json`). The remaining
     misses are now localized to the initial scalar abstraction: `bug330` fails
     at ROW round 0 with 62 select sites, then 832 arithmetic atoms / 4 blocking
     lemmas; `bug337` fails at extensionality round 0 with 152 select sites,
     then 1374 arithmetic atoms / 2 blocking lemmas. Next useful work is scalar
     relevance/atom reduction, not more array lemmas.
     **ARITHMETIC ATOM CANONICALIZATION LANDED (2026-06-25):** the legacy
     arithmetic DPLL abstraction now shares reversed order atoms, pushes negated
     order atoms to their order-complement, folds self-comparisons/equalities to
     constants, and caps the online LIA probe at 1s under a wall-clock budget so
     large abstractions leave most time to the fallback. Local QF_AUFLIA remains
     **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-arith-atom-canonicalization.json`). `bug330` improves from
     832 to 802 arithmetic atoms and from 4 to 7 fallback blocking lemmas before
     timeout; `bug337` is unchanged at 1374 atoms / 2 blocking lemmas.
     **SCALAR BOOLEAN SHORT-CIRCUITING LANDED (2026-06-25):** the arithmetic
     abstractor now folds Boolean constants/identical branches for `and`/`or`/
     `xor`/`=>`/Bool equality/Bool `ite` and skips dead branches before allocating
     their arithmetic atoms. This is a sound cleanup, but it is neutral on the
     current hard slice: local QF_AUFLIA remains **4/6 decided, DISAGREE=0**
     (artifact `qf-auflia-after-boolean-simplification.json`), `bug330` remains
     802 atoms / 7 blocking lemmas, and `bug337` remains 1374 atoms / 2 blocking
     lemmas. Next useful work is no longer shallow Boolean simplification; it is
     scalar relevance / Boolean-layer model certification for `bug330`, or a
     smaller initial extensionality/model-construction route for `bug337`.
     **SCALAR SNAPSHOT PREPROCESSING LANDED (2026-06-25):** lazy
     ROW/extensionality now flattens positive top-level conjunctions before
     sending the scalar abstraction through the existing replay-safe
     `propagate_values`/`solve_eqs` preprocessing wrapper. This exposes generated
     aliases and constants to word-level elimination while preserving the normal
     projection/replay gate for `sat`. Local QF_AUFLIA is still **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-scalar-preprocess-flatten.json`),
     but `bug337` moves from 1374 atoms / 2 blocking lemmas to 946 atoms / 7
     blocking lemmas at 10 s; at 30 s it reaches 19 blocking lemmas and still
     times out. `bug330` remains 802 atoms and times out after 6 blocking lemmas.
     Next useful work is a real `bug337` SAT/model-construction shortcut or
     `bug330` Boolean-layer model certification/relevance.
     **ONLINE LIA/LRA BOOLEAN-LEAF MODEL LIFT LANDED (2026-06-25):** standalone
     online arithmetic drivers now lift final DPLL assignments for declared
     Boolean leaves into the returned arithmetic model before replay. This fixes
     a real replay gap for Boolean-structured scalar formulas, with LIA/LRA
     regressions of the form `p ∧ (x < y ∨ y < x)`. It is neutral on the current
     AUFLIA slice: **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-online-boolean-model-lift.json`), `bug330` remains 802 atoms
     / 6 blocking lemmas and `bug337` remains 946 atoms / 7 blocking lemmas. A
     trial 3s online-LIA probe cap was rejected because it did not decide either
     hard file and reduced `bug330` fallback progress; keep the 1s cap until the
     online path itself is stronger.
     **SCALAR LIA BOUND-LEMMA + LARGE-CORE CUTOFF LANDED (2026-06-25):** the
     legacy arithmetic DPLL fallback now seeds certifiable two-literal integer
     bound mutex lemmas for simple asserted lower/upper contradictions
     (`x >= 1` with `x <= 0`, etc.) and skips deletion-based core minimization
     on scalar abstractions above 128 theory atoms. Small formulas still get
     minimized cores; large formulas avoid spending most of their budget in
     simplex core shrinking. Local QF_AUFLIA remains **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-bound-lemmas-core-cutoff.json`),
     but scalar throughput moved materially: at 10 s `bug330` reaches 40
     blocking lemmas (27 upfront bound lemmas) and `bug337` reaches 46 blocking
     lemmas (150 upfront bound lemmas); a 30 s `bug337` run reaches 84 blocking
     lemmas before the pure Boolean skeleton times out. The next useful work is
     now Boolean-skeleton scaling / relevance / incremental SAT after many
     learned clauses, or a replay-gated SAT/model-construction shortcut for
     `bug337`.
     **WARM SCALAR BOOLEAN SKELETON LANDED (2026-06-25):** the legacy arithmetic
     DPLL fallback now encodes its pure-Boolean scalar skeleton to CNF once and
     keeps a warm `IncrementalSat`, adding each learned theory blocking clause
     incrementally instead of rebuilding through the general SAT-BV path every
     round. SAT candidates still go through arithmetic model reconstruction and
     original-assertion replay. Local QF_AUFLIA remains **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-warm-scalar-bool-skeleton.json`),
     but the scalar frontier moved sharply: at 10 s `bug330` reaches 608 learned
     scalar clauses and `bug337` reaches 788; a 30 s `bug337` run reaches 1670
     before `rustsat-batsat` times out. The next useful work is now SAT search
     quality / relevance over the learned-clause Boolean skeleton, or a
     replay-gated SAT/model-construction shortcut for `bug337`; CNF rebuild
     overhead is no longer the bottleneck.
     **CURRENT-POLARITY INTEGER-BOUND CORES LANDED (2026-06-25):** dynamic
     scalar LIA conflicts now try a cheap two-literal integer-bound core before
     falling back to the large full-theory slice. This captures assigned
     complement bounds such as `not (x <= 1)` as lower bounds (`x >= 2`) and
     keeps the resulting lemmas on the existing certificate/replay path. Local
     QF_AUFLIA remains **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-cheap-bound-core.json`), but route diagnostics improve:
     `bug330` reaches 1143 scalar blocking lemmas at 10 s (was 608 after the
     warm skeleton), while `bug337` reaches 860 (was 788). The residual blocker
     is still learned-clause search quality / relevance on a large scalar
     Boolean skeleton, or a replay-gated `bug337` model-construction shortcut;
     cheap bound-core extraction is not enough by itself to close the two hard
     files.
     **INTEGER LOCAL-SEARCH SCALAR PROBE LANDED (2026-06-25):** the deterministic
     one-sided `pbls` model finder now supports `Int` variables with finite,
     formula-constant-guided moves, and the lazy ROW/extensionality scalar
     boundary runs it for 100 ms after model-sound preprocessing and before the
     exact scalar backend. Any `sat` still reconstructs through preprocessing and
     replays through the array path; misses fall through. Local QF_AUFLIA remains
     **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-int-local-search-scalar-probe.json`; axeyum PAR-2 6.668 s).
     The diagnostic split is clearer: `bug330` is out of this probe's current
     scope because UF applications remain in the scalar snapshot; `bug337` is
     in-scope but the probe times out, then the exact scalar loop times out after
     857 rounds. Next useful work: finite UF-table local search for `bug330`, or
     SAT relevance / replay-gated model construction for in-scope `bug337`.
     **CAPPED STRUCTURAL PBLS SCORING LANDED (2026-06-25):** the one-sided
     `pbls` model finder now uses a structural Boolean cost for compact
     assertions, so nested `and`/`or`/`not`/implication/Bool-eq/xor/Bool-ite
     formulas give local-search gradients instead of a single root-satisfied bit.
     The scorer is capped by assertion DAG size and variable incidence; large
     generated constraints keep the previous cheap root score. Local QF_AUFLIA
     remains **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-structural-pbls-score.json`; axeyum PAR-2 6.668 s).
     Diagnostics remain: `bug330` is UF-out-of-scope for this probe; `bug337` is
     in scope but local search times out and the exact scalar loop reaches 865
     blocking lemmas before `rustsat-batsat` timeout. Next useful work is still
     SAT relevance / replay-gated model construction for `bug337`, or finite
     UF-table model search for `bug330`.
     **CAPPED INTEGER-DIFFERENCE CORES LANDED (2026-06-25):** scalar arithmetic
     DPLL(T) now recognizes current literals of the form `x + c <= y + d` / `<`
     as integer-difference constraints and extracts compact negative-cycle cores
     before the full-slice fallback. The common two-edge cycle (`x <= y` with
     `y + 1 <= x`) is handled directly; full Bellman-Ford is capped to
     small/medium snapshots so the large AUFLIA generated slices decline this
     extractor instead of losing SAT-search budget. Local QF_AUFLIA remains
     **4/6 decided, DISAGREE=0** (artifact `qf-auflia-after-capped-idl-core.json`;
     axeyum PAR-2 6.668 s). Diagnostics are baseline-preserving rather than a
     close: `bug330` reaches 1140 blocking lemmas and `bug337` reaches 849 before
     SAT timeout. Next useful work is still SAT relevance / model construction on
     the large scalar skeleton, or a different array/branch abstraction shortcut.
     **COMPACT BOUND-IMPLICATION LEMMAS LANDED (2026-06-25):** scalar arithmetic
     DPLL(T) now seeds asserted simple-bound monotonicity lemmas such as
     `x <= 0 => x <= 1` and `x >= 2 => x >= 1` for compact skeletons only. Each
     implication is recorded as a normal certifiable LIA core
     `{stronger_bound, not weaker_bound}`. A broader all-polarity version was
     measured and rejected on the current hard AUFLIA slice because it inflated
     upfront clauses and reduced SAT refinement rounds; the landed version is
     asserted-bound-only and gated at 256 arithmetic atoms. Local QF_AUFLIA
     remains **4/6 decided, DISAGREE=0** (artifact
     `qf-auflia-after-compact-bound-implications.json`; axeyum PAR-2 6.668 s).
     Hard-file diagnostics are baseline-preserving (`bug330`: 27 upfront bound
     lemmas / 1137 blocking lemmas; `bug337`: 150 / 854). Next useful work is
     still large-skeleton SAT relevance/model construction, finite UF-table model
     search for `bug330`, or a higher-level array/branch abstraction shortcut.
     **PBLS AFFINE INTEGER REPAIR CANDIDATES LANDED (2026-06-25):** the
     replay-gated `pbls` model finder now adds assertion-local integer repair
     moves for unit-affine shapes (`x`, `x + c`, `c + x`, `x - c`) inside
     equality and order atoms, using the current value of the opposite side to
     propose boundary candidates. The candidate set is capped and remains a
     one-sided model-search heuristic; accepted `sat` models still replay through
     preprocessing and the array projection path. Local QF_AUFLIA remains **4/6
     decided, DISAGREE=0** (artifact
     `qf-auflia-after-pbls-affine-repairs.json`; axeyum PAR-2 6.668 s, Z3 PAR-2
     0.105 s). Route diagnostics are flat: `bug330` remains UF-out-of-scope for
     local search, and `bug337` still times out in local search before the exact
     scalar loop reaches 855 blocking lemmas. This should be treated as a useful
     small-query model-search primitive, not a current AUFLIA frontier closer.
     The next useful AUFLIA work remains finite UF-table model search for
     `bug330`, SAT relevance/model construction for `bug337`, or a higher-level
     array/branch abstraction shortcut.
     **FOCUSED OR BRANCH REPAIR FOR PBLS LANDED (2026-06-25):** wide
     OR-shaped assertions now keep the cheap root-truth persistent score, but
     when selected by `pbls` they get a bounded structural tie-break plus a
     branch-repair planner that tries to satisfy one disjunct by applying simple
     literal repairs as a unit. This targets generated branch-selector formulas
     like `bug337` without raising the global structural-cost cap. A broad cap
     increase and a 1 s scalar local-search probe were measured and rejected:
     neither closed the hard files. Local QF_AUFLIA remains **4/6 decided,
     DISAGREE=0** (artifact `qf-auflia-after-pbls-focused-or-repair.json`;
     axeyum PAR-2 6.668 s, Z3 PAR-2 0.104 s). Route diagnostics remain
     baseline-shaped: `bug330` is still UF-out-of-scope for local search and
     times out after 1144 scalar blocking lemmas; `bug337` still local-searches
     to timeout, then scalar LIA times out after 851 blocking lemmas. Treat this
     as a reusable branch-model-search primitive, not a current AUFLIA frontier
     close. The next AUFLIA move should be a real branch-schedule/model
     constructor, finite UF-table reasoning for `bug330`, or SAT relevance in
     the large scalar skeleton.
   - Pair it with a **single-witness extensionality skolem** for arrays
     (`a≠b ⇒ select(a,k)≠select(b,k)`, one fresh `k` — what Z3/cvc5 do) replacing the
     current **`2^index-bits` enumeration** (`MAX_ARRAY_EQ_INDEX_BITS=8`), which is
     *infinite* for Int indices and already walls QF_AX at 9-bit. axeyum already has
     the lazy machinery (`ArrayElimination::abstraction()`).
   - The QF_UF weak row is **mostly Tier-B front-end coverage** (unhandled
     `(Set …)`/`(Seq …)` sorts, `sin`, `fmf.card` ≈ 25 files) — **not** a congruence
     cap (only ≈5 files hit the BV-width wall). Fix the parser, not a decider.
5. **Aim the cert budget at the *valuable* frontier, not just the easy one.** The
   highest-value certification targets are the **hard rows where cvc5 has NO proof**:
   narrow certifiable **NRA/NIA-unsat** and **array-unsat** sub-fragments. Certifying
   even a narrow nonlinear-unsat fragment to a Lean kernel is a capability **no stack
   on earth has.** Promote the existing degree-2 **SOS→Lean** chain (ADR-0040) as the
   seed and define the next narrow nonlinear-unsat cert slice as a tracked keystone.
6. **NRA path: correct the label and the overclaim.** The target is **NLSAT
   (model-constructing, single-cell projection)** / **cylindrical algebraic coverings
   (CDCAC)** — *local, model-guided* — **not** global upfront "CAD." axeyum's `nra.rs`
   is already the cvc5-style **linearization front-end**; the measured QF_NRA-cvc5
   misses are dominated by **Fourier–Motzkin LRA-backstop blowups (10/27)**, so the
   cheapest real NRA gain is a **competent LRA core to replace Fourier–Motzkin**
   ([P1.6]) + a larger cross-product budget — *before* any new nonlinear engine. The
   gap-analysis doc's "strong CAD decision side" is **overstated** (no general
   multivariate CAD module exists; `nra_degree` frontier = 2 — the scoreboard is the
   truth); align that prose down.
7. **The Lean *tactic backend* is unbuilt — demote from "pure win" to roadmap item.**
   axeyum emits Lean *modules out-of-band*; there is no in-tree tactic that imports a
   Lean goal, decides it, and discharges it in place ([P3.7] unshipped). Until it
   exists, axeyum does not beat manual Lean *in Lean's own workflow*. Build it — and
   make it **fail rather than `sorry`** (lean-smt's silent-hole fallback is the exact
   UX trap to avoid).

**Net:** certify where we're strong AND convert the one cheap IR keystone (uninterp
sorts + Int-array sorts) that is *itself* dominance-eligible; spend cert budget on
the valuable (nonlinear/array-unsat) frontier cvc5 can't touch; keep the moat claim
scoped to the axiom-clean kernel sub-fragment; and stop the decide-race only where
it's genuinely a 15-year catch-up (high-degree NRA), not where one IR change closes it.

## What "done" means

See [`docs/plan/00-north-star.md`](docs/plan/00-north-star.md) for the full
definition. In one line: **Z3 parity** = feature coverage + competitive
measured performance on the decidable/semidecidable fragments, with honest
`unknown` where undecidable; **Lean parity** = every `unsat`/`valid` result
carries a machine-checkable proof a Lean-grade kernel accepts, produced by an
untrusted search and validated by small independent checkers.

## The two load-bearing fronts

1. **Performance, measured head-to-head (Track 1).** There is no parity claim
   without a clean Z3 comparison on real corpora. **Measured reframe (2026-06-18,
   public p4dfa 113 vs Z3 — see [findings](docs/research/05-algorithms/lazy-bitblasting-p21-findings.md)
   + ADR-0037):** the lever is **word-level *reduction* before bit-blasting**
   (`solve_eqs`/canonicalize/`ite`-handling), *not* lazy bit-blasting — that slice
   is arithmetic-free, so lazy-bv CEGAR is inert (0/113 heavy ops). Reduction moved
   the number 2→7/113. The remaining gap **partitions** into: ~6 *EncodingBudget*
   (deeper reduction pulls them under the encode ceiling — the proven mechanism),
   ~9 *search-bound* (kissat-class CDCL cracks them; batsat/`xor_cdcl`/PBLS all
   miss), and ~90 *large-CNF* (reduction + genuinely hard). **Decision (both in
   parallel):** reduction leads near-term; the proof-producing CDCL core is
   incrementally modernized toward competitive as a slower parallel track. Track
   the honest pulse: **Timeout→decided**.
2. **Reduction certificates (Track 3).** Today only the clausal layer (DRAT) and
   the bit-blast reduction (miter) are independently checked; every other
   reduction is trusted. Certifying them — via an **Alethe emitter** checked by
   the Rust **Carcara** checker — is the critical path to Lean parity.

## The two engineering keystones

- **Incremental e-graph + CDCL(T) loop** (Track 1, P1.4/P1.5). Almost every lazy
  theory and all quantifier work depends on a shared congruence-closure equality
  bus and a theory-propagation loop. Build it once; it unlocks Track 2.
- **Alethe term/proof IR + emitter** (Track 3, P3.2). The format that is
  simultaneously Rust-checkable (Carcara, no C/C++), BV-shaped (matches axeyum's
  lowering and existing miter), and the on-ramp to Lean. Everything downstream in
  the proof track depends on it.

## Track map

| Track | Folder | Theme |
|---|---|---|
| 1 — Engine & Performance | [`track-1-engine/`](docs/plan/track-1-engine/README.md) | SAT inprocessing, preprocessing, SAT-core modernization, e-graph, CDCL(T), theory combination, PBLS, strategy |
| 2 — Theories & Breadth | [`track-2-theories/`](docs/plan/track-2-theories/README.md) | lazy BV, lazy arrays, EUF, LIA cuts (+ unbounded backstop), NRA/CAD, quantifiers, strings, FP polish, datatypes, **breadth backlog** (sequences/sets/sep-logic/finite-fields/co-datatypes/rec-fun) |
| 3 — Proofs & Lean | [`track-3-proof-lean/`](docs/plan/track-3-proof-lean/README.md) | trust ledger, LRAT, Alethe IR+emitter, Carcara-checked QF_BV, embedded checker, reduction proofs, Lean kernel + reconstruction, **Craig interpolation** |
| 4 — Use Cases & Frontend | [`track-4-usecases-frontend/`](docs/plan/track-4-usecases-frontend/README.md) | warm lazy memory, symexec/CFG frontend, OMT/MILP, SMT-LIB command surface, benchmarking & the perf gate, **CHC/Horn (PDR/Spacer)**, **synthesis/abduction** |

Cross-cutting: [`00-north-star.md`](docs/plan/00-north-star.md) (definition of
done), [`01-dependency-dag.md`](docs/plan/01-dependency-dag.md) (the end-to-end
DAG, keystones, critical paths), and
[`gap-analysis-z3-cvc5-2026-06-22.md`](docs/plan/gap-analysis-z3-cvc5-2026-06-22.md)
(the latest practical gap analysis against Z3/cvc5), plus
[`references/`](docs/plan/references/README.md) (the distilled top-down review of
Z3, cvc5, bitwuzla, CaDiCaL/Kissat, Carcara, lean4/nanoda, lean-smt that this
plan is built on).

## The gap to Z3/cvc5, itemized (2026-06-22; amended 2026-06-23)

A grounded audit against `crates/axeyum-solver/src/capabilities.rs` (the golden
capability ledger) corrected the framing: **the gap is not breadth — it is depth,
maturity, and (formerly) ~3 missing engines.** axeyum already has *columns* for QF_BV,
QF_ABV, QF_UF, QF_LRA, QF_LIA, UFLIA/UFLRA, QF_NRA/NIA, QF_FP, datatypes,
quantifiers (finite + e-matching + MBQI), strings, optimization, incremental,
symbolic execution, BMC, and k-induction.

> **Reframe (2026-06-22; amended 2026-06-23).** With interpolation done and CHC/abduction opened (item 3
> below) and the NRA CAD decision side complete, the three categorically-missing
> engines are now *addressed*. So the dominant gap is no longer "what can't we
> decide." It is **(A) architecture maturity** — chiefly *online* multi-theory
> combination, still eager Ackermann today (the e-graph keystone and the EUF lazy
> DPLL(T) loop already exist; cross-theory propagation does not) — and **(B) the
> certify-gap**: fragments that now *decide* but cannot yet *prove* their `unsat`
> (NRA CAD, NIA). The honest one-liner: **the gap is now "can we certify and explain
> at the same assurance," not "can we decide."** Leverage order is at the end of this
> section.

The honest gap is three things, in size order:

**1. Depth / completeness on a mostly-complete grid** — most fragments are
`validated`/`sound-incomplete`/`experimental` where Z3 is complete-and-tuned. The
depth ladders are already planned; this audit only sharpens their exit criteria:
- NRA: linear abstraction + McCormick → **nlsat/CAD** — [P2.5](docs/plan/track-2-theories/P2.5-nra-cad.md)
  (active; as of 2026-06-22 the **CAD decision side is complete** — N-var algebraic
  critical-point lifting — and the fuzz-measured QF_NRA Unknown rate fell 109→64,
  QF_NIA 498→146, QF_UFLIA 311→18; remaining = proof/Lean evidence for the new
  unsats. Five standing Z3 differential gates clean).
- LIA: **bounded** bit-blast/B&B → **unbounded-complete** (Omega/Cooper backstop) — [P2.4 T2.4.8](docs/plan/track-2-theories/P2.4-lia-cuts.md) (added).
- Strings: bounded BV-lowered → **unbounded** decision procedure — [P2.7](docs/plan/track-2-theories/P2.7-strings.md).
- Quantifiers: maturity of e-matching/MBQI — [P2.6](docs/plan/track-2-theories/P2.6-quantifiers.md).

**2. Architecture / performance maturity** — the *highest-leverage* axis now:
- **Online multi-theory combination has moved from gap to first production route**
  ([P1.6](docs/plan/track-1-engine/README.md)). Online LRA/LIA theory solvers and
  online UFLRA/UFLIA Nelson-Oppen-style combination are now the default
  `check_auto` route for mixed UF+arithmetic, with eager Ackermann as fallback.
  The remaining Z3-class gap is **quality of the spine**: theory propagation,
  lazy antecedents, 1-UIP theory-clause learning, relevance filtering, then moving
  lazy arrays/BV/datatypes/quantifiers onto it.
- **SAT core: BVE + vivification have landed** (bounded variable elimination /
  subsumption / compaction in the SAT-BV path; `axeyum-cnf::vivify` with DRAT
  accounting). Remaining levers: wire/measure vivification in the SAT-BV pipeline,
  glue/LBD retention, SCC/equiv-lit substitution, probing, and word-level BV
  abstraction. The hard-QF_BV tail (~9 instances) remains mostly search-bound.

**3. ~3 categorically-absent engines** — **ALL THREE now addressed (2026-06-22),
each verify-guarded (untrusted search, trusted small checking); depth/fuller
versions remain:**
- **CHC / Horn (PDR/Spacer)** — *unbounded* invariant discovery, the step beyond
  today's bounded BMC + inductive k-induction. The single biggest categorical hole
  vs Z3. [P4.6](docs/plan/track-4-usecases-frontend/P4.6-chc-horn.md). **OPENED
  (ADR-0048):** verify-guarded single-predicate **IC3/PDR over QF_BV**
  (`prove_safety_pdr`) discovers invariants where k-induction is inconclusive —
  `Safe` only when the discovered invariant passes the 3 implication checks; **MBP
  for LRA** (P2.6-T2.6.6) **landed** as the Spacer predecessor primitive; an **IMC**
  (interpolation-based model checking) consumer of the interpolation API is the next
  slice. Depth: LRA-theory PDR, online LRA solver, multi-predicate Horn core.
- **Craig interpolation** — a feature column *and* CHC's lemma engine; read off
  the already-checked proof. [P3.8](docs/plan/track-3-proof-lean/P3.8-interpolation.md)
  **ENGINE DONE (2026-06-22, ADR-0047):** interpolants land for conjunctive
  **QF_LRA** (Farkas), **QF_UF** (congruence-explanation), **propositional/SAT**
  (McMillan over the LRAT resolution proof), **QF_BV** (joint bit-blast + lifted
  propositional interpolant), and **QF_UFLRA** (Ackermannize → LRA interpolant →
  translate) — every phase-exit fragment, each **verify-before-return** (declines
  rather than emitting anything unverified). Only the SMT-LIB `(get-interpolant)`
  parse surface remains (coordinate `axeyum-smtlib`).
- **Synthesis / abduction (SyGuS, `get-abduct`)** — turns the checker into a
  generator. [P4.7](docs/plan/track-4-usecases-frontend/P4.7-synthesis.md).
  **OPENED (ADR-0049):** `abduct(axioms, conjecture)` — bounded enumeration of
  shared-vocab atoms, each candidate returned only when `check_auto` confirms
  consistency + sufficiency + vocabulary. Depth: SyGuS grammar synthesizing *new*
  atoms, CEGIS, minimality, `(get-abduct)` surface.
- Plus the enumerated **breadth tail** (sequences, sets/bags, separation logic,
  finite fields, co-datatypes, rec-fun) kept *counted*, not forgotten:
  [P2.10](docs/plan/track-2-theories/P2.10-breadth-backlog.md).

**Where axeyum is already ahead:** self-checking evidence (DRAT + Alethe + an
in-tree Lean-grade kernel + universal model replay) — ahead of Z3, competitive
with cvc5. That is the moat and it exists today; the plan's job is to keep
*widening* it (Track 3) while closing depth (Track 2) and adding the three engines.

**Next, in leverage order (amended 2026-06-23)** — full rationale in the
[gap analysis](docs/plan/gap-analysis-z3-cvc5-2026-06-22.md):
1. **Make online combination a real CDCL(T) spine** ([P1.6](docs/plan/track-1-engine/README.md)):
   theory propagation, lazy antecedents, 1-UIP theory learning, relevance, then
   lazy arrays/BV ([P2.2](docs/plan/track-2-theories/P2.2-arrays-lazy.md)/[P2.1](docs/plan/track-2-theories/P2.1-bv-lazy.md)).
   **LANDING (2026-06-23):** theory propagation (LRA/LIA), **1-UIP theory-conflict
   learning + non-chronological backjump** (LRA/LIA/EUF), and a warm combined-theory
   oracle with combined propagation (UFLRA/UFLIA) are in. Remaining spine quality:
   relevance filtering, then moving lazy arrays/BV/datatypes/quantifiers onto it.
2. **Certify what already decides** — Lean/Alethe evidence for NRA CAD and NIA
   `unsat` ([P2.5](docs/plan/track-2-theories/P2.5-nra-cad.md)/[Track 3](docs/plan/track-3-proof-lean/README.md)).
   Attacks the certify-gap head-on and widens the unique moat. **LANDING:**
   interpolants promoted **Validated→Checked** (LRA/EUF/LIA/UFLRA/UFLIA/QF_BV), and
   Lean reconstruction extended (more QF_LIA shapes, disjunctive QF_LRA, QF_ABV ROW
   Carcara-checked). Remaining: NRA CAD / general NIA `unsat` certificates.
3. **Measure** the levers as they land — this is the [measurement-debt](#true-parity-the-maturity-ladder-and-the-measurement-debt-2026-06-23)
   payoff. **SAT vivification is now wired into the SAT-BV pipeline** (gated by
   `cnf_vivify`, default off) **and exposed to the harness** (`axeyum-bench --vivify`),
   so its QF_BV effect is now measurable; word-level BV abstraction is next.
   **Quantifier maturity** ([P2.6](docs/plan/track-2-theories/P2.6-quantifiers.md);
   MBQI is now MBP-driven).
4. **Deepen the seeded engines** behind a stable API — CHC/PDR ([P4.6](docs/plan/track-4-usecases-frontend/P4.6-chc-horn.md))
   and the `(get-interpolant)`/`(get-abduct)` SMT-LIB surfaces — then the breadth tail.

## True parity: the maturity ladder and the measurement debt (2026-06-23)

A sober big-picture check, because the ledger now reads as "we have almost
everything Z3/cvc5 have." That is true **at the seed level** and misleading as a
parity claim: **a sound, verify-guarded first slice of an engine is not parity
with a 15-to-20-year production engine.** Every capability climbs a ladder, and
naming the rung honestly is the difference between a real roadmap and a feature
checklist:

| Rung | Meaning | Where axeyum mostly is |
|---|---|---|
| **Seeded** | sound, verify-guarded first slice (often conjunctive / bounded / single-predicate) | **most newer engines** — CHC/PDR, abduction, interpolation, online combination |
| **Decides** | complete on the decidable fragment; honest `unknown` outside | QF_BV, QF_UF, QF_LRA; NRA CAD decision side |
| **Measured-competitive** | solved-count + PAR-2 within target of Z3/cvc5 on a *committed* corpus, same hardware/timeout | **QF_BV only** (p4dfa 113, parity, both hard-capped) |
| **Certifying** | every `unsat` carries a Lean-checkable certificate | QF_BV (DRAT), QF_LRA (Farkas), QF_UF, degree-2 SOS — **ahead of Z3** |
| **Production** | tuned, scalable, robust across the division's *full* benchmark suite | **none yet** — Z3/cvc5 are here across all divisions |

**The honest position:** axeyum has **breadth of seeds + a leading *certifying*
story + one measured division.** It is *not* at Z3/cvc5 parity, and the distance
is dominated by two things the ledger does not show — **production depth** (the
bulk of Z3's ~688k LoC) and **measurement debt** (only QF_BV is measured; every
other "parity" is a feature-ledger assertion, not a number).

**The phase pivot.** Breadth acquisition is essentially done — the ledger has a
seed for nearly everything. **The standing rule now inverts: stop adding new engine
seeds; deepen, *measure*, and certify the ones that exist.** A new seed without a
measured corpus behind it adds claim-surface, not parity.

**What true parity actually requires — and the realistic bet:**
1. **Measured per-division corpora vs Z3/cvc5 — the #1 credibility item.** Today
   [P4.5](docs/plan/track-4-usecases-frontend/P4.5-benchmarking.md) measures QF_BV
   alone. Parity is a *number per division* (QF_LRA, QF_LIA, QF_UF, QF_UFLIA,
   QF_ABV, QF_NIA, QF_NRA, QF_S), not a ledger row. **Gate every "parity" claim on a
   committed measured slice; until a division has one, its status is
   "seeded/decides," never "parity."**
2. **Do not race Z3 to production depth on every division** — that is a 15-year
   loss. **Pick the divisions where axeyum can be both measured-competitive *and*
   fully-certifying** — QF_BV, QF_LRA, QF_UF, QF_LIA, QF_ABV — and drive those to the
   top of the ladder. "Fast-enough **and** every `unsat` carries a Lean-checkable
   proof" is a position **neither Z3 nor cvc5 occupies**; that is the winnable parity.
3. **Accept sound-incompleteness on the hard frontiers** (NRA, strings, full
   quantifiers, large-scale CHC) as the honest steady state — match Z3's *practical*
   heuristics where cheap, return first-class `unknown` otherwise, and let
   **certification, not raw decide-rate, be the differentiator.**

In one line: **true parity is measured-and-certified on a chosen set of divisions —
not a feature checklist — and the next phase is depth + evidence, not more seeds.**

## How to use this plan each session

1. Read **[STATUS.md](STATUS.md)** — it names the current focus and the next
   task.
2. Open that task's phase file under `docs/plan/track-*/`. Each task lists its
   goal, the reference file paths to read, its size, and its exit criteria.
3. Do the task as a sound, tested, committed increment (the project's normal
   discipline: `just check`, model replay / independent re-check, ADR if it's a
   new public surface or decision).
4. Update STATUS.md (the phase row + changelog). Keep the capability ledger
   (`crates/axeyum-solver/src/capabilities.rs`) and its golden matrix in sync.

## Standing rules (do not violate)

- Default build is **pure Rust, no C/C++**; native/feature-gated leaves only.
- `unsafe_code` is denied workspace-wide; exceptions need an ADR.
- `unknown` is a first-class result; never a wrong `sat`/`unsat`.
- **Graceful `unknown`, never OOM/crash.** Every solving path must degrade to
  `Unknown` under a *deterministic* resource bound — no unbounded memory/time on
  adversarial input. Precedent: sat_bv's pre-lowering oversized-encoding refusal;
  NRA's `MAX_CROSS_PRODUCTS` admission bound (2026-06-19, refuses ≥3 distinct-operand
  cross-products before building lemmas — bounded *or* unbounded, since the blowup is
  inside a single LRA solve call that the wall-clock checks can't intercept). Add a
  bound before adding a feature that can blow up.
- Every `sat` replay-checks; every new `unsat` route gets an independent checker
  or an explicit, ledgered trust note.
- **Build caps:** `CARGO_BUILD_JOBS=4` / `-j4`. Default 16-way parallelism and
  high-`--jobs` benches OOM-kill this host. **Run test/build/bench under the 64 GiB
  memory cap** — `scripts/mem-run.sh <cmd>` (or `just test-guarded`) applies a
  `ulimit -v` so a runaway allocation aborts *that process* instead of OOM-killing
  the host. Override the cap with `MEM_LIMIT_GB=N`.
- **Coordination (multi-agent):** a second agent works `axeyum-rewrite` /
  `axeyum-smtlib` (word-level reduction, P1.2 — the destination-2 near-term lever).
  Treat those crates as theirs; this agent covers measurement, proof/Lean
  (Track 3), breadth/feature-parity (Track 2), and incremental SAT-core
  modernization. Do not edit `canonical.rs` etc. without coordinating.
- **Do not sweep the 41GB public corpus** to "make progress." Measure once on a
  committed slice, then stop.
- Decisions are recorded as ADRs in `docs/research/09-decisions/`.
- Commit trailer:
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`.

## Provenance

The plan was synthesized from a top-down review of the cloned reference solvers
in `references/` (Z3 ~688k LoC, cvc5 ~512k, bitwuzla, CaDiCaL, Kissat, Carcara,
lean4, nanoda_lib, lean-smt, drat-trim) by five parallel Opus sub-agents on
2026-06-15; their full reports are in
[`docs/plan/references/`](docs/plan/references/README.md). axeyum today (2026-06-22)
is **~143k LoC of Rust across 14 crates** with a broad, evidence-backed
decidable+arithmetic foundation (destination 1) — including a complete CAD
decision side for NRA, a competitive pure-Rust proof-emitting SAT core, and
self-checking evidence (DRAT + Alethe + an in-tree Lean-grade kernel + universal
model replay) that already leads Z3. This plan is the route to destinations 2
(Z3-class performance) and 3 (Lean-checkable proofs). Live per-session state is in
[STATUS.md](STATUS.md); the foundation phase history is in the research
[roadmap](docs/research/08-planning/roadmap.md).
