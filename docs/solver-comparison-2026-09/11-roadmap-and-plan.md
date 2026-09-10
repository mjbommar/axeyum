# Roadmap and plan — from the inventory and gap analysis (2026-09-09)

This distills [`docs/solver-inventory-2026-09/`](../solver-inventory-2026-09/00-README.md)
(what we have, and what is actually wired), the nine reference-solver files in
this folder, and [10-gap-analysis.md](10-gap-analysis.md) into an ordered plan.

It is written backwards from **exit criteria**. Every item names the observation
that would show it is done, and that observation is one a referee can re-run.
Items without a falsifiable exit criterion were left out on purpose.

Ordering rule: **value today ÷ cost to close**, then dependencies. That rule puts
checker fixes first (a checker that cannot fail makes the whole ledger
unfalsifiable), routing second (the engines exist), and algorithm work last.

## What the evidence says, in one paragraph

We are not behind on capability in the way the crate count suggests. We are
behind on **integration**: a warm incremental SAT engine, five inprocessing
passes, a machine-independent work meter, and both halves of stable/focused mode
switching all exist in the tree and are not reached by a default solve. On
evidence we lead the field by more than we have said — four reference solvers
produce no proofs, Z3 removed interpolation and ships a bit-vector proof checker
whose six functions all `return true` — but our own external-checker gates skip
and pass, so we cannot currently *demonstrate* that lead. The real algorithmic
gaps are specific and mostly in the SAT layer: equivalent-literal substitution,
a gate-structure interface to CNF, and propagation-based local search.

## Phase 0 — make the checkers able to fail (days)

Rationale: the repository's own rule. At N lanes the ledger is the product, and
every claim in Phases 1–3 will be *measured* through these gates. They must be
trustworthy before anything else is.

| # | Item | Do | Exit criterion (falsifiable) |
|---|---|---|---|
| 0.1 | `minus_simplify` | Add the name to `CARCARA_CHECKED_RULES` (`crates/axeyum-cnf/src/alethe.rs:868` region). Carcara aliases it at `carcara/src/checker/shared.rs:292`. | The pinned list has 180 entries and equals the set of Carcara's `get_rule` match-arm strings at clone `6624ea80c`; a test derives that set from the clone rather than a literal. |
| 0.2 | A Carcara gate that runs Carcara | `scripts/check-carcara-gate.sh` modeled on `check-lean-gate.sh`; `AXEYUM_REQUIRE_CARCARA=1` mode in `tests/carcara_crosscheck.rs`. Copy cvc5's shape (`references/cvc5/test/regress/cli/run_regression.py:312-335`): check exit status **and** `"valid" in stdout`, and pass `--allowed-rules` naming our three in-tree-only rules explicitly. | Under `AXEYUM_REQUIRE_CARCARA=1`, a proof with one rule renamed to `hole` **fails** the gate; with the binary absent the gate **fails**, not skips. Register the gate in `just check`. |
| 0.3 | drat-trim exit contract | Audit every recipe that invokes drat-trim; require the `s VERIFIED` grep that `check-claim-certificates.py:1227` already does. drat-trim has 17 `exit (0)` sites incl. MEMOUT and TIMEOUT (`drat-trim.c:905`). | A deliberately truncated proof reports failure from every recipe; `exit 0` alone never counts as a pass. |
| 0.4 | Support matrix behavioral probes | `SUPPORT_MATRIX` (19 rows) and `CAPABILITIES` (105) are hand-written literals dispatch never reads. Add a probe per row that runs a one-line query through the front door and asserts the claimed verdict class. | Flipping any row's claimed logic support makes exactly one probe fail. 12 of 19 matrix rows currently have no probe; `CAPABILITIES` has none. |
| 0.5 | Trust ledger derived, not typed | `ALL_TRUST_IDS` (15) and `is_certified` are hand-written. Derive the certified set from which `Evidence` variants carry a checked certificate. | Adding a `TrustId` without an evidence route fails a test; the ledger markdown regenerates from the derived set. |
| 0.6 | Documentation drift | Fix the ten drifted docs and two ADRs listed in the gap analysis §7, and `CLAUDE.md:319` (axeyum-fp deps) and the varisat sentence (splr ships DRAT; varisat remains the only Rust SAT solver with LRAT). Update `07-strings-and-regex.md` to include `str.update` and `seq.*`. | `docs/internals/cnf-and-sat.md` no longer says RAT is rejected; `support-matrix.md` column count matches source; ADR-0009 no longer claims a real incremental façade until 1.1 lands. |

## Phase 1 — wire what already exists (weeks)

Rationale: the top of the gap analysis. No new algorithms; each item has an
engine with tests already in tree.

| # | Item | Do | Exit criterion |
|---|---|---|---|
| 1.1a | **Warm engine in the CEGAR loops** — **DONE.** | The lazy-ROW and extensionality CEGAR loops hold one `IncrementalBvSolver` across rounds (`abv.rs` `RowEngine`, routed from `auto.rs:dispatch_pure_qf_abv`). **Corrected 2026-09-09:** there are SEVEN `SatBvBackend::new()` sites in `auto.rs`, not five (`:3993 :4735 :4853 :5563 :6672 :6689 :7250`); only `:5563` was a warmable refinement loop. `abv.rs` has none — it receives a backend from its caller. | **The original criterion was defective and is replaced.** "Assert clause count is monotone" CANNOT FAIL: a fresh engine at round *n*+1 encodes the whole larger working set, so its counts are monotone too — measured byte-identical, `[673, 1143, 2099, 2800]`, warm and rebuilt. The load-bearing assertion is `encodes_each_assertion_once` (`warm_asserted == working_final`): 18 vs 18 warm, 56 vs 18 rebuilt. Corpus verdicts identical. |
| 1.1b | **Warm `Solver` façade** — **BLOCKED, and correctly so.** | Route `Solver::check`/`solve_smtlib` through the warm engine and make `push`/`pop` real scopes. | **Prerequisite: an incremental-script corpus (new item 2.9).** 0 of 1,101 committed `.smt2` files contain `(push`, only 4 have two `check-sat`s, and `corpus_regression.rs:149` skips scoped scripts outright — so a façade leaking an assertion across a `pop` (a wrong `unsat`) would leave every committed gate green. Three further blockers: `Solver<B>` cannot ask a backend whether it is the pure-Rust BV path (needs a defaulted `warm_bv_engine_equivalent()` on `SolverBackend`); `Solver::assert` takes no arena; `smtlib.rs run_session` calls the full dispatcher per `check-sat`. ADR-0009's Status correction STAYS until this lands. |
| 1.2 | **Inprocessing on by default** — **MEASURED, DECIDED AGAINST.** | Stays `false`. Frontier at a comparable pinned frame: `bv_reduction` **35 → 26** (baseline 30) — PROGRESS off, REGRESSION on, scales within 1%, reproduced across a 33-commit gap. Corpus **137 → 130/131 agree**: 6-7 decided files become 2000 ms timeouts, none gained, wall time 17.4s → 35.0s. **0 DISAGREE both arms** — nothing became wrong; the cost is the objection. | Measurement note: `docs/research/03-measurements/inprocessing-default-flip-2026-09-09.md`. The certificate half was already met (117/117 inprocessed `unsat` check against the ORIGINAL formula), so evidence is not the blocker. **What would change the answer:** route `TickValve` (item 1.5) onto the shipping path with a budget-derived grant, then re-measure — today the valve is confirmed off that path, so it does not yet reduce the cost. |
| 1.3 | **One inprocessing pipeline** — **DECIDED, see ADR-1810.** | **Corrected 2026-09-09:** the shipping path is the PROOF-CARRYING one. `ReductionLink` (`axeyum-cnf/src/reduction_link.rs:156`, same crate as `inprocess.rs`) has, since ADR-1780 on 2026-09-08, made `sat_bv_backend.rs:2812` check its `unsat` against the ORIGINAL formula; `inprocess.rs` cannot express the `compact()` renumbering. The shipping SEQUENCING survives and moves into `axeyum-cnf`. | The old criterion ("the other's file is gone") is the wrong shape — no file disappears. Replacement from ADR-1810: `sat_bv_backend.rs` contains zero calls to the seven pass-sequencing names, the 117 `unsat` files on the 200-file QF_BV parity list still report `ProofCoverage::Original`, and all 200 verdicts are unchanged. |
| 1.4 | **One preprocessing pipeline** — **DECIDED, see ADR-1811.** | `preprocess.rs` (8 rounds; `real_div_zeros`, no function carry) vs `auto::preprocess_reduce` (1 round; carries BOTH). **Corrected 2026-09-09:** the original row said "neither is a superset" — false, the front door is the superset (`auto.rs:2335`, `:2344`). ADR-1811 makes `preprocess.rs` the one home, parameterized over the solve call, and lands at cap 1. | A fixture with a `/0` witness AND a function interpretation replays through the merged path. Three negative controls: delete each witness loop in turn, require exactly one different test to die each time. Raising the cap above 1 is a SEPARATE gated step — `reduction_shrinks_encoding`'s rows (`auto.rs:2209-2232`) were measured at one round. |
| 1.5 | **The tick valve** — **DONE (valve), feed OUTSTANDING.** | `TickValve` in `axeyum-cnf` admits each inprocessing pass on a per-mille slice of accrued search ticks, refuses below a formula-scaled threshold, and backs off exponentially — CaDiCaL's `SET_EFFORT_LIMIT` + `Delay`. | **The original criterion was partly cosmetic and is replaced.** I asked that `span_log.rs:75` "no longer say 'No ticks'" — but that sentence is TRUE: `SearchCounters` are filled only by the `count_search` variants and nothing in `axeyum-solver` calls them, so rewording it would be a doc change dressed as an implementation. What was met: an 8-round schedule is byte-identical across runs with a 7.1× wall-time spread, and contains granted, refused and backed-off decisions. What is OUTSTANDING: **the feed** — a solver-side lane must route the SAT solve through `solve_with_drat_proof_counted` and wrap the existing observer. Until then no span carries a tick and the valve is off the shipping path. |
| 1.6 | **Stable/focused switching** | Expose the `proof_sat.rs` EMA restart and `phase_policy.rs` target/best-phase machinery outside `#[cfg(test)]`; add the mode switch on a tick budget with quadratic interval growth, starting focused (`restart.cpp:19-84`). | `use_ema_restart` has a production setter; a curated corpus shows the mode schedule in the span log; ratchets non-regressing. |
| 1.7 | **Portfolio default** | `portfolio::FusedGroup` needs `AXEYUM_PORTFOLIO_WORKERS ≥ 2`; default is 1. Commit `613bc3f35` measured two workers faster on decided files. Make it default where the measurement holds. | Default run on that slice reproduces the +6/−0 result; verdicts deterministic under the race (the divergence at `auto.rs:2890-2894` is either removed or shown verdict-neutral). |
| 1.8 | **Route trace for quantified inputs** | The quantified ladder (`auto.rs:492-1108`) records nothing; eleven rungs report only to stderr under `AXEYUM_QTRACE`. Add `RouteTrace` recording. | A quantified corpus file's trace names the rung that decided it, not the QF sub-route it fell into. |

## Phase 2 — cheap, well-bounded engineering (weeks)

| # | Item | Do | Exit criterion |
|---|---|---|---|
| 2.1 | **SCC / equivalent-literal substitution** | The cheapest CaDiCaL pass (`decompose.cpp`) and the one every other pass feeds. Tarjan over the binary implication graph, substitute representatives, emit RUP for each replaced clause. | A curated instance with *k* equivalence classes shrinks by the expected variable count; DRAT accepted; the pass runs under the 1.5 valve. |
| 2.2 | **Keep gate structure across the CNF boundary** | CaDiCaL spends 7,925 lines (`congruence.cpp`) recovering AND/XOR/ITE that Tseitin destroyed; we still have it in the AIG and discard it at `tseitin_encode`. Carry a gate table beside the CNF so `xor_extract.rs` reads it instead of re-mining clauses. **Size this as an interface, not an algorithm.** | `xor_extract` finds the same XOR set from the table as from clause mining on the XOR curated corpus, in a fraction of the time; the mining path becomes a fallback for foreign CNF. |
| 2.3 | **The `i128` boundary** — **MEASURED, deliberately NOT opened.** | Opening `narrow()` turns a sound `unknown` into a PANIC. Measured: a 131-var doubling chain has an exact vertex at 2^130 that the boundary discards; the evaluator then cannot replay it (`ArithmeticOverflow { op: "real_mul" }`) because `Rational`'s `checked_*` family computes exactly then DEMOTES; and forcing `narrow` open leaves the corpus tally byte-identical, so nothing committed exercises this and no gate would catch the panic. | **My prerequisite was wrong.** This row said "the evaluator already handles `Value::WideInt`" — true but insufficient: `Value::Real` carries a `Rational`, not a `WideInt`, and has NO wide path. Real order: (1) a wide-real path in `eval.rs`; (2) the model-path panic sites (`auto.rs:2537`, `:2570`, `smtlib.rs:3904` — `get-model` cannot print a wide model today, `eval.rs:772`, `:776`); (3) the certificate residue (`alethe_lra.rs:944`, `reconstruct/arithmetic.rs:4778`); (4) THEN delete two lines in `narrow`. |
| 2.3b | **The wide-witness replay check is VACUOUS** — **NEW, found by 2.3.** | A correct 2^130 and a deliberately corrupt 2^131 produce the identical `ArithmeticOverflow`. Sound (declines to `unknown`, never a wrong `sat`) but zero discrimination. | Pinned as `the_replay_check_cannot_distinguish_a_correct_wide_witness_from_a_corrupt_one`. No claim that "the replay catches a corrupted wide witness" may be inherited from today's code. Closing 2.3 must make this test's premise false and flip its assertion. |
| 2.4 | **ABC as a bit-blasting cross-check** | Our AIGER export is ASCII (`aig/lib.rs:636`); ABC reads binary only (`giaAiger.c:1980`). One hop through `aigtoaig`. Add an optional gate: export, convert, `cec` against a second lowering. | `just abc-crosscheck` fails on a deliberately mis-lowered operator (one negative control), passes on the curated set. Optional dependency; skip-and-**fail** under `AXEYUM_REQUIRE_ABC=1`. |
| 2.5 | **Vendor the string corpus** | cvc5's strings/seq regression is 583 files (150 `QF_SLIA`, 74 `QF_S`); we vendored 20, zero `QF_SLIA`. Vendor the rest with `:status`; add the missing operators to the `:status` sweep. | `corpus/regression/cvc5/qf_slia/` exists; the sweep's file count rises accordingly; every new file's verdict is either matched or explicitly `unknown` — never wrong. |
| 2.6 | **Differential fuzz where none exists** | Difference logic runs *first* in the ladder and has no oracle fuzz; nor do pure `QF_LIA`, `int_real_relax`, `lia_gcd`, `bmc`/`imc`/`pdr`. | A `--features z3` suite per route; each generates the route's degenerate case (Hard Rule) and reports a nonzero test count. |
| 2.7 | **Retire or wire the eleven test-only modules** | `abduct`, `enums`, `faithfulness`, `horn`, `hypothesis_min`, `imc_lia`, `lex_reconstruct`, `pb`, `pdr_lia`, `records`, `toy_bv_vm`. Per module: dispatch it, move it to an example, or delete it. ADR for the deletions. | Module-level measurement (`11-wiring-and-integration.md` method) reports 0 test-only modules, or each survivor has a recorded reason. |
| 2.9 | **An incremental-script corpus** — **NEW, prerequisite for 1.1b.** | Today 0 of 1,101 committed `.smt2` files use `(push`, so every push/pop path in this solver is ungated. Vendor or generate scoped scripts with `:status`, and stop `corpus_regression.rs:149` from skipping them silently. | A script that asserts under `push`, pops, and re-checks is in the sweep; deliberately leaking that assertion across the `pop` makes it fail. Until this exists, no warm-façade work can be gated. |
| 2.10 | **Int-linear replays against the eliminated form** — **NEW, from SOUND-1's sibling hunt. Highest-value follow-up.** | `auto.rs:2836`, `:2894`, `:3088-3093` replay the model against `lin`, the `!divmod_*`-eliminated form, NOT the original assertions, and return it for the original query. `Model` has no `int_div_zero` component, so a chosen `(div x 0)` value structurally cannot be carried, while `eval.rs:830-846` pins `div a 0 = 0`. This is the SOUND-1 shape one theory over. | SOUND-1 found no exploit — every shape it built declined soundly upstream — so this is UNEXPLOITED, not a known defect. Exit: replay against the ORIGINAL assertions, or prove no reachable query can differ. |
| 2.11 | **Eleven sites emit a narrower `Model` than they replayed** — **NEW, from SOUND-1.** | `aufbv.rs:126`, `combined.rs:237`, `abv.rs:263`/`:11091`, `lia.rs:145`, `ufbv_online.rs:3168`, `datatype_native.rs:665`, `nia_linearize.rs:1837`, `lazy_bv.rs:323`, `pbls.rs:1151`, `incremental.rs:7616`. Most drop `real_div_zero` in fragments where a real `/0` should not arise — structural, not currently exploitable. | Adopt SOUND-1's guard 2 (re-replay against `out.to_assignment()`) at all eleven. NOTE: `incremental.rs:7616` and `lazy_bv.rs:323` also drop `uninterpreted_cardinalities` and `quantified`, which are INVISIBLE to `to_assignment` replay — only `check_model` sees them — so guard 2 alone will not cover those two. |
| 2.8 | **Lean-kernel-checked interpolants** — **DONE for 6 of 7.** | `dispatch_interpolant` routes through a new `dispatch_interpolant_certified`; six `certify_*` helpers attach the certificate AFTER the plain rung produced the interpolant, so the term never changes and a decline leaves `certificate: None`. The seventh is deliberately out: `propositional_interpolant_certified`'s DRAT lives in the CNF variable space and does not cover the lift to terms. | Six `*_certified` names have a `src/` caller (0 before). Unwiring any rung flips exactly one row of the pinned list in `tests/dispatch_interpolant_certified.rs`. Confirmed: all eight interpolators DO enforce Craig symbol containment — with a control showing conditions 1+2 do not imply it. |
| 2.8b | **Two certified rungs are unreachable through the ladder** — **NEW, found by 2.8.** | `certify_qf_bv` is SHADOWED: the ground-EUF rung sits above QF_BV and decides the canonical `x=y` / `x≠y` fixture, so the BV certificate never ships for that shape — while `capabilities.rs:236` advertises it without the caveat. `certify_uflia` is unreached for the same class of reason. | Either reorder the ladder so a BV-sorted equality partition reaches the BV rung, or state the caveat in the capability text. The measured per-rung list is pinned as a test, so any change fails loudly. |

## Phase 3 — the real algorithmic gaps (months, prioritize by corpus evidence)

Each of these should be gated by a measurement showing the gap costs us on a
public corpus *before* the work starts. Several may not survive that gate.

| # | Item | Evidence | Prerequisite measurement |
|---|---|---|---|
| 3.1 | **Propagation-based local search with invertibility conditions** | Bitwuzla `src/lib/ls/`, 10,227 lines: four functions × 17 operator classes, `preprop` portfolio. Ours is WalkSAT scoring (`pbls.rs`, 1,456 lines). | Count QF_BV *sat* instances where `pbls` fails and bit-blasting is slow; if small, defer. |
| 3.2 | **Remaining inprocessing passes** | Failed-literal probing, hyper-binary resolution, blocked/covered clause elimination, BVA, SAT sweeping. 19 missing; take them in CaDiCaL's schedule order after 2.1. | Per-pass ratchet delta on the QF_BV parity slice; keep only passes that move it. |
| 3.3 | **Word-level rewrite depth with levels** | 59 rules, no levels, vs Bitwuzla 296 (levels 0–2 + arithmetic) and Boolector 127 (0–3). | Measure AIG size before/after on the parity slice per candidate rule; land rules by measured reduction. |
| 3.4 | **LIA branching as SAT lemmas** | All three arithmetic references branch by lemma and have no node cap; we cap at 50,000 and return `unknown`. Two use HNF cuts-from-proofs. | Count `unknown` verdicts on `QF_LIA` public corpora attributable to the cap. |
| 3.5 | **Instantiation strategies** | cvc5: conflict-based (default on), CEGQI per theory, enumerative, pool, SyGuS, sub-conflict. Ours: E-matching + MBQI + a certificate family. | The UF corpus's declined files (dated 2026-09-09 comment in `auto.rs`) — classify which strategy each needs. |
| 3.6 | **Strings inference depth** | 87 cvc5 inference ids vs our 4; loop detection; four disequality procedures. | After 2.5, count `unknown` on the vendored `QF_SLIA` set by missing inference kind. |
| 3.7 | **Interpolation strength and shape** | No strength parameter, no tree/sequence interpolants, decline on AB-mixed literals (`euf_interpolant.rs:503`). OpenSMT has six systems; SMTInterpol checks every leaf. | Only when a consumer (IMC/PDR) needs it; those routes are themselves unwired (2.7). |
| 3.8 | **Store-pattern recognition** | Boolector recognizes `memset`/`memcpy` chains into lambdas with range conditions; we expand store chains (STP measured 48× slower than refinement). | Count store-chain depth on `QF_ABV` public corpora. |

## Phase 4 — decisions to record, not code to write

| # | Decision | Inputs |
|---|---|---|
| 4.1 | **The Z3 demotion path (ADR-0002).** Our three differential suites use exactly `Solver::new`, `set_params("timeout")`, `assert`, `check` — no tactics, cores, proofs, assumptions or push/pop anywhere in the workspace. The oracle we depend on is `smt_context` + `theory_lra` + exact simplex. | A replacement oracle needs only that surface. Candidates: cvc5, Yices2 (no proofs, but fast and exact). Decide and record. |
| 4.2 | **Eager vs lazy arrays.** Keep ADR-0010 (it buys a certificate nobody else produces) but adopt STP's staged rule (eager only when reads < 10 and expansion < 200) to remove the `MAX_ARRAY_EQ_INDEX_BITS = 8` refusal. | 3.8's measurement. |
| 4.3 | **Proof format target.** cvc5's default is CPC/Eunoia, not Alethe; its Alethe printer translates 97 of 172 rules and holes the entire strings family. Carcara remains the checker for what we emit. | Decide whether to stay Alethe-only or add an Ethos route; do not do both without a consumer. |
| 4.4 | **FP.** We eliminate at parse (ADR-0028, replay checks the same circuit); Bitwuzla/STP word-blast lazily via SymFPU. This is a fork, not a gap. | Revisit only if an FP corpus shows parse-time elimination losing on size. |
| 4.5 | **Stop claiming exact arithmetic as a differentiator.** Z3's `lp::mpq` is bignum rational + δ, same as ours. | Remove from any comparison prose. |

## What not to do

- **Do not size 2.2 as CaDiCaL's 7,925 lines.** They recover structure we never lost.
- **Do not build an FP theory solver because Bitwuzla has one** (4.4).
- **Do not flip `cnf_inprocessing` before 1.2's measurement.** The ratchets exist for this.
- **Do not add a reference solver as a dependency** for anything but oracle, differential, or cross-check duty (ADR-0002, ADR-1703). ABC in 2.4 is a cross-check.
- **Do not search for a thing by the name you have in mind.** Ten coordinator greps failed this way in the session that produced these documents (`exit(0)` vs `exit (0)`, a module name vs its exported function, a nested `carcara/carcara/`). Search for the string an author would have written, and run a positive control.

## Metrics to carry

Each phase reports against the existing instruments, not new ones:

| Metric | Instrument | Phase |
|---|---|---|
| Gates that can fail | The delete-one-guard, exactly-one-test-dies rule, per checker | 0 |
| Modules reachable from the default solve path | `11-wiring-and-integration.md` method, re-run | 1, 2.7 |
| Capability frontier | `progress_frontier` at a stated reference frame | 1.2, 1.6, 3.2 |
| Z3 parity | `bench-public-qfbv-sat-bv-compare` | 1.1, 3.1, 3.3 |
| Unsat routes with no evidence | count of `Evidence::Unsat(None)` construction sites (8 today) | ongoing |
| Trusted base | kernel `axiom_footprint`, never source text | unchanged |

## Sequencing

```
Phase 0  ──►  Phase 1.1–1.4  ──►  1.5–1.8  ──►  2.1–2.3  ──►  measure  ──►  Phase 3 (gated)
(days)        (routing)           (valve,       (SAT layer)                  (only what the
                                   modes)                                     measurement justifies)
Phase 4 decisions can be taken at any point; 4.1 and 4.5 now.
```

Phase 0 and Phase 1 fit in a small number of lanes with clear file ownership and
no shared allocation points beyond one ADR number each. Phase 3 should not
start until Phase 2's measurements say which items are worth it — several of
them may turn out to cost nothing on the corpora we actually run.
