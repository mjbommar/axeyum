# Axeyum plan, status, and next actions

> **Generated; do not edit by hand.** Sources: project-wide sections in
> [`docs/plan/global/`](docs/plan/global/README.md), one file per lane in
> [`docs/plan/status/`](docs/plan/status/README.md). Edit **your lane's file**
> and run `python3 scripts/gen-plan.py`; `--check` is a gate. This file was
> touched 67 times in 24 hours by concurrent lanes on 2026-08-13/14 and one
> lane's edit was swept into another's commit — that is what the split fixes.

**Canonical project tracker.** This is the repository's single mutable source
for current project status, ordered work, blockers, and resume guidance. Read it
first and update it before ending a project-level work session.

- Last consolidated: **2026-08-13**
- Current `main` contains linear A5 through exact commit
  `4b6b765556c4ff1fb4dc47ffd75568a3ed1f9246` by conflict-free fast-forward
- Active A5 large-equality DL repair: code at exact pushed
  `46edad8bac7e193303871d601914fef2115bf721`; its documentation descendant
  `d1b570f91c27f83ef55127ea3d1c8baf700f05a5` passed the full release gate
- Latest full-gate attempt: exact pushed checkpoint `d1b570f91c27f83ef55127ea3d1c8baf700f05a5`
  passed `just check` with external frontier artifacts and exit 0
- Latest comprehensive green exact-commit gate:
  `d1b570f91c27f83ef55127ea3d1c8baf700f05a5` (`just check` exit 0)
- Latest integrated A3 code increments: bounded SMT-LIB `distinct` expansion at
  `63c82a6ef`, typed arithmetic-model reconstruction at `4ff9a82c6`, and
  deterministic string/integer coupling at `db7b426e8`
- Status vocabulary: `TODO` · `WIP` · `BLOCKED` · `DONE`

`STATUS.md` is now a compatibility pointer. There is intentionally no root
`TODO.md`. Detailed phase plans, ADRs, result notes, generated matrices, and
benchmark ledgers remain under [`docs/plan/`](docs/plan/README.md),
[`docs/research/`](docs/research/README.md), and
[`bench-results/`](bench-results/README.md). They provide evidence and task
detail; they do not override the order or current state in this file.

Pre-consolidation journals are immutable in Git at revision `803c08439`.

## Status

**A5 repair history.** Fail-closed LRA/IDL restarts exposed wide-core and
first-solve allocation growth, mixed-numeric parsing, native recursion,
unhonored construction deadlines, and declaration-scale quadratic work. Their
pushed bounded/iterative repairs and every non-credited partial stream are
retained in the
[failure/repair record](docs/plan/qf-linear-a5-wide-core-memory-repair-2026-08-08.md);
the current release returns typed `unknown` on each former abort trigger.

Axeyum is a working research-grade automated-reasoning stack with a pure-Rust
default path, replay-checked SAT models, multiple independently checked UNSAT
evidence routes, broad but uneven theory support, an independent Lean-core
checker/importer, and several consumers. It is not yet a drop-in Z3 replacement
or a replacement for the Lean system.

The [Lean requirements](docs/plan/lean-kernel-requirements-2026-08-13.md) are
**WIP**. Nat is zero-axiom; Int reconstruction remains assumption-bearing.

Exact pushed repairs for the A5 (linear-arithmetic), A3 (string/integer) and
A2 (stale-branch) streams — commit-by-commit, with the non-credited partial
streams retained — are in the
[A5/A3/A2 repair journal](docs/plan/a5-a3-repair-journal-2026-08.md). The
current release returns typed `unknown` on each former abort trigger; A3 yields
to A4.

### A1 arithmetic resource closure

A1 is **DONE**. Resource increment `96ff85930` (merge `14f80a2bf`) resolves the
two measured arithmetic resource defects:

1. ADR-0377 makes arithmetic timeout query-global across sequential exact-real,
   NRA, real-relaxation, NIA-linearization, bounded-blast, and width-ladder
   routes. The same absolute deadline is polled inside solver-local CAD
   polynomial, projection, determinant, exact-division, and rational-cell loops.
   The public QF_NIA `ext-rew-aggr-test` now returns `Unknown(Timeout)` in 0.30 s
   for a 250 ms optimized request instead of 1.10 s; a committed debug regression
   finishes in 0.28 s and requires less than 1 s.
2. Online LRA normalization now has deterministic node, coefficient-work, and
   retained-cache ceilings. Production entry points distinguish deadline expiry
   from resource exhaustion and return `Unknown(Timeout)` or
   `Unknown(ResourceLimit)` rather than constructing a partial theory. The
   existing 1,024-atom front-door cap remains; current `sc-39.base.cvc.smt2`
   declines in 0.10 s at roughly 13 MiB instead of reproducing the historical
   8 GiB abort seen when that cap was experimentally raised.

Focused resource gates are green: deadline 6/6, online-LRA 7/7, CAD 37/37, the
normalization exhausted/near-miss unit, full all-feature solver Clippy, format,
and documentation links. The terminal aggregate solver gate
`CARGO_BUILD_JOBS=2 cargo test -p axeyum-solver --all-features --quiet --
--test-threads=2` passed 1,073 library tests and every integration/doctest bin,
including the 397.85-second UFLIA and 286.00-second word-equation differential
tests. `just parity-docs` is independently green at 35 rows, 24 logics, 992
files, 762 decided, 674 oracle-compared, and zero disagreements; its unrelated,
load-sensitive frontier refresh was discarded.

All six required retained lists were rerun fresh from row 1. Results are QF_NIA
34/200 versus 89, QF_LIA 117/200 versus 140, QF_LRA 86/200 versus 146, QF_RDL
105/200 versus 155, QF_IDL 68/200 versus 124, and QF_UFLIA 94/200 versus 180;
all have zero disagreements. The sole lower whole-sweep decision, one QF_LIA
`ex3000...` UNSAT, reproduced 3/3 in isolation at about 8.1 seconds under the
24-second protocol and is classified as load-sensitive sweep timing, not a
semantic loss. The ledger honestly retains 117.

The QF_IDL run exposed and then closed a real fallback-reservation regression.
Commit `4477f2bb9` bounds every probe-front-end phase and uses a measured 12/12
probe/fallback split only for 128–1,024-atom numeric equality gates; a global
12/12 split was rejected after losing five controls. A 171-case QF_IDL/QF_RDL
A/B was monotone. The final full sweep recovers `lpsat-goal-18.smt2` as UNSAT,
retains the BubbleSort gain, adds one SAT graph case, and has no Axeyum loss.

Commit `5ce07c55e` (merge `8ea6a7cad`) also makes parity resume identity
fail-closed: exact committed-list paths are canonical; ambiguous legacy
basenames, duplicate rows, and population drift are rejected. The six accepted
A1 runs were fresh and non-resumed. Full evidence, sidecar hashes, rejected IDL
policies, and gate separation are retained in
[`docs/plan/arithmetic-a1-retained-result-2026-08-06.md`](docs/plan/arithmetic-a1-retained-result-2026-08-06.md).

Disk cleanup preserved every branch and salvaged dirty inactive-worktree deltas
to labelled Git stashes before retiring their checkouts. Reproducible Cargo
artifacts and empty failed-run directories were removed only after ancestry,
cleanliness, and open-file checks. Only clean `main` remains registered; retained
evidence and unrelated temporary projects were untouched.

### Current evidence snapshot

- The committed regression scoreboard contains **35 baselines across 24 logic
  fragments**: **762/992** files decided, **674** oracle-compared, and **zero
  recorded disagreements**. This is bounded regression evidence, not universal
  soundness or representative SMT-LIB coverage. See
  [`bench-results/SCOREBOARD.md`](bench-results/SCOREBOARD.md).
- The refreshed 4-second frontier artifacts report BV reduction **38**
  (baseline 30), LIA cuts **35** (baseline 26), NIA UNSAT **40** (baseline 40),
  NRA degree **40** (baseline 40), and string bound **40** (baseline 8). These
  are load-sensitive local frontier measurements; they do not raise baselines.
- The append-only head-to-head ledger currently covers **eleven divisions**.
  Its weak measured edges are QF_NIA **34/89 = 38.2%**, QF_UFLIA
  **94/180 = 52.2%**, QF_IDL **68/124 = 54.8%**, QF_LRA
  **86/146 = 58.9%**, and QF_RDL **105/155 = 67.7%**. Every credited entry has
  zero disagreements. Read the latest entry per division in
  [`bench-results/PARITY.md`](bench-results/PARITY.md); never copy an older
  entry merely because it has a higher score.
- QF_BV evidence mode decides 130 UNSAT rows: **92/130 certified**,
  **78/130 rechecked from serialized text alone**, and **92/92 certified rows
  independently checked against a fresh re-parse and term arena**. Neither
  check had a failure. The remaining 38 are bare UNSAT decisions because the
  evidence-producing route could not decide them within 60 seconds.
- The broader evidence audit still records **58 uncertified occurrences**,
  **eight independently checked results without Lean reconstruction**, and
  **two QF_NIA `IntPow2` proof-production errors**. Do not combine these
  denominators with the newer QF_BV-only experiment.
- The current official-source proof-family population has a retained local
  Lean 4.30 result of **70/70 accepted**. A corrected remote attestation and the
  exhaustive tier remain open. Lean language, ecosystem, and complete native
  compatibility remain far beyond the current K0/K1 slices.
- The previous 64,345-file full-library candidate is not a result: it produced
  zero admissible raw shards. Resumable/process-free readiness work exists, but
  a representative current-main run has not been admitted or published.

### Recent landed changes that set the next direction

| Date | Commit | Result |
|---|---|---|
| 2026-08-18 | `00f998ccb` | ℤ categoricity: the existence half of the universal property (`iter` + three preservation equations, making `Int` the initial ℤ-structure) and `categorical` — every generated aperiodic ℤ-structure is in structure-preserving bijection with `Int`, universe-polymorphic. `iso` is the constructed two-sided-inverse form, honest about hypothesising the back-map. 32 theorems, all footprints empty; 22 injected weakenings each refused at their own declaration, now bracketed by `reached_declaration` on the near side too. |
| 2026-08-18 | `a2a36590b` | `F:int-categoricity` recorded, and `F:int-characterization`'s "not proved that they determine it" caveat removed because it stopped being true. Every checker anchored on the declaration name AND the empty-footprint column, each run with its subject mangled: 0 on the finding, 1 on the mangle. |
| 2026-08-18 | `pending` | binding coverage: +20 bound (105 → 125), 124 modules proved content-free, and the converse direction measured at 286/531 |
| 2026-08-18 | `dc72f0bed` | ℝ gets **Bishop's order**: `CReal.le` plus `le_refl`, `le_trans`, `add_le_add` — three of the 22 **verbatim**, none of them mentioning `Eq`. `le_trans` is `Equiv.trans` with the lower half deleted, sharing the extracted `telescope_four`/`six_term_bound` with it. `not_le_one_zero` is the order's discrimination witness (refuted at index 3 by pure reduction) and `le_of_equiv`/`equiv_of_le_le` pin `le` to the setoid. **7 of 22**, 31 declarations, trusted surface still 0. |
| 2026-08-18 | `9e32ab17d` | The **additive group closes**: `add_zero` and `add_assoc` in `Equiv` form — the first two laws that are not pointwise. Neither needs `natDivSucc` antitone in its index, which the previous costing had put in front of them; both reduce to `1/(2n+2) + 1/(n+1) ≤ 2/(n+1)`, i.e. `3 ≤ 4` at the common denominator. **4 of 22**. |
| 2026-08-18 | `fd2759c8b` | ℝ additive structure: `zero`/`one`/`neg`/`add` with Bishop's index shift `(x+y)_n := x_{2n+1} + y_{2n+1}`, the `neg`/`add` congruences, and **2 of the 22** ordered-ring laws in `Equiv` form (`add_comm`, `add_neg`, both pointwise via `Equiv.of_pointwise`). `add_assoc` and `add_zero` are not pointwise; `add_zero` also needs `Rat.natDivSucc` antitone in its index. |
| 2026-08-18 | `ca0e9ea75` | ℝ constructed: `CReal` as a Bishop setoid over ℚ with `Equiv` refl/symm/**trans**, `zero`/`one`/`neg`/`add` and two congruences — 22 declarations, trusted surface **0**, with inhabitation and discrimination witnesses the example's exit status depends on. 2 of the 22 ordered-ring laws hold in `Equiv` form. |
| 2026-08-18 | `f527e7ddb` | The **Archimedean property of ℚ** proved axiom-free (`Rat.le_of_le_add_natDivSucc`), plus a 16-lemma ordered-group toolkit derived from the 22 ring laws alone and the `Rat.add` mirror of `iprod_perm`. Decidability replaces contradiction; the witness index is computed, not searched. |
| 2026-08-17 | `67960fc1c` | D3 grouping refuted at the point of execution: arithmetic-as-a-directory grows the largest dependency cycle 58,215 → 103,514 lines. `analyze_solver_group_collapse.py` + mutation controls; no files moved. |
| 2026-08-17 | `d23a9d883` | `Nat.exists_prime_dvd` — every `m ≥ 2` has a prime divisor — admitted axiom-free in a new `nat_prelude::primes` module, with `Nat.le_of_dvd`, `Nat.two_le_succ_or_eq_one` and `Nat.least_divisor_search` beneath it (137 Nat theorems, up from 133). Recorded as `F:nat-exists-prime-dvd`, whose `kernel-term` checker pins the entire rendered type rather than the name — verified against the `1 ≤ p` weakening, which the kernel accepts and a name-only grep would not catch. |
| 2026-08-17 | `8f8c12dce` | ℕ-induction wired into `solve` as the last rung of the quantified ladder (`unknown` → `unsat` only, on `original_assertions` because normalization + skolemization have erased the negated universal by that point). New `tests/nat_induction_adversarial.rs`: 22 adversarial shapes, hand-derived truths, measured on the route and through the front door, 0 violations. Fixed an index-out-of-bounds panic in `is_nonneg_guard` on one-argument guards. `nat_induction_corpus` re-measured (3 contradictions → 0) and its gate widened to the front-door column. Both suites mutation-verified. Blast radius: `--lib` 1159 unchanged, `corpus_regression` 152/0 DISAGREE unchanged, whole crate 285 suites / 3861 tests green, clippy and fmt clean. |
| 2026-08-17 | `pending` | `string` prelude reaches **axiom=0**: `append` becomes a checked `Str.rec` recursion with four proved monoid laws (ADR-0469); ledger `total` 31 → 30, row filed as retired; real-Lean cross-check pins that `#print axioms` names no `axeyum.string.*` row. |
| 2026-08-17 | `fae708aa5` | Characterization theorems: our ℕ proved categorical (any Peano structure is uniquely isomorphic to it), our ℤ proved no-junk + generated by 1 + discrete everywhere + unique maps out. 18 theorems, all footprints empty; 9 injected weakenings each refused at their own declaration. |
| 2026-08-17 | `f532e04d3` | Restored `rat_prelude` after `fae708aa5` reverted `cf205e9a8`: a per-lane index refreshed in one shell invocation and committed in the next, with HEAD moving in between. The refresh must be in the SAME invocation as the commit, and `git show --stat`'s file COUNT is the tell — the diff you expected to see is not. |
| 2026-08-17 | `b15debdfa` | One Lean resolution policy (the `lean-toolchain` pin) shared by `check-lean-gate.sh` and `lean_probe.rs`; every suite names the binary and version it used and the gate cross-checks them; `replay-lean4export.lean` elaborates under 4.30 and 4.34; exercised negative controls in `scripts/tests/test-lean-toolchain-policy.sh` (ADR-0470) |
| 2026-08-17 | `pending` | transcription: bind every rendered Lean hypothesis back to the query text — 105 instances, 248 hypotheses, 869 corruptions caught per run |
| 2026-08-17 | `7337f708` `caaf2906` | A SKOLEMISED refutation certifies: the elimination is recorded POSITIONALLY (binder counts, anchor by index, a binding as "the k-th witness of assertion i"), so the checker re-runs the eliminator in its own arena and no producer-side id is trusted. `F:barber-no-such-barber` closes on `smt-clausal` with a NON-EMPTY axiom footprint naming skolemisation and universal instantiation. The negative control failed on purpose and moved to `F:no-integer-square-is-minus-one`; the gate now sweeps 18/18. |
| 2026-08-17 | `ae13cd6e` | A kernel fact's `depends_on` is DERIVED from the proof term, not transcribed: `Kernel::theorem_dependencies` keeps the half of the constant closure `axiom_footprint` discards. 18 edges were missing — two of them on facts proved the same day, by hand. Isolation 65 → 62. Restraints pinned by tests; the vacuity floor had no test until mutation-checking found it killed zero. |
| 2026-08-17 | `07ffe852` `9853fb6c` `28755674` | The e-matching route certifies, on the third design. It first shipped `certified=1` on evidence whose independent re-check said FAIL (one instance passed by `TermId` coincidence, two did not); reverted, then made portable — instances rebuilt in the checker's arena, ground set rebuilt rather than stored. `tests/certified_implies_revalidatable.rs` is the guard that caught it and now licenses it. |
| 2026-08-17 | `c2365718` `4cd5d6f0` `c5f4c04b` `078b2776` | The Lean gate stops overstating: 41 of 74 crosscheck families hand Lean an `axiom P` shim, so the headline is split, the reasoning half floored, and every fragment's class pinned by name. `qf_bv` was a WIDTH, not a defect — enumeration beats bit-blasting below ~16 bits — so `qf_bv_wide` now exercises the real reconstruction (33 theory / 41 attestation). |
| 2026-08-17 | `3cc574c7` `502c0503` | Both counted proof-production errors closed (`int_blast`'s deliberate `int.pow2` decline was mapped to a backend error, losing a verdict `check_auto` decides in 0.13ms), and settled SMT-route facts gated on certification rather than verdict — 17 of 17, enforced. |
| 2026-08-17 | `ea9500bc` `e97db72b` `2c535667` `f40f7dc4` | Gate repairs: `check-parity-docs.py` crashed before running a single check (hiding 14 failures); CI's crosscheck grep still pinned 73 families; and `PLAN.md`'s sources were 24 KB over a 52 KB budget, journal moved to result notes. |
| 2026-08-17 | `07de6526` | Mathematics strand's primary metric derived and gated: 36 of 101 capabilities name an external artifact checker, across 11 of 23 logics, against a documented 4 of 26. Control: disabling the external tier drops it to 0 and the floor fires. |
| 2026-08-17 | `a8a862133` | Denominator counts LOGICS not `area` strings: a compound like `QF_UFLIA/UFLRA` spans two, and its abbreviated second element named a phantom `UFLRA`. The 12 logics with no external check are now an explicit queue. |
| 2026-08-17 | `549a1ecc7` | Item B answered by derivation: the gap is banded by distance to an external checker, and the ranking found QF_RDL already renders a Lean theory module official Lean accepts — a "gap" logic blocked only on gate wiring. Controls: 6 new tests, incl. one proving a solved logic never appears in the queue. |
| 2026-08-17 | `69026936d` | A control no gate RUNS cannot fail, so it is not a control: 63 of 137 control modules were executed by nothing, and running the 51 needing no cargo found 264 tests — 258 passing and gated for free, 6 erroring, four of them import failures against renamed scripts. Ratcheted; the gate caught its own controls being unwired. |
| 2026-08-17 | `19f739a57` | 44 orphaned controls adopted (257 tests, ~31s) and the baseline ratcheted 63 → 17. Fixing the scanner to join line continuations found 2 more already-wired — it had counted 3 of 44 and would have called them orphans. Corrected an overstatement: 5 of the 7 unadopted need `pytest` (absent here), 1 has an order dependency, and exactly 1 has genuinely rotted (`producer drift: Cargo.lock`). |
| 2026-08-17 | `60a7b4712` | QF_RDL closed end to end: `lean_crosscheck` now hands official Lean a QF_RDL theory module every run (33 → 34 theory families), and only then did the table gain a QF_RDL-specific row — 11 → 12 of 23 logics externally checked. Controls: two mutations of the module are rejected by Lean; the attestation class is proven still reachable. |
| 2026-08-17 | `bfc16da51` | The reachability gate contradicted itself and was wrong in my favour: `check-adopted-controls.sh` documents its exclusions as "pytest-style", so those COMMENT lines contained a runner word and vouched for the two modules the comment says are NOT run. Comments are mentions now; baseline corrected 17 → 19. |
| 2026-08-17 | `pending` | `SAT` closed: `propositional_interpolant_certified` returns the two DRAT refutations `verify_interpolant` already built and threw away; drat-trim accepts both, on PHP(3,2) as well as the trivial case. 12 → **13 of 23 logics**, floor 38, band 1 down to `QF_IDL` alone. One control was written, found vacuous (both proofs are the single step `0`), and replaced with one that discriminates. |
| 2026-08-17 | `pending` | Item A's minimum landed: `check-capability-routes.py` requires every function the table names to exist (42 routes, 0 missing — a ratchet, not a repair). The naive version's two false positives (`(vocabulary)` is prose, `(nia_square)` is a `mod`) are pinned as controls. |
| 2026-08-17 | `pending` | Item C: `Capability.checked_by` states who checks each artifact (+ a **Checked by** column in the matrix), replacing the prose regex. Reading all 15 unclassified rows showed the bucket was a regex gap, not a real category — 14 were self-checks phrased "re-checked"/"VERIFY-BEFORE-RETURN". Heuristic kept only as an asymmetric cross-check (claiming external with no checker named fails). Headline unmoved at 38 / 13 of 23; unclassified 15 → 0. |
| 2026-08-17 | `pending` | `instantiate_at_int_model`: a Farkas refutation, generalized over the ordered ring, instantiated at ℤ — `∀ (x0 x1 x2 : Int), … → False`, kernel-checked, **axiom footprint empty**. The machinery for both halves existed; nothing had joined them. Not yet dispatched, so no capability row. Controls: the statement is asserted to mention `Int`, conclude `False`, and keep 3 variables + 4 hypotheses, since an empty footprint on a vacuous statement proves nothing. |
| 2026-08-17 | `pending` | The motivating query closed as a measurement: `x > 5 ∧ x < 3` — the `(set-logic QF_LIA)` instance that renders a structural attestation today — has an axiom-free integer refutation, `∀ (x0 : Int), 5-x<0 → x-3<0 → False`. The reasoning is available; only the dispatch that reaches for it is missing. |
| 2026-08-17 | `pending` | `refutation_over_int_axioms` closes the integer route: the ∀-statement's binders are discharged against fresh `Int` axioms, giving a kernel-checked `False` and a 221 KB module **official Lean 4.30.0 accepts** — and REJECTS when one hypothesis relation is swapped, so acceptance is not vacuous. Content class is `TheoryReconstruction`, not the attestation those queries render today. Still undispatched: fragment + routing + a crosscheck family are the remaining slice. |
| 2026-08-17 | `pending` | `ProofFragment::IntFarkas` dispatched: `QF_LIA` and `QF_IDL` conjunctive systems whose rational relaxation is infeasible now reconstruct instead of attesting, with a crosscheck family each (footprint = the query's own vars/hyps, no Real axioms, no sorryAx). Split 34 → 37 theory families vs 40; a committed QF_LIA corpus row moved with it. Declines integer-only infeasibility (3x≥1 ∧ 3x≤2). **Band 1 empty**; 13 → 14 of 23 logics, floor 39. |
| 2026-08-17 | `pending` | Qualified the "axiom-free" claim against official Lean rather than leaving it to be overread: instantiating at Lean core's standard `Int` costs `propext` — a FLOOR, since every core `Int` ring/order lemma carries it — so axiom-freedom over the standard ℤ is unreachable by anyone. Our empty footprint follows from instantiating at our own constructed ℤ (zero axioms, but no proved bridge to Lean's). Even bridged, this route lands at `propext` vs `omega`'s `propext + Quot.sound` on the identical goal. |
| 2026-08-17 | `f18904db7` | R3: reachability census re-derived and committed as `artifacts/reachability/r3-census.tsv` (190 rows over both corpora); the ranked tables in `04-reachability.md` are now a generated view of it, gated by `scripts/check-reachability-census.py` inside `check-foundational-resources.sh`. 13 guards, each with its own rejection path; mutation-verified that deleting any one kills exactly one test. Corpus coverage checked in both directions and reported SKIPPED, never passed, when the sibling checkout is absent. Stale numbers corrected in `04` and `05`. |
| 2026-08-17 | `pending` | ADR-0468: ℝ is a Bishop setoid over ℚ at **zero** trusted declarations, with `creal_shape_probe` measuring the carrier's admissibility against a `funext` negative control; ℂ scoped and deferred. |
| 2026-08-16 | `pending` | Claim dashboard regenerated and gated: `gen-claims-dashboard.py --check` added and wired into `generated-trackers` (justfile) and `check.sh`; `validate-claims.py` now type-checks `frontier.known` / `would_settle` / `attack_notes` against `claim.schema.json`; the one schema-violating claim normalised. DASHBOARD.md goes from a stale 38 claims / 1 family / 81 rows to the actual 104 / 3 / 266. Both negative controls exercised. |
Older landed changes (including the 2026-08-06 A1/A2 closure commits) remain
in Git and their dated result notes; this table is deliberately bounded to
changes that still determine the immediate queue.

## Next Actions

Work in this order unless new evidence reveals a wrong verdict, crash, data-loss
risk, or invalid gate. Those are P0 and preempt the queue.

The ordered ten-item programme remains A2 through A11. A1 and A2 are retained
here as closed evidence boundaries. A3 remains incomplete, but all currently
preregistered bounded mechanisms are closed negatively. A4 has now also yielded;
A5 is the first active item.

**D3 grouping is BLOCKED, not queued (`BLOCKED`, solver-arith-group,
2026-08-17).** Sent to execute the one D3 group the 2026-08-17 edge measurement
supported (arithmetic; the other three were refuted). Re-measured first, and did
not move any files — two reasons, both in
[`03-solver-decomposition.md`](docs/refactor-2026-08/03-solver-decomposition.md)
under "Measured 2026-08-17 (second pass)".

1. The first pass committed no script, so its membership rule is unrecoverable
   and its arithmetic verdict does not survive re-derivation: sweeping plausible
   boundaries moves the degree-matched p from <0.0001 (23 modules) to 0.377 (39),
   crossing out of significance **at the 34–35 modules the first pass itself
   reported** (p = 0.110). Only the `strings` row reproduces exactly, because
   zero internal edges pins the set.
2. The move fails the gate for every membership. A directory is *one* node in
   `analyze_solver_module_graph.py`, so grouping merges nodes and creates cycles
   no member had. Best case (23-module core): `mbp` newly enters the theory
   core's cycle and the largest cycle grows **58,215 → 103,514 lines**, 25.8% →
   45.8% of the crate, while its module count moves 24 → 25. Every wider
   membership also adds `arith -> reconstruct`, destroying D1's precondition.

Landed the measurement as code instead — `scripts/analyze_solver_group_collapse.py`,
exit status is the finding — so the next lane decides this before moving a file
rather than after.

**Next:** not this. The blocker is the arithmetic ↔ `auto` / `reconstruct`
cycle; D3's sequencing item 3 now depends on item 4 (`D1` narrowing), not the
other way round. Whoever takes that: run
`scripts/analyze_solver_group_collapse.py --group arith-core --check` and watch
it go green — that is the exit criterion, and it is currently red.

**Both of Euclid's missing ingredients are in; `F:nat-exists-prime-gt` is one
slice from closing** (`WIP`, nat-prime-divisor, 2026-08-17).
`Nat.exists_prime_dvd : ∀ m, 2 ≤ m → ∃ p, (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p) ∧ p ∣ m`
is admitted axiom-free, recorded as `F:nat-exists-prime-dvd`. It did **not** go
through `lt_well_founded`, which is what the previous lane's note predicted:
strong induction on `m` has to *decide* primality of `m`, and a bounded `∀` is
not decidable constructively without a bounded search anyway — so the search is
done directly, by ordinary `Nat.rec` on the bound, returning the **least**
divisor `≥ 2`. Leastness is what makes primality free; a proper divisor of the
least divisor would be a smaller divisor of `m`. Each step decides `succ j ∣ m`
by reducing `beq (mod m (succ j)) 0`, with the branches separated by the checked
`div_mod_remainder_eq_zero_iff_dvd`. Nothing classical, nothing well-founded.

**A theorem-only slice is kernel-guarded, but its *statement* is not.** No
`Definition` was added, so there is no degenerate computation rule to fear — the
kernel refuses a false theorem and a non-prime witness never gets in. What the
kernel cannot see is a statement weaker than intended. Measured: spelling the
primality bound `1 ≤ p` instead of `2 ≤ p` still type-checks, still admits, and
passes every pre-existing test including axiom-freedom and the determinism
count — and is satisfied by `p = 1`. That mutation was run and killed **exactly
one** test, the new one, which compares the admitted type against an
independently built term. The fact's `kernel-term` checker greps the whole
rendered type for the same reason; a name-only grep survives the mutation.

**Next.** Close `F:nat-exists-prime-gt`. Two small steps remain, both resting
only on already-admitted axiom-free lemmas: (1) `1 ≤ Nat.factorial n` (induction,
`one_le_mul` at the successor), which is what makes `2 ≤ 1 + n!` and so lets
`exists_prime_dvd` apply to it at all; (2) the assembly — take `p` prime with
`p ∣ 1 + n!`; if `p ≤ n` then `dvd_factorial_of_le` gives `p ∣ n!`, `add_comm`
reshapes the sum, `dvd_add_right_cancel_of_pos` yields `p ∣ 1`, and
`not_dvd_one_of_two_le` refutes it; `le_total` then leaves `n ≤ p` and
`lt_or_eq_of_le` sharpens it to `n < p`.

**ℕ-induction is in dispatch; the front door now decides 4 of the 12 corpus
instances where it decided 1** (`WIP`, induction-dispatch, 2026-08-17).
`prove_by_nat_induction` had been built, exported, and deliberately kept out of
`solve` because it applied ℕ-induction to goals quantified over all of `Int` and
answered `unsat` for satisfiable sets. `a32280b6a` made a recognised `n >= 0`
guard mandatory; this lane re-measured that fix, attacked it, and wired the route
in as the last rung of the quantified ladder.

Re-measurement of `corpus/regression/uflia_induction` (12 instances): the three
`unguarded_*` rows are declines and the four unique `unsat` decisions survive —
**0 status contradictions, down from 3**. The route decides `guarded_linear_
closed_form`, `guarded_linear_nonneg`, `guarded_monotone_step` and
`guarded_parity_range`; the two nonlinear-step instances (`guarded_sum_gauss`,
`guarded_product_factorial_bound`) still overrun.

**No wrong `unsat` was found, and one crash was.** The new
`tests/nat_induction_adversarial.rs` carries 22 shapes chosen because a plausible
recogniser gets them wrong, each with a hand-derived truth and its witness — a
`<= n 0` guard, `>= 0 n`, `>= n (- 5)`, `>= (+ n 1) 0`, a guard on a *different*
variable, a vacuous `true` guard, a disjunctive guard admitting `-1`, nested
binders, a conclusion carrying its own quantifier, binders shadowing free
symbols, nested and n-ary implications, three multi-goal orderings. Every one
declines, on the route alone and through the front door. The defect that surfaced
was arity, not soundness: `is_nonneg_guard` bound `(args[0], args[1])` before
matching the operator, so a one-argument guard (`(=> (not (= n 5)) …)`, legal
SMT-LIB) panicked — unreachable while the route sat outside dispatch, a
front-door crash the moment it did not.

Both suites are mutation-verified, not assumed live. Restoring the
pre-`a32280b6a` fall-through turns 8 of 22 probes into wrong `unsat` and kills
exactly one test; disabling the dispatch rung kills exactly one test in each of
the two suites that assert it fires, and nothing else.

One thing worth carrying forward: **`corpus_regression` could not have caught
this either way.** That gate calls `check_auto` — the quantifier-*free* dispatch
— while the rung lives in `solve`, so its 152 files / 0 DISAGREE is unchanged and
structurally blind to this change. The `nat_induction_corpus` gate now checks the
front-door column as well as the route's own, because a wrong `unsat` from a
wired rung is a shipped verdict.

**Next.** Two things the measurement names. (1) The nonlinear step obligations:
`2·s(n) = n(n+1)` and `fact(n) ≥ 1` both time out in the step, so the rung stops
exactly where NIA does — that is a NIA task, not an induction task. (2) The
recogniser declines any goal whose *other* assertions include a quantifier it
cannot instantiate, which is why all three multi-goal probes decline; widening
`hypotheses` to carry a universal it cannot instantiate as an assumption rather
than dropping the goal would reach them. Neither is a soundness item.

**`string` is axiom-free (`DONE`, agent-strings, 2026-08-17).** The last
prelude assumption outside `real` is retired: `axeyum.string.<n>.append` was a
`Declaration::Axiom` and is now a checked structural recursion over `Str.rec`,
with `nil_append` / `cons_append` / `append_nil` / `append_assoc` admitted as
`Declaration::Theorem`s the kernel re-checks (ADR-0469). Measured, not read off
the diff: `nat_axiom_inventory` reports `string: axiom=0 opaque=0 quotient=0`,
and the derived ledger is `total=30 | real=30 | everything else 0`. Verified
outside this kernel as well — a real `lean` 4.34.0-rc1 accepts the exported
module and its `#print axioms` lists only the problem's own opaque words.

The whole trusted surface of this project is now the `real` prelude (30 rows,
being constructed under ADR-0468 by another lane).

Next for this lane: length (`str.len : Str → Nat`) and the cancellation lemmas,
which are what the monoid laws were the prerequisite for — a word-level
refutation that reasons by length rather than by first clash. `word_reconstruct`
still only needs `append` as a function symbol, so nothing consumes the new laws
yet; that is the gap to close.

Not done, and deliberately: the `real` rows are a different case (their carrier
is genuinely opaque), and `nat_axiom_inventory`'s doc header still cites a stale
`integer=1` — owned by another lane.

**The ℕ side is closed; the ℤ side is half-closed, and the half that is missing
is named (`DONE`/`PARTIAL`, agent-characterization, 2026-08-17).** The gap was
real: `nat_axiom_inventory` reports `nat: axiom=0` and `integer: axiom=0`, and
neither number says the objects are the standard ones. A `Nat` with a subtly
wrong order reports the same zero, and rendered Lean modules run in `prelude`
mode re-declaring their own `Nat`/`Int`/`Eq`/`False`, so official Lean accepting
one certifies "typechecks against THESE definitions", not that they are the
usual ones.

Closed by proof rather than by inspection, in `crates/axeyum-lean-kernel/src/characterization/`:

- **ℕ is pinned.** The three Peano axioms (`Nat.Peano.zero_ne_succ` was
  genuinely absent — the prelude's own docs said successor/zero discrimination
  was not there), the universal property (`iter` + `iter_zero`/`iter_succ`
  definitionally + `iter_unique`), and `Nat.Peano.categorical`: **every**
  structure `(N, z, s)` satisfying the Peano axioms is in structure-preserving
  bijection with ours, universe-polymorphically. That is second-order
  categoricity stated inside the kernel, and it is strictly stronger than a
  bridge lemma to one other definition of ℕ.
- **ℤ is pinned as a *theory*, not up to isomorphism.** No junk (`cases`,
  `of_nat_or_neg`), generation by `1` (`induction` on `±1` — what lexicographic
  `ℤ[x]` fails), discreteness at **every** point (`discrete_everywhere`, derived
  by translating `(a, a+1)` down to `(0,1)` — what `ℚ` fails), `le_total`,
  `zero_ne_one`, and the **uniqueness** half of the universal property
  (`rec_unique`). The existence half — a map `Int → R` built from an arbitrary
  target's own data — is not proved, so "these properties determine `Int`" is
  **not** claimed.

18 theorems, every axiom footprint measured empty. Two things stop this from
being an unfalsifiable claim: the theorems are instantiated at structures we
actually have (a categoricity theorem whose premises nothing satisfies would be
axiom-free and worthless), and nine `Weakening` variants replace one hypothesis
with `True` and must each be refused **at the declaration they were aimed at**.
A guard-mutation check — disabling one injection — killed exactly one test.

**Also recorded here because it cost another lane 1,514 lines:** the per-lane
index protocol has a gap the written rule does not close. `git read-tree HEAD`
in one shell invocation and `git commit` in the next is not a refresh — HEAD
moved in between (`cf205e9a8`), and the bare commit from the stale private index
reverted it inside a commit whose stat otherwise looked exactly like the eleven
files staged. Repaired in `f532e04d3`. The operative rule: read-tree in the
**same invocation** as the commit, and read `git show --stat` for the file
*count*, not for the diff you were expecting.

**Next:** the ℤ existence half. It needs a map out of `Int` built from a target
ring's own data, which means either parameterising over a small ordered-ring
interface or constructing the comparison map from `natAbs` plus the sign split.
That is the one theorem standing between `F:int-characterization` and an `ℤ`
categoricity fact with the same standing as `F:nat-peano-categoricity`.

**The real-Lean gate now names its checker, and there is only one rule for
picking it (`DONE`, agent-lean-toolchain, 2026-08-17).** Two Lean toolchains are
installed on this box (4.30.0, the pin, and 4.34.0-rc1) and **two discovery
implementations disagreed about which to use**: `scripts/check-lean-gate.sh`
tried `command -v lean` and found elan's default, while `lean_probe.rs` sorted
elan's toolchain directories newest-name-first and took the release candidate.
Under 4.34, 21 of 77 `lean_crosscheck` families were rejected and
`scripts/lean/replay-lean4export.lean` did not elaborate at all — so the gate's
verdict depended on which toolchain happened to be installed and on which entry
point ran, and nothing in the output said which one produced it.
[ADR-0470](docs/research/09-decisions/adr-0470-the-pinned-lean-toolchain-is-the-one-that-runs.md)
decides **the pin runs**: `lean-toolchain` is the single source, `PATH` and other
elan toolchains are candidates only if `--version` matches it, there is no
"newest wins" step, and a non-pinned toolchain is a refusal naming both versions
rather than a substitution. Not newest, because
`real_lean_strict_positivity_crosscheck` asserts an exact commit and
`real_lean_wire_differential` is a differential against the reference
implementation; "whatever was installed" makes both meaningless.

Every suite now prints `AXEYUM-LEAN-TOOLCHAIN … bin=… version=… matches_pin=…`
and the gate **fails** if any suite reports a different binary than it resolved,
or reports none — a result that does not name its checker is not evidence.
Measured after the change: 17 suites, 57 tests, **223 real-Lean checks** (floor
208), 37 theory families (floor 37), every suite confirming the same binary.

**The guard is exercised, not asserted.** `scripts/tests/test-lean-toolchain-policy.sh`
(now in `just check` and `check.sh`, ahead of the gate) points both entry points
at the non-pinned 4.34.0-rc1 and requires the refusal by name, checks that the
shell gate and the Rust probe resolve the *same* binary, and — control 5c —
requires the same suite to **pass** once the deviation is stated, so 5b's failure
cannot be dismissed as "4.34 is broken here". Three separate one-guard deletions
each killed **exactly one** control. It also fails rather than passing when no
second toolchain is installed to exercise the wrong-toolchain case.

**4.34 breakage fixed, not merely diagnosed.** `Environment.addDeclCore` gained a
`maxRecDepth : USize` parameter in 4.34, so the replay script died before reading
a byte of the stream; the call is now resolved at elaboration time and
`real_lean_kernel_replay` passes under **both** toolchains (positive replay and
tampered negative control alike).

**Next:** `real_lean_wire_differential`'s own `pinned_lean()` is now a redundant
assertion of the same policy rather than a competing one — collapse it onto
`lean_probe::lean_bin()` when that file is next touched. Unrelated finding for
whoever owns it: `cargo clippy -p axeyum-lean-import --tests -- -D warnings`
fails on `real_lean_wire_differential.rs:458` (`too_many_lines`, 121/100) on
unmodified `HEAD` content.

**ℤ is now pinned up to bijection, and the limit of that is stated rather than
blurred (`DONE`, agent-int-categoricity, 2026-08-18).** Lane
`agent-characterization` closed ℕ and named its own gap exactly: for ℤ only the
**uniqueness** half of the universal property was proved, so those properties
were proved to *hold* of `Int` and not to *determine* it. `rec_unique` was
uniqueness of a map nobody had constructed.

Built in `crates/axeyum-lean-kernel/src/characterization/int_categoricity.rs`,
declaring into the existing `Int.Characterization` namespace:

- **The existence half.** A **ℤ-structure** is a carrier `R : Sort u` with a
  point and two mutually inverse endomorphisms (`down ∘ up = id`,
  `up ∘ down = id`) — a pointed set with an automorphism.
  `Int.Characterization.iter` maps into any of them, built from that structure's
  own data; `iter_zero`/`iter_succ`/`iter_pred` are its three
  structure-preservation equations. With `rec_unique` this makes `Int` the
  **initial** ℤ-structure. Which hypothesis each equation needs is itself
  measured: `iter_succ` needs only `up ∘ down = id`, `iter_pred` only
  `down ∘ up = id`, because in the normalized `ofNat`/`negSucc` representation
  every case is definitional except the one that crosses zero.
- **Categoricity.** Adding generation (a `Prop`-valued induction principle on
  `R`) and aperiodicity at the point (`e ≠ up^(n+1) e`),
  `Int.Characterization.categorical` proves the comparison map is a
  structure-preserving **bijection**. Universe-polymorphic, the same shape as
  `Nat.Peano.categorical`. Each hypothesis rules out a specific counter-model:
  `ℤ/n` satisfies everything but aperiodicity, `ℤ ⊔ ℤ` everything but
  generation, `ℕ` everything but `up ∘ down = id`.

**Framing that keeps it honest, and is the reason this is not called a ring
theorem:** the categoricity is over ℤ-structures, **not** over discretely
ordered rings. "Every discretely ordered ring generated by `1` is isomorphic to
`Int`" would need the order axioms as hypotheses and a derivation of the
automorphism from them. What is proved is that the order properties hold of
`Int` (`F:int-characterization`) and that the ℤ-structure properties determine
it (`F:int-categoricity`).

**The two strengths of "isomorphism", kept apart:**

- `categorical` proves injective **and** surjective, and surjectivity is a
  `Prop`-level `∃` with **no inverse function extracted** — the same limit
  `Nat.Peano.categorical` has, and for the same reason: a `Prop`-valued
  generation principle on the target can prove `∀ y, ∃ t, iter t = y` and cannot
  define a function `R → Int`. With `Prop`-valued generation that is the
  strongest form available, and claiming more would be false.
- `Int.Characterization.iso` **is** the constructed form — `iter ∘ psi = id_R`
  and `psi ∘ iter = id_Int`, two equations between maps — at the price of taking
  the back-map `psi` as a hypothesis. So any structure-preserving map back is
  automatically a two-sided inverse and is unique; that one *exists* is not
  proved and does not follow from these premises.

14 new theorems (32 in the package), every axiom footprint measured empty.

**Non-vacuity is a declaration, not a test.** `categorical_at_int` instantiates
`categorical` at `(Int, 0, (·+1), (·−1))` with every hypothesis discharged by a
real theorem — the inverse laws from `add_assoc`/`add_neg`/`add_zero`, generation
from `Int.Characterization.induction` verbatim, aperiodicity from
`Nat.Peano.zero_ne_succ` through `Int.natAbs` — and pushes the result back
through the trusted gate. It is checked on every build and printed as its own
row, because premises nothing satisfies would be axiom-free and worthless.

**The negative-control machinery got the guard it was missing.**
`refused_declaration` alone only asserts the aimed-at declaration is *absent*,
which an early unrelated failure also achieves — and with 22 injected defects
spanning three modules that stops being hypothetical.
`Weakening::reached_declaration` names the declaration immediately **before** it
in build order, and both `characterization_tests` and the
`characterization_status` example require it to be present, so the failure is
bracketed on both sides. Both guards were mutation-probed rather than asserted:
making one injection inert killed **exactly one** test, and aiming one defect at
the wrong declaration made the test *and* the example fail with the bracket
message.

**Next:** two things are genuinely open, in this order. (1) The ring-theoretic
statement — categoricity over discretely ordered rings rather than
ℤ-structures — which needs the order axioms as hypotheses and the successor
automorphism derived from them, and would connect `F:int-characterization`'s
order rows to the categoricity theorem instead of leaving them adjacent. (2) The
same treatment one level up: `ℚ` as the field of fractions (initial among
ordered fields of characteristic zero) is the next object whose prelude proves
laws without pinning the object, and `agent-creal` owns that surface.

**The transcription check now covers three routes, and the denominator is
measured rather than estimated** (`WIP`, binding-coverage, 2026-08-18).

Lane `agent-transcription` closed the SMT-LIB → rendered-statement gap
(trust-surface item 3, *weaker than the kernel*) for the two Farkas routes and
declined the rest. This lane widened it and, more usefully, **measured what the
rest actually is**. Swept all **1404** committed `.smt2` files: **270** render a
Lean module at all, and those 270 split exactly three ways.

| verdict | n | what it means |
| --- | --- | --- |
| **bound** | 125 | every rendered hypothesis bound back to an `(assert …)` line |
| **attested** | 124 | the module transcribes **nothing**; verified content-free |
| **declined** | 21 | neither — named, not pinned, not checked |

**+20 bound (105 → 125), and the 124 are the finding.** The `ArrayAxiom`,
`QfAbv` and `Sos` reconstructions render an *opaque-skeleton attestation*: their
entire vocabulary is `α atom._N prop._N func._N Eq.{1} Not And`, with no
numeral, no `Int.*`/`Real.*` constructor and no carrier of any route. Lean checks
that `False` follows — and it would follow just as well if the `.smt2` file said
something else entirely, because the module's trusted base is a **fresh
vocabulary with no declared relationship to any symbol in the query.** Binding
them would be a check that cannot fail, so they are classified instead, in their
own manifest, reported as `attested=` and never as coverage. What *is* checked,
every run, is that each really is that shape: one smuggled `Int.one`, one
undeclared opaque name, one truncated type or one extra axiom takes a module out
of the class and fails the run. **One of the 124 is self-refuting** — its
`Not (Eq.{1} α atom._0 atom._0)` is an axiom Lean's own `rfl` refutes, so its
`False` needs none of the module's other axioms and not even the propositional
step is taken (`attested_vacuous=1`).

**Two prior claims were wrong, and both were measurements nobody had taken.**
The SOS route does **not** render `Real.mul` monomials on 10 QF_NRA instances:
9 of them render the content-free propositional skeleton above, and **exactly
one** file in the whole corpus (`nra-neg-square-d01.smt2`) renders a monomial at
all. `ArrayAxiom` is 102 instances in the corpus, not 14.

**The Diophantine route (`axeyum.reconstruct.dio.hyp._N`) is bound**: 18 of its
20 instances, the ground-linear ones. Its hypotheses are `Eq.{1} Int` equalities
with coefficients rendered as repeated `Int.add`. Adding it exposed a real defect
in the checker: the `=` canonical form sign-normalized on the **lexicographically
first variable**, which reads a name and so is *not rename-invariant* — the two
sides of this check use different names by construction, and four faithful
modules were being rejected. Both orientations of every equality go into the pool
instead, which needs no name ordering at all.

**The converse direction is now measured, not just admitted.** Binding proves
every rendered hypothesis comes *from* the query; it says nothing about the
query's rows that were never rendered. That shortfall is counted from the
accepted renaming (never from the search's own bookkeeping) and printed:
**286 of 531 spine assertions are represented** — barely half. Not a soundness
hole (a refutation of a subset refutes the whole) but the precise size of what
the subset check does not show, floored by `--min-represented` so a wholesale
drop cannot pass quietly.

**Two defects that made the checker lie rather than decline.** (1) A module with
no hypothesis in any bound route *bound vacuously* — the empty renaming satisfies
every requirement — so a pinned instance degrading to a content-free skeleton
would have stayed green. (2) `read_query` died with `Unsupported: arithmetic head
'forall'` on a `let`-bound quantifier and ended the run in a **traceback**, which
is neither a pass nor an honest decline; the name is now bound opaquely, and
referencing it contributes no atom rather than inventing a free variable a
hypothesis could match.

**24 guards, each driven to failure** in `scripts/tests/mutation_controls.py`
(12 → 24); 83 offline control tests. Every run corrupts each hypothesis six ways:
1210 caught, 427 accepted and each re-verified from its own binding.

**Next, in measured order.** (1) The 13 quantified LIA/BV instances whose
hypothesis is a pi-type `((x0 : Int) -> … Or/Not/Iff …)` — the largest declined
group, and the one needing a genuinely different binding argument. (2) Monomial
support, worth **one** instance, not ten: it means canonicalizing over monomials
rather than variables, which touches the matching code all 125 bound instances
rest on. (3) The 8 ground declines whose hypothesis is the *output* of an array
or BV abstraction step rather than a transcription of any assertion — these need
the abstraction itself bound, which is a different check.

**The weakest link in the trust chain is now gated** (`WIP`, transcription,
2026-08-17).

`docs/prover-track/research/13-residual-trust-surface.md` ranks what a third
party must believe, and puts the SMT-LIB → rendered-statement transcription at
item 3, **weaker than the kernel**: a reconstructed UNSAT declares the query's
constraints as the Lean module's own axioms and proves `False` from them, and
nothing checked that those axioms are the `.smt2` file's `(assert …)` lines. A
dropped negation would typecheck, report a clean axiom footprint, and be
worthless.

Measured first, as the note said: **nothing checked it.** The closest existing
instruments count hypotheses (`hypotheses >= assertions.len()`) or test the
declared type for the substring `Real.le`. Neither reads what a hypothesis
*says*.

`scripts/check-lra-hypothesis-binding.py` closes it for the two arithmetic
hypothesis routes. Both sides are re-parsed and re-normalized in Python —
sharing no code with each other or with `axeyum-smtlib` — because the renderer
emits `x > 5` as `-x + 5 < 0` and normalization is exactly where the bug would
hide. Every rendered hypothesis must be an atom the query **entails**, under one
injective, sort-respecting renaming; every axiom in the module must be a
carrier, a bound hypothesis, or a pinned prelude law, so `axiom smuggled : False`
cannot pass unread. **105 instances, 248 hypotheses, 0 failures** (~30s), swept
from the committed corpora rather than hand-picked.

Two things it does that the count above does not convey:

- **It corrupts the real artifacts on every run.** Each hypothesis, five ways.
  869 caught. The gate cannot pass without its detector firing — this repository
  measured 40 of 162 checker runs exiting 0 on completion alone.
- **The search is untrusted.** Its 329 *accepts* of corrupted modules are not
  misses: `x ≤ 0` shifted to `x ≤ 1` names a different genuine row, and swapping
  the sides of `x − y < 0` is faithful again under the renaming that swaps `x`
  and `y` (measured, on a real cvc5 regression file). Each accept is re-derived
  by `verify_binding`, which shares no control flow with the search. A pristine
  accept the binding cannot justify fails the run too.

Writing it found a defect in the checker's own search — it committed to the first
permutation inside a matched atom and reported a transcription defect on a
**faithful** module (`x+y=1 ∧ x=2 ∧ y=0`). Pinned as a regression.

**Scope, stated so nobody over-reads it.** Linear atoms only, and only the
`lra.hyp._N` / `lra.int_hyp._N` routes. The SOS route's `Real.mul` monomials and
every other `axeyum.reconstruct.*` namespace are **declined, not skipped** — an
unrecognized query-derived axiom fails the run, so the uncovered routes are
visible rather than silently blessed. 11 instances are excluded for exactly
these reasons, each named in the manifest.

**Next.** (1) Monomial support would take the 10 QF_NRA SOS instances, which is
the only route in the swept corpus that renders arithmetic this checker cannot
read. (2) `axeyum.reconstruct.dio.*` (18 Diophantine instances) is the next
namespace by instance count. (3) The 14 `ArrayAxiom` and 5 `QfAbv` modules
render hypotheses that are not linear atoms at all and need a different binding
argument.

**Claim-dashboard gate, finding-8 re-measurement, and PLAN.md returned under its
ceiling** (`WIP`, ledger-integrity, 2026-08-16). Three defects behind a dashboard
reporting 38 claims against an actual 104; finding 8 re-measured as remediated
(177/177 checker runs can fail) after a regex audit of my own produced 19 false
positives; and `plan-authority` taken from 233,888 bytes to 46,820 by archiving
finished lanes to [`docs/plan/archive/`](docs/plan/archive/README.md). Full record:
[`diary-ledger-integrity.md`](docs/refactor-2026-08/diary-ledger-integrity.md).

**`int_prelude` is axiom-free.** `Int.euclidean_decomposition` is a theorem;
`Int: 54 derived (54 with an EMPTY axiom footprint), 0 still asserted`, trusted
surface `34 → 6 → 1 → 0`. Measured downstream under real Lean: the Diophantine
reconstructions now depend on **no library axiom at all**, and `check_one_lean`
gates that. Fourteen `kernel-lean` fact checkers were rebound from a whole-suite
run to their own theorem.

**Next.** ℚ, scoped in
[`02-the-library.md`](docs/mathematics-2026-08/02-the-library.md): build it as a
normalised structure (as Lean core itself does), not a setoid quotient. First
slice is `Int.natAbs`, then `Int.div`/`Int.mod` specified against the
freshly-proved decomposition.

**Certification is now gated on being re-derivable, not on being claimed**
(`WIP`, evidence-certification, 2026-08-17). Full record:
[`diary-evidence-certification.md`](docs/refactor-2026-08/diary-evidence-certification.md).

Three measurements drove the day, each a claim that was true in a way that read
as stronger than it was:

- **Ledger.** Settled SMT-route facts test the *verdict* (`… | tail -1` =
  `unsat`) and are blind to certification. 17 of 17 happened to be
  `certified=1`; nothing enforced it. Now gated, with the barber instance as a
  real negative control — genuinely unsat, genuinely uncertified.
- **Lean gate.** Of 74 crosscheck families, **41 hand Lean a structural
  attestation** — an axiom pair it cannot fail on the merits. The gate reported
  one undifferentiated total; it now prints both halves and floors the
  *reasoning* one, because flooring the sum lets reasoning be swapped for
  attestation with the headline unmoved. `qf_bv` was one of the 41: not a defect
  but a **width**, since enumeration beats bit-blasting below ~16 bits.
  `qf_bv_wide` now exercises the real reconstruction (33 theory / 41 attestation).
- **My own claim.** I wired the e-matching route to `Evidence` and shipped
  `certified=1` on evidence whose independent re-check said FAIL. Reverted, then
  fixed properly: the certificate is portable now — instances are rebuilt in the
  checker's arena rather than trusted by `TermId`, and the ground set is rebuilt
  rather than stored. One/two/four instances all `certified=1 arena=ok`.

**Next.** A6's remainder, now scoped: the "38 QF_BV bare-UNSAT rows" are
evidence-production TIMEOUTS (`PARITY.md` 92/130), and the per-file detail is
gitignored — so it is a measurement run, not desk analysis.

**Two standing cautions for anyone quoting these numbers.** `certified=` and Lean
reconstruction are *independent axes* — a fact can be certified with no Lean
module, and 41 of 74 Lean-checked families prove nothing about their proposition
— so the two must never be summed. And `just check` is red independently of this
lane: `check-plan-authority.py` budgets the `PLAN.md` sources at 52 KB and they
were already 57 KB before this lane existed.

**The mathematics strand's primary metric drifted 4 → 11 areas unnoticed**
(`WIP`, capability-assurance, 2026-08-17). Detail:
[`01-decide-vs-certify.md`](docs/mathematics-2026-08/01-decide-vs-certify.md).

```
CAPABILITY_ASSURANCE|entries=101|areas=23|external=36|self=48|differential=2|unclassified=15
```

It asks "can a third party check without trusting us?" and calls that the
strand's primary metric — but the answer lived in 101 prose `evidence` fields,
so nobody could count it. Seven areas beyond the documented four had gained
external checking, mostly via Carcara. Agreement with an oracle is tiered
separately so it cannot inflate the number; 15 entries stay `unclassified`
rather than being sorted into a flattering bucket. Now floored.

**Item B is done, and derived** (`--rank`, also in `just flywheel`): the 12
unchecked logics are banded by *distance to an external checker*, not by
opinion. Band 1 — `QF_IDL`, `QF_RDL`, `SAT` — already build a refutation
artifact; `propositional_interpolant` constructs a DRAT proof, checks it with
`check_drat`, and returns `Option<BoolExpr>`, dropping the artifact on the floor.

Ranking exposed a defect in the metric itself: `tier` is per *row*, and three
logics (`QF_AUFBV`, `QF_IDL`, `QF_RDL`) are known only through a compound row,
so a quarter of the gap was uniform-by-assumption. Measured, `QF_IDL / QF_RDL`
genuinely differ — QF_RDL renders a 47 KB Lean theory reconstruction that
official Lean 4.30.0 accepts (two mutations rejected), QF_IDL renders only an
attestation. The table is deliberately **not** edited to claim QF_RDL as
external: `check-lean-gate.sh` compiles a one-module-per-family slice that
contains no QF_RDL module, and moving this metric by rewriting the prose it
reads is the failure this strand exists to prevent.

**Done same day:** QF_RDL is handed to official Lean by `lean_crosscheck`
(`family=qf_rdl_difference`, `representative=theory-reconstruction`, axiom
footprint = ordered field + the query's hypotheses, no `sorryAx`), theory-family
ratchet 33 → 34. Only after that was the table edited — gate first, transcribe
second, because `tier` reads prose and the reverse order would move the metric
by writing a sentence. 11 → **12 of 23 logics**, floor raised to 37.

**`SAT` closed too.** It was the same shape QF_RDL was, and the ADR worry
dissolved on inspection: every other interpolating area already ships a
`*_certified` sibling (QF_BV, QF_UF, QF_LRA, QF_LIA, QF_UFLRA, QF_UFLIA), all of
one shape, so propositional was the seventh case of an accepted pattern.
`verify_interpolant` had already built and checked both DRAT proofs and returned
a bool; `propositional_interpolant_certified` returns them. drat-trim accepts
both, including on a PHP(3,2) partition needing real resolution.

**Band 1 is empty as of 2026-08-17** — `QF_RDL`, `SAT`, `QF_IDL` all closed.
14 of 23 logics externally checked, gap 9, floor 39. What remains is band 2 (six
logics with no UNSAT proof format) and band 3: research, not plumbing.

Chasing `QF_IDL` turned up something larger: a
conjunctive integer system whose *rational* relaxation is already infeasible
(`x > 5 ∧ x < 3`, `x - y ≤ 1 ∧ y - x ≤ -3`) has an ordinary Farkas refutation,
yet every such query routes to `ArithDpll` and renders a structural attestation
— an `axiom P` / `axiom ¬P` shim carrying none of the reasoning. The proof
existed; only a `Real`-shaped destination for it did.

`instantiate_at_int_model` supplies the destination. `generalize_over_ordered_ring`
already abstracts a Farkas refutation over the 22 ordered-ring laws (axiom-free),
and `build_int_model_of_arith` already exhibits ℤ as a model of all 22 with empty
witness footprints; nothing had ever instantiated at it. Measured, `x+y+z ≤ 1 ∧
1 ≤ x,y,z` becomes a kernel-checked theorem over `Int` with **an empty axiom
footprint**.

Not yet wired into dispatch, and deliberately no capability row until it is —
the same gate-first discipline QF_RDL followed. That wiring is the next slice. Then items A (generate the table) and C (explicit
"decided, not certified" status), which are the real fix: this checker is a
heuristic over prose and says so.

**ℝ is built, it is free, and 7 of the 22 ordered-ring laws hold over it
(`WIP`, agent-creal-laws, 2026-08-18).** ADR-0468 phase R1 is complete and R2 is
most of the way: `CReal` — a Bishop setoid of regular ℚ-sequences — with `Equiv`
**reflexive, symmetric and transitive**, `zero`/`one`/`neg`/`add` with the
`neg`/`add` congruences, and now the **whole additive group plus Bishop's
order**. Thirty-one declarations, every axiom footprint empty, whole trusted
surface **0**:
`cargo run -q -p axeyum-lean-kernel --example creal_setoid_witness`. No
`Quot.sound`, no `funext`, no `propext`; the kernel did not change.

**7 of the 22, and they split into two kinds.** Four hold in `Equiv` form —
`add_comm`, `add_neg` (pointwise, one `Rat` law each through
`Equiv.of_pointwise`) and `add_zero`, `add_assoc` (**not** pointwise: their two
sides are equal at no index, and only `Equiv` can relate them). Three restate
**verbatim** — `le_refl`, `le_trans`, `add_le_add` — because none of them
mentions `Eq`, which is ADR-0468's Measurement 2 cashed.

**`add_zero` and `add_assoc` did not need the missing ℚ lemma.** The previous
costing put both behind `Rat.natDivSucc` antitone in its index (~250 lines).
They are not: the gap in each is a sample at the shifted index `2n+1` compared
with one at `n`, regularity bounds it by `1/(2n+2) + 1/(n+1)` against the
setoid's `2/(n+1)`, and read at the common denominator `2n+2` — which
`natDivSucc_halve` already supplies — that is `3 ≤ 4`, one nonnegative
`1/(2n+2)`. Two helpers carry both laws: `shifted_bound_le` (the inequality) and
`weaken` (widen a `−b ≤ a ∧ a ≤ b` pair). `add_assoc` is then a rearrangement,
not an estimate: `y` is sampled at the SAME index on both sides and cancels
through `rsum_perm`, leaving `(x_M − x_N) + (z_N − z_M)`.

**`CReal.le` is the one-sided reading of `Equiv`, and that is the whole reason
the order was cheap.** `le x y := ∀ n, x_n − y_n ≤ 2/(n+1)`; `Equiv` is
literally `le` both ways, so `le_trans` is `Equiv.trans` with the lower half
deleted — the same four-term estimate at an arbitrary index `j`, now sharing
`telescope_four` and `six_term_bound` with it verbatim (both were extracted from
the existing proof, which still checks), `Rat.add_le_add` in place of
`Rat.bounds_add`, and the same Archimedean lemma. **`le_total` is absent on
purpose**: it holds for ℚ and does not lift, and nothing here assumes it.

**Three guards, each measured, and the example's exit status depends on all of
them.** `CReal.ofRat` (the carrier is inhabited), `Equiv.not_zero_one` (`Equiv`
is not the total relation) and now `not_le_one_zero` (`le` is not either — all
three order laws hold, footprint-free, of the order relating every pair; at
index 3 the claim `1 ≤ 1/2` unfolds through `Int.le` to `Nat.le 2 1`). Both new
negative controls were verified BOTH ways: the `add_zero` script with
`CReal.one` for `CReal.zero` is refused and flipping the constant back makes the
test fail, and `Not (le zero one)` is refused. `le_of_equiv` and
`equiv_of_le_le` pin the order to the setoid: a `le` weakened to `≤ 100/(n+1)`
satisfies all three laws and closes neither.

**The shape that keeps working, from the Archimedean proof and confirmed by
everything since.** No `sub_le_iff` — the gap is written `(−b) + a`. No proof by
contradiction, because `¬¬P → P` does not exist here and is not needed: `Int.le`
is decidable, so `Rat.le_or_lt` is *proved* and any "suppose not" is a case
split. No `Exists` where an index can be computed. And no reasoning about
representations: `rat_prelude/group.rs` derives its 18 lemmas from the 22 laws
alone, never a numerator, which is why `weaken` and `shifted_bound_le` are
theorems of ordered groups plus one `natDivSucc` identity rather than facts
about ℚ's encoding.

**Next, in cost order — and the two cheap strands are gone, so what is left is
genuinely analytic.** (a) `mul`, which unlocks 4 of the remaining 15
(`mul_comm`, `mul_assoc`, `mul_one`, `mul_zero`, `left_distrib` are 5, of which
the first four plus `mul_nonneg`/`sq_nonneg`/`mul_le_mul_of_nonneg_left` need
it): the blocker is a canonical bound on a representative derived from
regularity, and this is the one place a Mathlib port will NOT transfer, because
`CauSeq` gets its bound from an *existential* modulus that a fixed modulus does
not supply. Expect to invent. (b) `lt`, which is the other 7 and is harder than
"restate verbatim" suggests — a constructive `<` needs a witness index, so
`Exists` (which the logic prelude has, `exists_elim`), and the naive
`lt x y := ∃ n, y_n − x_n > 2/(n+1)` does NOT give `lt_trans` without a
quantitative gap lemma: the margin is exactly consumed by two regularity round
trips. `lt := Not (le y x)` is a dead end — `le_of_lt` is then not constructive
and `le_total` is unavailable. Budget `lt` as new mathematics, not as
transcription.

**`real: axiom=30` is unchanged, deliberately.** ADR-0468 retires those by
*deletion* in phase R3 — once `generalize_over_ordered_ring` grows an equality
slot and no consumer references the `Real` package — not by exhibiting a model.
Nor is `Eq CReal` the equality of real numbers: `CReal.Equiv` is, `0.999…` and
`1` are distinct `CReal`s and `Equiv`-equal, and every downstream statement will
say so.

**R3 done; the census is an artifact now, and `17` was not one** (`WIP`,
math-r3, 2026-08-17). The 2026-08-13 misconception audit's `census.tsv` was
never committed, so its headline "17 out of fragment" reached both
[`04`](docs/mathematics-2026-08/04-reachability.md) and
[`05`](docs/mathematics-2026-08/05-the-mathematics-dag.md) with nothing behind
it. Re-derived against the sibling `math-education` graph at `ce3e2a5`
(unchanged since, so this is not drift): **85 / 16 / 46**, not 86 / 17 / 44.
One of the 17 was a *distractor form inside* a file counted as a separate
corpus row; one genuine out-of-fragment row (`infinity-minus-infinity-is-zero`)
was missing; one (`angle-size-depends-on-arm-length`) reduces to a polynomial
identity and is moved to A, marked CONTESTED rather than asserted. Also: the
graph carries **1,567** concepts, not 1,566 — a locale collation artefact
(`sort -u` folds `C:trend-line` and `C:trendline`; `LC_ALL=C` does not).

**The adversarial corpus ranks something else first.** Censused the graph's 42
`techniques` — proof *shapes*, not propositions: 11 reachable, 19 out of
fragment, 12 heuristics (exactly the 12 the corpus itself marks
`epistemic_status: empirical`). **16 of the 19 want one thing: induction over ℕ
as a discharged schema**, against 7 for limits. Induction is the one entry on
the ranked list that is not a missing logic — the kernel has an inductive `Nat`
with an ι-computing `Nat.rec`, while the curriculum map records the `induction`
node's fragment as `LIA / BV (base + step instances)`: instances, not the
schema. So the largest single item the mathematics asks for is automating an
arrow the flywheel already has, not adding a theory.

**Next.** The obvious slice is the one the ranking names: a goal → induction
schema → reconstructed kernel term route, tested first on the technique rows
that are pure ℕ schemas (`telescoping`, `parity-argument`, `pigeonhole` at
fixed hole count). Second, the census wants a third corpus — its two are both
school-and-olympiad, adversarial along the *shape* axis but not the
*difficulty* axis.

**ℝ has a route and it is free (`DONE`, agent-reals-design, 2026-08-17).**
[ADR-0468](docs/research/09-decisions/adr-0468-real-is-constructed-as-a-setoid-over-the-rationals.md)
decides **a Bishop setoid of regular ℚ-sequences** — no quotient, no cuts.
ADR-0456's two rejections were both correct and its conclusion did not follow:
equality does not have to be `Eq`. Measured, not argued —
`cargo run -q -p axeyum-lean-kernel --example creal_shape_probe` admits the
carrier, its recursor, the representative projection (large elimination) and the
setoid relation over the *constructed* `Rat` with a **trusted surface of 0**, and
a `funext` negative control in a second kernel returns a non-empty footprint so
the zero is discriminating. The price is counted too: **9 of 30** `Real`
declarations mention `Eq`, so 13 of the 22 laws are discharged verbatim and 9
only in `Equiv` form — the order fragment Farkas actually uses is untouched.
Adding `Quot.sound` instead would read `real: axiom=0 quotient=5` and put
`[Quot.sound]` in every real footprint permanently; Dedekind costs two trusted
items, not fewer.

**One correction worth propagating beyond this lane:** the widely-repeated claim
that Coq's standard library *axiomatizes* ℝ with ~17 axioms has been false since
Coq 8.11 (Jan 2020) — `Raxioms.v` declares zero, all 17 are `Lemma`s. I wrote it
into the ADR from memory and an independent survey caught it. What is actually
there is `ConstructiveCauchyReals`: Cauchy sequences with a fixed explicit
modulus, no quotient, axiom-free, computing — i.e. this ADR's route, arrived at
independently. Corrected in place with a dated note. If you cite Coq's reals
anywhere, pin the version.

**Next:** R1 is **unblocked**. The ADR's first draft said ℚ had no order — true
of `int_prelude/rat.rs`, false of `rat_prelude.rs`, which `agent-rationals`
landed in the worktree mid-draft with `le`/`lt`/`inv`/`sub`/`div` and all 22
ordered-ring laws. The correction is recorded in the ADR rather than quietly
fixed. The only gap left is `1/(n+1)` (one definition), and writing `|a| ≤ b` as
`−b ≤ a ∧ a ≤ b` removes the `Rat.abs` dependency entirely. So: R1 carrier
(~10 decls), R2 ordered
ring + congruences (~35), R3 the one thing outside the kernel — ADR-0457's
telescope gains an equality slot (`RING_BINDER_NAMES` 30 → 39), R4 the model
witness. ℂ is scoped and **deferred with a finding**: nothing in the solver needs
it, and the only shipped complex arithmetic is exact ℚ(i) in
`axeyum-cas/src/geometry_certify.rs`, which wants a ring over ℚ and not ℝ
underneath — so ℚ(i) before ℂ, if either.

### A1 and A2 — `DONE`, archived

Both completed. Moved to
[`docs/plan/archive/30-a1-a2-completed-programme-items.md`](docs/plan/archive/30-a1-a2-completed-programme-items.md)
so this file carries actions that are next.
### A3 — Re-certify and deepen QF_NIA (`WIP`, P1)

**Why now.** The current clean entry is 34/200 versus 89/200 (38.2%), a material
gain over the former 21-decision entry but still the weakest retained arithmetic
ratio. Twelve Axeyum-only decisions also make replay and causal classification
important, not just score growth.

**Completed checkpoint.** The exact 67-row causal census and 13-row diagnostic
are retained. Giant `distinct` expansion is bounded and typed. Model
reconstruction no longer erases oracle declines or fabricates a default model.
Probe-model reuse failed its seven-target retention gate and its temporary code
was removed. Focused SMT-LIB, solver, explanation, DPLL, NIA-linearization,
route-trace, integration, Clippy, docs, and link gates are green. One aggregate attempt found the
load-sensitive coupling deadline; the repaired attempt passed all code, solver,
frontier, CAS, rustdoc, resource, policy, resume, and Lean suites but found a
one-field stale generated CI-workflow identity at final parity-docs. Both defects
are repaired. Exact topic `3586c41d9` passed one uninterrupted external-frontier
`CARGO_BUILD_JOBS=2 just check` with exit 0 and a clean tracked tree. Topic push,
merge `0c31baf97`, and combined-main `just check` are complete and green.
Exact-SHA docs run `31190516093` and CI run `31190517748` are terminal failures
at the registered-`just` path lookup, while every non-doc CI job is green.
Repair `259797459` is integrated at `bd413357c`; exact-SHA docs run
`31192792512` and CI run `31192792245` are terminal green. This remote gate is
separate from the green solver gates.
The reconstruction-deadline diagnostic then measured both targets with
size-inadmissible dense Gomory and zero B&B nodes after deadline expiry. Its
follow-up root-repair discriminator was route-unstable under host contention,
so the cluster was rejected and every temporary solver edit removed. See the
[`v1 result`](docs/plan/qf-nia-a3-reconstruction-deadline-cluster-v1-result-2026-08-07.md).
The next cluster confirmed repeated size-admission broad cores on `SAT14/1051`
(3/3) and `SAT14/1280` (2/3). Its preregistered four-group deletion mechanism
made clauses narrower but spent up to four extra exact-theory calls per
conflict, moved both budget stops earlier, and decided neither target. The
implementation was rejected and fully removed. See the
[`large-core v1 result`](docs/plan/qf-nia-a3-large-core-cluster-v1-result-2026-08-07.md)
and
[`group-deletion v2 result`](docs/plan/qf-nia-a3-large-core-group-deletion-v2-result-2026-08-07.md).

The cheaper
[`relevance-activated bound-ladder experiment`](docs/plan/qf-nia-a3-relevant-bound-ladders-v1-result-2026-08-07.md)
then activated hundreds of checked adjacent implications without an additional
theory-oracle call, but all six target observations remained `unknown`. Its
target gate failed, controls and aggregate runs were not authorized, and all
temporary solver code was removed. The resulting
[`typed-budget partition`](docs/plan/qf-nia-a3-budget-partition-v1-result-2026-08-07.md)
classifies all 52 deferred rows as 37 mixed width timeouts, 11 all-SAT
pre-lowering estimate refusals, three UNSAT combined-theory timeouts, and one
UNSAT replay-detected model overflow. Fresh current-baseline traces show the
four-row UNSAT tail is downstream of the owning exact-search stop and cannot be
recovered soundly by the SAT-only width ladder.

**Next slice.** None is currently evidence-authorized. The v1/v2
[`clause-estimate result`](docs/plan/qf-nia-a3-clause-estimate-attribution-v2-result-2026-08-07.md)
closed the final selected route at its complete-record gate without changing
production code. Preserve the 34/200 ledger, every negative control, the
64,000,000 pre-allocation ceiling, and original-term replay, then move to A4.
Resume A3 only when independent new evidence identifies a bounded mechanism;
do not revive probe-model reuse, reconstruction reservation, group deletion,
relevance ladders, or fresh-parse clause attribution, and do not raise general
caps.

**Exit.** One preregistered cluster improves a fresh whole-list result without
losing any of the 34 decisions; all SAT answers replay on the original terms and
the ledger remains disagreement-free.

**Stop.** Do not optimize on the 12 Axeyum-only cases as if they were reference
failures, and do not raise general caps to convert time into apparent breadth.

### A4 — Deepen QF_UFLIA combination (`WIP`, yielded, P1)

**Why now.** QF_UFLIA is 94/180 (52.2%) with zero Axeyum-only decisions and 86
reference-only cases, making it the clearest combined-theory depth gap.

**Next slice.** None is evidence-authorized. The theory-model reuse result
stopped negatively; revisit only with deterministic-work evidence for the
conjunctive LIA probe. The 26 wide-integer rows remain ADR-0376 controls.

**Exit.** One preregistered, replay-checked cluster improves the clean full-list
result without losing any of the 94 decisions or weakening retained controls.

**Stop.** No general cap increase, speculative recursive MBQI, or unchecked SAT
model credit.

### A5 — Consolidate linear arithmetic after warm simplex and DL (`WIP`, P1)

**Why now.** QF_LRA, QF_IDL, and QF_RDL improved sharply but remain strict
subsets of their references. The newest architecture has not yet received one
cross-division residual census.

**Next slice.** Restart and derive the complete V2 census from the fully gated
classifier repair. Only after a zero-loss
derivation may normalization failures,
unsupported difference shapes, disequalities, explanation blowups, and
ordinary search failures be classified across the three current ledgers. Treat
the repaired high-memory LRA normalization case and the rejected global 12/12
DL split as permanent controls before adding new DL syntax. The
[`v2 cross-division census preregistration`](docs/plan/qf-linear-a5-cross-division-census-v2-preregistration-2026-08-09.md)
freezes all three populations and historical sidecars, makes all 259 retained
decisions monotonicity controls, and authorizes only fresh current-Axeyum traces
plus lossless derivation. No production change is yet authorized.

**Exit.** A/B measurement is monotone across all three divisions, exact
Farkas/DL evidence checks pass, deep input returns without recursion abort, and
the retained arithmetic fuzz suites execute nonzero cases.

### A6 — Close proof-production errors and evidence gaps (`TODO`, P1)

**Why now.** Definitive answers without checkable evidence violate the product's
core direction even when verdicts are sound.

**Next slice.** Fix the two QF_NIA `IntPow2` production errors first. Then use
route provenance—not query syntax alone—to split the 38 QF_BV bare UNSAT rows
and the broader arithmetic/string-sequence proof gaps.

**Exit.** Zero production errors; every newly credited certificate passes its
own independent checker; text-only recheck, arena-backed check, Lean
reconstruction, and bare-result counts remain separate fields.

**Stop.** Never relabel arena-backed checking as serialized proof replay or
generate proof credit through query-only re-derivation.

### A7 — Finish route observability before searched policy (`TODO`, P1)

**Why now.** `RouteTrace::to_json` landed, but the bench path and quantifier
preamble are incomplete. The proposed exploration tracker also incorrectly
placed T3.5 before its own G1 phase-3 gate.

**Required order.** Accept or revise the blocking ADRs; complete T0.2 route
registry; complete T0.6 recorder sites and `solve_explained`; finish T0.1 bench
persistence; add T2.5 public-corpus coverage; run T2.3/G1; only then consider
T3.5 policy-v0 equivalence.

**Exit.** Every registered route has a stable ID, the representative corpus
covers the catalogue or records explicit gaps, legacy dispatch replays exactly,
and G1—not enthusiasm—decides whether searched policy proceeds.

**Stop.** The exploration track remains proposed and may not preempt A2–A6.
See [`docs/plan/exploration-track/`](docs/plan/exploration-track/README.md).

### A8 — Implement SMT-LIB ordered command/event capture (`TODO`, P2)

**Why now.** The checked conformance matrix has six absent command families,
seven accepted no-ops, and zero interactive textual-session rows.

**Next slice.** Accept or revise ADR-0342, then implement S1 capture-only ordered
command/event IR with scoped declarations/definitions, reset epochs, exact query
snapshots, immediate options, and atomic continued errors before rendering.

**Exit.** The registered 14 invariants and 20 fixtures/107 commands pass through
the product path; malformed commands cannot partially mutate session state.

**Stop.** Do not add isolated output helpers and call them textual conformance.

### A9 — Restore official Lean execution and shrink the prelude (`TODO`, P2)

**Why now.** The local host currently has neither `lean` nor `elan`; remote
70/70 attestation remains open; seven ledger rows are already classified as
derivable theorems.

**Next slice.** Provision the checksum-pinned Lean 4.30 executable, prove it
runs outside the repository working directory, obtain the remote 70/70 result,
then replace the seven derivable axioms with theorem terms in dependency order.

**Exit.** Kernel tests, official Lean, generated ledger counts, declaration
order, parity docs, and mutation controls all pass; no hard-coded old count
survives.

**Stop.** Do not widen into String literals, quotient computation, or broad
ecosystem claims during this bounded trust-reduction slice.

### A10 — Build the SMT-LIB product surface after S1 (`TODO`, P2)

**Why now.** Production replacement requires more than solver depth. Once A8
freezes session semantics, add canonical response rendering and the missing
command families in dependency order.

**Next slice.** Use the generated conformance matrix to choose the first absent
family whose semantics and reset/scoping behavior are already representable.

**Exit.** End-to-end textual fixtures compare ordered outputs and state changes,
errors remain atomic, and API helpers and text mode share one semantic core.

### A11 — Make worktree and build-cache retirement routine (`WIP`, P2)

**Why now.** Accumulated per-worktree Cargo targets and the agent-target cache
filled the filesystem until a valid post-merge build failed at 585 MiB free.
The bounded cleanup recovered about 885 GiB without deleting dirty or unmerged
work, but the same failure will recur without a documented retention loop.

**Next slice.** Add a read-only inventory command or script that reports each
worktree's branch, dirty/merged state, target size, last activity, and safe
cleanup classification. Document an operator procedure that uses `cargo clean`
before worktree removal and requires explicit review for every dirty, unmerged,
detached, or cache-tag-missing path.

**Completed checkpoint.** The manual bounded cleanup and post-A3 retirement
proved the safety procedure for clean merged worktrees and reproducible Cargo
targets. The later authorized cleanup salvaged inactive dirty deltas, removed
the inactive checkouts, and retired the merged A3 targets. On 2026-08-12 all
refs were captured in a verified external Git bundle before old local/remote
branches and salvage stashes were removed. Only clean `main` is registered and
published. Automation and fixture coverage remain open.

**Exit.** The inventory is deterministic and tested against dirty, merged,
unmerged, detached, missing-target, and malformed-cache fixtures. A dry run
identifies disposable bytes without mutation; cleanup requires explicit exact
targets and preserves branches and live work.

**Stop.** Never recursively delete a worktree root, infer safety from age alone,
or remove dirty/unmerged state to meet a free-space target.

## Workstream state

| Workstream | State | Current boundary / next action |
|---|---|---|
| Integration and gates | `DONE`; 2026-08-12 | Linear A5 through `4b6b76555` is on `main` by conflict-free fast-forward. Integrated code, frontier, CAS, rustdoc, Glaurung, resource, resume, Lean, and parity gates are green; volatile frontier timings were not credited. Verify the remote ref before resume; hosted CI is separate. |
| Arithmetic deadline reliability | `DONE` | Shared deadline, CAD polls, LRA ceilings, bounded DL probing, exact resume identity, and six fresh retained divisions are complete; see the 2026-08-06 closure note. |
| Full-library measurement | `WIP`; A2 readiness `DONE` | The R1--R5 readiness stack is integrated by `8ed5ad089` and focused/aggregate/scoped/topic/full-main green; the real registered offline-build smoke passed. No live run, preparation root, or launch authority exists. A later live C0/F2 step requires separate review. |
| QF_NIA breadth | `WIP`, yielded | Current clean result remains 34/200 versus 89/200. Reconstruction, large-core deletion, relevance activation, and bounded clause-estimate attribution are closed negatively without production solver code. The final diagnostic failed its exact pipeline-boundary record gate; no mechanism or 200-row run is authorized and the 64,000,000 ceiling remains. Move to A4 unless independent new NIA evidence appears. |
| QF_UFLIA breadth | `WIP`, yielded | Historical 94/180 remains; the exact-commit restart produced 93/200 because one SAT case is wall-clock unstable. No sidecar or new result was credited. |
| LRA/IDL/RDL | `WIP`; V2 failed | QF_LRA passed; QF_IDL lost two decisions. Replay confirmed both. B1 failed and was removed; G1 found a nearby existing DL boundary. Preregister separate follow-ups; QF_RDL is forbidden. |
| QF_BV/QF_SLIA/UF/QF_ABV | `WIP`, strong selected cells | Preserve current ledgers; do not prioritize small score gains above A2–A6. |
| Evidence and Lean reconstruction | `WIP` | A6 and A9; distinct certificate/check/reconstruction claims. |
| Route exploration | `BLOCKED` beyond catalogue work | Proposed track; T0.2/T0.6/T0.1/T2.3 precede T3.5. |
| SMT-LIB/API conformance | `WIP` | A8 then A10; S1 command/event IR first. |
| CAS parity | `BLOCKED` by deliberate pause | Wave-24 code `01d47334` and pause commit `245d8f25` are ancestors of current main. Do not start wave 25 until the user resumes it and retained specialized gate evidence is re-audited. |
| Consumer apps / verified systems | `WIP`, non-critical path | Existing EVM, verifier, property, reflection, and symbolic-execution slices remain useful; do not preempt A2–A7 without measured demand. |
| Foundational resources | `WIP`, separate content lane | Keep generated-resource gates green; record only project-level priority changes here. |
| Public documentation and examples | `DONE`, current comprehensive pass | Public/crate/consumer/prover/curriculum/contributor front doors are indexed; all 80 Cargo examples and the consumer 48-case aggregate are guarded. Corrected built/planned, Lean 4.30/offline quotient, strings/P2.7, proof assurance, `i128` LRA/Farkas, native-CDCL/BatSat, RUP-only LRAT, online combination/fallback, CAS-local-vs-solver evidence, route-specific FP/datatype/nonlinear/quantifier boundaries, optional EVM/verifier certificate fields, and source-comment UNSAT-proof overclaims. Source-backed guards require nonzero full-feature tests across cookbook, learner, contributor, foundational-resource, and rules docs. Generated authorities remain canonical; reopen only for concrete drift. |
| Worktree and build-cache hygiene | `WIP`, recovered | A11; only clean `main` is registered and published. A verified 2026-08-12 external Git bundle preserves the retired refs/stashes; all old branches, salvage stashes, inactive checkouts, and their large Cargo targets are removed. Next automate deterministic read-only inventory and exact-target cleanup classification. |

## Resume protocol

1. Read this file first. Do not reconstruct current priority from historical
   result notes, old status journals, branch names, or worktree age.
2. Verify live state:

   ```sh
   git status --short --branch
   git fetch origin
   git rev-parse HEAD origin/main
   git worktree list
   gh run list --limit 10
   ```

3. If `main` is dirty, diverged, or owned by another lane, create an isolated
   worktree from current `origin/main`. One writer, one branch, one worktree.
4. Select the first unblocked item in **Next Actions**. Read its detailed phase,
   ADR, result notes, foundational DAG implications, and named handoff before
   editing.
5. During iteration, run the narrowest relevant crate or script tests. Run the
   aggregate pre-merge gate once on the finished branch. Confirm nonzero test
   counts and retain real exit codes.
6. Commit and push owned paths only. Integration requires conflict preview,
   green branch gates, merge, green main gates, pushed main, and remote-ref/CI
   verification.
7. Update this file in the same bounded increment:
   - status and exact evidence;
   - next executable action;
   - blocker or stop condition;
   - committed/pushed/integrated/remote states separately.

For concurrency and resource rules, follow
[`docs/contributor-guide/multi-agent-operations.md`](docs/contributor-guide/multi-agent-operations.md).

## Planning rules

- **One mutable project tracker:** update this file only. Root `STATUS.md` is a
  pointer; do not create root `TODO.md`; subsidiary `STATUS.md` files may retain
  local historical evidence but may not claim project-wide priority.
- **Evidence outranks prose:** benchmark JSON/TSV, generated matrices, test
  output, Git objects, remote refs, and CI results determine status. Correct this
  file when they disagree.
- **Wrong verdicts preempt everything:** reproduce, root-cause, regress, and
  repair before breadth or performance work.
- **No false green:** a focused pass is not a full gate; a running job is not a
  pass; a process-free readiness artifact is not launch authorization; a
  local commit is not integration.
- **No journal growth:** result detail belongs in a dated note under
  `docs/plan/` or a committed benchmark artifact. Keep only the current state,
  ordered queue, and a short recent-change table here.
- **Decisions require ADRs:** public operators, rewrites, encodings, backends,
  evidence artifacts, logic fragments, or priority-changing architecture need
  the applicable research question and ADR resolved first.
- **Determinism and replay are product promises:** stable order, explicit seeds
  and limits, original-term SAT replay, and independent UNSAT checking remain
  mandatory.

## Durable detail map

- **Archived lane status** (43 lanes of the 2026-08-13→15 campaign, each with the
  next action it left behind): [`docs/plan/archive/README.md`](docs/plan/archive/README.md).
  `PLAN.md` carries only lanes with work in progress; a finished or cut-off lane
  keeps its file there verbatim and is restored by moving it back into
  `docs/plan/status/`.
- Short public implementation account: [`docs/PROJECT-STATE.md`](docs/PROJECT-STATE.md)
- Full plan index: [`docs/plan/README.md`](docs/plan/README.md)
- Foundation roadmap: [`docs/research/08-planning/roadmap.md`](docs/research/08-planning/roadmap.md)
- Foundational dependency DAG: [`docs/research/08-planning/foundational-dag.md`](docs/research/08-planning/foundational-dag.md)
- Open research questions: [`docs/research/08-planning/research-questions.md`](docs/research/08-planning/research-questions.md)
- ADR index: [`docs/research/09-decisions/README.md`](docs/research/09-decisions/README.md)
- Capability matrix: [`docs/research/08-planning/capability-matrix.md`](docs/research/08-planning/capability-matrix.md)
- Scoreboard and parity: [`bench-results/SCOREBOARD.md`](bench-results/SCOREBOARD.md), [`bench-results/PARITY.md`](bench-results/PARITY.md)
- Proof gaps: [`docs/plan/generated/proof-gap-matrix.md`](docs/plan/generated/proof-gap-matrix.md)
- SMT-COMP lane: [`docs/plan/smtcomp-full-library-workstream/README.md`](docs/plan/smtcomp-full-library-workstream/README.md)
- Lean implementation: [`docs/plan/lean-system-implementation-plan-2026-07-21.md`](docs/plan/lean-system-implementation-plan-2026-07-21.md)
- Exploration proposal: [`docs/plan/exploration-track/README.md`](docs/plan/exploration-track/README.md)
- CAS pause handoff: [`docs/plan/cas-parity-handoff-2026-07-22.md`](docs/plan/cas-parity-handoff-2026-07-22.md)

## Consolidation record

The 2026-08-05 consolidation removed two conflicting append-only root journals
and one subsidiary live tracker from active use. It corrected these stale
claims:

- CAS wave 24 was described as unpushed and unintegrated; its code and pause
  commits are both ancestors of current main.
- An August 1 shell-failure resume block remained active after later green CI
  and clean parity reruns.
- The reality summary still said seven measured parity divisions after the
  ledger reached eleven.
- The exploration tracker called T3.5 next while its own G1 gate blocked all of
  phase 3.
- Repository instructions disagreed about whether `PLAN.md` or `STATUS.md` was
  the mutable source.

The containing commit establishes this file as the only current project-level
authority. Historical claims remain reviewable through Git and the dated result
notes they cite.
