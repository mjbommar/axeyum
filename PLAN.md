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
**WIP**. Trusted surface, re-derived by `gen-lean-axiom-ledger.py --check`
rather than authored, 2026-08-19: `complex 0 · creal 0 · integer 0 · logic 0 ·
nat 0 · rat 0 · string 0 · real 30` — `real`, the axiomatized package, is the
only nonzero row. "Int reconstruction remains assumption-bearing" was true until
that day and is not.

**Declared is not reached; both are published**
([ADR-0509](docs/research/09-decisions/adr-0509-the-trusted-surface-is-measured-as-reached-not-only-declared.md)).
The 30 stay declared, reached by no shipped route. The package is kept as the
negative control those measurements are read against — delete it and no such
measurement can fail — now one assumed law over a constructed carrier
([ADR-0515](docs/research/09-decisions/adr-0515-a-negative-control-is-one-assumed-law-over-a-constructed-carrier.md)).

Exact pushed repairs for the A5 (linear-arithmetic), A3 (string/integer) and
A2 (stale-branch) streams — commit-by-commit, with the non-credited partial
streams retained — are in the
[A5/A3/A2 repair journal](docs/plan/a5-a3-repair-journal-2026-08.md). The
current release returns typed `unknown` on each former abort trigger; A3 yields
to A4.
### A1 arithmetic resource closure — `DONE`, archived

The two measured resource defects and their pushed repairs are in
[`docs/plan/archive/30-a1-a2-completed-programme-items.md`](docs/plan/archive/30-a1-a2-completed-programme-items.md).
Moved 2026-08-19: it is closed work, and this file is for what is true
now. Nothing was deleted.

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
| 2026-08-21 | (pending) | All 35 dominance audits re-run at `496288979` from a `lane-snapshot` tree; `dominant_unsat` 262 / 324 → **269 / 326**, `lean-reconstruction-gap` 15 → **10**, certified/checked 278 → 280. Four rows moved: QF_NRA cvc5 (+3, `RealProduct`×2 + `MonomialBound`), QF_S (+2, `StringLength`), QF_NRA synthetic (+2, the prelude-warm instrument fix, proved by an A/B with the warm suppressed at two revisions), QF_SEQ (a `parse-error` became `sat`, no dominance change). `gen-proof-gap-matrix`, `gen-proof-gap-shape-census`, `gen-dominance-scoreboard` and `gen-autogenesis-baseline` regenerated; the six moved markers in `PROJECT-STATE.md` and the gap analysis renumbered **with** the account of what moved them, and the ten remaining Lean-reconstruction gaps recorded one line each with the fragment's own decline reason rather than the fallback route's. |
| 2026-08-21 | `a3799dca2` | **`QF_FP/fp_misc`'s "timeout" was an unmemoized DAG walk in the classifier.** `array_bv_abs::abstract_term` re-explored shared subterms once per path; 8/8 `gdb` samples sat in it. Memo + visit budget, each guard mutation-verified to kill exactly one test: **124.7 s timeout → 314 ms**, 4,194,309 visits → 4,365 over 5,762 nodes. QF_FP `timeouts 1 → 0`, certified/checked 15/16 → **16/16**; `dominant` stays 15/16 and the row now declares `bit-blast` instead of `timeout`, because `887b52e64` withdrew its term-level FP route on purpose. Also measured and pinned: `QF_BVFP/Float-no-simp3-main` is not the "evidence exceeds 120 s" it was recorded as — its reduction certificate is `proved` in **28.3 ms** and is withheld only by `produce_evidence`'s blanket "timeout set → skip", whose deadline covers the SAT search and none of `lower_terms` / `tseitin_encode` / `check_drat` / LRAT. QF_FP and QF_BVFP audits re-run at `a3799dca2`; `proof_errors` 4 → **3**, certified/checked 280 → **281**, and the four moved markers in `PROJECT-STATE.md` and the gap analysis renumbered with the account of what moved them. |
| 2026-08-21 | `fc191b3e5` | Full stable statement-survival atlas is preregistered before the one authorized comparison pass |
| 2026-08-21 | `7edebb579` | Full Nat/Int atlas classifies all 9,839 v4.30/v4.32.1 union names and isolates representation-wide drift |
| 2026-08-21 | `030d82adb` | First proof-isolated joint quotient/remainder reconstruction fails closed with a measured `propext` footprint |
| 2026-08-21 | `ed3a69efb` | Direct-dependency footprint audit is frozen before its one importer pass |
| 2026-08-21 | `2ae095f07` | The joint invariant's sole assumption carrier is localized to `Nat.sub_add_cancel` |
| 2026-08-21 | `d204ddd51` | Local primitive-recursive subtraction restoration is selected as the exact replacement |
| 2026-08-21 | `94b62795d` | The one missing primitive subtraction equation is bound proof-free |
| 2026-08-21 | `7c7bb1f54` | The private joint Euclidean invariant reconstructs twice with an empty footprint |
| 2026-08-21 | `bc529aab9` | Transparent public wrapper lift is preregistered before source execution |
| 2026-08-21 | `aded65e22` | Wrapper lift fails closed at opaque official division before kernel submission |
| 2026-08-21 | `47322738b` | Synchronized public quotient/remainder recursion is preregistered |
| 2026-08-21 | `653cd1518` | Exact public recursion compiles but fails its first kernel gate through generated `_unary` |
| 2026-08-21 | `54cdc1375` | Primitive bounded induction is frozen as the generated-recursion replacement |
| 2026-08-21 | `cf41dba10` | Primitive induction removes generated recursion but retains one explicit `propext` footprint |
| 2026-08-21 | `75c7668c2` | The complete 22-dependency footprint audit is preregistered before execution |
| 2026-08-21 | `6e5779f0f` | One importer pass localizes the public proof footprint to `Nat.div_eq` and `Nat.mod_eq` |
| 2026-08-21 | `5599832dd` | Public equation closure shows quotient fuel congruence clean and proposition/remainder wrappers contaminated |
| 2026-08-21 | `c108486b4` | Target coprime shortcut declines through quotient and proposition axioms |
| 2026-08-21 | `8e78f75e9` | Reusable ordered batch auditor reports identities, dependencies, and kernel footprints without proof rendering |
| 2026-08-21 | `7e20d5288` | Seven subtractive gcd convenience roots all decline and expose an exact 17-name dependency union |
| 2026-08-21 | `15398b7a9` | Fourteen-root descent splits seven clean helpers from seven gcd/proposition carriers |
| 2026-08-21 | `327e4952c` | Pruned gcd route exposes the generated private recursion equation carrier |
| 2026-08-21 | `748a3457b` | Generated gcd equation carrier narrows to three previously unmeasured dependencies |
| 2026-08-21 | `656538cf9` | `WellFounded.Nat.fix_eq` is isolated as the sole generated gcd assumption carrier |
| 2026-08-21 | `a3bc37896` | One direct public `Nat.gcd_def` compilation declines in both opaque constructor branches |
| 2026-08-21 | `a87967970` | Exact Mathlib 4.30 extended-gcd root audit is bound to the clean `s5` export environment |
| 2026-08-21 | `2fd42c900` | Official `Nat.gcd_eq_gcd_ab` declines with a measured Quotient-plus-`propext` footprint |
| 2026-08-21 | `f611d3ffb` | All twelve direct extended-gcd theorem dependencies are frozen before rereading the sealed stream |
| 2026-08-21 | `550badedf` | Eight clean helpers split from three contaminated xgcd coefficient roots and `eq_self` |
| 2026-08-21 | `70eff2366` | Seventeen novel xgcd dependencies are preregistered while identity-matched clean `Eq.symm` is reused |
| 2026-08-21 | `17cf9888b` | Imported xgcd projection routes close while empty-footprint `Nat.gcd.induction` remains available |
| 2026-08-21 | `9485270f6` | One direct `rfl` reconstruction of public `Nat.xgcd_val` is frozen before source execution |
| 2026-08-21 | `9f135d4f0` | The first execution ends before elaboration at Lean's package-root boundary without retry |
| 2026-08-21 | `7f0f25baa` | Corrected rooted execution binds exact temporary paths and two-sided checkout cleanliness |
| 2026-08-21 | `1e74d4601` | Full-status preflight preserves three pre-existing untracked sources and performs zero execution |
| 2026-08-21 | `3cf835d15` | The exact three-file `s5` baseline is bound before the baseline-preserving projection run |
| 2026-08-21 | `de5264b64` | A twice-imported `rfl` theorem still reaches `propext`, closing the public xgcd coefficient surface |
| 2026-08-21 | (pending) | Generic official-gcd balanced Bézout bypasses public quotient and binds clean gcd leaves as specialization parameters before execution |
| 2026-08-21 | (pending) | First generic balanced-Bézout source stops at three compiler diagnostics with zero export/import and exact baseline cleanup |
| 2026-08-21 | (pending) | Corrected generic balanced-Bézout source binds direct Nat.mod equations and coefficient-scoped transport before execution |
| 2026-08-21 | (pending) | V2 stops at dependent-conditional and definitional-shape diagnostics with zero export/import and exact cleanup |
| 2026-08-21 | (pending) | V3 binds positivity reduction, normalized congrArg types, and induction-hypothesis change before execution |
| 2026-08-21 | (pending) | V3 compiles but first audit localizes Quotient axioms to funext/conditional rewriting and propext to ring normalization |
| 2026-08-21 | (pending) | Pointwise V4 quotient witness forbids binder rewriting, function equality, public division, and ring before execution |
| 2026-08-21 | (pending) | Pointwise V4 quotient witness reconstructs twice with byte-identical empty footprints and seals exact evidence |
| 2026-08-21 | (pending) | Explicit four-Nat balanced-Bézout Euclidean update is frozen before its one authorized compilation |
| 2026-08-21 | (pending) | Explicit update compiles but its first audit retains one `propext`; exact nine-dependency descent replaces source guessing |
| 2026-08-21 | (pending) | Exact nine-root dependency-local audit is frozen before one non-rendering sealed-stream read |
| 2026-08-21 | (pending) | One sealed-stream read localizes the V1 footprint exactly to `Nat.mul_assoc` and `Nat.right_distrib` |
| 2026-08-21 | (pending) | V2 injects exactly two clean leaf contracts while retaining the explicit balanced-Bézout update chain |
| 2026-08-21 | (pending) | Parameterized V2 Euclidean update reconstructs twice with byte-identical empty footprints and no contaminated leaves |
| 2026-08-21 | (pending) | Primitive-induction target-owned replacements for the two contaminated multiplication leaves are frozen before execution |
| 2026-08-21 | (pending) | Both target-owned multiplication leaves reconstruct twice with empty footprints, closing the V2 parameter gap |
| 2026-08-21 | (pending) | Exact three-theorem wrapper is frozen to close the balanced-Bézout Euclidean update before gcd induction |
| 2026-08-21 | (pending) | Closed Euclidean update reconstructs twice empty-footprint with exactly the accepted update and two leaf dependencies |
| 2026-08-21 | `99ea0b1e7` | Clean official-gcd balanced-Bézout induction is frozen with only two gcd computation leaves still explicit |
| 2026-08-21 | `c8fae7455` | Generic official-gcd balanced-Bézout reconstructs twice with an empty footprint and preserves zero specialization authority |
| 2026-08-21 | `0e23382f8` | Dependency-bound closure freezes exact accepted zero-left and successor gcd identities before implementation |
| 2026-08-21 | `496e916b8` | First closed specialization declines at an exact `WellFounded.fix` type-shape mismatch with zero retry or theorem credit |
| 2026-08-21 | `7550b31c4` | Proof-free `WellFounded.fix` closure audit is frozen before code or stream access |
| 2026-08-21 | `96a6a4c34` | Twice-reproduced audit selects official-kernel gcd-leaf reconstruction over native representation transport |
| 2026-08-21 | `3e6373de5` | Pointwise official-representation gcd zero-left reconstruction is frozen before compilation |
| 2026-08-21 | `0a73f8458` | Source compiles but unbounded 340 MB export hits the unchanged two-million-record importer ceiling |
| 2026-08-21 | `b866b31ee` | Exact theorem-root exporter retry is frozen with unchanged proof and importer limit |
| 2026-08-21 | `dfcff00d1` | Root-selected zero-left gcd reconstructs twice with an empty footprint and only its local model dependency |
| 2026-08-21 | `fb1a3613e` | Official-representation successor gcd root export is frozen without double-counting the native-support theorem |
| 2026-08-21 | `9ec4bcfa1` | Official-representation successor gcd reconstructs twice empty-footprint, completing the leaf pair for composition |
| 2026-08-21 | `1d03f09b3` | Five-stream official-kernel balanced-Bézout composition is frozen before implementation |
| 2026-08-21 | `f1e0edb57` | Dedicated official-kernel driver compiles Clippy-clean and passes the full importer test suite without stream execution |
| 2026-08-21 | `47343f64f` | First official-kernel invocation declines at missing recursive `Acc`; reverse composition base is selected with zero theorem credit |
| 2026-08-21 | `2d62fc4a7` | Generic-kernel-base reversal is frozen with the same five streams and zero downstream authority |
| 2026-08-21 | `c4bf44f90` | Reverse-direction driver compiles Clippy-clean with generic composition removed and no execution |
| 2026-08-21 | (pending) | First generic-base run finds `Nat.mod_lt` already present; exact reuse replaces a zero-addition composition |
| 2026-08-21 | `7e4af7cde` | Exact `Nat.mod_lt` identity reuse and the remaining three-root composition are frozen before code or stream access |
| 2026-08-21 | `384826f41` | Exact-reuse driver compiles Clippy-clean, passes the full importer suite, and clears both full remote push gates without stream execution |
| 2026-08-21 | (pending) | Exact `Nat.mod_lt` reuse closes official-representation balanced Bézout twice with byte-identical empty-footprint evidence |
| 2026-08-21 | `3c2a2b29e` | Generic coprime-factor cancellation is frozen over an explicit balanced-Bézout parameter before source construction |
| 2026-08-21 | (pending) | First generic cancellation source stops before elaboration at an unbound local module and restores the exact baseline |
| 2026-08-21 | `cce486823` | Self-contained cancellation V2 freezes the same proof with only its four-natural certificate definition inlined |
| 2026-08-21 | (pending) | Self-contained cancellation reconstructs twice deterministically but localizes its rejected footprint to `propext` |
| 2026-08-21 | `efe97708a` | All seventeen direct cancellation dependencies are frozen before one non-rendering sealed-stream audit |
| 2026-08-21 | (pending) | One exact audit splits eleven clean cancellation dependencies from six `propext` carriers |
| 2026-08-21 | `4c81f2ce2` | Residual cancellation freezes direct witness replacements and leaves exactly three explicit theorem parameters |
| 2026-08-21 | (pending) | Residual replay accepts the additive witness but retains one unexpected multiplicative-witness `propext` edge |
| 2026-08-21 | `352a9c12a` | The multiplicative witness's exact three theorem dependencies are frozen before one same-stream audit |
| 2026-08-21 | (pending) | Same-stream audit identifies `Nat.mul_assoc` as the witness's sole direct assumption carrier |
| 2026-08-20 | `9eb81822f` | Isolate persistent pre-push worktree metadata from the caller lane and register the two-sided control |
| 2026-08-20 | `24b16642e` | Confirm the repaired hook against a live Rust push with unchanged caller state and a clean exact-SHA gate checkout |
| 2026-08-20 | (pending) | The string family's first re-derivable UNSAT artifact beyond word-clash/regex-emptiness: `Evidence::UnsatStringLength` abstracts every string term to an integer length keyed on its SOURCE NAME, names the five theory lemmas the argument uses, and closes with one nonnegative combination per case-split branch. The checker is two stages — bind each lemma to the conjunct that licenses it, then re-derive the arithmetic — and is arena-free, because a string script's flat view is the bounded packed-BV encoding rather than the query. 23 guards mutation-checked; two killed nothing and were fixed rather than kept (one was dead code the command allow-list already covered, one had no multi-`check-sat` fixture). Also: `diagnose_evidence` reported the ARENA front door for string files, i.e. a query nobody solves — it now reports the text front door too, and agreed with the dominance audit for the first time. |
| 2026-08-20 | `0797719a7` | Rational operands no longer defeat algebraic field arithmetic; the NRA `sat` witness replays and the evidence route matches the decision route |
| 2026-08-20 | (pending) | `Evidence::UnsatRealHandelman`: multi-term Handelman/Positivstellensatz refutations for `QF_NRA`, with case splitting over a top-level disjunction and polynomial multipliers on asserted equalities. Certifies the three corpus rows `nra_product_cert` declined by design. 15 guards mutation-checked; 14 kill at least one test, and the fifteenth (the producer's own self-check) kills nothing and is documented as such at the function rather than pretended to be a guard. Three checks that provably could not fail were deleted instead of kept. `NamedPoly` is now shared with `nra_product_cert` rather than reimplemented — two name-keyed polynomial types would be two chances to disagree about what `a*b` means. |
| 2026-08-20 | (pending) | `Kernel::whnf_core` is memoised — the second of Lean's two reduction caches (`m_whnf` beside `m_whnf_core`), which this kernel never had. `build_creal_prelude` 33.0 s → 13.0 s, template reuse 0.41 s → 0.15 s. Pure memoisation: same key discipline as the δ-free memo, split on `has_fvars`, cleared by `push`/`pop` and by environment revision, closed half covered by the `reduction_ctx_reads` tripwire. Six guards mutation-checked, each killing at least one test and four killing exactly one; a seventh looked unreachable and a `debug_assert_eq!` proved it is not, which is what the comment on it now records instead of the argument that was wrong. Root cause recorded: `502184d3f` did not slow the kernel down, it switched the literal-`Nat` acceleration ON for the first time, because `build_nat_binop_table` gates on `Bool`'s constructor order. |
| 2026-08-20 | (pending) | `Kernel::reduce_nat_binop` moves out of the δ-free normaliser to Lean's two call sites — `whnf_core`'s δ loop (Lean `whnf`, `type_checker.cpp:670`) and `lazy_delta_step` (Lean `lazy_delta_reduction`, `:978`) — both under Lean's `!has_fvar` guard. `build_creal_prelude` 12.99 s → 6.79 s (median of three interleaved rounds), against 8.71 s before the acceleration was ever switched on. Measured separately: Lean's placement *without* the guard is 12.12 s, so the guard is the entire win and the placement is faithfulness, not speed. Identification unmoved — kernel lib 399/0; full kernel crate 609 passed / 1 failed, the one (`real_lean_wellfounded_elaborator_divergence`) failing byte-identically on an unmodified `HEAD` and being a real-Lean *elaborator* rejection rather than ours; solver `reconstruct::` 312/0; clippy 618/618 targets 0 diagnostics; prelude-reuse differential `compared=8 failures=0`; axiom ledger `axreal=30` and all others 0. Three new tests in `tests/nat_literal_arithmetic.rs` pin both call sites and both guards on an environment where the accelerated answer and the declared body disagree; each guard mutation kills exactly one. ADR-0536. |
| 2026-08-20 | `b5c4bb48b` | Binder-info-insensitive kernel type-shape identity with adversarial controls |
| 2026-08-20 | `24b16642e` | r082 overlap probe classifies kernel-compatible and structurally different types |
| 2026-08-20 | `8dbd18c82` | Required Nat theorem closure census isolates a structurally unblocked first replay slice |
| 2026-08-20 | `9caac0bf5` | First probe-local checked native Nat theorem slice composes over the imported r082 kernel |
| 2026-08-20 | `b7573a525` | ADR-0523 fixes theorem-only identity-gated completed-clone composition as the public V1 boundary |
| 2026-08-20 | `bdc9bf1c9` | Public checked theorem-slice composition API publishes only a fully admitted owned clone and replayable receipt |
| 2026-08-20 | `75aa21d1a` | Composition boundary controls cover unsupported kinds, type mismatch, binder metadata, free variables, partial staging, and receipt mutation |
| 2026-08-20 | `0bcbe935d` | The r082 public-API probe exposes the exact source closure and canonical composition receipt identity |
| 2026-08-20 | `c17b7e65b` | Receipt V2 records translated definitional equality as attempt-only reuse authority and moves the r082 blocker to missing `Exists` |
| 2026-08-20 | `fced2b166` | Receipt V3 atomically reconstructs a demanded singleton inductive and advances the r082 root to missing definition `Nat.mul` |
| 2026-08-20 | `acade2a45` | Receipt V4 target-checks exact demanded definitions and advances the r082 root to the `Bool.rec` branch-order seam |
| 2026-08-20 | `502184d3f` | Native Bool adopts official Lean constructor order with kernel-prelude consumers migrated |
| 2026-08-20 | `012c6b4f6` | Solver reconstruction preserves semantic false/true branches under the official order |
| 2026-08-20 | `866add778` | Official-order fixtures and golden reconstruction bodies pass the authoritative pre-push gate |
| 2026-08-20 | `a5a111498` | Native `Nat.mod_lt` proves Lean's general positive-denominator contract and migrates GCD/Bezout consumers |
| 2026-08-20 | `ac33a0a2d` | Named compatibility diagnostics bind `Nat.mod_lt` translated definitional equality and expose `Acc` next |
| 2026-08-20 | `3d466b45c` | Receipt V5 reconstructs only canonical native `Acc` exactly and exposes `Nat.div_mod_exec` target type mismatch |
| 2026-08-20 | `f099a4a37` | Semantic admission diagnostics isolate the 92-declaration division mismatch and the missing `Nat.dvd_mod_iff` consumer |
| 2026-08-20 | `a12d44858` | Lean export audit reports canonical theorem identities, direct dependencies, and kernel-derived axiom footprints |
| 2026-08-20 | `dd79317c5` | Proof-isolated theorem-pack composition replays two axiom-free official `Nat.mod` computation equations into r082 |
| 2026-08-20 | `667201932` | Receipt-backed checked specialization admits constructive target `Nat.dvd_mod_iff` with an empty footprint and native type shape |
| 2026-08-20 | `7e6e28c1f` | Explicit target-owned theorem leaves cut only compatible axiom-free source proofs and replay from a distinct receipt |
| 2026-08-20 | `5fb817301` | Real r082 leaf probe removes `Nat.div_mod_exec` with two cuts and exposes assumption-bearing `Nat.gcd_succ` next |
| 2026-08-20 | `91d7df736` | Dependency-ordered mixed composition moves exact `Nat.fib` and the established recurrence into the axiom-free native gcd kernel |
| 2026-08-20 | `8403e6f65` | Twice-reconstructed native Fibonacci coprimality theorem closes with the exact planned dependency set and exposes the official/native gcd semantic bridge |
| 2026-08-20 | `f94489c74` | Pointwise well-founded fuel congruence reconstructs axiom-free official `Nat.gcd_succ` and advances the checked target through `Nat.dvd_gcd` |
| 2026-08-20 | `9e83ab67a` | All seven planned Fibonacci gcd/divisibility support roots compose and replay together in the official r082 target |
| 2026-08-20 | `d12736b63` | Exact official Fibonacci coprimality reconstructs four times with an empty footprint and sealed deterministic evidence |
| 2026-08-20 | `b44bf0ecb` | Dependency-bound theorem receipts require exact sorted premise names and canonical declaration identities |
| 2026-08-20 | `b55bc977e` | Two fresh full audits preregister the exact eight-premise authority for the official Fibonacci receipt |
| 2026-08-20 | `169aab71b` | Two fresh official reconstructions issue and replay one exact dependency-bound Fibonacci theorem receipt |
| 2026-08-20 | `d5aed52ff` | Distinct registered admission preserves exact direct and transitive dependency identities without weakening isolated receipts |
| 2026-08-20 | `3f96b5463` | Crash-safe exact Fibonacci coprimality admission makes one descendant ready and reproduces from a clean worktree |
| 2026-08-20 | `e06115972` | Sealed admission evidence binds the exact post-recovery fact and frontier state |
| 2026-08-20 | `6902efad7` | Historical child qualification accepts only the selected axiom-free settled child while retaining its deferred sibling open |
| 2026-08-20 | `eca29a441` | Proof-free r091 qualification isolates Fibonacci addition, coprime-factor cancellation, and gcd extensionality obligations |
| 2026-08-20 | `989e6242e` | One support-first construction and six-submission, zero-retry ceiling are frozen before implementation |
| 2026-08-20 | `f8c7febc6` | Paired native induction reconstructs Fibonacci successor addition twice and composes it into the exact r091 target kernel |
| 2026-08-20 | `1f9f01b3a` | Immutable first-support observation and mutation-tested checker preserve the empty-footprint, zero-target-credit boundary |
| 2026-08-20 | `3acb61ef5` | Balanced-Bézout coprime-factor cancellation reconstructs twice and fails closed at the exact official/native Euclidean seam |
| 2026-08-20 | `a29b99e15` | Immutable second-support evidence and mutation controls retain the typed composition decline without target credit |
| 2026-08-20 | `62858ff72` | Support-only bridge plan freezes a constructive official Euclidean and balanced-Bézout route with zero target authority |
| 2026-08-20 | `c4f133a00` | Official quotient and remainder computation roots import with stable identities and empty footprints |
| 2026-08-20 | `a21f42b06` | Generated proof-isolated capsule exposes only the exact Euclidean statements and audited identities needed by a fresh context |
| 2026-08-20 | `cf1a203d1` | Current-stable comparison plan corrects the target to Mathlib/Lean v4.32.1 and freezes one proof-free extraction |
| 2026-08-20 | `f91670cd9` | Stable comparison classifies all 240 selected statements, with 234 structurally identical and six exact drifts |
| 2026-08-20 | `01d54044a` | **Certified 278/324 (85.8%)**, from 267/327 (81.7%) this morning. Timeouts 10 -> 4, `proof_errors` 10 -> 4. Four of the recovered rows were emitters that had returned the CORRECT answer and were billed 31.9s of shared prelude construction inside a 15s cap; `prelude_warm_ms` is now a visible artifact field instead of one instance's bad luck. |
| 2026-08-20 | `5a25f247a` | **Four DAG walks were exponential today, all the same bug written four times** — `contains_quantifier`, `lower_derived_bv`, `collect_enumerable_symbols_rec` (1.28e10 calls in 90s), `collect_nested_registrations`. `Float-no-simp3-main` >300s -> 19.4ms, `fp_fromsbv` 45s -> 3.8ms. The `certify.rs` memo deliberately does NOT collapse occurrences for the quantified-bit budget: that is a tree-sum, and collapsing it would undercount an exponentially shared quantifier nest and let a query past a budget check it cannot satisfy. |
| 2026-08-20 | `71f1c29a0` | **Second Lean reconstruction**: the degree-2 Positivstellensatz product, `mul_nonneg` -> `lt_of_le_of_lt` -> `lt_irrefl`, kernel-checked over `CReal` (trusted surface 0) with a test naming the carrier. A strict factor is minted as `0 < e` — what the query says — and weakened with `le_of_lt`, rather than minting `0 <= e` directly: both are sound, but the latter puts a proposition in the module the query never states. |
| 2026-08-20 | (open) | The two `BvAlternationCounterexample` rows still time out. The 64 MiB cap refuses their 625 MB / 2.38 GB modules but bounds what is RETURNED, not construction — they spend the budget building a module that is then thrown away. Bounding construction means threading a budget through every renderer. |
| 2026-08-20 | `cfc5f8078` | **A Lean module too large to be useful is now refused, not returned.** `BvAlternationCounterexample` was returning `Ok` with 2.38 GB held as one `String`, on a box whose kernel OOM-killed a live session on 2026-08-17. Threshold measured across 262 recorded modules: median 3,169 B, largest legitimate 28.6 MB, pathological 625 MB / 2.38 GB — 64 MiB sits ~2x over the first and 10-37x under the second. Three rounds of mutation testing each found a real hole: deleting the guard left everything green (no fixture reached it), the threshold test hardcoded the cap so raising it would not fail, and clippy correctly flagged the result as assertions on constants — they are now `const` assertions, so the BUILD fails. Bounds what is RETURNED, not the peak; the code says so. |
| 2026-08-20 | `9824cbff2` | **A timeout row now says which ROUTE it was attempting.** Nine of ten timing-out instances landed in one phase and were three unrelated failures — exponential blowup, a CORRECT decline arriving 35s late, and a success emitting 2.4 GB — indistinguishable in the JSON, with the second scored as a proof-production error while the emitter behaved correctly. `timeout_phase_detail` carries the `ProofFragment`, recorded before the attempt; it costs microseconds against a 35-second prelude. |
| 2026-08-20 | `e14a13b5d` | **Two DAG walks were exponential because they recursed as trees.** `contains_quantifier` made 9.8e9 calls scanning a QUANTIFIER-FREE query for quantifiers on a 2,971-node arena; `lower_derived_bv` made 2.24e9. Neither is new — `lower_bv.rs` is unchanged since June — they were latent behind routes nothing reached until `887b52e64` correctly made FP rows decline `BvDefinedEnum`. `fp_misc` >40s -> **0s**, `fp_fromsbv` >40s -> 45s, both now DRAT-certified. `Float-no-simp3-main` decision is 4.6ms but its evidence still exceeds 120s — NOT fixed, left open. |
| 2026-08-20 | (open, NOT mine) | **`lra_ctx()` builds a 35s CReal prelude before the route knows it will decline.** Measured: `cli__regress0__arith__div.01` returns the SAME decline message it always did, 35s later, of which `build_creal_prelude` is 35.23s. Two commits compound: `a6ee37c6a` moved the carrier (2.6ms -> 4.6s) and `502184d3f` — a 31-line commit that only swaps `Bool`'s constructor order — made prelude construction **4.7x slower** (6.9s -> 32.5s). Almost certainly an iota-reduction ordering accident, not a necessary cost. |
| 2026-08-20 | (open, NOT mine) | **`BvAlternationCounterexample` returns `Ok` with a 2.4 GB module held in memory**, on a box that OOM-killed a live agent session on 2026-08-17. `bug802` 625 MB, `small-pipeline-fixpoint-3` 2.38 GB. Introduced by `8173bfc1b` 41 minutes AFTER the audit that recorded these as "declined fast", so the baseline never saw it. A route that succeeds at 2.4 GB is worse than one that declines. |
| 2026-08-20 | (open) | **The audit's 15s cap cannot distinguish three different failures.** All eight timing-out rows land as `trust_holes: ["timeout"]` with `lean_error: null` — an exponential blowup, a CORRECT decline arriving 35s late, and a success emitting 2.4 GB are indistinguishable in the JSON. The second is scored as a proof-production error while the emitter behaved correctly. |
| 2026-08-20 | `544778da6` | **Monomial bounds certified: three more corpus rows, seven QF_NRA files for the day** (`ones`, `mult.01`, `simple-mono-unsat`). Even exponents need no bound (`d^2 >= 0` for every real `d`); odd ones on an unbounded variable make the monomial unbounded below, so parity is carried and re-derived. Lower bounds must be NONNEGATIVE — `(-2)*(-3) = 6` is not a lower bound for `a*b`. **Three bugs found by instrumenting rather than guessing**: the disjunction handler was UNREACHABLE (a 2-arg `BoolOr` destructures as `[lhs, rhs]`, fell through the comparison `match` and hit an unconditional `continue`); the checker was `fresh == *certificate`, which subsumes every other guard so mutation testing showed the arithmetic killing NOTHING; and stage 1 then masked stage 2, so each stage-2 guard needed a forgery the query genuinely supports. 8 guards, each killed by exactly one test. |
| 2026-08-20 | `e75ccc821` | **Refreshed 4 of 35 audits; certified moves 267/327 (81.7%) -> 273/323 (84.5%).** The number I quoted this morning to justify a work item is now partly measured rather than inherited. QF_S decides 87 -> 93, QF_SLIA 18 -> 25 — both strictly more than the committed audits recorded, the direction the stale-audit finding predicted. |
| 2026-08-20 | `(open, NOT mine)` | **A corpus file no longer parses**, found only by refreshing: `sat__regress0__strings__issue5542-strings-seq-mix.smt2` panics with `Ir(SortsDiffer(BitVec(100), BitVec(197)))` — it mixes `String` and `(Seq Int)` in one query and the two encode at different bit-widths. The committed audit records it as decided `sat` with a replayed model. The panic is in `parse_script`, before any solver or evidence code, so it is not from this lane's work. Second defect the audits were hiding, after `replace-find-base`. |
| 2026-08-20 | `(open, NOT mine)` | `cli__regress0__nl__issue3003`: `check_auto_explained` answers `sat` in 0.87 ms and `produce_evidence` answers `unknown` on the same query in the same tree. Confirmed not mine by disabling both new NRA producers and re-running — identical. The decision route and the evidence route disagree, which is the divergence class an independent NRA survey flagged the same day. |
| 2026-08-20 | `1f61b1605` | The `source_revision` stamp needed one fix to be usable, found by using it: `scripts/lane-snapshot.sh` extracts `git archive`, so the clean tree an audit most wants has **no `.git`** — the recommended way to get an unmodified tree was the only way to lose the sha. It now reads `.lane-ref` and records `source: git \| lane-snapshot \| none`, so a supplied sha is never mistaken for a measured one. |
| 2026-08-20 | `ae4f3edf0` | **Degree-2 Positivstellensatz certified: two more real corpus rows, four QF_NRA total today.** Two asserted lower bounds whose exact product is the polynomial a third assertion calls negative (`coeff-unsat-base`, `simple-mono`) — decided today by CAD, which is more machinery than the argument needs and emits nothing readable. Exact rational arithmetic over a NAME-KEYED polynomial, because `nra_real_root::MultiPoly` is private and keyed on arena-local `SymbolId`. **Strictness is the soundness argument**: `p >= 0` and `q >= 0` give `pq >= 0`, refuting `pq < 0` but NOT `pq <= 0` (satisfiable at p = 0); carried and re-derived, with a test in each direction since a rule that never refutes `<= 0` would satisfy one of them alone. `coeff-unsat` and `combine` need a product PLUS a linear step and are DECLINED with a test pinning the decline. 8 guards, 7 killed individually; the eighth is documented unreachable behind stage 1 rather than implied to be tested. |
| 2026-08-20 | `cbba2efa3` | **QF_NRA monomial divisibility certified — and unlike the QF_NIA one, this covers REAL CORPUS FILES.** `cli__regress1__nl__zero-subset` and `cli__regress0__nl__subs0-unsat-confirm` are refuted by "this product divides that one" and shipped as bare `Unsat(None)`; both now report `real-zero-product-unsat certified=true checked=true`. Factors carried by SOURCE NAME, not arena-local ids. **Placement was the bug, not the matcher**: hooked in after the route `match` it passed every unit test and fired on neither corpus file, because the `PureReal` arm returns through `produce_nra_evidence` first. A hand-parsed unit test could never have caught that; running the corpus file did. Worth recording against my own QF_NIA work, which I measured against all eight committed QF_NIA rows and which fires on **none** — they are `div`/`mod` and multivariate shapes it declines. |
| 2026-08-20 | `cbba2efa3` | Mutation testing needed two rounds again: 4 of 7 guards killed first time. Isolating stage-2 containment needed a certificate whose halves the query genuinely asserts but whose containment fails (`(= (* x x) 0)` vs `(not (= (* d e) 0))` — a SATISFIABLE query a checker without stage 2 would certify unsat); isolating the arm-drop needed a disjunct zeroing a SUM, which is a zeroing but not of a factor. One guard stays unkilled and the code says why: the empty-case check is unreachable behind stage 1 and becomes load-bearing only if stage 1 is loosened — `all()` over an empty list is vacuously true. |
| 2026-08-20 | `(pending)` | `lane-push.sh --retry N`. A push passed every gate in 205s and was then rejected — `cannot lock ref 'refs/heads/main': is at 4c7ad5e63 but expected 92fa6188a` — because main advanced DURING the hook. The fast-forward pre-check cannot close the window it opens. `--retry` re-merges the target and pushes again, and only on a lock conflict, so a genuinely failed gate still fails at once (they both exit 1 and their messages are hundreds of lines apart). The fixture moves the remote ref from inside a pre-push hook, and it caught a real bug in my own guard: GitHub says `cannot lock ref`, a local file remote says `incorrect old value provided`, and matching only the phrasing I had seen in production left the control green while the retry never fired. |
| 2026-08-20 | `6ae02f26c` | **All 35 dominance audits are stale, and one direction of the drift hid a capability regression.** I quoted "60 of 327 uncertified" to justify a work item; that number replays committed audits which record `logic`, `slice`, `timeout_ms`, a `version` integer — and **no sha, no date**. Every audit predates the newest solver-source commit, the oldest by 55 days. Newly certified but still counted bare: 20 of 31 string-family `bare-unsat` paths are certified today. **Newly UNDECIDED but still counted decided:** `replace-find-base` (2 paths) and `str-code-unsat-2` are recorded `audit_outcome=unsat, baseline_matches_audit=true` and now return `unknown` — verified with the shipped front door at 60s, axeyum 1/4 vs z3 4/4, DISAGREE=0. Sound, but a real loss no gate reported. The report now states its as-of date above the numbers and carries a per-audit provenance table; `--check` is gated in both aggregate gates, and a tampered provenance date exits 1. |
| 2026-08-20 | `(corrected)` | **I got the regression claim wrong, and it was already published.** I reported `replace-find-base` and `str-code-unsat-2` as regressed from `unsat` to `unknown`, inferring it from the audit rows plus today's behaviour. Building the audit's own commit `8aff8d507` and running the byte-identical corpus files (`git hash-object` matches) shows otherwise: `str-code-unsat-2` returned `unknown` there too — never a regression — and `replace-find-base` returned **`sat`**, a WRONG ANSWER on a query z3 decides unsat. Today's `unknown` is therefore a FIX, not a loss. Corrected in the generated matrix and in the commit that follows. |
| 2026-08-20 | (open) | **What the correction found is worse than what I claimed.** An audit row can disagree with the tree at its own commit: `replace-find-base` is recorded `audit_outcome=unsat, baseline_matches_audit=true` in an audit last touched by `8aff8d507`, and that commit's tree answers `sat`. `8aff8d507` is titled "refresh bare-route audits to v2" — a schema migration that can rewrite JSON without re-running anything. So the file's commit date is not the measurement's date, and there is no way to recover the real one from the artifact. **Next: make `audit_dominance` stamp the source sha it ran against**, so the question becomes answerable for future audits; then re-run the 35 and see what the real numbers are. |
| 2026-08-20 | `e44f9d715` | **QF_NIA `unsat` now carries a refutation, band 2 -> band 1.** The proof-gap matrix loses 60 of 327 instances at "evidence marked certified" — four times what Lean reconstruction costs — and `QF_NIA` ranked *band 2, needs an UNSAT proof format first*. But `nia_square` was already deciding this fragment EXACTLY; the artifact existed and nothing emitted it. Three arguments certified (non-square discriminant, non-integral rational roots, rational-root exhaustion at degree >= 3). **The checker does not call the producer**: the in-tree `fresh == *cert` convention re-runs the matcher, which binds a certificate to its source but cannot discover that the producer's reasoning is wrong — both would be wrong together. Stage 2 re-derives from the coefficients alone, scanning `1..=|a0|` where the producer pairs cofactors to `sqrt|a0|`, so a completeness bug in the step that could turn a `sat` into a wrong `unsat` is not repeated. |
| 2026-08-20 | `119a91c53` | Mutation testing the above, and the first run is the part worth keeping: nine guards, **five killed one test each and four killed nothing** — another guard rejected the same forgery first, the "six of seven were removable while green" shape. Isolating them needed certificates the producer would never emit: a degree-2 argument over `x^3+x^2+x-3 = 0`, which is SATISFIABLE at x=1 and whose leading three coefficients give a genuine non-square 13 with a valid bracket, so every other guard passes and only the degree check prevents certifying a satisfiable query; a constant term of right magnitude and wrong sign, leaving divisor set and recomputed count identical; and two cubics with IDENTICAL reason data so only the coefficient binding separates them. All nine now die individually. Two of my own harness bugs found on the way, both silent — a positional filter that matched no integration test name, and classifying cargo's `error: test failed` as `DID NOT BUILD`, which reported five real kills as compile failures. |
| 2026-08-20 | `4e1f9b092` | **The `whnf_core` tripwire was gated on the ENTRY, and the links it guards are not the entry.** The new δ-chain memo routes each link into the split cache by *that link's own* closedness, but the `reduction_ctx_reads` assertion beside it read `!entry_closed || …` — a different set. An OPEN entry δ-unfolds to a CLOSED link, and that link is written to the kernel-global half whose key has **no context component at all**, unchecked. Measured before writing the guard: one `build_creal_prelude` routes **6 links** that way (0 with a tail context read, so the memo was correct — just unchecked). Now per-link, against a `reduction_ctx_reads` snapshot taken when each link is pushed. Reachability is what makes it more than decoration, so it has a test; `chain.into_iter().take(1)` kills exactly that test. **Neutering the assertion itself kills nothing, and the code says so** — no input can make it fire, because "a closed term's reduction cannot reach a context lookup" is a theorem about `has_fvars`. Its `entry_closed` sibling was always in that category too, and did not say so. |
| 2026-08-20 | `813b80daa` | **13 stale measured markers, and renumbering them would have been wrong.** The prose explained the numbers and the explanations no longer described the artifacts. Fully-dominant fell 23/35 → 20/35, and **only two of the four losses are losses**: `QF_FP/fp_misc` went from fully Lean-reconstructed to a timeout, and `QF_BVFP/Float-no-simp3-main` stopped producing a certificate; against those, `fp_fromsbv` merely began declaring a `bit-blast` trust hole and `seq-ex1` merely met the redefinition of `evidence_checked` as *re-derives* rather than *portable*. A criterion that tightens under a metric moves it in the same direction as a capability regression, so the two are now reported apart. Also corrected: the baseline/audit gap was documented as "QF_NIA proof production rejects `IntPow2`", i.e. a refusal — all four are evidence-audit **timeouts**, which is a different fact. And two of the 20 "fully dominant" rows audited **zero** decisions, since `dominant_pct_audited == 100.0` and `audited_decided == 0` are not distinguished. |
| 2026-08-20 | (open, dispatched) | **`QF_FP/solver__fp__fp_misc.smt2` no longer reconstructs, and it is not the prelude.** Fully Lean-reconstructed on 2026-07-21; at HEAD it times out in the `lean-reconstruction` phase at **14.7 s of 15 s and 124.7 s of 125 s**. The obvious hypothesis — that the audit ran inside the 11-hour window when `502184d3f` had prelude construction at 33 s — is **wrong**, and I tested it rather than publishing it: warming is now 6.6–11.9 s and the instance still times out at a 125 s budget. First hypothesis for whoever picks it up is the exponential-DAG-walk bug this repository has now shipped five separate times; FP lowers into exactly the large shared BV DAGs that trigger it. |
| 2026-08-20 | `609417c9e` | `MAX_UNARY_TERMS` 4096 → 128: mutating the size guard away aborted the test binary rather than failing a test (cost 1026 overflows the stack; cost 514 renders a 13.2 MB module), so the budget admitted the crash it existed to prevent. Now pinned from both ends. The inequality sign re-check killed nothing and was deleted — positivity is enforced upstream by `checked_refutation` and downstream by both Farkas engines. The hypothesis-count check and the external `infer == False` re-gate also kill nothing and are kept, with the mutation pair that shows what the first one does (removing the equality registration kills 7 tests *through* it; removing both kills 1 and ships a quietly weaker module). New `lean_crosscheck` family `qf_s_string_length`: real Lean 4 accepts both modules, 173/173 in the full sweep. |
| 2026-08-20 | `b495a396e` | The string-length certificate reaches the kernel. `reconstruct_string_length` folds the certificate's own facts into a `False` over the constructed integers; `checked_refutation` is now the single derivation both `check_string_length_refutation` and the reconstruction read, so the exported view cannot drift from the validated one. An asserted **equality** enters as an equality — `LraReconstructCtx` grew `hyp_overrides` so the route mints `a = 0` and derives the `≤` half rather than assuming it, which is the one distinction the certificate's fact table turns on. A single-disjunct `(or A)` declines: the query states the disjunction, not the disjunct. Variables are named after their source (`len_xx`, `code_x`). `Evidence::UnsatStringLength` became a struct variant carrying `lean_module: Option<String>`, re-derived on `check` and never read back; a decline is `None`, not a weaker certificate. No `ProofFragment` variant — `scan_proof_fragment` is arena-based and a string script has no faithful arena. |
| 2026-08-19 | `pending` | `scripts/check-kernel-suites.sh`: the kernel's push-time / real-Lean suite partition, discovered from the source and asserted total; `hooks/pre-push` repointed at the non-Lean half (2,296 s → 80 s warm). Found `real_lean_string_monoid_crosscheck` owned by nothing and mis-formatting its check count; floor 218 → 219. |
| 2026-08-19 | `e3e105cd6` | The local-ci freshness gate is ENFORCING in both `check.sh` and `justfile`, on a `PASS` record (`57af69142-s4.json`, 6656 s, 7561 tests + 179 doctests, no vacuous/unreadable step). Landed report-only the day before because the only record was FAIL; that was the sole blocker. Flip re-tested through the real call site: NO_RECORD / STALE / STEP VACUOUS all red, unmodified green. |
| 2026-08-19 | (pending) | `artifacts/local-ci-runs/57af69142-s4.json`: first all-pass authoritative-gate record (5/5 steps, 7561+179 tests, 6656 s); `check-local-ci-freshness` flipped from `--report-only` to ENFORCING in `scripts/check.sh` and `justfile`. |
| 2026-08-19 | `ae0676aec` | `docs/formalized-math-2026-08/` corrected against measurement: "system-proved theorems = zero" falsified (3 facts, re-derived, heavily qualified; C2 still zero); C1 landed 2026-08-14 and did **not** deliver `N x 149/day`, so the single-file-lock diagnosis is falsified by its own remedy; the rate metric retired as unmeasurable across preludes; ADR-0517/0518's two-checker finding and the 122-declaration coverage hole recorded, with the limitation stated at its true width (shipped artefact does not carry the whole carrier; 4 declarations kernel- but not elaborator-checkable). |
| 2026-08-19 | `1afe65473` | Native/imported Nat prelude composition probe |
| 2026-08-19 | `d1eb38a13` | Alpha-stable cross-kernel expression identity |
| 2026-08-19 | `4c7af898d` | **ℝ is a lattice.** 15 `Rat` + 18 `CReal` declarations, every one accepted on first submission, all footprint-free. The predicted obstacle — a four-way sign split over `|a| − |b| ≤ |a − b|` — never appears. Nothing here has a side condition, so the failure mode is a *degenerate operation*, not a vacuous guard: `max x y := x` satisfies `le_max_left` by reflexivity and `abs x := x` satisfies `le_abs_self`, `neg_le_abs` and `abs_le`. So `not_le_zero_neg_one` and `not_equiv_abs_neg_one` are proved from the laws alone, the witness's exit status depends on both, and `max x x ≈ x` / `max 0 1 ≉ 0` / `min 0 1 ≉ 1` are admitted **through the kernel**. One level down, `Rat.max`/`Rat.min` are checked to COMPUTE on both branches with the wrong answer REFUSED — the nine `ℚ` laws are all one-sided and would hold of a projection. Three one-token mutations refused. |
| 2026-08-19 | `e9f5cf287` | **The mathematics strand stops advising against work that is finished.** `02` gains a dated ℝ/ℂ status block, a `ℂ` row and a corrected `ℝ` row in the construction-order table, measured prelude counts, and a "not built" table with reused costings (cotransitivity ~400 lines, `apart_mul` ~300, completeness/`sqrt`/suprema uncosted, ℂ `abs` downstream of both). `05`'s D3 is re-ordered rather than deleted: it was a pre-flight check on a construction order that has since been walked, and is now a coverage measurement against Mathlib. `04` closes R4 and keeps the 30 `Real` axioms as the ADR-0509 negative control. `01`, `03`, `README` and `diary-real-keystone.md` corrected in place. |
| 2026-08-19 | `c26e492b1` | **The axiomatized reals are renamed `AxReal` (ADR-0522 step 1), and two green assertions were reading the wrong carrier.** `CReal` contains `Real`: a front-door test asserting `contains("Real.add_le_add")` was satisfied by `CReal.add_le_add`, and `infeasibility_farkas_lean`'s ordered-field scan by `CReal.le` — the latter is a `proved` fact's checker command. One string literal moves the whole 30-row package. `--accept-rename OLD=NEW` is new: routing a rename through `--accept-population-change` would have published 30 retirements that never happened. |
| 2026-08-19 | `417b9216b` | **Finished the `AxReal` rename at the place that publishes the name.** ADR-0522 renamed the axiomatized ordered field's declarations; the ledger kept filing them under prelude `real`, so the table a referee reads said `real 30` about 30 rows all named `AxReal.…` — the label contradicting its contents, and inviting the exact reading the rename existed to prevent (the reals this project ships are `creal`, in the same table at **0**). Landed atomically per that ADR's own warning: `total=30|axreal=30|…`, thirty before and thirty after, never thirty-one. The table now carries a generated paragraph saying what `axreal` is and that ADR-0509's *declared* is not *reached*; it previously assumed the reader knew. Generalises: **a rename is not landed until the thing that publishes the name has moved** — the declaration half is the half a compiler checks, and therefore the half that gets done. |
| 2026-08-19 | `417b9216b` | Two substring bugs of the shape CLAUDE.md warns about, found by the rename and caught by neither gate. `real (\d+), integer (\d+), string (\d+)` matches inside **`creal 0, integer 0, string 0`** — ordinary prose now that the constructed carrier is the one at zero — captured (0,0,0), scored it against `axreal` (30) and reported a stale count, so a document stating the counts CORRECTLY would have redded the gate. And `check-fact-depends-derived.py`'s namespace list contains `Real`, matching at offset 2 of `AxReal.add_comm` to yield a name no kernel declares: `unnamed` never fires because a name WAS found, the lookup misses, and the fact is skipped **in silence** — the very silent-skip that file's header promises to report. Both fixed with `(?<![A-Za-z])`; the first controlled both ways (remove the lookbehind → 1 test dies; make the pattern inert → 5 do). |
| 2026-08-19 | `17df9ba63` | **A control script that nothing invokes, found by a control script.** `scripts/tests/` held 8 controls and `test-check-lean-golden-pins.sh` was run by nothing — not `check.sh`, not the justfile, not the hook, not CI — while passing 6 assertions daily. Fifth instance of this shape here. `check-control-registration.sh` now derives the registry from the filesystem, so a new control is red until a gate names it. Also `lane-push.sh --to <branch>`: landing work is `push HEAD:main`, and without a target the range, the cost estimate and the fast-forward check all read `origin/<current-branch>` — measured on a fixture, the same doc-only landing reads FULL BATTERY instead of FREE. |
| 2026-08-19 | `ad7f99e72` | Two `real-inverse` facts were red because of a lemma about `max`: both pinned `76 declarations admitted` and the lattice work made it 94. **A total every lane increments is not an anchor for a fact about one declaration** — replaced by the invariant the facts are about (trusted surface = 0) plus an explicit `>= 76` floor, demonstrated able to fail. They were also unreplayable: ~19 min in debug against the replay gate's 120 s budget, so it recorded TIMEOUT rather than a result. `--release` is ~12x here. |
| 2026-08-18 | `4b5613e26` | `check-fact-derived-numbers.py`: every number a fact asserts about its own `axiom_footprint` re-derived from the array. Fixes `F:schedule-critical-chain-infeasible` (prose 30 vs array 26, plus an obsolete facade paragraph found by re-measuring: `Lra`/62 lines, not a 21-line shim) and the example's stale module doc. 52 of 3,243 prose numbers bound, denominator printed every run; 7 guards, each deletion kills exactly 1 test; wired into both `just check` (`facts`) and `check.sh` so `check-aggregate-scope.sh` records no new divergence. |
| 2026-08-18 | `24578036f` | `gen-lean-axiom-ledger.py`: coverage command gains `--include-constructed` (on `--release`, 12x faster), `EXPECTED_PRELUDES` gains `rat`/`creal`/`complex`, and measurement drift is reported per prelude **with its direction** — REGRESSION / IMPROVEMENT / COVERAGE LOST / ADDED / RESHAPED, each with the re-pin command. Ledger now pins 8 groups by value (was 6); 39 tests (was 24); 11-mutation control registered in `mutation_controls.py`, no survivors. Already wired in both `check.sh` and `just check`, so no new gate divergence. |
| 2026-08-18 | `7646b2c04` | `reject_self_refuting_module` at `gate_module_content` — the one boundary every route's module crosses; the Python predicate widened from one shape to the property and run over EVERY class; DECLINED pinned two-sided in its own manifest; the shadowed attested-path copy deleted after the mutation control that used to kill a test reported SURVIVED. 6 mutations, 0 survivors; 9 Rust unit tests, each with its discriminating twin. |
| 2026-08-18 | `31442bd5d` | `quant_{affine_growth,counterexample_cover,eq_partition,residue}` — four golden Lean-module pins re-pinned at cause (+1 640 header bytes from `b760fd6ae` and `46724faec`), unredding `main`. Found by the first completed run of the authoritative gate. |
| 2026-08-18 | `e069afa03` | `local-ci`: the zero-test guard could not fire on the workspace sweep — nextest's summary is indented and the pattern was `^`-anchored. Fixtures now captured from the tool; a test step whose count is unparseable is `unreadable` (89), not `pass`. |
| 2026-08-18 | `69c12646c` | `artifacts/local-ci-runs/a6ee37c6a-s4.json` — first completed run of `scripts/local-ci.sh` in this repository's history. FAIL, 6401 s, 4 of 7511. |
| 2026-08-18 | `a2841965e` | `local-ci` gates the COMMIT, not the working tree: stable flock'd detached worktree, `--no-worktree` opt-out, controls mutation-tested. |
| 2026-08-18 | `PENDING` | Lean has two checkers (ADR-0517): the kernel accepts all 470 carrier declarations, the elaborator refuses those whose checking must reduce a `theorem`. `real_lean_creal_carrier_kernel_replay` (whole carrier, no reachability filter, count-equality + tamper control) and `real_lean_wellfounded_elaborator_divergence` (`gcd` refused / `mod` accepted / same module with `theorem`->`def` accepted / kernel takes both); gate floor 212 -> 218. |
| 2026-08-18 | `00f998ccb` | ℤ categoricity: the existence half of the universal property (`iter` + three preservation equations, making `Int` the initial ℤ-structure) and `categorical` — every generated aperiodic ℤ-structure is in structure-preserving bijection with `Int`, universe-polymorphic. `iso` is the constructed two-sided-inverse form, honest about hypothesising the back-map. 32 theorems, all footprints empty; 22 injected weakenings each refused at their own declaration, now bracketed by `reached_declaration` on the near side too. |
| 2026-08-18 | `a2a36590b` | `F:int-categoricity` recorded, and `F:int-characterization`'s "not proved that they determine it" caveat removed because it stopped being true. Every checker anchored on the declaration name AND the empty-footprint column, each run with its subject mangled: 0 on the finding, 1 on the mangle. |
| 2026-08-18 | (pending) | ADR-0512 phase R3: the ordered-ring telescope gains an equality slot (30 → 39 binders) and `specialize_setoid_to_eq` proves it specializes back to today's statement — conclusion **and** all 30 non-slot binder types, node for node. Three mutation kills recorded; `residual_eq_constants` guards the one failure the footprint cannot see. |
| 2026-08-18 | (pending) | `Sos` reconstruction accepts a **nonzero affine row** in the `LDLᵀ` linear forms (`rational_affine_squares`, `int_affine_lin_to_rexpr`), so `Σ xᵢ² + 1 < 0` and `(x−1)² + (y−2)² + 1 < 0` reconstruct instead of emitting `axiom P; axiom Not P`. The transcription checker's two normalizers learned degree-2 monomials to match, with square/cross discrimination driven to failure six ways. Binding gate `instances=125 → 135`, `attested=28 → 19`, `failures=0`. |
| 2026-08-18 | (this change) | Round 3: corpus widened 51 -> 66 mutation families over a development that now carries a Type-valued structure, a `Nat` literal, an indexed family, a parameterized family and a mutual group; a fourth defect found and fixed — a **recursor's** `levelParams` was decorative, because a recursor is generated and compared rather than admitted, and the comparison's positional alpha-rename leaves an unbound parameter untouched |
| 2026-08-18 | `2633d7186` | Kernel-vs-Lean differential widened to 51 mutation families; recursor/constructor regeneration compared against Lean's own, closing the 37% of the stream `addDeclCore` never reads; two defects fixed — universe closure on `check_declaration` **and** the inductive gate, and the recursor `k` flag validated on import |
| 2026-08-18 | (pending) | ADR-0512 phase R4: `build_creal_model_of_arith` — the `Real` axiom package modelled by the **constructed** reals. 22/22 witnesses axiom-free, 9/22 restated over `CReal.Equiv`, 7/7 discrimination witnesses, exit status depending on all of it (`creal_model_witness`). Four mutation kills; ADR-0456's "`Int` is not ℝ" caveat discharged. |
| 2026-08-18 | (this change) | Round 4: the fourth admission gate (`restore_nested_inductive_group`) gains adversarial coverage — the auxiliary recursor was never unread by Lean's kernel, only by `Environment.find?`, the elaborator's lookup; the replay script now asks `env.toKernelEnv`, a nested group is on the wire, and 14 `ind.aux-*` families cover it. 0 violations in 274 and 752 mutants, 80 families; residue measured exhaustively and is one non-type-checking field |
| 2026-08-18 | (pending) | `LraReconstructCtx`'s carrier is a parameter: `RingSignature` + `RingEquality` replace the by-value `ArithPrelude`, `with_ring_signature`/`try_new` replace the panicking constructor, and five mutation-verified guards check a signature against the kernel. `CReal` passes them today with `CReal.Equiv` in the equality slot. Baseline output byte-identical. |
| 2026-08-18 | (pending) | **ADR-0512 phase R4 reaches reconstruction: `LraReconstructCtx::adopt_setoid_equality` fills the ring interface's equality slot from `CRealPrelude`'s own theorems, and a Farkas/SOS refutation over the CONSTRUCTED reals rests on zero carrier axioms.** Measured on all five `ordered_ring_refutation` fixtures: 30 carrier axioms over `Real` against **0** over `CReal`, and the slot costs **0** declarations against 18 for the `Real` route — both read out of `Environment::len` and `Kernel::axiom_footprint`, with the `Real` column as the in-output control. Four adoption guards plus the ctx's one-slot rule, each killed by exactly one test under mutation. The nine slot-member types come from one builder shared with `declare_setoid_equality`, so an interface change cannot move only one of them. `--require-empty` output is byte-identical to before. |
| 2026-08-18 | (pending) | **`PreludeKey::CReal`, and the shipped LRA/SOS front door moves onto the constructed reals.** `build_creal_prelude` 43.97 s -> **0.149 s** per call (debug; release 4.69 s -> 0.067 s) via the ADR-0464 template. `prove_unsat_to_lean_module` now reconstructs over `CReal` with an adopted equality slot: carrier axioms 12/17/8 -> **0/0/0** on three front-door fixtures, `Real` control non-empty, module axiom lines equal the kernel footprint. Also fixes a module-renderer ordering defect the constructed carrier exposed, which rejected 5 of 77 `lean_crosscheck` families; 77 of 77 now check under lean 4.30.0. Cost: modules 2.4-41 kB -> ~2.6 MB. Every new guard mutation-checked, exactly one test dead each. `nat_axiom_inventory --include-constructed` is now under the prelude-reuse differential gate. |
| 2026-08-18 | 61c466b53 | **The shipped front door reaches no `Real` axiom, measured at `build_arith_prelude` itself.** `RingSignature: From<IntPrelude>` + `try_new_over_integers`; `reconstruct_int_farkas_to_lean_module` off the `Real` package. `arith_prelude_builds()` = 0 across all four arithmetic arms, 1 for the control. Mutation-checked twice, exactly one test dead each — and all 9 tests of the suite named for that route pass under both mutations. Fact + ADR-0509 (declared vs reached). Also unbroke `clippy` on STABLE, red on `main` since `94d51fbc6`. |
| 2026-08-18 | `5734b7449` | **Positivity is closed under multiplication**, over ℚ and over ℝ. Not one of the 22 — they give `mul_nonneg`, of which the zero product is a model — and over ℚ it is a *field* lemma, going through `inv_pos`. Over ℝ it needs no estimate: `CReal.lt`'s rational gaps plus `ofRat_mul`. First proof to open the strict order's `Exists` twice, which works because the target is a `Prop`. |
| 2026-08-18 | `fc52b07f3` | **The inverse's domain, both directions, and the Prop/data line drawn correctly.** `0 < x` and `∃ k, 1/(k+1) ≤ x` are the same proposition, and the `Exists` is a `Prop`, so the modulus can never be extracted into a `CReal`. It is *computed*, not searched: `CReal.lt` already carries a rational gap. **Corrects the previous commit's doc** — a function may TAKE a `Prop` and return a `Type`, it may not BRANCH on one, so the disjunctive `Apart` blocks a definition and the one-sided `PosBound` does not. Plus `CReal.ofRat_le`, `Rat.natDivSucc_pos`. |
| 2026-08-18 | `b91b6dac5` | The four ordered-field lemmas ℝ's inverse is written in — `sub_mul`, `mul_inv_sub_one`, `inv_sub_inv`, `inv_le_of_pos_le` — from `mul_inv_cancel` and the 22 alone, so each transcribes one level up. |
| 2026-08-18 | `6375d7746` | **ℚ is a FIELD.** `Rat.mul_inv_cancel : 0 < q → q·q⁻¹ = 1`, axiom-free: the one proof here about the representation, since `Rat.inv q` is stuck until `num q` is in constructor form. The `negSucc` branch needs no lemma — `Int.lt Int.zero (negSucc m)` **ι-reduces to `False`**. Guard: `Rat.inv (2/1)` REDUCES to `1/2`; the identical script pointed at `= 2/1` is REFUSED. |
| 2026-08-18 | `baf81fd66` | ℝ gets **Bishop apartness**, verbatim rather than encoded — `CReal.lt` already carries the separation as a rational gap. Four laws, `not_equiv_of_apart` ONE-WAY (its converse is Markov's principle), and `CReal.no_total_inverse`. |
| 2026-08-18 | `57af69142` | **`CReal.inv` is built**, with `mul_inv_cancel`, `inv_congr` and `inv_index_irrelevant`, all footprint-free and accepted on FIRST submission. Index `(C+1)n + C`, `C+1 = (4k+4)(k+2)`, read back *two* ways so `natDivSucc` still need not be antitone. Non-vacuity is admitted **through the kernel** (`PosBound one 0`), and `∀h, ¬(1⁻¹ ≈ 0)` follows from `mul_inv_cancel` alone, so the operation is neither vacuous nor the zero function. Negative controls: `x·x⁻¹ ≈ 0` and `x⁻¹ ≈ x` both REFUSED. |
| 2026-08-18 | `facde4243` | The two ℕ/ℚ lemmas the index arithmetic is written in. `Rat.inv_natDivSucc : (1/(m+1))⁻¹ = (m+1)/1` — the only place the *value* of an inverse is computed, and needed because every bound over ℝ is one `natDivSucc` with a `Nat` numerator. `Rat.nat_index_symm : (a+1)b + a = (b+1)a + b` — **Bishop's sampling index is symmetric in shift and argument**, which is how a bound read at a product index comes back to the *shift* rather than to `n`. |
| 2026-08-18 | 570b5c738 | **The interface as a telescope, and it is the same over ℤ.** `ring_interface_telescope` + `examples/ring_interface_pin.rs`, 30 of 30 byte-identical. Also repaired a test `61906c585` swept in broken, and the finding behind it: a `NameId` is an INDEX, so a signature read against another *populated* kernel resolves silently to `Nat.le`, `Nat.beq_refl`, … rather than failing. |
| 2026-08-18 | 9ab8d7977 | **The negative control at one axiom instead of thirty.** `build_control_carrier`, three mutations, one test dead each. |
| 2026-08-18 | 6c08c906f | **ADR-0515** + `F:ordered-ring-interface-is-the-same-over-the-axiom-free-integers`. |
| 2026-08-18 | `74946dd3b` | Split Lean module layout: `render_lean_prelude_module` / `render_lean_module_compact_importing` / `declarations_reached` / `lean_name`, `real_lean_shared_prelude_crosscheck` (4 real-Lean checks, 2 of them refusals), `examples/shared_prelude_module.rs --require-split`, gate floor 208 -> 212. 257x per query; found two `CReal` theorems Lean 4.30.0 rejects that the in-tree kernel admits. |
| 2026-08-18 | `035a92d9a` | ADR-0518: proofs stay spelled `theorem`. `Kernel::set_render_proofs_as_def` built as a `Kernel` field, OFF by default, so nothing shipped moves; 7 guards in `tests/proof_keyword_render_option.rs` (no `lean` binary, 0.69 s, so `hooks/pre-push` is unaffected), mutation-checked 1/1/1/1/2; `examples/proof_keyword_cost.rs` renders the front door, the shared half and the whole carrier both ways and `--require-keyword-only` fails if the switch moves anything but the keyword. Measured: the shipped artefacts already elaborate clean under `theorem`; flipping the default costs 1.36-1.69x elaboration, +9.7% on the Lean gate, and makes `real_lean_wellfounded_elaborator_divergence` report that Lean CLOSED the divergence. |
| 2026-08-18 | `c9223e4` | binding: the converse number says which side of the check the missing 245 rows are on — `undecomposable_spine=0` measured and gated, `represented` is a maximum matching rather than an overlap. |
| 2026-08-18 | `b9d2f0a` | binding: the 4 `FiniteArrayExtensionality` rows were never content-free — the emitter collapsed each `(select a i)`; `attested` 9 → 5, `structural` 98 → 102 with 360 new matched term nodes. |
| 2026-08-18 | `a25b18a` | binding: 66 rows were recording the weaker of two true statements — four verdicts become a partition with two-sided pins; `anchored` 10 → 73, `structural_anchored=66` new. |
| 2026-08-18 | `3076b6ae0` | the one Lean module `rfl` refuted on its own: root-caused to a degenerate `(t, t)` witness, the route now declines, and a self-refuting attestation FAILS the run instead of being counted |
| 2026-08-18 | `8e4894de4` | `ArrayAxiom` renders the query's own terms; a third `structural` verdict binds 95 modules to their query's subterms, 359 of 372 corruptions caught, and the attested class drops 124 → 28 with an anti-absorption guard |
| 2026-08-18 | `pending` | binding coverage: +20 bound (105 → 125), 124 modules proved content-free, and the converse direction measured at 286/531 |
| 2026-08-18 | `pending` | `scripts/cargo-serialized.sh`: heavy cargo now takes an flock and a memory ceiling, because "serialize" was prose and prose does not hold a lock (two dev boxes downed, one agent session OOM-killed). **`MemoryMax` alone does not bite** — it *is* applied (`memory.max` = 67108864) and a 400 MB allocation still succeeds by swapping, on a box whose 7 G of swap is 6 G full. With `MemorySwapMax=0` the same allocation is SIGKILLed by the cgroup (137), host untouched. `--self-check` proves it per host and discriminates: `AXEYUM_CARGO_SWAP=1G` flips it to `SURVIVED`, exit 1. |
| 2026-08-18 | `pending` | `local-ci.sh`, the declared authoritative gate for `main`, cannot run on any fleet host and never has (`cargo nextest` 101, `rustup run 1.88.0` 1, on s4/s5/s7). Now refuses to start rather than limp, `--record` leaves a tracked per-(sha,host) JSON, and `provision-fleet-host.sh` installs the prerequisites (`1.88.0` needs `--profile minimal`, else rustup fails on `miri`/`cranelift` inherited from the nightly profile). The record carries per-step TEST COUNTS and marks a step that exited 0 having run zero tests as `vacuous`. |
| 2026-08-18 | (pending) | `gen-adr-index.py --check-remote`: cross-checkout ADR-number collision detector, wired into `just check` and `check.sh`; found a second live collision (0468-0470) beyond the one already fixed today (471-474) |
| 2026-08-18 | (pending) | `lean_pp::split_module_banner` + `tests/support/lean_golden.rs`: golden pins cover the module BODY, banner pinned once as committed text in `module_banner_pin`. |
| 2026-08-18 | (pending) | `scripts/check-lean-golden-pins.sh` (+ controls): the golden-module gate, membership DISCOVERED not listed; wired into `just check`, `check.sh`, and diff-scoped `hooks/pre-push`. |
| 2026-08-18 | (pending) | `mutation_controls.py`: a mutation check can no longer report a result it did not measure. `DID NOT BUILD` / `DID NOT RUN` / `AMBIGUOUS ANCHOR` / `INCONSISTENT` are distinct from `killed N` and `SURVIVED` and are counted separately; build probe, two independent kill counts, baseline test count, verified restore, and a `cargo` runner for the route the defect was reported on. `self-demo` demonstrates all four outcomes live; `mutation-controls` mutation-checks the harness (24 guards, 31 controls, 24/24 killed after 3 real survivors were fixed). Found and repaired two dead controls in `lra-hypothesis-binding` (53/53), and one mutation in `lean-axiom-ledger` that was scored as a kill while running **zero** tests, so that control is 10 guards and not the 11 recorded. Wired into both `just check` and `check.sh`. |
| 2026-08-18 | `pending` | **ADR-0521: ℂ is constructed over the constructed ℝ at zero trusted declarations, and ℂ's absence of an order becomes a theorem.** `Complex` is `mk : CReal → CReal → Complex` with `Complex.Equiv` componentwise — no quotient at either level, so `Quot.sound` is never needed. Every ℂ law reduces by δι to two `CReal.Equiv` obligations that are *algebraic*, so they are **decided, not hand-derived**: `complex/ring.rs` normalizes a `CReal` expression to a sorted multiset of signed monomials with opposite pairs cancelled and emits the `Equiv` proof, declaring nothing (every function returns a proof term, in `shifted_bound_le`'s style), so the `CReal` namespace and the trusted surface are untouched by construction. `add` and `mul` are the same commutative monoid, so the reassociation machinery is `rsum_perm`/`iprod_perm` written once against an `Op` tag, one level up and over a *defined* equality — the transcription ADR-0512 predicted. Landed with `conj`, `normSq`, `mul_conj` (`z·z̄ = ‖z‖²`, the law that needs the cancellation pass) and `normSq_nonneg` into `CReal`'s existing nonneg cone. **The finding that is not a construction:** `Complex.no_compatible_order : ∀ le lt, le_refl → lt_irrefl → lt_of_le_of_lt → add_le_add → le_congr → sq_nonneg → zero_lt_one → False`, proved directly with no classical step, so the 13 order laws are refuted rather than skipped. |
| 2026-08-18 | `590e2ff8c` | **ADR-0512 phase R2 completes: all 22 ordered-ring laws hold over the constructed ℝ.** `mul_assoc`, `left_distrib` and `mul_le_mul_of_nonneg_left` land, plus `mul_congr` — the fifth congruence obligation and the R4 prerequisite. The four were one problem: each compares two products whose *sampling indices differ*, so `CReal.mul`'s exact estimate is unavailable and the naive bound is `C/(n+1)` for a `C > 2`. Two new pieces make that enough. `CReal.Equiv.of_bounded` — **`Equiv` only needs the difference to be `O(1/n)`; the constant is free** — is `Equiv.trans`'s argument with one term deleted, closing on `Rat.le_of_le_add_natDivSucc`, whose numerator is a `Nat` *parameter* so a symbolic `K` is as good as a literal; and `Rat.nat_index_compose` says **Bishop's sampling indices are closed under composition** (the additive shift `2n+1` is the `c = 1` case), so every nested index reads back at `n` through one `natDivSucc_le_scaled`. `mul_le_mul_of_nonneg_left` needed no estimate at all, exactly as costed — it is `left_distrib` + `mul_nonneg` + `mul_congr`. **22 of 22**, 58 declarations, trusted surface still 0, and the count is now read out of the kernel: `CRealPrelude::ordered_ring_laws` must name 22 *distinct* footprint-empty theorems matching `RatPrelude::ring_laws` position by position, asserted by the example's exit status and three tests, verified by deleting `mul_assoc`. |
| 2026-08-17 | `67960fc1c` | D3 grouping refuted at the point of execution: arithmetic-as-a-directory grows the largest dependency cycle 58,215 → 103,514 lines. `analyze_solver_group_collapse.py` + mutation controls; no files moved. |
| 2026-08-17 | `d23a9d883` | `Nat.exists_prime_dvd` — every `m ≥ 2` has a prime divisor — admitted axiom-free in a new `nat_prelude::primes` module, with `Nat.le_of_dvd`, `Nat.two_le_succ_or_eq_one` and `Nat.least_divisor_search` beneath it (137 Nat theorems, up from 133). Recorded as `F:nat-exists-prime-dvd`, whose `kernel-term` checker pins the entire rendered type rather than the name — verified against the `1 ≤ p` weakening, which the kernel accepts and a name-only grep would not catch. |
| 2026-08-17 | `8f8c12dce` | ℕ-induction wired into `solve` as the last rung of the quantified ladder (`unknown` → `unsat` only, on `original_assertions` because normalization + skolemization have erased the negated universal by that point). New `tests/nat_induction_adversarial.rs`: 22 adversarial shapes, hand-derived truths, measured on the route and through the front door, 0 violations. Fixed an index-out-of-bounds panic in `is_nonneg_guard` on one-argument guards. `nat_induction_corpus` re-measured (3 contradictions → 0) and its gate widened to the front-door column. Both suites mutation-verified. Blast radius: `--lib` 1159 unchanged, `corpus_regression` 152/0 DISAGREE unchanged, whole crate 285 suites / 3861 tests green, clippy and fmt clean. |
| 2026-08-17 | `pending` | `string` prelude reaches **axiom=0**: `append` becomes a checked `Str.rec` recursion with four proved monoid laws (ADR-0513); ledger `total` 31 → 30, row filed as retired; real-Lean cross-check pins that `#print axioms` names no `axeyum.string.*` row. |
| 2026-08-17 | `fae708aa5` | Characterization theorems: our ℕ proved categorical (any Peano structure is uniquely isomorphic to it), our ℤ proved no-junk + generated by 1 + discrete everywhere + unique maps out. 18 theorems, all footprints empty; 9 injected weakenings each refused at their own declaration. |
| 2026-08-17 | `f532e04d3` | Restored `rat_prelude` after `fae708aa5` reverted `cf205e9a8`: a per-lane index refreshed in one shell invocation and committed in the next, with HEAD moving in between. The refresh must be in the SAME invocation as the commit, and `git show --stat`'s file COUNT is the tell — the diff you expected to see is not. |
| 2026-08-17 | `b15debdfa` | One Lean resolution policy (the `lean-toolchain` pin) shared by `check-lean-gate.sh` and `lean_probe.rs`; every suite names the binary and version it used and the gate cross-checks them; `replay-lean4export.lean` elaborates under 4.30 and 4.34; exercised negative controls in `scripts/tests/test-lean-toolchain-policy.sh` (ADR-0514) |
| 2026-08-17 | `pending` | transcription: bind every rendered Lean hypothesis back to the query text — 105 instances, 248 hypotheses, 869 corruptions caught per run |
| 2026-08-17 | `7337f708` `caaf2906` | A SKOLEMISED refutation certifies: the elimination is recorded POSITIONALLY (binder counts, anchor by index, a binding as "the k-th witness of assertion i"), so the checker re-runs the eliminator in its own arena and no producer-side id is trusted. `F:barber-no-such-barber` closes on `smt-clausal` with a NON-EMPTY axiom footprint naming skolemisation and universal instantiation. The negative control failed on purpose and moved to `F:no-integer-square-is-minus-one`; the gate now sweeps 18/18. |
| 2026-08-17 | `ae13cd6e` | A kernel fact's `depends_on` is DERIVED from the proof term, not transcribed: `Kernel::theorem_dependencies` keeps the half of the constant closure `axiom_footprint` discards. 18 edges were missing — two of them on facts proved the same day, by hand. Isolation 65 → 62. Restraints pinned by tests; the vacuity floor had no test until mutation-checking found it killed zero. |
| 2026-08-17 | `07ffe852` `9853fb6c` `28755674` | The e-matching route certifies, on the third design. It first shipped `certified=1` on evidence whose independent re-check said FAIL (one instance passed by `TermId` coincidence, two did not); reverted, then made portable — instances rebuilt in the checker's arena, ground set rebuilt rather than stored. `tests/certified_implies_revalidatable.rs` is the guard that caught it and now licenses it. |
| 2026-08-17 | `c2365718` `4cd5d6f0` `c5f4c04b` `078b2776` | The Lean gate stops overstating: 41 of 74 crosscheck families hand Lean an `axiom P` shim, so the headline is split, the reasoning half floored, and every fragment's class pinned by name. `qf_bv` was a WIDTH, not a defect — enumeration beats bit-blasting below ~16 bits — so `qf_bv_wide` now exercises the real reconstruction (33 theory / 41 attestation). |
| 2026-08-17 | `3cc574c7` `502c0503` | Both counted proof-production errors closed (`int_blast`'s deliberate `int.pow2` decline was mapped to a backend error, losing a verdict `check_auto` decides in 0.13ms), and settled SMT-route facts gated on certification rather than verdict — 17 of 17, enforced. |
| 2026-08-17 | `ea9500bc` `e97db72b` `2c535667` `f40f7dc4` | Gate repairs: `check-parity-docs.py` crashed before running a single check (hiding 14 failures); CI's crosscheck grep still pinned 73 families; and `PLAN.md`'s sources were 24 KB over a 52 KB budget, journal moved to result notes. |
| 2026-08-17 | `f18904db7` | R3: reachability census re-derived and committed as `artifacts/reachability/r3-census.tsv` (190 rows over both corpora); the ranked tables in `04-reachability.md` are now a generated view of it, gated by `scripts/check-reachability-census.py` inside `check-foundational-resources.sh`. 13 guards, each with its own rejection path; mutation-verified that deleting any one kills exactly one test. Corpus coverage checked in both directions and reported SKIPPED, never passed, when the sibling checkout is absent. Stale numbers corrected in `04` and `05`. |
| 2026-08-17 | `pending` | ADR-0512: ℝ is a Bishop setoid over ℚ at **zero** trusted declarations, with `creal_shape_probe` measuring the carrier's admissibility against a `funext` negative control; ℂ scoped and deferred. |
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

**The prose half of the ledger is now derived, not transcribed** (`WIP`,
ledger-freshness, 2026-08-18). `F:schedule-critical-chain-infeasible` said "the
30 axioms the kernel module actually rests on" for three days after its
`axiom_footprint` was corrected to 26 — with a correct `--expect-axioms 26`
sitting in the same JSON object. `depends_on` and the footprint array are both
derived and gated; the sentences *about* them were not, and nothing in the ledger
linked a number in English back to the thing it came from.

`scripts/check-fact-derived-numbers.py` closes that for one quantity, and only
one. It anchors **structurally**, not lexically: an `evidence[i].supports`
beginning with the literal field name `axiom_footprint` (the ledger's existing
convention, 48 slots), plus `--expect-axioms N` inside a command. Measured
2026-08-18 it binds **52 claims across 48 slots, 1 unchecked, out of 3,243
numeric tokens in fact prose** — and the docstring names the 3,191 it cannot see.
That gap is deliberate: 3 of the 7 phrases matching a naive `N axioms` regex are
about Peano's axioms, Armstrong's axioms, and a *different* theorem's footprint,
so a lexical gate over all of them would be 43% wrong and worse than none.

Seven guards, each with a fixture that trips it and no other; `mutation_controls.py
fact-derived-numbers` deletes each in turn and **every deletion killed exactly one
test**. Exit status was demonstrated on a scratch fact carrying the original stale
wording: exit 1 with three FAIL lines naming field and both numbers, exit 0 either
side of it.

Detail moved to [`../notes/100-ledger-freshness.md`](docs/plan/notes/100-ledger-freshness.md).

**The pre-push kernel step ran the real-Lean suites a second time; it no longer
does (`DONE`, agent-prepush-scope, 2026-08-19).** `hooks/pre-push` ran
`cargo test -p axeyum-lean-kernel` wholesale. Fifteen of that crate's 46
integration suites hand modules to a real `lean` and `scripts/check-lean-gate.sh`
already owns them — with a pin, a counted floor and a no-skip rule this step had
none of. Measured warm on s4: **2,296 s → 80 s.**

The deliverable is not the split but the assertion that it is total.
`scripts/check-kernel-suites.sh` DISCOVERS membership (a suite is real-Lean
exactly when it carries `#[path = "support/lean_probe.rs"]`, the same
"membership is the act itself" shape as `check-lean-golden-pins.sh`) and fails if
any `tests/*.rs` is in neither half — so removing duplication cannot silently
create a suite nothing runs. A hand-written list of 31 names would have been a
list someone forgets to extend, failing silently.

**It found one on its first run.** `real_lean_string_monoid_crosscheck` (landed
2026-08-17) invokes a real Lean and was in no gate's table; only the wholesale
`cargo test` ever ran it. It also printed its count as
`AXEYUM-LEAN-CHECKED|string-monoid|1|…` where the gate parses
`AXEYUM-LEAN-CHECKED <tag> checked=<n>` — so it would have summed as zero.
Both fixed; `CHECK_FLOOR` 218 → 219, verified `checked=1` against the pin.

The step is now diff-scoped, and unlike the frontier ratchet's filter this scope
is **derived**: the crate's `Cargo.toml` has one dependency (`num-bigint`) and
nothing from this workspace, so no other crate can move these suites. The
partition assertion runs on either branch — it is what makes the skip safe.

10 guards, 10 controls, each deletion killing **exactly one** control. Needed one
mutation-harness fix: `Unittest.build` ran `py_compile` on every subject, so a
shell subject scored `DID NOT BUILD` on all ten — unmeasurable, in the harness
built to tell that apart. Shell subjects now use `bash -n`.

Detail in [`../notes/100-prepush-scope.md`](docs/plan/notes/100-prepush-scope.md).

**The axiom ledger now pins all eight prelude groups by value and names the
direction a number moved** (`WIP`, expect-axioms, 2026-08-18). The brief's
premise was mostly already met and one of its numbers was wrong: **28** fact
files (not 58) run `nat_axiom_inventory` in a `checker_command`, and the ledger
has pinned every *default* prelude by value since ADR-0465 — a fall fails that
comparison exactly as a rise does. Converting those 28 would change no bit:
`--require-axiom-free L` pushes `(L, 0)` into the same list `--expect-axioms L=0`
does, and the only preludes any fact names (`nat` 23, `integer` 6, `logic` 2)
already measure 0, the floor.

The real gap was coverage. `creal` (ADR-0512) and `complex` (ADR-0521) were in
**no** measurement the ledger consumed — they need `--include-constructed`, and
the coverage command did not pass it — so their counts could move either way
unobserved; `rat` was measured but missing from `EXPECTED_PRELUDES`. All three
are now in both. A pin for a group the command never builds would pass
vacuously, so dropping the flag is itself a gate failure.

`--check` no longer prints two JSON blobs for the reader to diff. It reports per
prelude, with direction and remedy: a **rise** is a regression (something
previously proved is now assumed), a **fall** is a result the ledger has not
published yet — the direction a blanket axiom-free assertion structurally cannot
see, because it only ever becomes more true. Both fail; re-pinning is one
command. Demonstrated failing on 28 -> 30 and on 32 -> 30 and on a 1 -> 0, then
green.

Profile decided the shape: `--include-constructed` costs **2 m 03 s debug against
10.3 s release**, so the coverage command moved to `--release` — affordable once
in a generator that already runs, not affordable in 28 `checker_command`s.

Guards: `python3 scripts/tests/mutation_controls.py lean-axiom-ledger`, 81 s, 11
mutations, **no survivors**; ten kill exactly one test. The two that do not are
recorded, not smoothed over.

Detail, including a near-miss where the shared worktree briefly measured
`creal: axiom=30` — the whole `Real.*` package — from another lane's in-flight
prelude cache, in [`../notes/101-expect-axioms.md`](docs/plan/notes/101-expect-axioms.md).

**Not 124 attestations — 5. And a second Lean module that refutes itself, found
in the class the checker's own manifest said was "NOT checked"** (`WIP`,
attestation-gap, 2026-08-18).

Re-measured first. `check-lra-hypothesis-binding.py` reports **135 bound / 102
structural / 73 anchored / 5 attested**, not the `125 BOUND / 124 ATTESTED / 21
DECLINED` the brief carried. That figure came from
`crates/axeyum-solver/src/capabilities.rs`, which had been stale for a day;
lanes 93/94 had already moved 95 of the 124 to `structural` and 9 to `bound`.
The row is corrected. **A stale capability row is how a wrong number becomes a
brief.**

So the gap was closed before this lane started. The prior census generalizes: its
2-rewrite/3-unanchorable split is all that is left, and is understated —
**4 of the 5 are rewrite output**, both `replace_all` rows being a constant-fold.

The live hole was **DECLINED** — 20 instances the manifest listed and nothing
ran on. Two costs, both already paid:

- `extract-concat` rendered `Not (And (Iff prop._24 prop._24) …)` — eleven
  reflexive `Iff`s under one negation, so Lean's `False` follows from that one
  axiom with the `.smt2` file never consulted. The 2026-08-18 self-refutation
  check recognized `Not (Eq α t t)` only, and ran only over attestations.
  Widened to the property and run over every module: **4,652 axioms, 1
  self-refuting.** The emitter now declines it.
- The class is now a two-sided pin, and its first run as a check **evicted two of
  its own members**: the `bug593` rows bind structurally. Reading their φ is the
  lane's other finding — it maps the module's function onto the query's INNER
  `g`, not its outer `f`, so `structural` means *the module names terms this file
  contains*, not *the module says what this file says*.

**The gate is RED at HEAD `570b5c738`, and not from this lane**: 133 of 249
pinned instances fail because `a6ee37c6a` migrated the shipped LRA route to
`CReal` without the checker's carrier vocabulary following. Measured from a clean
snapshot. Migrating it is the reals lane's call; loosening it here is the one
outcome worse than under-covering.

Detail in [`../notes/102-attestation-gap.md`](docs/plan/notes/102-attestation-gap.md).

**`scripts/local-ci.sh` has completed once, and it was RED** (`WIP`,
local-ci-run, 2026-08-18). Hosted CI has called it "the authoritative gate for
`main`" since it existed; nothing had run it. The record is
[`artifacts/local-ci-runs/a6ee37c6a-s4.json`](artifacts/local-ci-runs/a6ee37c6a-s4.json):
**6401 s (1 h 47 m), 7511 tests, 7507 passed, 4 failed, 32 skipped.**

All four were deterministic and one cause: `b760fd6ae` (+863) and `46724faec`
(+777) added **1 640 bytes of module header** to every emitted Lean module, each
re-pinning only the golden module that sits in a gate. Third recurrence;
`6389e0194` said the same of three of these on 2026-08-15. Re-pinned at cause,
green. The point is not the pins: **no pre-merge gate runs those four
`tests/*.rs` suites**, so their only reader was the gate nobody ran.

Two defects in the gate itself, both found by running it:

- It gated the **WORKING TREE**, so a sibling lane's uncommitted work decided
  whether a SHA passed. Now gates a detached worktree at the commit, which is
  `hooks/pre-push`'s own solution (`a2841965e`).
- `count_tests` anchored nextest's summary at `^`; nextest indents it five
  spaces, so it never matched: the recorder wrote `tests: -1` for the 7511-test
  step and the zero-test rule **could not fire on the sweep it exists for**. The
  control's fixture was typed from the docs, not captured (`e069afa03`).

Cost is not core-bound: 2.47x parallelism on 16 cores, five single-test binaries
being 40% of the wall. And **nextest is 3.5x slower than `cargo test` on the
heaviest binary** (399 s vs 114 s), so the runner is likely costing real time.
Next: a timer on s5/s7 — which **measured today cannot run it** (no stable, no
1.88.0, no nextest; 342 and 422 commits behind) — read by a freshness step in
`just check`, not a dashboard.
Detail in [`../notes/102-local-ci-run.md`](docs/plan/notes/102-local-ci-run.md).

**Lean's kernel accepts all 470 declarations of the constructed-real carrier;
it is Lean's ELABORATOR that refuses four** (`WIP`, creal-lean-divergence,
2026-08-18). The handover said our kernel admits what Lean's kernel rejects. It
does not. `scripts/lean/replay-lean4export.lean` drives
`Environment.addDeclCore` from our NDJSON — Lean's kernel, from
`mkEmptyEnvironment` — and over the **whole** carrier reports `environment now
holds 470 constants` in **1.4 s**. Tampering `CReal.Equiv.not_zero_one`'s proof
makes the same binary reject it naming `Not (CReal.Equiv (CReal.ofRat Rat.zero)
(CReal.ofRat Rat.one))`, so it checked *that* declaration against *that* type.

**The mechanism, isolated to one token per line.** Lean's elaborator does not
unfold a `theorem` while reducing; its kernel does. Re-spell every `theorem` in
the *same emitted file* as `def` — nothing else changed — and the elaborator
accepts it: the `not_zero_one` module (695,655 B) in 5.0 s and the **whole
carrier** (2,541,928 B) in 27.9 s, against 4 refusals as emitted (two, plus two
`unknown constant` cascades).
`Nat.gcd`'s descent is justified by the *theorem* `Nat.mod_lt`, so `gcd 0 3` is
accepted and every recursive `gcd` refused, while `Nat.mod/div/sub` and a bare
`WellFounded.fix` reduce fine. Not the sharing pass (hand-inlined: identical
refusal), not a budget. `internal exception #3` is the command abort.

**The coverage hole is closed.** Emission was reachability-driven, so Lean saw
only the reachable slice (343 of 465 when ADR-0511's lane measured it).
`real_lean_creal_carrier_kernel_replay` exports the complete environment and
requires Lean's constant count to **equal** our kernel's, so "accepted" cannot
mean "accepted a subset"; `real_lean_wellfounded_elaborator_divergence` pins the
residue. Gate **20 suites, floor 212 -> 218**; measured `declared=470
lean_kernel_constants=470`, `checked=2`/`checked=4`. Mutations bite: dropping
one theorem record kills the carrier suite on the COUNT alone (469 vs 470, Lean
still accepting); a no-op `theorems_as_defs` kills the divergence suite on the
`def` row alone; each left the other green. The fix (`theorem` -> `def` in the
renderer) is measured and handed to the renderer's owner, not taken here.

ADR-0517. Detail in
[`../notes/103-creal-lean-divergence.md`](docs/plan/notes/103-creal-lean-divergence.md).

**`scripts/check-local-ci-freshness.sh` exists and is wired in REPORT-ONLY
mode** (`WIP`, local-ci-freshness, 2026-08-18). Continues 102-local-ci-run's
proposed-not-landed piece: a record for `scripts/local-ci.sh --record` proves
nothing by itself — it can be green for a sha nobody has built on in days, a
rebased-away branch, or a step array that disagrees with its own top-level
`verdict`. This checker re-derives pass/fail from the record's own `steps[]`
(never trusts the summary field) and requires the sha be HEAD-or-an-ancestor
and no older than 48h (chosen over a commit-count budget: velocity measured
7–10 commits/h in bursts across lanes, so a fixed commit ceiling is either too
strict in a burst or too loose on a quiet weekend; the run's own cost —
~107 min, one lock across the whole fleet — sets the 48h floor).

**Wiring is ENFORCING in both `scripts/check.sh` and `justfile`'s `check`**
(`e3e105cd6`, 2026-08-19). It was `--report-only` for one day, deliberately,
because the only record that existed was `a6ee37c6a-s4.json` with
`verdict: FAIL` — enforcing then would have red-ed the aggregate gate for every
lane over a 110-minute run nobody had re-triggered, and a gate that is red from
the day it lands is one people learn to ignore. That was the whole blocker and
it is gone: `57af69142-s4.json` is `PASS`, `rc: 0`, 6656 s, `7561 tests run:
7561 passed`, 179 doctests, no `vacuous` and no `unreadable` step.

Nine guards, each mutation-tested by deletion to kill exactly one control. The
near-miss worth keeping: the first fail/vacuous/unreadable fixtures carried a
top-level `verdict: "FAIL"`, so the separate top-verdict guard silently did the
per-step guards' work and deleting one of them killed **zero** controls. Fixed
by making those fixtures top-level `PASS` with a bad step — which both isolates
the guards and is the more dangerous case: a record falsely claiming PASS while
hiding a bad step.

The flip was re-tested through the real call site, not the control suite.

Detail moved to [`../notes/104-local-ci-freshness.md`](docs/plan/notes/104-local-ci-freshness.md).

Detail: [`../notes/104-local-ci-freshness.md`](docs/plan/notes/104-local-ci-freshness.md).

**`scripts/local-ci.sh --record` PASSED at `57af69142`, and
`check-local-ci-freshness` is now ENFORCING at both call sites** (`DONE`,
local-ci-run-2, 2026-08-19). Record: `artifacts/local-ci-runs/57af69142-s4.json`
— 5/5 steps `pass`, rc=0, 6656 s wall. Steps: fmt 4 s · stable clippy
`-D warnings` 29 s · MSRV 1.88 check 15 s · `cargo nextest --profile local
--workspace --all-features` **7561 tests run, 7561 passed** (87 slow, 32
skipped) in 6588 s · doctests **179 passed** in 20 s. Zero `FAIL [` lines in
the run log, cross-checked against the record rather than read off the exit
code. The four golden-pin failures in the first record (`a6ee37c6a`, FAIL
rc=100) were genuinely fixed by `31442bd5d`; nothing else regressed, and the
suite grew 7511 → 7561 tests in between.

**The `tests: -1` bug is confirmed fixed by measurement, not by reading the
patch**: the old record recorded `-1` for the 7511-test sweep (nextest indents
its `Summary` five spaces, the pattern was `^`-anchored), so the vacuous-step
guard could not fire on the one step it exists for. This record reads 7561.

**Flipped to enforcing** in `scripts/check.sh` and the `justfile`'s
`local-ci-freshness` recipe (plus the checker's own header, which still
described itself as report-only). Then proved the enforcing call site's exit
status depends on the finding, through `just`, not just through the control
suite: empty record dir → rc=1 `NO_RECORD`; a copy of this record with
`finished_utc` backdated 5 days → rc=1 `STALE: 120h`; the nextest step
rewritten to `vacuous` → rc=1 naming that step. All 9 controls green.

**Standing cost this imposes on every lane:** the sweep is ~110 min behind one
box-wide lock and the budget is 48h, so roughly one lane per day must run
`scripts/local-ci.sh --record` and commit the record. It needs `setsid` — a
foreground shell caps at 10 min and an ordinary background job was killed at
59 m 59.9 s with no record written (the recorder only writes at the end).

Detail: [`../notes/105-local-ci-run-2.md`](docs/plan/notes/105-local-ci-run-2.md).

**Done (`DONE`, doc-refactor, 2026-08-19).** `docs/refactor-2026-08/` corrected
against 2026-08-18/19, by amending specific claims and keeping the original
reasoning visible — no rewrites. Five files touched of 18; thirteen left alone
because dated lane diaries are records, not assertions about now.

Corrections, each re-measured here rather than taken from a brief: `04` G2 said
"Unfixed" (`check-clippy-complete.sh` is in both gates); ADR count 455 → `rows=523`;
G4–G8 added (ADR `--check` exiting 0 on duplicates, the mutation harness scoring
a non-building mutant as a kill, axiom-freedom run by no gate, `local-ci.sh`
never having run, `just check` aborting at #18 of 41 so 23 gates never ran).
`gate-divergence-2026-08-14.md`'s 112/61 → 203/278 and its completeness ordering
INVERTED — while `aggregate-scope` was red at #18 the no-`just` fallback was the
more complete gate. `00` gained the three new hygiene incident classes and a
closing open-items list; `06` gained the shared scratchpad.

**Open, and recorded as open in `00` and `04`:** `check-aggregate-scope`'s 32
unrecorded steps (fix by wiring, not re-pinning); ADR numbering's structural fix
(non-sequential allocation, unbuilt); no `axeyum-lean-kernel` suite registered
with the mutation harness (six are: five Python plus `fp-width-guard`).

**Found while writing, not in the brief:** the record
`check-local-ci-freshness.sh` enforces has five steps; `local-ci.sh` has had a
sixth (the frontier ratchet) since `69f2cffb8` the same morning. The gate reports
`PASS -- fresh, ancestor, all-pass` over a run in which that step did not exist.
Freshness of a record is not coverage by it. Owner: whoever owns `local-ci.sh`.

**Not touched, deliberately:** CLAUDE.md still says to treat `just check` as the
gate and `check.sh` as the fallback that may lag it. G8 inverted that for the
duration of the red-gate window. It is the repository's most contested file and
outside this lane's paths.

**The strand's headline claims were falsified in both directions and are now
corrected in place, not rewritten** (`WIP`, doc-formalized, 2026-08-19).

- **"Theorems the system proved without a human writing the proof: zero"** —
  false since 2026-08-18. Three facts are `kernel-term` / `checked` / empty
  footprint, and all three re-derive today (`check-autogenesis-fact-operation.py`
  exits 0 on each). Two are `Eq.refl` from a blind producer (2 of 138 rows); the
  third (`Nat.fib_add_two`) was built by a target-specific program and repaired
  by hand across two failed runs, so it fails the autogenesis programme's own
  autonomy bar. **C2 — solver refutation → library theorem — is still zero.**
- **The 149/day rate**: the counter reads **139, unchanged**, on 2026-08-19 —
  6.4/day over 5.16 days. But it counts one prelude and production moved off it
  (Int: 57 derived, axiom-free). **No tool measures this project's theorem rate.**
- **"Lean's own kernel accepted an axeyum development"** was true and narrower
  than it read — reachability-filtered, 343 of 465. ADR-0517/0518 now live in
  the strand: Lean's kernel takes all 470 carrier declarations, its elaborator
  refuses four, our kernel is **not** the permissive one, and any decline census
  must name which checker it ran.
- **C1 (shard `nat_prelude`) is DONE and did not deliver.** 845 lines in eleven
  modules, first splits 2026-08-14; five days of collision-free library produced
  +33 theorems. `N x 149/day` is falsified by its own remedy.
- Stale status blocks in `03`/`04` (13-of-40, population UNSTARTED, "import ℚ
  and ℝ", "`#print axioms` run by hand") left visible with what falsified them.

Measured, not cited: trusted surface `…/rat/string 0 · real 30`; front door
1,304,276 / 1,330,091 / 1,442,247 B, zero carrier axioms, `Real` control
non-vacuous; `check-lean-gate.sh` green at **21 suites, 66 tests, 473 checks**
(floor 219) — **40 of 77 crosscheck families are attestations**, now in `03`
because "473 modules read" is not "473 propositions proved".
Detail: [`../notes/107-doc-formalized.md`](docs/plan/notes/107-doc-formalized.md).

**The persistent pre-push checkout no longer inherits the caller lane's Git
metadata (`DONE`, codex-autogenesis-prepush, 2026-08-20).** Git exports
`GIT_DIR` and related local variables to hooks; previously, `git -C` changed
the filesystem path but still detached and rewrote the caller's HEAD/index.
`prepare-prepush-worktree.sh` clears those variables at the foreign-worktree
boundary, checks out and cleans the exact target, then fails unless its
registered HEAD and status agree. The registered control preserves a caller
with staged and untracked work across fresh and reused gate checkouts and
rejects an unsafe root and nonexistent target.

The first post-repair Rust push checked exact topic SHA `24b16642e` in the
registered gate checkout, left it clean, and preserved the caller branch,
index, and status. The operational incident is closed; future changes remain
covered by the registered control and the live hook.

**Three of the 26 uncertified string UNSATs now carry a re-derivable
certificate; the other 23 need regex/`replace`/`contains` reasoning, not
lengths** (`WIP`, string-cert, 2026-08-20).

The refreshed dominance audits
(`bench-results/dominance/qf-{s,slia,seq}-cvc5-regress-clean-dominance-audit.json`)
list 26 rows at `evidence_kind = bare-unsat`, every one decided by
`smtlib-string-front-door` with `certified=false checked=false`. A length /
code-point abstraction plus a Farkas-style linear refutation closes the three
that are arithmetic once the strings are abstracted away (`str004`, `str005`,
`str-code-unsat-2`). The remaining 23 are regex membership, `str.replace`,
`str.contains`, lexicographic order, `seq.nth` congruence, and one pigeonhole
over `str.to_code` — none of them a length argument, and none of them silently
approximated.

Next: the `str.to_code` **injectivity** lemma
(`code(y) = code(z) ∧ code(y) ≥ 0 → y = z`) would take
`r1_QF_SLIA_str-code-unsat`, whose refutation is linear right up to the final
`distinct`; its sibling `-3` additionally needs pigeonhole over seven pinned
code points and is a different argument.

**The decision route and the evidence route agreed again on
`QF_NRA/.../cli__regress0__nl__issue3003.smt2` (`DONE`, agent-route-divergence,
2026-08-20).** `check_auto_explained` said `sat` in 0.9 ms; `produce_evidence`
said `unknown certified=false checked=false`. Both run the same exact real-root
decider, so the decider was never the difference — the evidence route replays
its candidate model through the ground evaluator first (the Hard Rule), and the
replay was failing on a CORRECT model.

`poly_big::combine` reaches an operand's interval only by bisection, and
bisecting toward a *rational* root lands the midpoint exactly on it: the
interval collapses and the code declined. Every rational lifted by
`from_rational` hits that on its first refinement, so `c + α` — here
`1 + (−3/4)`, from the witness `y = −√3/2` — never computed. A collapsed
interval is more information, not less: the operand is exactly that rational, so
`α + c` is a root of `p(x − c)` and `α · c` of `p(x / c)`, isolation carried
over by bijection instead of re-derived inside a resultant's interval. Accepted
under `combine`'s own criterion (opposite endpoint signs, exact Sturm count 1),
so a decline stays a decline.

The instance now reports `sat-model certified=true checked=true`. Worth noting
for the next lane on this axis: nothing else in the tree compares the two routes
on the same query, so a divergence is only visible when someone points
`diagnose_evidence` at a file by hand.

**The three `QF_NRA` corpus rows that `nra_product_cert` explicitly declined now
carry a re-derivable certificate, including the one whose exact refutation does
not fit in `i128`** (`DONE`, agent-handelman, 2026-08-20).

`cli__regress1__nl__coeff-unsat`, `cli__regress1__nl__combine` and
`cli__regress1__nl__approx-sqrt-unsat` all shipped as bare `Evidence::Unsat(None)`
— decided, unfalsifiable. Each needs more than one product term, which is
exactly what the two-factor route was written to refuse rather than guess at.
All three now report `real-handelman-unsat certified=true checked=true`.

The producer does not implement a Positivstellensatz search from scratch: it
abstracts every monomial to a fresh real variable and hands the resulting linear
system to the exact Fourier–Motzkin/Farkas engine already in `lra.rs`, then reads
the multipliers back. The checker never runs an LP — it binds each carried atom
to something the query literally asserts and multiplies the polynomials out — so
producer and checker can disagree, which is the property a `fresh == certificate`
re-run does not have.

The interesting one is `approx-sqrt-unsat`'s third disjunct, whose constant is
`2.0000000000000000000000000001`. Its exact refutation needs `(2+k)²`, numerator
`1.6·10^57`, and `Rational` is an `i128` fraction — so no exact `i128` derivation
of that refutation exists and an approximate one is not a certificate. A
certificate atom may therefore carry a **relaxation** `r ≥ 0` and the derivation
uses `nonneg_form(atom) + r`: still implied by the atom, still something the
query licenses, and rounding the constant up to `2.000000000001` puts every
product back inside `i128` with margin. The relaxation is carried and re-derived,
never assumed; only the one disjunct that needs it has a nonzero one, and a test
pins that.

Next on this axis: the equality multiplier basis is degree ≤ 1 and products are
pairwise, which is what the committed corpus needs and no more. A shape needing a
degree-2 multiplier or a triple product will decline rather than approximate.

**`build_creal_prelude` went 8.7 s → 33.0 s across `502184d3f`, and the kernel
was missing the second of Lean's two reduction caches. Adding it takes it back
to 13.0 s** (`DONE`, agent-prelude-perf, 2026-08-20).

The bisected commit aligns the native `Bool` with official Lean order and is
correct. What nobody noticed is what that *switched on*.
`Kernel::build_nat_binop_table` admits the literal-`Nat` acceleration only in an
environment whose `Bool` has constructors `[false, true]` **in that order**
(ADR-0459). While `Bool` was `[true, false]` the table was `None` and every
probe returned immediately — the whole rule had been dead since it landed.
Aligning `Bool` turned it on, and in this workload it fires **1,192,536 times
and produces a literal 575 times** (0.05%). Every one of the 1,191,961 failures
δ-normalises *both* arguments, from inside the δ-**free** normaliser, so the work
lazy-delta exists to avoid is done eagerly and speculatively. 99.98% of the
probes are on terms that mention a free variable.

Measured by disabling the rule at HEAD: 33.6 s → 10.0 s. The regression is that
rule, not the constructor order.

The fix is a memo, not a change to any reduction rule: `Kernel::whnf_core` (the
δ-performing normaliser) had no cache at all, only its δ-free inner step did.
The pinned reference carries **both** — `type_checker.h:31-32` declares
`m_whnf_core` *and* `m_whnf` — so this is convergence on Lean, not a local
trick. The whole δ chain is memoised, not just its head, because every δ step
mints a fresh expression that no cache has ever seen.

Acceptance is unchanged by construction: the memo returns exactly what the walk
would have returned, the key is complete (revision + expression, split on
`has_fvars` exactly as the δ-free memo is split, with the same `push`/`pop`
scoping), and the closed half is covered by the existing `reduction_ctx_reads`
tripwire.

Verified: `prelude_build_timing` creal 33.0 s → **12.98 s** and template reuse
0.41 s → 0.15 s; `axeyum-lean-kernel --lib` **398 passed**;
`axeyum-solver --features full --lib reconstruct::` **300 passed** in 186 s
against the ~294 s this suite normally takes, because it builds preludes;
`gen-lean-axiom-ledger.py --check` exit 0 with `axreal=30` and every other
prelude 0, unmoved; clippy `--workspace --all-targets --all-features -D
warnings` clean. Peak RSS of a full uncached prelude sweep is 512 MB against
368 MB before — the debug unit sweep's multi-GB profile is pre-existing and was
measured on a clean HEAD snapshot to rule the memo out.

Next on this axis, and the remaining 6.7 s: **our nat rules are in the wrong
loop.** Lean calls `reduce_nat` from `whnf` — after `whnf_core`, before δ
(`type_checker.cpp:765`) — and in `lazy_delta_reduction` guards it with
`!has_fvar(t_n) && !has_fvar(s_n)` (`type_checker.cpp:1093`). Ours is called
from inside `whnf_no_unfolding_uncached`, which *is* Lean's `whnf_core`, with no
`has_fvar` guard anywhere. ADR-0459 already describes the intended placement as
"tried after `whnf_core` and before δ", so the code does not match its own ADR.
Moving it changes what the kernel identifies, so it needs an ADR and differential
evidence, not a perf commit — but the prize is measured: with the rule off and
this memo on, the same build is **6.56 s**, better than the pre-regression 8.7 s.

**`Kernel::reduce_nat_binop` now sits where Lean calls `reduce_nat` — in the δ
loop and in lazy-delta, never in the δ-free step — under Lean's `has_fvar`
guard. `build_creal_prelude` 12.99 s → 6.79 s, and nothing stopped admitting**
(`DONE`, agent-nat-rule-placement, 2026-08-20).

ADR-0459 described the placement as "tried after `whnf_core` and before δ". The
code called it from inside `whnf_no_unfolding_uncached`, and that function *is*
Lean's `whnf_core` — one layer too deep, with no `has_fvar` guard anywhere. In
the pinned reference (`v4.30.0`, `d024af09`) `reduce_nat` is called from
`type_checker::whnf` at `:670` and from `lazy_delta_reduction` at `:978`, the
second under `!has_fvar(t_n) && !has_fvar(s_n)`. Both are now ported; the
`whnf_core` site also carries the guard, which is stricter than Lean and is the
decision ADR-0536 records.

**The placement alone buys nothing — the guard is the whole prize, and that
distinction is the finding.** Three interleaved rounds, release,
`AXEYUM_PRELUDE_CACHE=0`, `taskset -c 0-7`, median `creal` seconds: before
**12.99**, Lean's placement unguarded **12.12**, Lean's placement + guard
**6.79**. 12.99 → 12.12 is inside this workload's run-to-run spread on a shared
box. The rule fires 1.19 M times per `build_creal_prelude` and produces a literal
575 times, and 99.98% of the probes are on a term that mentions a free variable —
so the O(1) structural guard removes essentially all of the cost, and moving the
call site removes essentially none of it. For scale, 8.71 s was the time *before*
the acceleration was ever switched on.

**Identification is unmoved, measured rather than argued.** `axeyum-lean-kernel`
lib **399 passed / 0 failed**; the full kernel crate (lib + all 46 integration
suites) **609 passed / 1 failed**, the one being
`real_lean_wellfounded_elaborator_divergence`, which fails **byte-identically on
an unmodified `HEAD`** in a snapshot tree and is a *Lean elaborator* rejection,
not ours — a live separate finding, flagged for whoever owns ADR-0517;
`axeyum-solver --features full --lib reconstruct::` **312 passed / 0 failed**;
clippy 618/618 targets, 0 diagnostics; `check-prelude-reuse-equivalence.sh`
`compared=8 failures=0` with live counters;
`gen-lean-axiom-ledger.py --check` exit 0 with
`total=30 axreal=30` and every other prelude 0. No declaration stopped admitting.
That is a measurement over this repository's corpora, not a proof: the class the
guard gives up is nonempty and a fixture constructs one — `Nat.mod ((fun _ => 7)
x) 0`, whose operands reduce to literals while `has_fvars` is structurally true.
Our corpus simply does not reach it.

Four mutations, each alone: dropping either `has_fvars` guard kills exactly one
test, dropping the `whnf_core` call site kills exactly one, and dropping the
lazy-delta call site kills five — one of them by **overflowing the stack** on
`2^64`-scale literals, which is ADR-0459's unbounded-successor-chain hazard
reproducing on demand. That is which of the two sites carries the rule's reason
for existing.

Next on this axis: `reduce_nat_succ` is still in the δ-free step, a residual
divergence from Lean's `reduce_nat`. It is one interned-name comparison per
constant-headed reduction step, so it is not a cost today — revisit only if a
profile says otherwise, since moving it would change identification for no
measured gain.

**All 35 dominance audits re-run at `496288979`; the fully-dominant UNSAT count
is 269 / 326, not 262 / 324, and five of the fifteen "Lean-reconstruction gap"
rows were stale records rather than gaps** (`DONE`, agent-audit-refresh,
2026-08-21).

Every committed audit was stamped between `2e207eba5` and `562b65f13` — all of
them before today's reconstruction work landed — so the artifact said "gap"
about instances the code had already closed. Four rows moved and 31 are
identical in every summary field, which is what makes the two runs comparable.

**+5 of the +7 dominant outcomes are capability; +2 are the instrument.**

- Capability, QF_NRA `qf-nra-cvc5-regress-clean` 21/32 → 24/32:
  `coeff-unsat-base` and `simple-mono` reconstruct as `RealProduct`
  (`71f1c29a0`), `ones` as `MonomialBound` (`77c70d3e0`).
- Capability, QF_S `qf-s-cvc5-regress-clean` 9/93 → 11/93: `r0_QF_SLIA_str004`
  and `r0_QF_S_str005` gained a kernel-checked `StringLength` module
  (`b495a396e`).
- Instrument, QF_NRA `qf-nra-synthetic-graduated` 31 → 33 audited: the two
  `d01` instances were being billed for a process-wide ~32 s `CReal` prelude
  build inside a 10 s per-instance cap. `562b65f13` moved that build outside the
  timer. A/B, corpus and cap fixed: `1fff66825` 31, `cfc5f8078` 31,
  `71f1c29a0` 33, `71f1c29a0` with the warm suppressed **31**, HEAD 33, HEAD
  with the warm suppressed **33** — the last row because `0887ab652` made the
  prelude cheap enough to pay for inside the cap. This is the whole baseline
  denominator movement, 324 → 326.

**A directory-backed audit row silently drops an instance it fails to decide.**
That is how those two went missing while the row reported `timeouts 0`: the
directory branch `continue`s past an undecided instance and leaves no record, so
numerator and denominator shrink together. Only the two synthetic rows take that
branch; the instances-array branch records the row instead. Not fixed here.

**The audit's `lean_error` is the fallback route's message, not the fragment's
reason.** All six QF_NRA gap rows classify as `Lra`, so the facade falls through
to the generic LRA route and records *its* complaint (`QF_LRA: nonlinear real
multiplication`). Calling the fragment entry points directly gives the real
answer, and the three that matter split two ways: `simple-mono-unsat` and
`subs0-unsat-confirm` are **principled declines** — their bound / zeroing case is
only *entailed*, by `(or …)`, and minting it would put a proposition in the Lean
module no assertion states; closing them needs kernel case analysis, not a
looser mint. `mult.01` is **unimplemented and scoped**: the `Exactly` bound
refuting `M != k` needs the upper bounds and an equality transport. The three
`real-handelman-unsat` rows have no reconstruction at all and are the largest
single QF_NRA item left. Per-instance table is in the gap analysis.

Next on this axis: the three Handelman reconstructions; the `Or.rec` case
analysis that would close the two principled declines; and the dir-branch drop,
which makes a synthetic row's denominator depend on what the audit could decide
that day.

**`QF_FP/solver__fp__fp_misc.smt2` timed out because `array_bv_abs::abstract_term`
walks a DAG as a tree; memoized, the row goes from 124.7 s of a 125 s budget to
314 ms. It is now certified and independently checked and it is still not
dominant, and that second half is correct rather than unfinished** (`DONE`,
agent-fp-misc-hang, 2026-08-21).

**The null was the finding.** `audit_dominance` fills `timeout_phase_detail`
from `scan_proof_fragment` *before* reconstruction starts, so `fp_misc`'s
`detail: null` meant classification itself never returned — while three sibling
rows in the same run did name their fragment, which is the positive control that
the mechanism worked. Eight of eight `gdb` samples, 100% of the axeyum frames,
were in `abstract_term`, self-recursive dozens of frames deep. `perf` and a bare
`gdb -p` are both blocked on this host (`perf_event_paranoid=4`,
`ptrace_scope=1`); an unprivileged sampling loop returns an empty file that reads
exactly like "nothing to see". `sudo gdb -p` works.

**Every cap in that module was on the walk's RESULT.** `MAX_ABSTRACTED_TERMS`,
`MAX_ABSTRACTED_NODES` and the 1 s solve timeout all run after
`build_bv_abstraction` returns, so nothing bounded the walk itself. Memoizing
took `fp_misc` from 4,194,309 visits to 4,365 over 5,762 reachable nodes; the new
visit budget is what makes the memo's guard fail in 0.23 s instead of hanging.
Sixth instance of this bug in this repository, and the second this week — the
2026-08-20 pair (`contains_quantifier`, `lower_derived_bv`) were latent behind
routes nothing reached until `887b52e64` made FP rows decline `BvDefinedEnum`,
which is the same commit that exposed this one.

**Not dominant, and that is the honest answer.** The 2026-07-21 row was dominant
through `bv_defined_enum`, which `887b52e64` deliberately withdrew for FP
arithmetic pending a certified `Fpa2Bv` reduction — pinned by that commit's own
`declines_qf_fp_misc_without_certified_fpa2bv`. `fp_misc` now decides through
bit-blast with an explicit `bit-blast` trust hole. `trust_holes: ["timeout"]`
becoming `["bit-blast"]` is the whole improvement, and restoring dominance means
certifying `Fpa2Bv`, not raising a budget.

**`QF_BVFP/Float-no-simp3-main` is a budget, but not the one that was recorded.**
The standing note said "decision is 4.6 ms but its evidence still exceeds 120 s".
Measured at HEAD, `produce_evidence` returns in 19 ms and nothing times out. The
same `887b52e64` decline removes its certifying route, and what it falls back to
is a bare `unsat` only because `produce_evidence` skips
`reduction_unsat_certificate` **outright** whenever `config.timeout` is set —
which `audit_dominance` and `diagnose_evidence` both always do. Run the same
export unbudgeted and it is `proved` in **28.3 ms**.

I did not loosen that guard, and the measurement says why not: the `deadline` it
would rely on reaches only `solve_with_drat_proof_within`. `lower_terms`,
`tseitin_encode`, `check_drat` and the LRAT elaboration are all unbounded, and
the guard covers 42 bare-`unsat` rows across the committed audits. Landed
instead as a two-test pair asserting opposite outcomes on the same instance, so
neither can pass vacuously and either direction of change breaks one.

Next on this axis, in cost order: thread the deadline through
`export_qf_bv_unsat_proof_impl`'s unbounded phases and then narrow the blanket
budget guard to a real remaining-time attempt (this alone would move
`Float-no-simp3-main` and any other BV-reducible bare `unsat` to certified);
then `Fpa2Bv` certification, which is what both FP rows actually need for
dominance.

**Status:** Exact official Lean 4.30 `Nat.fib_coprime_fib_succ` remains durably `proved` through dependency-bound receipt `34b9aad06fc8a640c81df0951b1af37a464f2d9305c048784e4f590b83ff0d0e`, and its sole newly ready child `F:ml430-nat-gcd-fib-add-self-5a92d5e3` remains open. Bottom-up Euclidean reconstruction has unconditional official balanced Bézout. Residual cancellation removes five measured carriers and accepts a clean additive divisibility-witness leaf; the remaining multiplicative witness footprint is now localized exactly to this stream's direct-`propext` `Nat.mul_assoc`, for which an accepted clean target-owned leaf already exists.

**Next:** preregister residual V2 with multiplication associativity added to the explicit parameter list, then reconstruct the multiplicative witness and residual theorem twice. Preserve zero official cancellation/Fibonacci authority until all residual roots are empty-footprint.

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

Detail moved to [`../notes/51-induction-dispatch.md`](docs/plan/notes/51-induction-dispatch.md).

**`string` is axiom-free (`DONE`, agent-strings, 2026-08-17).** The last
prelude assumption outside `real` is retired: `axeyum.string.<n>.append` was a
`Declaration::Axiom` and is now a checked structural recursion over `Str.rec`,
with `nil_append` / `cons_append` / `append_nil` / `append_assoc` admitted as
`Declaration::Theorem`s the kernel re-checks (ADR-0513). Measured, not read off
the diff: `nat_axiom_inventory` reports `string: axiom=0 opaque=0 quotient=0`,
and the derived ledger is `total=30 | real=30 | everything else 0`. Verified
outside this kernel as well — a real `lean` 4.34.0-rc1 accepts the exported
module and its `#print axioms` lists only the problem's own opaque words.

The whole trusted surface of this project is now the `real` prelude (30 rows,
being constructed under ADR-0512 by another lane).

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

Detail moved to [`../notes/53-nat-int-characterization.md`](docs/plan/notes/53-nat-int-characterization.md).

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
[ADR-0514](docs/research/09-decisions/adr-0514-the-pinned-lean-toolchain-is-the-one-that-runs.md)
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

Detail moved to [`../notes/54-lean-toolchain.md`](docs/plan/notes/54-lean-toolchain.md).

**ℤ is now pinned up to bijection, and the limit of that is stated rather than
blurred (`DONE`, agent-int-categoricity, 2026-08-18).** Lane
`agent-characterization` closed ℕ and named its own gap exactly: for ℤ only the
**uniqueness** half of the universal property was proved, so those properties
were proved to *hold* of `Int` and not to *determine* it. `rec_unique` was
uniqueness of a map nobody had constructed.

Built in `crates/axeyum-lean-kernel/src/characterization/int_categoricity.rs`,
declaring into the existing `Int.Characterization` namespace:

Detail moved to [`../notes/55-int-categoricity.md`](docs/plan/notes/55-int-categoricity.md).

**ADR-0512 phase R3 has landed: the ring interface takes equality as a
parameter, 30 → 39, and instantiating it back at `Eq` reproduces today's
statement node for node (`WIP`, agent-r3-telescope, 2026-08-18).**
`LraReconstructCtx::enable_setoid_equality` declares nine equality-interface
axioms (`eq`, `eq_refl`/`eq_symm`/`eq_trans`, and `add`/`mul`/`neg`/`le`/`lt`
congruence) plus the nine `Eq`-stated `Real` laws **restated through them** —
whose types are computed from the environment by rewriting the partial
application `Eq Real` to `eq`, never written out, so a changed law changes its
restatement rather than silently disagreeing with it. Every equality step in the
LRA/SOS reconstruction then routes through the slot, and
`RingTelescope::SetoidInterface` binds 39. All five fixtures of
`cargo run -q -p axeyum-solver --features full --example ordered_ring_refutation
-- --require-empty`: **39 binders, footprint 0, zero kernel-`Eq` constants left
in the proof term, 30 of 30 non-slot binder types reproduced exactly.**
`farkas_over_the_integers` (9 tests) is untouched — the `Eq` route is the
default and is unchanged.

**Why the five congruences are exactly five is a measurement, not a taste.**
Every `Eq.rec` in the whole arithmetic reconstruction sits inside one of eleven
helpers, and those eleven collapse onto symmetry, transitivity, `add`- and
`mul`-congruence (each left and right), `neg`-congruence, and the `le`/`lt`
casts (each left and right). One-sided congruence is the two-sided law with
`eq_refl` on the argument that does not move, so the two-sided form is what gets
bound. Nothing else in the LRA or SOS routes touches `Eq` at the carrier.

Detail moved to [`../notes/56-r3-telescope.md`](docs/plan/notes/56-r3-telescope.md).

**The `Sos` route stopped attesting and started reconstructing: nine
content-free skeletons and one declined module became ten *bound* ones
(`WIP`, agent-sos-normalizer, 2026-08-18).** Gate line
`python3 scripts/check-lra-hypothesis-binding.py`:

    before  instances=125 | structural=95 | attested=28 | failures=0
    after   instances=135 | structural=95 | attested=19 | failures=0

with `hypotheses` 288 → 298, `mutants_caught` 1210 → 1259, `mutants_accepted`
unchanged at 427, `represented_assertions` 286 → 296.

**The whole gap was one predicate, and it was never mathematical.** A degree-2
SOS certificate's Gram matrix is `(n+1)×(n+1)` over the *homogenized*
`v = [x₀ … x_{n−1}; 1]`, so `p(x) = vᵀMv` and `M = LDLᵀ` gives
`p = Σₖ dₖ·(Σᵢ L[i][k]·vᵢ)²` — in which the last coordinate is the constant `1`.
`SosCertificate::rational_squares` nevertheless declined any column with
`L[n][k] ≠ 0`, and the comment said why: the reconstructor's linear-form builder
could emit variables and nothing else. Every corpus row that needs a constant
term — `Σ xᵢ² + 1 < 0` (k01…k08) and `(x−1)² + (y−2)² + 1 < 0` — fell through to
a `prop._0` wrapper that renders `axiom P; axiom Not P` and says nothing about
the query. `rational_affine_squares` returns the affine entry under the index
`n_vars`; `int_affine_lin_to_rexpr` maps that index to the ring's `one`; the
degree-2 ring normalizer has had `Mono::Const` all along. The kernel still
re-proves `M·p = Σ (M·wₖ)(ℓₖ⁺)²` and declines on a canonical-generator mismatch,
so a wrong index convention would decline rather than fabricate.

Detail moved to [`../notes/57-sos-normalizer.md`](docs/plan/notes/57-sos-normalizer.md).

**Round 3: a fourth kernel-vs-Lean defect found and fixed, and the corpus
widened from 51 families to 66 over a development that finally carries the
constructs the kernel works hardest on (`DONE`, agent-kernel-adversary-2,
2026-08-18).** Rounds 1 and 2 damaged a `Prop`-only development, so 51 families
were rewiring the same handful of record shapes. Round 3 put a Type-valued
STRUCTURE (with a theorem provable only by structure eta), a `Nat` LITERAL (with
a theorem provable only by literal/constructor conversion), an INDEXED family, a
PARAMETERIZED recursive family, a MUTUAL group, an `axiom`, an `opaque` and the
`abbrev`/`opaque` reducibility hints on the wire, and added 15 families for
fields nothing had ever damaged: `levelParams` and `all` on families,
constructors and recursors; universe-parameter PERMUTATION at the binding site
and at the `Const` reference; a short universe-argument list; ι-rule right-hand
sides exchanged between rules of one recursor, and the rules permuted.

Detail moved to [`../notes/58-kernel-adversary.md`](docs/plan/notes/58-kernel-adversary.md).

**ADR-0512 phase R4 has landed: the `Real` axiom package is modelled by the
CONSTRUCTED reals, and ADR-0456's "`Int` is not ℝ" caveat is discharged
(`WIP`, agent-r4-model, 2026-08-18).** `build_creal_model_of_arith` admits one
theorem per law,

```text
Real.CRealModel.<law> : ⟦ type of Real.<law> ⟧ := CReal.<law>
```

with `⟦·⟧` **computed from the axiom as it stands in the environment** —
`arith_model`'s discipline — so an axiom whose statement changes changes the
obligation and an axiom `CReal` does not satisfy makes the build fail rather
than dropping a row. `cargo run -q -p axeyum-lean-kernel --example
creal_model_witness`: **22/22 witnesses footprint-empty, 22/22 syntactically
the `CReal` law up to binder names, 9/22 restated over `CReal.Equiv`, 7/7
discrimination witnesses**, exit 0.

**The interpretation is not a constant renaming, and that is the whole content
of R4.** `Eq` is polymorphic and `CReal.Equiv` is not, so no map from `Eq`
alone is type-correct; what gets replaced is the *partial application*
`Eq Real`, which is exactly R3's `rewrite_eq_at_real` applied to the axioms
instead of to the telescope. The rewrite is **self-guarding**: fail to fire and
the obligation still reads `Eq CReal …` while the proof proves
`CReal.Equiv …`, so the kernel refuses it. Verified — disabling the match makes
`build_creal_model_of_arith` return `DeclarationValueMismatch` and the example
exit 101.

**9 of 22 is now measured three independent ways.** ADR-0512 Measurement 2
counted `Eq` in the axiom types; R3's η-expansion mutation isolated the same
nine as binder-type mismatches; this model reports `restated_over_equiv` from
whether the rewrite fired, and the nine names agree exactly.

Detail moved to [`../notes/59-r4-model.md`](docs/plan/notes/59-r4-model.md).

**Round 4: `restore_nested_inductive_group` now has adversarial coverage, and
the reason it did not was a defect in the instrument, not a property of Lean
(`DONE`, agent-nested-gate, 2026-08-18).** Round 3 left the fourth admission
gate uncovered and stated why: a NESTED group's *undamaged* stream failed on
`axeyum_wire_rose.rec_1`, read as "`addDeclCore` regenerates the group's own
recursor but not the auxiliary one, so every field of an auxiliary recursor is
a byte Lean never reads". Stopping there was right; the reading was wrong.

Detail moved to [`../notes/60-nested-gate.md`](docs/plan/notes/60-nested-gate.md).

**The reconstruction context's carrier is now a parameter, and the constructed
reals already satisfy it (`WIP`, agent-real-migration, 2026-08-18).**
`LraReconstructCtx` no longer holds an `ArithPrelude`; it holds a
`RingSignature` — the same 31 field names, so all 158 field reads across
`arithmetic.rs`, `ordered_ring.rs` and `setoid.rs` are unchanged — plus a
`RingEquality` saying *which relation plays the role of equality*. `new()` keeps
its contract and supplies the `Real` package's instance; `try_new()` is the same
without the panic; `with_ring_signature(kernel, sig)` is the seam: a caller
brings its own kernel and names its own carrier.

**The signature is checked, not trusted.** `RingSignature::validate_in` runs five
guards — presence of all 30; the carrier is a `Sort` and its level is *measured*;
the seven operation/relation shapes by `def_eq` against types built from the
signature's own carrier; every law inhabits `Prop`; every `Const` in a law
statement is one of the eight symbols, a propositional connective, or the
signature's declared equality. Each guard is its own function with its own
negative test. **Mutation-verified twice** (before and after the split into
per-guard functions): deleting guard 2, 3, 4 or 5 kills **exactly one** test out
of 1191 and no other; deleting guard 1 kills two, which are its two entry points
(`validate_in` directly, and through `with_ring_signature`) rather than one
shared rejection path.

**Nothing changed today, and that is measured rather than argued.**
`cargo run -q -p axeyum-solver --features full --example ordered_ring_refutation
-- --require-empty` is **byte-identical to the pre-change baseline** (`diff`, all
five fixtures: footprint 0, 39 setoid binders, 30 of 30 non-slot binder types,
0 residual kernel-`Eq` constants). `farkas_over_the_integers` 9/9,
`sos_lean_reconstruct` 14/14, `--lib --features full` 1191/1191, clippy
`-D warnings` clean, `RUSTDOCFLAGS="-D warnings" cargo doc` clean (that gate
caught three broken intra-doc links nothing else did).

Detail moved to [`../notes/61-real-migration.md`](docs/plan/notes/61-real-migration.md).

**ADR-0512 phase R4 reaches the reconstruction route: a Farkas/SOS refutation
now reconstructs over `CReal`, and the closed `False` rests on ZERO carrier
axioms (`WIP`, agent-creal-reconstruct, 2026-08-18).** R3 made equality a
parameter of the ring telescope; R4 modelled the `Real` package by `CReal`. The
gap between them was the *proof-term* route: the only way to fill the equality
slot was `enable_setoid_equality`, which **declares eighteen axioms** — nine
slot members plus the nine `Eq`-stated laws restated through them — because the
`Real` package cannot prove any of it. `LraReconstructCtx::adopt_setoid_equality`
is the other half: it takes the nine members from `CRealPrelude`, which proves
every one of them footprint-free, and reads the nine ring laws off the
signature, which under `RingEquality::Defined` already states them over
`CReal.Equiv`.

**Measured, `cargo run -q -p axeyum-solver --features full --example
ordered_ring_refutation -- --require-empty --constructed-reals`:**

| | equality slot | closed `False` footprint | of which CARRIER axioms |
|---|---|---|---|
| over `Real` | **18 axioms declared** | 32–37 | **30** |
| over `CReal` | **0 declarations added** | 2–7 | **0** |

Detail moved to [`../notes/62-creal-reconstruct.md`](docs/plan/notes/62-creal-reconstruct.md).

**The shipped front-door LRA/SOS reconstruction now runs over the CONSTRUCTED
reals, and a refutation it returns rests on ZERO carrier axioms (`WIP`,
agent-creal-default, 2026-08-18).** `PreludeKey::CReal` puts the construction in
the ADR-0464 template, removing the cost objection: `build_creal_prelude` was
**43.97 s** per call in debug and is now **0.149 s** after the first (294x;
release 4.69 s -> 0.067 s). Then `try_new_over_constructed_reals` — the
`RingSignature`/`EqualitySlot` seam plus `adopt_setoid_equality`, from
`CRealPrelude`'s own theorems at 0 declarations added — becomes what
`ProofFragment::Lra`, `DisjunctiveLra` and `Sos` dispatch to, through one
`lra_ctx()` the classifier and the renderer share.

**Measured through `prove_unsat_to_lean_module` itself**
(`examples/front_door_carrier.rs --require-axiom-free`, whose exit status depends
on the finding). Footprint / of which CARRIER: over `Real` 15/**12**, 22/**17**,
10/**8**; over `CReal` 3/**0**, 5/**0**, 2/**0** — the residue is the query's own
variables and hypotheses. The `Real` column is the in-output control; an empty
one would mean the measurement broke, and the flag fails on it.

**Real Lean accepts it, after a renderer defect the flip exposed.** The first
run failed 5 of 77 `lean_crosscheck` families with `Unknown constant
Int.natAbs`: the renderer ordered an inductive by its own type while writing its
constructors inline, and `Rat.mk` mentions a definition emitted 110 lines later.
Fixed renderer-locally — **not** in `decl_deps`, which `axiom_footprint` shares.
77 of 77 now check, 0 failed. The module declares 3/5/2 axioms against 15/22/10
over `Real`, so Lean's `#print axioms` agrees with the kernel.

**The cost is module size:** 2.4-41 kB to ~2.6 MB (66x-1069x), carrying the
whole constructed N/Z/Q/setoid development.
`nat_axiom_inventory --include-constructed` still reports `real: axiom=30`,
`creal=0`, `complex=0`: the package is unused here, not retired.
[Notes](docs/plan/notes/63-creal-default.md).

**The shipped constructed-reals module halved, with what it proves unchanged
(`WIP`, agent-module-size, 2026-08-18).** Through
`examples/front_door_carrier --require-axiom-free` (exit status depends on the
finding, and it exits 0): strict-bound **2,623,005 -> 1,304,276 B**, three-row
2,673,154 -> 1,330,091, sos-square 2,551,806 -> 1,442,247. Carrier axioms still
0/0/0 against the `Real` control's 12/17/8, and the module's `axiom` lines still
equal `Kernel::axiom_footprint` (3/5/2). `scripts/check-lean-gate.sh`: **OK, 462
real-Lean checks under the pinned Lean 4.30.0, `lean_crosscheck` 77 of 77.**

**Bullet one of the brief was already done; bullet three is the real answer.**
`write_lean_module_impl` already opens with a constant-closure walk — the
`CReal` context holds **445** declarations and the module emits **280** blocks,
so selection has no headroom. The final theorem term is 4,193 bytes, 0.16% of
the module. The size is a hash-consed DAG printed as a *tree*: `CReal.mul_assoc`
is 1,296 kernel nodes and **324,609** printed ones.

**Why the existing compact writer saved 0.6%.** `compact_share_candidates`
requires `num_loose_bvars == 0` — a top-level `def` has no binder to read a
loose variable in, and a proof body is almost entirely open terms. Landed:
scope-aware `let` sharing (`ScopeId` = a hash chain over enclosing binder
occurrences; each `let` sits at the top of the innermost body whose binders the
term reads), and the front door switched to the compact writer.

**Raw-DAG sharing is unsound, so 19x is not the ceiling — 7.7x is** (193,197
scope-correct keys against 1,488,996 printed nodes). Achieved 2.01x in bytes: a
reference is overhead against ~3.7 bytes per node, which is why scoped names are
`_sN`. Naming alone was worth more than half the saving.

**A `let` chain is nested syntax** — 2,897 bindings in one lemma blew Lean's
default `maxRecDepth` of 512, so the banner now sets 65536 (elaborator counter
only; the kernel still checks every term).

**Next: a shared prelude, worth ~500x, not more sharing.** It changes the
single-file contract four Lean suites assume and needs an `.olean` build plus
`LEAN_PATH`. ADR-sized. Detail: `docs/plan/notes/64-module-size.md`.

**No shipped route BUILDS the `Real` axiom package, and a counter says so
(`WIP`, agent-retire-real, 2026-08-18).** The ledger's 30 does not move;
ADR-0509 says why rather than working around it. What that number stood for is
now measured and gated.

**The hole found.** `a6ee37c6a` moved the front door to `CReal` and the claim
went out as axiom-free. `ProofFragment::IntFarkas` — also shipped — still built
`LraReconstructCtx::new()`, refuted over the 30, abstracted them back out and
instantiated at ℤ. Its module named no `Real` axiom and its footprint was empty,
so every footprint-shaped check passed while the route built the whole trusted
surface **twice** per query (the scan trial-builds to classify).
`front_door_carrier --require-axiom-free`, the gate for exactly this claim, has
three fixtures, all real-typed: it never reached that arm.

**Fixed by an instance already there.** `IntPrelude` carries all 30 signature
fields with every law proved, so `RingSignature: From<IntPrelude>` is the
interface at ℤ with the kernel's own `Eq` — the corner `Real` (30 axioms) and
`CReal` (defined equality) cannot occupy. All 30 integer declarations are
footprint-empty against 30 non-empty for `Real` in the same test; the four
integer tests take **1.0 s** to the `CReal` tests' **98 s**. IntFarkas refutes
directly there; Lean still accepts the module (172,934 bytes).

**Measured, not argued.** `arith_prelude_builds()` counts calls to
`build_arith_prelude`. Through `prove_unsat_to_lean_module`: **0** on `Lra`,
`Sos`, `DisjunctiveLra`, `IntFarkas`; **1** for the control in the same process.
`F:shipped-front-door-reaches-no-real-axiom`, 7 rows, each proven to fail on
mutated output first.

**Why 30 stays.** They are the digest-pinned kernel statement of the interface
three constructed carriers are checked against, and the NEGATIVE CONTROL for
every axiom-freedom measurement here — delete them and no such claim can fail.
ADR-0509 names the bounded route to declared = 0: move the specification onto
the axiom-free 30-binder telescope the abstraction already produces, then shrink
the control from 30 axioms to one.
[Notes](docs/plan/notes/64-retire-real.md).

**ADR-0510: ℚ is now a FIELD, ℝ has Bishop apartness, and the inverse's
partiality is two theorems rather than a scoping note (`WIP`,
agent-creal-field, 2026-08-18).** The prerequisite nobody had listed:
`Rat.inv` existed from the start as a definition with **no law about it**, so
the development had 22 ordered-*ring* laws and an operation named `inv`.
`Rat.mul_inv_cancel` closes that, plus five derived ordered-field lemmas. Over
ℝ: `CReal.Apart := lt x y ∨ lt y x` with four laws, `CReal.no_total_inverse`,
and `pos_of_pos_bound`/`pos_bound_of_lt` — `0 < x` and `∃ k, 1/(k+1) ≤ x` are
the **same** `Prop`, so the modulus always exists and can never be extracted.
71 `CReal` declarations; `rat` and `creal` trusted surfaces still **0**.
**`CReal.inv` itself is NOT built**; design fixed and cost measured in
[`../notes/creal-field.md`](docs/plan/notes/creal-field.md), which is also where the
next task is.

**ADR-0516: `CReal.inv` is BUILT, and `x⁻¹` denotes one real rather than one
per modulus (`WIP`, agent-creal-inv, 2026-08-18).**
`CReal.inv : (x : CReal) → (k : Nat) → PosBound x k → CReal` — a function may
*take* a `Prop` and return a `Type`, it may only not *branch* on one, so the
**modulus** is the thing that must be data and the proof is only a proof. With
it `mul_inv_cancel` (`x · x⁻¹ ≈ 1` on the positive branch), `inv_congr` — which
quantifies over **two independent moduli**, because two callers with different
`k` for the same `x` build different sequences — and `inv_index_irrelevant`.
Congruence is *uniqueness of inverses in a commutative monoid*, not a second
estimate. **76 `CReal` declarations, trusted surface still 0**; `nat_index_symm`
is the fifth time `Rat.natDivSucc` has been kept off the antitone path. Design,
measurements and what is deliberately absent (the negative branch, `abs`,
cotransitivity): [`../notes/creal-inv.md`](docs/plan/notes/creal-inv.md).

**Both of ADR-0509's reasons for keeping the 30 axioms are discharged in
principle; the rows have not moved (`WIP`, agent-shrink-control, 2026-08-18).**
`real: axiom=30` is unchanged and I did not force it down — "what stops it"
below is the finding.

**The specification, measured rather than asserted.** ADR-0509 says the
30-binder telescope "is the interface, assuming nothing" — true only if the
telescope read off an axiom-free development says the *same* thing as the one
read off `Real`. `examples/ring_interface_pin.rs` compares them: **30 binders,
30 identical, 0 differing**, so the ledger's 30 SHA-256 type pins can be carried
by a development whose trusted surface is `0`. The gate fails on a mutated
subject: transposing `le_refl`/`le_trans` in `From<IntPrelude>` gives `28
identical, 2 differing`, exit 1 — the transposition an earlier lane found no
test could see.

**The control cannot be shrunk; it has to be inverted.** `Real` is an *opaque*
carrier, so nothing over it is definable and every law must be assumed — the
floor is the whole signature. `build_control_carrier` goes the other way: the
axiom-free `Int` development with exactly **one** deliberate axiom, typed as
`Int.lt_irrefl`, the step every Farkas chain ends on. Measured: the control run
reaches `["axeyum.control.assumed_lt_irrefl"]`, the same refutation over
untouched ℤ reaches `[]`. Three mutations, one test dead each. The control axiom
is **provably redundant** — discharged by a footprint-empty theorem in the same
environment, which `Real`'s relatively-consistent 30 are not.

**What stops the retirement, and it is not mathematics.** `build_arith_prelude`
must go before rows can retire; blocked on the three relative-consistency models
(`int`/`rat`/`creal`) re-expressed as telescope instantiations with two standing
facts riding on them, a new home for `arith_prelude_builds()`, and the ledger's
own control — its population must go `real: 30` → `control: 1` in **one**
change, since landing the control as a new row first publishes a trusted surface
of **31**. 29 `.rs` files name the package.
[Notes](docs/plan/notes/66-shrink-control.md).

**The split module layout lands, additive, and it found two theorems Lean
refuses** (`WIP`, prelude-module, 2026-08-18). Over the constructed reals a
refutation's Lean module is 1,304,276 bytes of which the theorem term is 4,193 —
0.16%. `Kernel::render_lean_prelude_module` emits the development once,
`render_lean_module_compact_importing` renders a query module that `import`s it:
**5,056 / 14,567 / 1,954 B** on the three front-door fixtures (**257x / 91x /
738x**), one 1,715,764-byte shared module byte-identical across all three.
Handed to the pinned Lean 4.30.0 it compiles in 14.4 s to a 3,786,256-byte
`.olean`, after which the query module checks in **0.102 s** and reports the
query's own three hypotheses and no carrier axiom.

The cost is stated, not hidden: the split is a **strictly weaker artefact** — a
single file needs `lean Query.lean`, this needs the prelude on `LEAN_PATH` and
`--root` is not optional. The recipe is generated by
`LeanPreludeModule::check_script` and is what the gate runs, with a
no-`LEAN_PATH` refusal so "Lean accepted it" cannot mean the import did nothing.
`prove_unsat_to_lean_module` is unchanged; `front_door_carrier
--require-axiom-free` still exits 0 and the Lean gate is **18 suites / 466
checks (floor 208 -> 212)**, `lean_crosscheck` 77 of 77.

**The finding.** Rooting the shared module at the whole carrier context emits a
file Lean REFUSES, at `CReal.Equiv.not_zero_one` and `CReal.not_le_one_zero`,
which this kernel admits. They had never been in an emitted module — the
renderer has always emitted only the reachable slice, so 122 of the carrier's
465 declarations had never been handed to any Lean. Not a rendering artefact:
reproduced with the sharing pass off, and `maxHeartbeats 0` does not move it.
**That belongs to the constructed-real lane and is not fixed here.** The root
set is the reached union (343 of 465) instead.

ADR-0511. Detail in [`../notes/67-prelude-module.md`](docs/plan/notes/67-prelude-module.md).

**Do not flip the default: every `.lean` artefact this repository SHIPS already
elaborates clean under `theorem`** (`DONE`, theorem-opacity, 2026-08-18).
ADR-0517 measured that re-spelling proofs as `def` makes Lean's elaborator take
the whole constructed-real carrier, and left the change untaken. Built as
`Kernel::set_render_proofs_as_def` — a `Kernel` field, off by default — and
measured on the pin (Lean 4.30.0 `d024af09`): the single-file front door
(1,304,276 B) and the shared half (1,300,891 B) **both exit 0 today**, at 9.3 s
and 9.7 s; under `def` they still exit 0, at 14.9 s and 13.2 s. Only the
whole-carrier module gains — 4 refusals to none — and ADR-0511 does not ship it,
while Lean's *kernel* already accepts it in 1.4 s. So the switch costs 1.36–1.69x
elaboration and 212 lines of "this is a proof" to fix a refusal no shipped
artefact suffers. `#print axioms` reads the same either way, so soundness is not
in play; ADR-0458's honesty argument is what decides it. Decision:
[ADR-0518](docs/research/09-decisions/adr-0518-proofs-stay-spelled-theorem-and-the-def-option-is-a-measuring-instrument.md);
numbers: [notes](docs/plan/notes/68-theorem-opacity.md).

**ADR-0517's blast-radius argument was narrower than stated.** "18 real-Lean
suites read the single-file front door" — they assert on the module's ROOT
theorem, which this option deliberately leaves alone, so they are indifferent to
it. The option's boundaries are pinned by 7 tests, mutation-checked 1/1/1/1/2.

**Nothing that ships moved.** The default path is byte-identical (the carrier
renders at 2,541,928 B, ADR-0517's figure to the byte),
`front_door_carrier --require-axiom-free` still reports
`the module's axiom lines equal the kernel footprint: true`, and
`scripts/check-lean-gate.sh` is **OK at 472 real-Lean checks** (floor 218),
`lean_crosscheck` 77 of 77.

**Next**: a structurally recursive `Nat.gcd`. It closes the same elaborator gap
from the other end, with no keyword change and no elaboration cost, and it is
now the preferred route to the residue ADR-0517 named.

**ADR-0519: `CReal.max`, `CReal.min` and `CReal.abs` are BUILT, and they cost
no index shift (`WIP`, agent-creal-order, 2026-08-19).**
`max` looks like it needs a decision, and ℝ has none — but it does not have to
be *derived* from one. `Rat.le a b` **is** `Int.le (num a·den b) (num b·den a)`,
so `Rat.max` dispatches by `Int.rec` on the sign of the cross-difference, where
the sign is a **constructor**; one `Rat.max_cases` carries every lattice law and
there is exactly one `Int.rec` in the module. And `Rat.sub_max_le` — joint
one-Lipschitz-ness — means `max` does not degrade the modulus, so `CReal.max`
samples at the **same** index as its arguments: the first operation since
`CReal.neg` that costs no shift. The same lemma with the `Equiv` hypotheses in
place of the regularity facts *is* `max_congr`. `CReal.abs x := max x (neg x)`,
so it adds no sequence and no regularity obligation. **94 `CReal` declarations,
trusted surface still 0**; `Rat.abs` still does not exist. Design, the measured
mutation counts, and what is left undone with its cost:
[`../notes/creal-lattice.md`](docs/plan/notes/creal-lattice.md).

**`docs/mathematics-2026-08/` said "do not start ℝ"; ℝ and ℂ are built, and the
strand now says so without losing the argument it used to make (`WIP`,
agent-doc-mathematics, 2026-08-19).** Seven files corrected in place — old text
struck through and left visible, new text dated and sourced to a command. The
load-bearing numbers were re-measured, not copied: `nat_axiom_inventory
--include-constructed` gives `complex 0 · creal 0 · integer 0 · logic 0 · nat 0
· rat 0 · string 0 · real 30`; `creal_setoid_witness` 94 declarations;
`complex_ring_witness` 39; `nat_theorem_inventory` **139** where the strand said
106; `int_theorem_inventory` 57 derived / 0 asserted; 340 facts (120 settled),
523 ADRs.

Three corrections were not in the brief and came out of measuring. `04`'s
trusted-surface table still carried `string 1` (retired 2026-08-17, ADR-0513),
so its "total 31" is now 30 and all of it ℝ. `01`'s quoted `qf_rdl_difference`
gate transcript still shows `[Real, Real.add, …]`; the shipped `Lra` route
reconstructs over `CReal` and `front_door_carrier` measures 0 carrier axioms
against 12/17/8 for the control. And `diary-real-keystone.md`'s conclusion — *"a
Cauchy-sequence construction of ℝ … is inexpressible"* — is wrong by one word:
the *quotient* is, the construction is not, which is exactly what ADR-0512
exploited. Its two measurements were right and forced the design.

`check-links.sh` green; `check-parity-docs.py` 19 errors, none in this strand
(21 at lane start, lowered by another lane).
[Notes](docs/plan/notes/doc-mathematics.md).

**`Real` -> `AxReal` (ADR-0522 step 1) turned two green assertions red and
rotted six more no validator was looking at (`WIP`, agent-axreal, 2026-08-19).**
Trusted surface unchanged and re-measured: `complex 0 · creal 0 · integer 0 ·
logic 0 · nat 0 · rat 0 · string 0 · real 30`, rows now `AxReal.*`.

**Caught.** `CReal` contains `Real`.
`the_theory_front_door_accepts_the_farkas_route` asserted
`contains("Real.add_le_add")` against a module the shipped route emits over the
CONSTRUCTED carrier — `CReal.add_le_add` satisfied it, so it could not tell the
carriers apart. `infeasibility_farkas_lean`'s "carries ordered-field content"
scan matched `ty.contains("Real.le")`, satisfied by `CReal.le`, and that example
is the checker command of the `proved` fact
`F:schedule-critical-chain-infeasible`, whose notes had transcribed the
collision as a finding. Both now name the carrier in full and stay able to
fail. Third and fourth instances of one collision; only the first was ever
noticed, and it was worked around rather than fixed.

**Broken, and the gap that hid it.** Six evidence rows on three settled facts
are `grep -E` patterns anchored on an example's stdout. `validate-facts.py` said
`340 facts, 0 errors` throughout — it never runs a `checker_command`;
`check-fact-evidence-replay.sh` is the gate that does. One of the six asserts a count of **zero** and so survived the rename by
going vacuous. All 18 rows on the affected facts re-run clean after the fix.

**A rename is not a retirement, so the ledger got a verb for it.**
`--accept-population-change` would have dropped 30 rows to `unclassified` and
filed them as retired — a 30-row reduction that never happened.
`--accept-rename OLD=NEW` re-keys live rows, carries their classification, and
takes type and digest from the measurement: `rows=30`, `retired=35`,
`unclassified=0`. Three guards, each mutation-checked to kill one test.

**Measured.** kernel `--lib` 393; solver `--lib --features full` 1223; the
three carrier examples green with controls non-vacuous (12/17/8 carrier axioms
over `AxReal` against 0 over `CReal`); ledger `--check`, golden pins, clippy on
STABLE (609/609) and rustdoc green. **Next:** ADR-0522 step 2.
[Notes](docs/plan/notes/71-axreal.md).

**66 instances were recording the weaker of two true statements, 4 more were
recording nothing at all, and the converse number could not be read** (`WIP`,
binding-tail, 2026-08-18).

Gate line, `python3 scripts/check-lra-hypothesis-binding.py` (~35 s), before →
after:

    instances=135 | structural=95  | anchored=10 | attested=9 | failures=0
    spine_assertions=541 | represented_assertions=296

    instances=135 | structural=102 | structural_anchored=66 | anchored=73
    anchored_nodes=1098 | attested=5 | failures=0
    spine_assertions=541 | represented_assertions=296 | undecomposable_spine=0

**Nothing was weakened to get any of it.** Every number that moved moved because
a check was added or a statement that was already true started being recorded.

**1. The overlap was measured and it is the largest class.** `structural` and
`anchored` answer different questions and the manifests were mutually exclusive
*by construction*, so nobody had ever run both binders over both lists. Doing it:
63 of the 95 `structural` rows also anchor — their query asserts the disequality
outright instead of leaving it a congruence conclusion — and 3 of the 10
`anchored` rows also bind structurally, because `(ite true x y)` is a four-node
term of the file. The dual class is 66, larger than the other three together.

The real change is not the class, it is that **every pin is now two-sided**:

    structural           binds structurally, and does NOT anchor        (32)
    structural-anchored  does BOTH                                      (66)
    anchored             anchors, and does NOT bind structurally         (7)
    attested             does NEITHER                                    (5)

Detail moved to [`../notes/92-binding-tail.md`](docs/plan/notes/92-binding-tail.md).

**Ten of the thirteen bare-leaf attestations now carry a checked anchor; three
are declined with a named reason** (`WIP`, array-anchor, 2026-08-18).

Lane `agent-attestation` left 13 `ArrayAxiom`/`TermIdentity` instances whose
whole rendered module is

    axiom axeyum.reconstruct.hyp._2 : Eq.{1} α atom._0 atom._1
    axiom axeyum.reconstruct.hyp._3 : Not (Eq.{1} α atom._0 atom._1)

— one assumed schema conclusion and one assumed disequality, over two bare
constants. `bind_structural` refuses them and is **right to**: an injective map
onto two of the query's symbols exists for any query with two symbols, so a
structural match there would be a check with no true instance. That refusal is
the guard, not the gap.

**The gap is the second axiom.** The module *assumes* `¬(lhs = rhs)` and nothing
in Lean checks that the query says so. Anchoring checks exactly that, and asks a
different question from the structural one — not "is this term in the file" but
**"do the file's own assertions FORCE this equality to be false, and is it the
only one they force that this module could stand for?"**

`forced_disequalities` reads the `.smt2` text and propagates a required truth
value down each `(assert …)`: through `not`/`and`/`or`/`=>`, through `distinct`,
and through the one-bit-vector encoding a BTOR-derived file writes Booleans in
(`(= #b1 t)`, `bvand`/`bvor`/`bvnot`, `(ite c #b1 #b0)`). It stops wherever the
value is not forced — an `or` under a true polarity, an `xor`, an n-ary `=` under
a false polarity, an `ite` without the Boolean branch pair — because each of
those entails a disjunction, not a fact.

**Uniqueness is what makes it an anchor rather than a formality, and it bites on
the very set it was built for: 3 of the 13 are refused.**
`solver__array__ext27.btor.smt2` forces four leaf disequalities (`i0≠i1`,
`v5≠v6`, `i0≠i2`, `i1≠i2`) and a bare module does not say which it means; the two
`unsat__replace_all__not-first-only` rows force none at all, their one assertion
being a forced-**true** equality whose sides the arena constant-folded — the same
rewrite residue as `ext10` and `redand-eliminate`. Those three stay attested.

Detail moved to [`../notes/93-array-anchor.md`](docs/plan/notes/93-array-anchor.md).

**Yes, for 95 of the 124 — it was how the emitter was written, and both the
emitter and a checker that can fail have landed** (`WIP`, attestation,
2026-08-18).

Lane `agent-binding-coverage` measured that 124 of the corpus's 270 rendered
Lean modules transcribe nothing: their entire vocabulary is
`α atom._N func._N Eq.{1} Not And`, a fresh vocabulary with no declared
relationship to any query symbol. It was right not to "cover" them. The
question this lane took is the next one: **is that abstraction necessary, or is
it how the emitter was written?** Measured per route, it is both, and the split
is sharp.

| n | route | why the module said nothing | now |
| --- | --- | --- | --- |
| 89 | `ArrayAxiom` | the emitter collapsed each whole term into ONE opaque constant | **structural**, checked |
| 6 | `QfAbv`, `QfUf` | nothing — they were structural all along, and were misfiled | **structural**, checked |
| 13 | `ArrayAxiom`, `TermIdentity` | both sides genuinely are bare query leaves | attested |
| 9 | `Sos` | the real reconstructor declined and a `prop._0` wrapper fired | attested |
| 4 | `FiniteArrayExtensionality` | the same nothing, under a conjunction | attested |
| 2 | `ArrayAxiom` | the rendered term is the output of a **rewrite** | attested |
| 1 | `ArrayAxiom` | *self-refuting* — its `False` needed no hypothesis | **declines** |

Detail moved to [`../notes/94-attestation.md`](docs/plan/notes/94-attestation.md).

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

> **SUPERSEDED 2026-08-18 by lane `agent-attestation`.** The 124 were not one
> class. Decomposed per route, **89 `ArrayAxiom` modules said nothing because of
> how the emitter was written** — `array_axiom_term_expr` collapsed each whole
> term into a single opaque constant keyed by arena index, though the certificate
> carried the query's own `TermId`s all along, and the trees are 10 nodes at the
> median. A test now pins the defect that hid behind it: read-over-write and
> select-over-ite rendered **the same module, byte for byte**. Six more
> (`QfAbv`/`QfUf`) were structural all along and merely misfiled.
>
> Current gate line: `structural=95 attested=28 attested_vacuous=0`. The
> **self-refuting** instance was a real bug — `conflicting_bool_negation_equalities`
> returned the pair `(p, p)` for `(not (not (= p (not p))))`, a *Boolean*
> conflict where no honest pair exists — and the route now declines it, which
> re-running the search could never have caught. The query is still `unsat` via
> `TermLevelEnum`, `certified=1`.
>
> `structural` is deliberately weaker than `bound`: for 89 of 105 queries no
> assertion says `¬(lhs = rhs)`, because the hypothesis is a congruence
> *conclusion*. Binding those to an assert line would be a check with no true
> instance — so they get their own verdict, and an anti-absorption guard **fails**
> if an instance pinned `attested` can be related to its query, which is exactly
> the silent lie that had already happened to those six.
| **declined** | 21 | neither — named, not pinned, not checked |

Detail moved to [`../notes/95-binding-coverage.md`](docs/plan/notes/95-binding-coverage.md).

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

Detail moved to [`../notes/96-transcription-binding.md`](docs/plan/notes/96-transcription-binding.md).

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

Detail moved to [`../notes/98-evidence-certification.md`](docs/plan/notes/98-evidence-certification.md).

**Open queue, in the order I intend to clear it** (`WIP`,
capability-assurance, 2026-08-20). Items that clear themselves are struck rather
than carried — a queue listing resolved work is the same defect as stale prose.

1. ~~`hooks/pre-push` runs `cargo test -p axeyum-lean-kernel` WHOLESALE~~ —
   **cleared 2026-08-20.** The Lean-prelude suites moved to `just check`, which
   already owned them and which gates a different property; the hook went
   **630 s → 130 s**. It also gained `cargo check --all-targets` (not
   `--workspace`, which does not compile the bench examples and let me break
   `main`) and a route-agreement step.
2. **One guard in `check-lra-hypothesis-binding.py:1244` measurably SURVIVES**
   (`bind_structural`'s opaque-sort check). Needs a control in
   `102-attestation-gap`'s test module; the mutation harness reports it rather
   than the harness having been wrong.
Items 3-4 (the 404 GB target-dir relocation, scheduled because it forces one
cold rebuild; and registering a heavy-cargo suite with the mutation harness)
are in [the lane note](docs/plan/notes/99-capability-assurance.md).

Cleared by their owners since this list was written: `103-creal-lean-divergence.md`
is under the ceiling (2,958 B), and `PLAN.md` now records the 11 -> 10 ledger
guard-count correction rather than publishing the wrong number.

**`gen-adr-index.py --check-remote` detects an ADR number two checkouts both
claimed, before merge (`DONE`, agent-adr-numbering, 2026-08-18).** `--check`
only ever reads this working tree, so it could not see `origin/main` reusing
0471-0474 (fixed earlier today, `61906c585`/`cd19e54ea`) — and while building
this gate, it found the SAME defect had already recurred: 0468-0470 are ALSO
claimed twice, live, right now. `--check-remote` diffs local `adr-NNNN-*.md`
filenames against `--remote-ref`'s (default `origin/main`) tree via `git
ls-tree`; a number where each side has a file the other lacks is a collision,
reported with the exact files and the next free number.

Deliberate, documented trade: an unresolvable ref (no fetch, no `origin`)
**SKIPs, exit 0** — failing closed would redden every offline lane for a
reason no code fixes. A resolvable-but-stale ref (`.git/FETCH_HEAD` older than
`--max-staleness-hours`, default 24) downgrades a CLEAN result to ADVISORY,
still exit 0 by default (`--require-fresh` makes it exit 1) — a clean verdict
on stale data is confidently wrong, which CLAUDE.md rates worse than no check.
A COLLISION found on stale data is never forgiven by either mode.

Wired last in `just check`'s dependency list and beside `adr-index` in
`check.sh` (see comments at both sites for why "last" matters for `just`
specifically). 6 new guards, each mutation-verified to kill EXACTLY one test
(`python3 scripts/tests/mutation_controls.py adr-index` — all green).

**Left undone, on purpose:** did not renumber the live 0468-0470 collision.
Fixing it means touching ~50 files (facts, plan docs, rustdoc, `.rs` source)
the same way 471-474 was fixed, and several of those files
(`crates/axeyum-solver/src/reconstruct/arithmetic/ordered_ring.rs` and its
tests) had another lane's uncommitted WIP in them at the time — editing them
was off-limits per CLAUDE.md's multi-agent rules. **Consequence: `just check`
and `./scripts/check.sh` are RED on this branch right now**, on the new
`adr-remote-collisions` step, for a real and correctly-reported reason. Detail
and full demo transcripts in
[`../notes/agent-adr-numbering.md`](docs/plan/notes/agent-adr-numbering.md).

**The module banner is out of the golden pins, and the golden suites have a
gate** (`WIP`, agent-golden-pins, 2026-08-18). Three commits in four days
changed the fixed banner every rendered Lean module opens with, re-pinned only
the golden that sat in a gate, and shipped the same delta red onto the rest
(`0fc7cc357`; `b760fd6ae` +863; `46724faec` +777). Two things were wrong and
both are fixed:

1. **the pins covered the banner.** `axeyum_lean_kernel::split_module_banner`
   plus `tests/support/lean_golden.rs` pin the module **body**; the helper still
   refuses a source that does not open with this kernel's banner byte for byte.
   The banner has one pin of its own, as committed text
   (`axeyum-lean-kernel --test module_banner_pin`, blessed by the same
   `AXEYUM_BLESS_LEAN_FIXTURES=1` as the 17 module fixtures). A header change
   now fails one named thing and its failure is a header diff.
2. **nothing ran the suites.** `scripts/check-lean-golden-pins.sh` **discovers**
   membership (a suite is in the gate exactly when it calls
   `assert_golden_module`) and refuses a hand-rolled whole-module `(len, fnv1a)`
   pin, so a new golden cannot be added outside the gate. Wired into `just
   check` and `scripts/check.sh` (both, keeping `check-aggregate-scope` clean)
   and diff-scoped into `hooks/pre-push` on `axeyum-lean-kernel/src/**` — the
   origin of all three recurrences.

Measured at `760befd16` in a clean lane snapshot: gate 6 suites / 33 tests, 35 s
wall warm (0 s on a push that does not touch the kernel); every pin moved by
exactly 2,122 bytes and nothing else; stable clippy, `fmt --check`,
`rustdoc -D warnings` and `check-aggregate-scope` all clean; seven guards, each
deleted in turn and each killing **exactly one** control.

Membership measured, not guessed: **five** suites, the four that failed plus
`diophantine_lean_reconstruct`. The four candidates in the brief's regex are all
false positives (`specs.len() == 720`, `== 640`, corpus population `226`,
`outer_bindings.len() == 318`) — element counts, not module bytes. Detail and
the full measurement table: [`../notes/agent-golden-pins.md`](docs/plan/notes/agent-golden-pins.md).

**A mutant that did not compile was scored as coverage** (`WIP`,
agent-mutation-harness, 2026-08-18). Measured against `mutation_controls.py` as
it stood: replacing `if len(unchecked) > ceiling:` with `if len(unchecked) > >
ceiling:` printed **`killed 0`** and counted the guard as tested. So did a suite
that executed zero tests — the `#![cfg(feature = "full")]` trap. Both push in the
unsafe direction, and every "exactly one test died" in this repository rests on
the mutant having been built and run.

Only `killed N` and `SURVIVED` are now measurements; `DID NOT BUILD`, `DID NOT
RUN`, `NOT APPLIED`, `AMBIGUOUS ANCHOR` and `INCONSISTENT` fail the run in a
**separately counted** bucket — "not tested" and "could not tell" have different
fixes. A build probe runs before any test count is believed; the two independent
kill counts (headers, summary) must agree with each other and the exit status;
collection size must match the baseline. A `cargo` runner covers the route the
defect was reported on.

`self-demo` produces one of each of the four outcomes from a real mutation and
fails unless the harness names all four; wired into `just check` and `check.sh`.
The harness is mutation-checked against itself (24 guards / 31 controls): first
run **21 killed, 3 SURVIVED**, all three real; now **24/24**.

Two findings in existing suites. The ambiguous-anchor check found **two dead
controls** in `lra-hypothesis-binding` (one mutating the same copy another
control already drove); repaired, 53/53. And `lean-axiom-ledger` — the control
over the axiom ledger, i.e. the axiom-freedom claim — was recorded as *11 guards,
no survivors* when it is **10**: its eleventh mutation sabotages the fixture, so
the suite ran **zero** tests and the old classifier read the non-zero exit as a
death. Removed with the reasoning in place; 10/10.

Detail: [`../notes/agent-mutation-harness.md`](docs/plan/notes/agent-mutation-harness.md).

**Two of the three string-length certificates now carry a Lean term real Lean 4
accepts; the third declines for two independent reasons, and the guard that was
supposed to catch the second admitted it** (`WIP`, string-recon, 2026-08-20).

`Evidence::UnsatStringLength` was rung 2 of the ladder — a certificate an
independent checker re-derives, with nothing kernel-checked behind it.
`reconstruct_string_length` builds the term for the **conjunctive** case over
the constructed integers (`try_new_over_integers`; `integer: axiom=0`), not
`AxReal` and not `CReal`: lengths and code points are integers, and `ℤ` models
every law a Farkas combination uses.

Measured over the 217 committed `QF_S`/`QF_SLIA`/`QF_SEQ` files: 3 certificates,
**2 reconstructed** — `r0_QF_SLIA_str004.smt2` and `r0_QF_S_str005.smt2`, taking
different engines (strict / non-strict), both accepted by real Lean 4 with
`#print axioms` reporting nothing but the query's own facts and the abstraction
variables. `r1_QF_SLIA_str-code-unsat-2.smt2` declines twice over: it is a
two-arm case split (refuting one arm proves nothing, and its first arm closes on
its own, so the guard is load-bearing), and its second arm needs `10^28 −
0x2FFFF` unary `one`s.

The finding worth carrying forward is about the size guard, not the route. It
was written at `4_096` and mutating it away did not fail a test — it **aborted
the process** with a stack overflow, because the fold builds a left-nested `add`
chain the kernel walks recursively. Measured: cost 514 renders a 13.2 MB module,
cost 1026 SIGABRTs. So the guard was calibrated to admit exactly the failure it
existed to prevent, and no test could have said so, because the test only ever
exercised the decline side. **A budget needs pinning from both ends: at the
budget it must still work.**

Next: the case-split arm needs `Or.elim` in the kernel — the machinery exists
(`reconstruct_disjunctive_lra_proof`) — but it buys nothing measurable while the
only case-split corpus file also needs a `10^28` numeral. A binary numeral
development for the ordered-ring engine is the change that would move that file,
and it would also lift every other route's constant ceiling off `k` copies of
`one`.

**ADR-0521: ℂ is built, it is free, and its missing order is REFUTED rather than
omitted (`WIP`, agent-complex-foundation, 2026-08-18).** `Complex` — a
one-constructor pair of `CReal`s with equality the *defined* relation
`Complex.Equiv` — carries `zero`/`one`/`I`/`ofReal`, `add`/`neg`/`mul`/`conj`,
four congruence obligations, and **9 of 9** commutative-ring laws. Thirty-nine
named declarations, every axiom footprint empty, whole trusted surface **0**
(`Axiom` + `Opaque` + `Quotient`, not `Axiom` alone):
`cargo run -q -p axeyum-lean-kernel --example complex_ring_witness`. No
`Quot.sound`, no `funext`, no `propext`; the kernel did not change.

The other 13 of the `Real` package's 22 laws are the order laws, and they are
**not deferred**: `Complex.no_compatible_order` quantifies over both relations
and derives `False` from seven of them, with `I` as the witness through
`Complex.I_sq`. The witness also checks that `Complex.le`/`Complex.lt` are not
declared — a refutation and an omission look identical otherwise.

Next: (a) a plain-commutative-ring telescope, since ADR-0457's is parameterised
over an *ordered* ring and ℂ is not one; (b) ℚ(i) for `geometry_certify`, which
ADR-0512 deferred ℂ in favour of; (c) `CReal` completeness, which `abs`, `√` and
algebraic closure are all downstream of.

**ADR-0512 phase R2 is COMPLETE: ℝ is built, it is free, and ALL 22
ordered-commutative-ring laws hold over it (`WIP`, agent-creal-mul,
2026-08-18).** `CReal` — a Bishop setoid of regular ℚ-sequences — with `Equiv`
**reflexive, symmetric and transitive**, `zero`/`one`/`neg`/`add`/`mul`, all
five congruence obligations, the additive group, Bishop's order, the strict
order and the product. Fifty-eight declarations, every axiom footprint empty,
whole trusted surface **0**:
`cargo run -q -p axeyum-lean-kernel --example creal_setoid_witness`. No
`Quot.sound`, no `funext`, no `propext`; the kernel did not change.

Detail and older landed rows moved to [`../notes/creal.md`](docs/plan/notes/creal.md).

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
[ADR-0512](docs/research/09-decisions/adr-0512-real-is-constructed-as-a-setoid-over-the-rationals.md)
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

Detail moved to [`../notes/reals-design.md`](docs/plan/notes/reals-design.md).

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
| Public documentation and examples | `DONE`, current comprehensive pass | Public/crate/consumer/prover/curriculum/contributor front doors are indexed; all 113 Cargo examples and the consumer 48-case aggregate are guarded. Corrected built/planned, Lean 4.30/offline quotient, strings/P2.7, proof assurance, `i128` LRA/Farkas, native-CDCL/BatSat, RUP-only LRAT, online combination/fallback, CAS-local-vs-solver evidence, route-specific FP/datatype/nonlinear/quantifier boundaries, optional EVM/verifier certificate fields, and source-comment UNSAT-proof overclaims. Source-backed guards require nonzero full-feature tests across cookbook, learner, contributor, foundational-resource, and rules docs. Generated authorities remain canonical; reopen only for concrete drift. |
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
